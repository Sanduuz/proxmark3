//-----------------------------------------------------------------------------
// Copyright (C) Proxmark3 contributors. See AUTHORS.md for details.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// See LICENSE.txt for the text of the license.
//-----------------------------------------------------------------------------
// High frequency Electronic Machine Readable Travel Document commands
//-----------------------------------------------------------------------------

// This code is heavily based on mrpkey.py of RFIDIOt

#include "cmdhfemrtd.h"
#include <ctype.h>
#include "fileutils.h"              // saveFile
#include "cmdparser.h"              // command_t
#include "cmdtrace.h"               // CmdTraceList
#include "cliparser.h"              // CLIParserContext etc
#include "protocols.h"              // definitions of ISO14A/7816 protocol
#include "iso7816/apduinfo.h"       // GetAPDUCodeDescription
#include "iso7816/iso7816core.h"    // Iso7816ExchangeEx etc
#include "crypto/libpcrypto.h"      // Hash calculation (sha1, sha256, sha512), des_encrypt/des_decrypt
#include "des.h"                    // mbedtls_des_key_set_parity
#include "crapto1/crapto1.h"        // prng_successor
#include "commonutil.h"             // num_to_bytes
#include "util_posix.h"             // msclock
#include "ui.h"                     // search home directory
#include "proxgui.h"                // Picture Window
#include <mbedtls/aes.h>
#include <mbedtls/cipher.h>
#include <mbedtls/cmac.h>
#include <mbedtls/ecdh.h>
#include <mbedtls/ecp.h>

// Max file size in bytes. Used in several places.
// Average EF_DG2 seems to be around 20-25kB or so, but ICAO doesn't set an upper limit
// Iris data seems to be suggested to be around 35kB per eye (Presumably bumping up the file size to around 70kB)
// but as we cannot read that until we implement PACE, 35k seems to be a safe point.
#define EMRTD_MAX_FILE_SIZE 70000

// ISO7816 commands
#define EMRTD_P1_SELECT_BY_EF       0x02
#define EMRTD_P1_SELECT_BY_NAME     0x04
#define EMRTD_P2_PROPRIETARY        0x0C

// App IDs
#define EMRTD_AID_MRTD {0xA0, 0x00, 0x00, 0x02, 0x47, 0x10, 0x01}

#define EMRTD_KMAC_LEN              16
#define EMRTD_PACE_AES256_KEY_LEN   32
#define EMRTD_PACE_BP384_COORD_LEN  48
#define EMRTD_PACE_BP384_PUB_LEN    (1 + (2 * EMRTD_PACE_BP384_COORD_LEN))
#define EMRTD_PACE_SSC_LEN          16
#define EMRTD_PACE_PASSWORD_MRZ     0x01
#define EMRTD_PACE_PASSWORD_CAN     0x02
#define EMRTD_INS_MSE               0x22
#define EMRTD_INS_GENERAL_AUTH      0x86

// DESKey Types
static const uint8_t KENC_type[4] = {0x00, 0x00, 0x00, 0x01};
static const uint8_t KMAC_type[4] = {0x00, 0x00, 0x00, 0x02};

typedef enum {
    EMRTD_SM_NONE = 0,
    EMRTD_SM_BAC,
    EMRTD_SM_PACE_AES
} emrtd_sm_type_t;

static emrtd_sm_type_t g_emrtd_sm_type = EMRTD_SM_NONE;

/*
* BAC = Basic Access Control
* PA = Passive Authentication
* AA = Active Authentication
* EAC = Extended Access Control
* SAC = Suppliment Access Control

File structures
----------------
 Mastefile MF
  -- EF.ATR/INFO (01)
  -- EF.DIR (1E)
  -- EF.CardSecurity (1D)
  -- EF.CardAccess (1C)
  Data Files DF
    -- eMRTD Application DF (AID: )
    -- Travel Records Application DF (AID: A0 00 00 02 47 20 01)
      - EF.Certificates (1A)
      - EF.EntryRecords (01)
      - EF.ExitRecords (02)
    -- Visa Records Application DF (AID: A0 00 00 02 47 20 02)
      - EF.Certificates (1A)
      - EF.ExitRecords (03)
    -- Additional Biometrics Application DF (AID: ‘A0 00 00 02 47 20 03)
      - EF.Certificates (011A)
      - EF.Biometrics1  (0201)
      - EF.Biometrics2  (0202)
      - EF.Biometrics64 (0240)

eMRTD Application DF
-----------------------
File names and what they contain
  EG.COM = Common data
  EG.DG1 = MRZ data
  EG.DG2 = Biometric template, Photo
  EG.DG3 = Biometric template, Fingerprint (EAC / AA)
  EG.DG4 = Biometric template, Iris (EAC / AA)
  EG.DG5 = Image template
  EG.DG6 = Image template
  EG.DG7 = Image template (Signature?)
  EG.DG8 = Data Feature
  EG.DG9 = Structure Feature
  EG.DG10 = Substance Feature
  EG.DG11 = Additional personal details
  EG.DG12 = Additional Document Detail
  EG.DG13 = Optional Details
  EG.DG14 = Security Options
  EG.DG15 = AA public key
  EG.DG16 = Persons to notify
  EG.SOD = Security, signatures of all data files


*/
const char *pad = ".....................................";

static int emrtd_dump_ef_dg2(uint8_t *file_contents, size_t file_length, const char *path);
static int emrtd_dump_ef_dg5(uint8_t *file_contents, size_t file_length, const char *path);
static int emrtd_dump_ef_dg7(uint8_t *file_contents, size_t file_length, const char *path);
static int emrtd_dump_ef_sod(uint8_t *file_contents, size_t file_length, const char *path);
static int emrtd_print_ef_com_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg1_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg2_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg5_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg7_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg11_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_dg12_info(uint8_t *data, size_t datalen);
static int emrtd_print_ef_cardaccess_info(uint8_t *data, size_t datalen);
static bool emrtd_pace_aes256_cmac8(const uint8_t key[EMRTD_PACE_AES256_KEY_LEN], const uint8_t *input, size_t input_len, uint8_t mac8[8]);

typedef enum  { // list must match dg_table
    EF_COM = 0,
    EF_DG1,
    EF_DG2,
    EF_DG3,
    EF_DG4,
    EF_DG5,
    EF_DG6,
    EF_DG7,
    EF_DG8,
    EF_DG9,
    EF_DG10,
    EF_DG11,
    EF_DG12,
    EF_DG13,
    EF_DG14,
    EF_DG15,
    EF_DG16,
    EF_SOD,
    EF_CardAccess,
    EF_CardSecurity,
} emrtd_dg_enum;

typedef struct {
    const emrtd_pacealg_t *alg;
    uint8_t oid[10];
    uint8_t oidlen;
    uint8_t version;
    uint8_t parameter_id;
    bool has_parameter_id;
} emrtd_pace_info_t;

static emrtd_dg_t dg_table[] = {
//  tag    dg# fileid  filename           desc                                                  pace   eac    req    fast   parser                          dumper
    {0x60, 0,  0x011E, "EF_COM",          "Header and Data Group Presence Information",         false, false, true,  true,  emrtd_print_ef_com_info,        NULL},
    {0x61, 1,  0x0101, "EF_DG1",          "Details recorded in MRZ",                            false, false, true,  true,  emrtd_print_ef_dg1_info,        NULL},
    {0x75, 2,  0x0102, "EF_DG2",          "Encoded Face",                                       false, false, true,  false, emrtd_print_ef_dg2_info,        emrtd_dump_ef_dg2},
    {0x63, 3,  0x0103, "EF_DG3",          "Encoded Finger(s)",                                  false, true,  false, false, NULL,                           NULL},
    {0x76, 4,  0x0104, "EF_DG4",          "Encoded Eye(s)",                                     false, true,  false, false, NULL,                           NULL},
    {0x65, 5,  0x0105, "EF_DG5",          "Displayed Portrait",                                 false, false, false, false, emrtd_print_ef_dg5_info,        emrtd_dump_ef_dg5},
    {0x66, 6,  0x0106, "EF_DG6",          "Reserved for Future Use",                            false, false, false, false, NULL,                           NULL},
    {0x67, 7,  0x0107, "EF_DG7",          "Displayed Signature or Usual Mark",                  false, false, false, false, emrtd_print_ef_dg7_info,        emrtd_dump_ef_dg7},
    {0x68, 8,  0x0108, "EF_DG8",          "Data Feature(s)",                                    false, false, false, true,  NULL,                           NULL},
    {0x69, 9,  0x0109, "EF_DG9",          "Structure Feature(s)",                               false, false, false, true,  NULL,                           NULL},
    {0x6a, 10, 0x010A, "EF_DG10",         "Substance Feature(s)",                               false, false, false, true,  NULL,                           NULL},
    {0x6b, 11, 0x010B, "EF_DG11",         "Additional Personal Detail(s)",                      false, false, false, true,  emrtd_print_ef_dg11_info,       NULL},
    {0x6c, 12, 0x010C, "EF_DG12",         "Additional Document Detail(s)",                      false, false, false, true,  emrtd_print_ef_dg12_info,       NULL},
    {0x6d, 13, 0x010D, "EF_DG13",         "Optional Detail(s)",                                 false, false, false, true,  NULL,                           NULL},
    {0x6e, 14, 0x010E, "EF_DG14",         "Security Options",                                   false, false, false, true,  NULL,                           NULL},
    {0x6f, 15, 0x010F, "EF_DG15",         "Active Authentication Public Key Info",              false, false, false, true,  NULL,                           NULL},
    {0x70, 16, 0x0110, "EF_DG16",         "Person(s) to Notify",                                false, false, false, true,  NULL,                           NULL},
    {0x77, 0,  0x011D, "EF_SOD",          "Document Security Object",                           false, false, false, false, NULL,                           emrtd_dump_ef_sod},
    {0xff, 0,  0x011C, "EF_CardAccess",   "PACE SecurityInfos",                                 true,  false, true,  true,  emrtd_print_ef_cardaccess_info, NULL},
    {0xff, 0,  0x011D, "EF_CardSecurity", "PACE SecurityInfos for Chip Authentication Mapping", true,  false, false, true,  NULL,                           NULL},
    {0x00, 0,  0, NULL, NULL, false, false, false, false, NULL, NULL}
};

// https://security.stackexchange.com/questions/131241/where-do-magic-constants-for-signature-algorithms-come-from
// https://tools.ietf.org/html/rfc3447#page-43
static emrtd_hashalg_t hashalg_table[] = {
//  name        hash func   len len descriptor
    {"SHA-1",   sha1hash,   20,  7, {0x06, 0x05, 0x2B, 0x0E, 0x03, 0x02, 0x1A}},
    {"SHA-256", sha256hash, 32, 11, {0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01}},
    {"SHA-512", sha512hash, 64, 11, {0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03}},
    {NULL,      NULL,       0,  0,  {0}}
};

static emrtd_pacealg_t pacealg_table[] = {
//  name                                       keygen descriptor
    {"DH, Generic Mapping, 3DES-CBC-CBC",      NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x01, 0x01}},
    {"DH, Generic Mapping, AES-CMAC-128",      NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x01, 0x02}},
    {"DH, Generic Mapping, AES-CMAC-192",      NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x01, 0x03}},
    {"DH, Generic Mapping, AES-CMAC-256",      NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x01, 0x04}},
    {"ECDH, Generic Mapping, 3DES-CBC-CBC",    NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x02, 0x01}},
    {"ECDH, Generic Mapping, AES-CMAC-128",    NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x02, 0x02}},
    {"ECDH, Generic Mapping, AES-CMAC-192",    NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x02, 0x03}},
    {"ECDH, Generic Mapping, AES-CMAC-256",    NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x02, 0x04}},
    {"DH, Integrated Mapping, 3DES-CBC-CBC",   NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x03, 0x01}},
    {"DH, Integrated Mapping, AES-CMAC-128",   NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x03, 0x02}},
    {"DH, Integrated Mapping, AES-CMAC-192",   NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x03, 0x03}},
    {"DH, Integrated Mapping, AES-CMAC-256",   NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x03, 0x04}},
    {"ECDH, Integrated Mapping, 3DES-CBC-CBC", NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x04, 0x01}},
    {"ECDH, Integrated Mapping, AES-CMAC-128", NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x04, 0x02}},
    {"ECDH, Integrated Mapping, AES-CMAC-192", NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x04, 0x03}},
    {"ECDH, Integrated Mapping, AES-CMAC-256", NULL, {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x04, 0x04}},
    {NULL, NULL, {0}}
};

static emrtd_pacesdp_t pacesdp_table[] = {
//   id  name                                                     size
    {0,  "1024-bit MODP Group with 160-bit Prime Order Subgroup", 1024},
    {1,  "2048-bit MODP Group with 224-bit Prime Order Subgroup", 2048},
    {2,  "2048-bit MODP Group with 256-bit Prime Order Subgroup", 2048},
    {8,  "NIST P-192 (secp192r1)",                                192},
    {10, "NIST P-224 (secp224r1)",                                224},
    {12, "NIST P-256 (secp256r1)",                                256},
    {15, "NIST P-384 (secp384r1)",                                384},
    {18, "NIST P-521 (secp521r1)",                                521},
    {9,  "BrainpoolP192r1",                                       192},
    {11, "BrainpoolP224r1",                                       224},
    {13, "BrainpoolP256r1",                                       256},
    {14, "BrainpoolP320r1",                                       320},
    {16, "BrainpoolP384r1",                                       384},
    {17, "BrainpoolP521r1",                                       521},
    {32, NULL, 0}
};

static emrtd_dg_t *emrtd_tag_to_dg(uint8_t tag) {
    for (int dgi = 0; dg_table[dgi].filename != NULL; dgi++) {
        if (dg_table[dgi].tag == tag) {
            return &dg_table[dgi];
        }
    }
    return NULL;
}
static emrtd_dg_t *emrtd_fileid_to_dg(uint16_t file_id) {
    for (int dgi = 0; dg_table[dgi].filename != NULL; dgi++) {
        if (dg_table[dgi].fileid == file_id) {
            return &dg_table[dgi];
        }
    }
    return NULL;
}

static int CmdHelp(const char *Cmd);

static bool emrtd_exchange_commands(sAPDU_t apdu, bool include_le, uint16_t le, uint8_t *dataout, size_t maxdataoutlen, size_t *dataoutlen, bool activate_field, bool keep_field_on) {
    uint16_t sw;
    int res = Iso7816ExchangeEx(CC_CONTACTLESS, activate_field, keep_field_on, apdu, include_le, le, dataout, maxdataoutlen, dataoutlen, &sw);

    if (res != PM3_SUCCESS) {
        return false;
    }

    if (sw != ISO7816_OK) {
        PrintAndLogEx(DEBUG, "Command failed (%04x - %s).", sw, GetAPDUCodeDescription(sw >> 8, sw & 0xff));
        return false;
    }
    return true;
}

static int emrtd_exchange_commands_noout(sAPDU_t apdu, bool activate_field, bool keep_field_on) {
    uint8_t response[PM3_CMD_DATA_SIZE] = {0};
    size_t resplen = 0;
    return emrtd_exchange_commands(apdu, false, 0, response, 0, &resplen, activate_field, keep_field_on);
}

static char emrtd_calculate_check_digit(char *data) {
    const int mrz_weight[] = {7, 3, 1};
    int value, cd = 0;

    for (int i = 0; i < strlen(data); i++) {
        char d = data[i];
        if ('A' <= d && d <= 'Z') {
            value = d - 55;
        } else if ('a' <= d && d <= 'z') {
            value = d - 87;
        } else if (d == '<') {
            value = 0;
        } else {  // Numbers
            value = d - 48;
        }
        cd += value * mrz_weight[i % 3];
    }
    return cd % 10;
}

static int emrtd_get_asn1_data_length(uint8_t *datain, int datainlen, int offset) {
    PrintAndLogEx(DEBUG, "asn1 datalength, datain: %s", sprint_hex_inrow(datain, datainlen));
    int lenfield = (int) * (datain + offset);
    PrintAndLogEx(DEBUG, "asn1 datalength, lenfield: %02X", lenfield);
    if (lenfield <= 0x7f) {
        return lenfield;
    } else if (lenfield == 0x80) {
        // TODO: 0x80 means indeterminate, and this impl is a workaround.
        // Giving rest of the file is a workaround, nothing more, nothing less.
        // https://wf.lavatech.top/ave-but-random/emrtd-data-quirks#EF_SOD
        return datainlen;
    } else if (lenfield == 0x81) {
        int tmp = (*(datain + offset + 1));
        return tmp;
        //return ((int) * (datain + offset + 1));
    } else if (lenfield == 0x82) {
        int tmp = (*(datain + offset + 1) << 8);
        tmp |= *(datain + offset + 2);
        return tmp;
        //return ((int) * (datain + offset + 1) << 8) | ((int) * (datain + offset + 2));
    } else if (lenfield == 0x83) {
        int tmp = (*(datain + offset + 1) << 16);
        tmp |= (*(datain + offset + 2) << 8);
        tmp |= *(datain + offset + 3);
        return tmp;
        //return (((int) * (datain + offset + 1) << 16) | ((int) * (datain + offset + 2)) << 8) | ((int) * (datain + offset + 3));
    }
    return 0;
}

static int emrtd_get_asn1_field_length(uint8_t *datain, int datainlen, int offset) {
    PrintAndLogEx(DEBUG, "asn1 fieldlength, datain: %s", sprint_hex_inrow(datain, datainlen));
    int lenfield = (int) * (datain + offset);
    PrintAndLogEx(DEBUG, "asn1 fieldlength, lenfield: %02X", lenfield);
    if (lenfield <= 0x80) {
        return 1;
    } else if (lenfield == 0x81) {
        return 2;
    } else if (lenfield == 0x82) {
        return 3;
    } else if (lenfield == 0x83) {
        return 4;
    }
    return 0;
}

static size_t emrtd_tlv_put_len(uint8_t *out, size_t len) {
    if (len <= 0x7F) {
        out[0] = (uint8_t)len;
        return 1;
    }
    out[0] = 0x81;
    out[1] = (uint8_t)len;
    return 2;
}

static bool emrtd_tlv_next(const uint8_t *data, size_t datalen, size_t *offset, uint16_t *tag, const uint8_t **value, size_t *value_len) {
    if (*offset >= datalen) {
        return false;
    }

    size_t pos = *offset;
    *tag = data[pos++];
    if ((*tag & 0x1F) == 0x1F) {
        if (pos >= datalen) {
            return false;
        }
        *tag = (*tag << 8) | data[pos++];
    }

    if (pos >= datalen) {
        return false;
    }

    size_t len = data[pos++];
    if ((len & 0x80) != 0) {
        size_t lenlen = len & 0x7F;
        if (lenlen == 0 || lenlen > 2 || pos + lenlen > datalen) {
            return false;
        }
        len = 0;
        for (size_t i = 0; i < lenlen; i++) {
            len = (len << 8) | data[pos++];
        }
    }

    if (pos + len > datalen) {
        return false;
    }

    *value = data + pos;
    *value_len = len;
    *offset = pos + len;
    return true;
}

static void des3_encrypt_cbc(uint8_t *iv, uint8_t *key, uint8_t *input, int inputlen, uint8_t *output) {
    mbedtls_des3_context ctx;
    mbedtls_des3_set2key_enc(&ctx, key);

    mbedtls_des3_crypt_cbc(&ctx  // des3_context
                           , MBEDTLS_DES_ENCRYPT    // int mode
                           , inputlen               // length
                           , iv                     // iv[8]
                           , input                  // input
                           , output                 // output
                          );
    mbedtls_des3_free(&ctx);
}

static void des3_decrypt_cbc(uint8_t *iv, uint8_t *key, uint8_t *input, int inputlen, uint8_t *output) {
    mbedtls_des3_context ctx;
    mbedtls_des3_set2key_dec(&ctx, key);

    mbedtls_des3_crypt_cbc(&ctx  // des3_context
                           , MBEDTLS_DES_DECRYPT    // int mode
                           , inputlen               // length
                           , iv                     // iv[8]
                           , input                  // input
                           , output                 // output
                          );
    mbedtls_des3_free(&ctx);
}

static int pad_block(uint8_t *input, int inputlen, uint8_t *output) {
    const uint8_t padding[8] = {0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};

    memcpy(output, input, inputlen);

    int to_pad = (8 - (inputlen % 8));

    for (int i = 0; i < to_pad; i++) {
        output[inputlen + i] = padding[i];
    }

    return inputlen + to_pad;
}

static int emrtd_pad_block_len(uint8_t *input, int inputlen, uint8_t *output, size_t blocklen) {
    memcpy(output, input, inputlen);
    int to_pad = blocklen - (inputlen % blocklen);
    output[inputlen] = ISO9797_M2_PAD_BYTE;
    memset(output + inputlen + 1, 0x00, to_pad - 1);
    return inputlen + to_pad;
}

static void retail_mac(uint8_t *key, uint8_t *input, int inputlen, uint8_t *output) {
    // This code assumes blocklength (n) = 8, and input len of up to 240 or so chars
    // This code takes inspirations from https://github.com/devinvenable/iso9797algorithm3
    uint8_t k0[8];
    uint8_t k1[8];
    uint8_t intermediate[8] = {0x00};
    uint8_t intermediate_des[256];
    uint8_t block[8];
    uint8_t message[256];

    // Populate keys
    memcpy(k0, key, 8);
    memcpy(k1, key + 8, 8);

    // Prepare message
    int blocksize = pad_block(input, inputlen, message);

    // Do chaining and encryption
    for (int i = 0; i < (blocksize / 8); i++) {
        memcpy(block, message + (i * 8), 8);

        // XOR
        for (int x = 0; x < 8; x++) {
            intermediate[x] = intermediate[x] ^ block[x];
        }

        des_encrypt(intermediate_des, intermediate, k0);
        memcpy(intermediate, intermediate_des, 8);
    }


    des_decrypt(intermediate_des, intermediate, k1);
    memcpy(intermediate, intermediate_des, 8);

    des_encrypt(intermediate_des, intermediate, k0);
    memcpy(output, intermediate_des, 8);
}

static void emrtd_deskey(uint8_t *seed, const uint8_t *type, int length, uint8_t *dataout) {
    PrintAndLogEx(DEBUG, "seed.............. %s", sprint_hex_inrow(seed, 16));

    // combine seed and type
    uint8_t data[50] = { 0x00 };
    memcpy(data, seed, length);
    memcpy(data + length, type, 4);
    PrintAndLogEx(DEBUG, "data.............. %s", sprint_hex_inrow(data, length + 4));

    // SHA1 the key
    unsigned char key[64] = { 0x00 };
    sha1hash(data, length + 4, key);
    PrintAndLogEx(DEBUG, "key............... %s", sprint_hex_inrow(key, length + 4));

    // Set parity bits
    for (int i = 0; i < ((length + 4) / 8); i++) {
        mbedtls_des_key_set_parity(key + (i * 8));
    }
    PrintAndLogEx(DEBUG, "post-parity key... %s", sprint_hex_inrow(key, 20));

    memcpy(dataout, &key, length);
}

static void _emrtd_convert_fileid(uint16_t file, uint8_t *dataout) {
    dataout[0] = file >> 8;
    dataout[1] = file & 0xFF;
}

static int emrtd_select_file_by_name(uint8_t namelen, uint8_t *name) {
    return emrtd_exchange_commands_noout((sAPDU_t) {0, ISO7816_SELECT_FILE, EMRTD_P1_SELECT_BY_NAME, 0x0C, namelen, name}, false, true);
}

static int emrtd_select_file_by_ef(uint16_t file_id) {
    uint8_t data[2];
    _emrtd_convert_fileid(file_id, data);
    return emrtd_exchange_commands_noout((sAPDU_t) {0, ISO7816_SELECT_FILE, EMRTD_P1_SELECT_BY_EF, 0x0C, sizeof(data), data}, false, true);
}

static int emrtd_get_challenge(int length, uint8_t *dataout, size_t maxdataoutlen, size_t *dataoutlen) {
    return emrtd_exchange_commands((sAPDU_t) {0, ISO7816_GET_CHALLENGE, 0, 0, 0, NULL}, true, length, dataout, maxdataoutlen, dataoutlen, false, true);
}

static int emrtd_external_authenticate(uint8_t *data, int length, uint8_t *dataout, size_t maxdataoutlen, size_t *dataoutlen) {
    return emrtd_exchange_commands((sAPDU_t) {0, ISO7816_EXTERNAL_AUTHENTICATION, 0, 0, length, data}, true, length, dataout, maxdataoutlen, dataoutlen, false, true);
}

static int _emrtd_read_binary(int offset, int bytes_to_read, uint8_t *dataout, size_t maxdataoutlen, size_t *dataoutlen) {
    return emrtd_exchange_commands((sAPDU_t) {0, ISO7816_READ_BINARY, offset >> 8, offset & 0xFF, 0, NULL}, true, bytes_to_read, dataout, maxdataoutlen, dataoutlen, false, true);
}

static size_t emrtd_sm_block_len(void) {
    return g_emrtd_sm_type == EMRTD_SM_PACE_AES ? 16 : 8;
}

static size_t emrtd_sm_ssc_len(void) {
    return g_emrtd_sm_type == EMRTD_SM_PACE_AES ? EMRTD_PACE_SSC_LEN : 8;
}

static void emrtd_bump_ssc(uint8_t *ssc) {
    size_t ssc_len = emrtd_sm_ssc_len();
    PrintAndLogEx(DEBUG, "ssc-b: %s", sprint_hex_inrow(ssc, ssc_len));
    for (int i = ssc_len - 1; i >= 0; i--) {
        if ((*(ssc + i)) == 0xFF) {
            // Set anything already FF to 0, we'll do + 1 on num to left anyways
            (*(ssc + i)) = 0;
        } else {
            (*(ssc + i)) += 1;
            PrintAndLogEx(DEBUG, "ssc-a: %s", sprint_hex_inrow(ssc, ssc_len));
            return;
        }
    }
}

static bool emrtd_sm_mac(uint8_t *key, uint8_t *input, size_t inputlen, uint8_t output[8]) {
    if (g_emrtd_sm_type == EMRTD_SM_PACE_AES) {
        uint8_t padded[600] = { 0x00 };
        size_t padded_len = 0;
        uint8_t mac[16] = { 0x00 };
        AddISO9797M2Padding(padded, &padded_len, input, inputlen, 16);
        if (emrtd_pace_aes256_cmac8(key, padded, padded_len, mac) == false) {
            return false;
        }
        memcpy(output, mac, 8);
        return true;
    }

    retail_mac(key, input, inputlen, output);
    return true;
}

static bool emrtd_sm_iv(uint8_t *kenc, uint8_t *ssc, uint8_t iv[16]) {
    memset(iv, 0x00, 16);
    if (g_emrtd_sm_type != EMRTD_SM_PACE_AES) {
        return true;
    }

    mbedtls_aes_context aes;
    int ret = 0;
    mbedtls_aes_init(&aes);
    ret = mbedtls_aes_setkey_enc(&aes, kenc, 256);
    if (ret == 0) {
        ret = mbedtls_aes_crypt_ecb(&aes, MBEDTLS_AES_ENCRYPT, ssc, iv);
    }
    mbedtls_aes_free(&aes);
    return ret == 0;
}

static bool emrtd_check_cc(uint8_t *ssc, uint8_t *key, uint8_t *rapdu, int rapdulength) {
    uint8_t k[700] = { 0x00 };
    uint8_t cc[8] = { 0x00 };
    size_t ssc_len = emrtd_sm_ssc_len();
    size_t offset = 0;
    const uint8_t *do8e = NULL;
    size_t do8e_len = 0;
    size_t klength = ssc_len;

    if (rapdulength <= 0) {
        return false;
    }
    emrtd_bump_ssc(ssc);
    memcpy(k, ssc, ssc_len);

    while (offset < (size_t)rapdulength) {
        size_t tlv_start = offset;
        uint16_t tag = 0;
        const uint8_t *value = NULL;
        size_t value_len = 0;
        if (emrtd_tlv_next(rapdu, rapdulength, &offset, &tag, &value, &value_len) == false) {
            return false;
        }
        if (tag == 0x8E) {
            do8e = value;
            do8e_len = value_len;
            break;
        }
        if (tag == 0x87 || tag == 0x99) {
            size_t tlv_len = offset - tlv_start;
            memcpy(k + klength, rapdu + tlv_start, tlv_len);
            klength += tlv_len;
        }
    }

    if (do8e == NULL || do8e_len != 8) {
        return false;
    }

    if (emrtd_sm_mac(key, k, klength, cc) == false) {
        return false;
    }
    PrintAndLogEx(DEBUG, "cc: %s", sprint_hex_inrow(cc, 8));
    PrintAndLogEx(DEBUG, "rapdu: %s", sprint_hex_inrow(rapdu, rapdulength));
    PrintAndLogEx(DEBUG, "rapdu mac: %s", sprint_hex_inrow(do8e, do8e_len));
    PrintAndLogEx(DEBUG, "k: %s", sprint_hex_inrow(k, klength));

    return memcmp(cc, do8e, 8) == 0;
}

static bool emrtd_secure_select_file(uint8_t *kenc, uint8_t *kmac, uint8_t *ssc, uint8_t p1, uint8_t p2, const uint8_t *select_data, size_t select_data_len) {
    uint8_t response[PM3_CMD_DATA_SIZE] = { 0x00 };
    size_t resplen = 0;
    size_t block_len = emrtd_sm_block_len();
    size_t ssc_len = emrtd_sm_ssc_len();

    uint8_t iv[16] = { 0x00 };
    uint8_t cmd[16] = { 0x00 };
    uint8_t data[64] = { 0x00 };
    uint8_t encrypted[32] = { 0x00 };
    uint8_t do87[36] = { 0x00 };
    uint8_t m[64] = { 0x00 };
    uint8_t n[96] = { 0x00 };
    uint8_t temp[16] = {0x0c, ISO7816_SELECT_FILE, p1, p2};
    size_t do87len = 0;
    size_t do87valuelen = 0;

    int cmdlen = emrtd_pad_block_len(temp, 4, cmd, block_len);
    int datalen = emrtd_pad_block_len((uint8_t *)select_data, select_data_len, data, block_len);
    PrintAndLogEx(DEBUG, "cmd: %s", sprint_hex_inrow(cmd, cmdlen));
    PrintAndLogEx(DEBUG, "data: %s", sprint_hex_inrow(data, datalen));

    emrtd_bump_ssc(ssc);
    if (emrtd_sm_iv(kenc, ssc, iv) == false) {
        return false;
    }

    if (g_emrtd_sm_type == EMRTD_SM_PACE_AES) {
        if (aes256_encode(iv, kenc, data, encrypted, datalen) != PM3_SUCCESS) {
            return false;
        }
    } else {
        des3_encrypt_cbc(iv, kenc, data, datalen, encrypted);
    }
    PrintAndLogEx(DEBUG, "encrypted: %s", sprint_hex_inrow(encrypted, datalen));

    do87[do87len++] = 0x87;
    do87valuelen = datalen + 1;
    do87len += emrtd_tlv_put_len(do87 + do87len, do87valuelen);
    do87[do87len++] = 0x01;
    memcpy(do87 + do87len, encrypted, datalen);
    do87len += datalen;
    PrintAndLogEx(DEBUG, "do87: %s", sprint_hex_inrow(do87, do87len));

    memcpy(m, cmd, cmdlen);
    memcpy(m + cmdlen, do87, do87len);
    PrintAndLogEx(DEBUG, "m: %s", sprint_hex_inrow(m, cmdlen + do87len));

    memcpy(n, ssc, ssc_len);
    memcpy(n + ssc_len, m, cmdlen + do87len);
    PrintAndLogEx(DEBUG, "n: %s", sprint_hex_inrow(n, ssc_len + cmdlen + do87len));

    uint8_t cc[8];
    if (emrtd_sm_mac(kmac, n, ssc_len + cmdlen + do87len, cc) == false) {
        return false;
    }
    PrintAndLogEx(DEBUG, "cc: %s", sprint_hex_inrow(cc, 8));

    uint8_t do8e[10] = {0x8E, 0x08};
    memcpy(do8e + 2, cc, 8);
    PrintAndLogEx(DEBUG, "do8e: %s", sprint_hex_inrow(do8e, 10));

    int lc = do87len + 10;
    PrintAndLogEx(DEBUG, "lc: %i", lc);

    memcpy(data, do87, do87len);
    memcpy(data + do87len, do8e, 10);
    PrintAndLogEx(DEBUG, "data: %s", sprint_hex_inrow(data, lc));

    uint16_t sw = 0;
    int res = Iso7816ExchangeEx(CC_CONTACTLESS, false, true, (sAPDU_t) {0x0C, ISO7816_SELECT_FILE, p1, p2, lc, data}, true, 0, response, sizeof(response), &resplen, &sw);
    if (res != PM3_SUCCESS || sw != ISO7816_OK) {
        PrintAndLogEx(WARNING, "Secure SELECT p1/p2 %02X/%02X status.. " _YELLOW_("%04X") " (%s)", p1, p2, sw, GetAPDUCodeDescription(sw >> 8, sw & 0xff));
        return false;
    }

    if (emrtd_check_cc(ssc, kmac, response, resplen) == false) {
        PrintAndLogEx(WARNING, "Secure SELECT response MAC check failed.");
        return false;
    }
    return true;
}

static bool emrtd_secure_select_file_by_name(uint8_t *kenc, uint8_t *kmac, uint8_t *ssc, uint8_t namelen, uint8_t *name) {
    return emrtd_secure_select_file(kenc, kmac, ssc, EMRTD_P1_SELECT_BY_NAME, EMRTD_P2_PROPRIETARY, name, namelen);
}

static bool emrtd_secure_select_file_by_ef(uint8_t *kenc, uint8_t *kmac, uint8_t *ssc, uint16_t file) {
    uint8_t file_id[2] = { 0x00 };
    _emrtd_convert_fileid(file, file_id);
    return emrtd_secure_select_file(kenc, kmac, ssc, EMRTD_P1_SELECT_BY_EF, EMRTD_P2_PROPRIETARY, file_id, sizeof(file_id));
}

static bool _emrtd_secure_read_binary(uint8_t *kmac, uint8_t *ssc, int offset, int bytes_to_read, uint8_t *dataout, size_t maxdataoutlen, size_t *dataoutlen) {
    size_t block_len = emrtd_sm_block_len();
    size_t ssc_len = emrtd_sm_ssc_len();
    uint8_t cmd[16] = { 0x00 };
    uint8_t data[32] = { 0x00 };
    uint8_t temp[16] = {0x0c, 0xb0};

    PrintAndLogEx(DEBUG, "kmac: %s", sprint_hex_inrow(kmac, g_emrtd_sm_type == EMRTD_SM_PACE_AES ? EMRTD_PACE_AES256_KEY_LEN : EMRTD_KMAC_LEN));

    // Set p1 and p2
    temp[2] = (uint8_t)(offset >> 8);
    temp[3] = (uint8_t)(offset >> 0);

    int cmdlen = emrtd_pad_block_len(temp, 4, cmd, block_len);
    PrintAndLogEx(DEBUG, "cmd: %s", sprint_hex_inrow(cmd, cmdlen));

    uint8_t do97[3] = {0x97, 0x01, bytes_to_read};

    uint8_t m[32] = { 0x00 };
    memcpy(m, cmd, cmdlen);
    memcpy(m + cmdlen, do97, 3);

    emrtd_bump_ssc(ssc);

    uint8_t n[64] = { 0x00 };
    memcpy(n, ssc, ssc_len);
    memcpy(n + ssc_len, m, cmdlen + 3);
    PrintAndLogEx(DEBUG, "n: %s", sprint_hex_inrow(n, ssc_len + cmdlen + 3));

    uint8_t cc[8] = { 0x00 };
    if (emrtd_sm_mac(kmac, n, ssc_len + cmdlen + 3, cc) == false) {
        return false;
    }
    PrintAndLogEx(DEBUG, "cc: %s", sprint_hex_inrow(cc, sizeof(cc)));

    uint8_t do8e[10] = {0x8E, 0x08};
    memcpy(do8e + 2, cc, 8);
    PrintAndLogEx(DEBUG, "do8e: %s", sprint_hex_inrow(do8e, sizeof(do8e)));

    int lc = 13;
    PrintAndLogEx(DEBUG, "lc: %i", lc);

    memcpy(data, do97, 3);
    memcpy(data + 3, do8e, 10);
    PrintAndLogEx(DEBUG, "data: %s", sprint_hex_inrow(data, lc));

    if (emrtd_exchange_commands((sAPDU_t) {0x0C, ISO7816_READ_BINARY, offset >> 8, offset & 0xFF, lc, data}, true, 0, dataout, maxdataoutlen, dataoutlen, false, true) == false) {
        return false;
    }

    return emrtd_check_cc(ssc, kmac, dataout, *dataoutlen);
}

static bool _emrtd_secure_read_binary_decrypt(uint8_t *kenc, uint8_t *kmac, uint8_t *ssc, int offset, int bytes_to_read, uint8_t *dataout, size_t *dataoutlen) {
    uint8_t response[500] = { 0x00 };
    uint8_t temp[500] = { 0x00 };
    size_t resplen = 0;
    uint8_t iv[16] = { 0x00 };

    if (_emrtd_secure_read_binary(kmac, ssc, offset, bytes_to_read, response, sizeof(response), &resplen) == false) {
        return false;
    }

    PrintAndLogEx(DEBUG, "secreadbindec, offset %i on read %i: encrypted: %s", offset, bytes_to_read, sprint_hex_inrow(response, resplen));

    size_t tlvoffset = 0;
    const uint8_t *do87 = NULL;
    size_t do87_len = 0;
    while (tlvoffset < resplen) {
        uint16_t tag = 0;
        const uint8_t *value = NULL;
        size_t value_len = 0;
        if (emrtd_tlv_next(response, resplen, &tlvoffset, &tag, &value, &value_len) == false) {
            return false;
        }
        if (tag == 0x87) {
            do87 = value;
            do87_len = value_len;
            break;
        }
    }

    if (do87 == NULL || do87_len < 2 || do87[0] != 0x01) {
        return false;
    }

    size_t encrypted_len = do87_len - 1;
    if (emrtd_sm_iv(kenc, ssc, iv) == false) {
        return false;
    }
    if (g_emrtd_sm_type == EMRTD_SM_PACE_AES) {
        if (aes256_decode(iv, kenc, (uint8_t *)do87 + 1, temp, encrypted_len) != PM3_SUCCESS) {
            return false;
        }
    } else {
        des3_decrypt_cbc(iv, kenc, (uint8_t *)do87 + 1, encrypted_len, temp);
    }

    size_t plain_len = FindISO9797M2PaddingDataLen(temp, encrypted_len);
    if (plain_len == 0 && bytes_to_read != 0) {
        return false;
    }
    if (plain_len > (size_t)bytes_to_read) {
        plain_len = bytes_to_read;
    }
    memcpy(dataout, temp, plain_len);
    PrintAndLogEx(DEBUG, "secreadbindec, offset %i on read %i: decrypted: %s", offset, bytes_to_read, sprint_hex_inrow(temp, encrypted_len));
    PrintAndLogEx(DEBUG, "secreadbindec, offset %i on read %i: decrypted and cut: %s", offset, bytes_to_read, sprint_hex_inrow(dataout, plain_len));
    *dataoutlen = plain_len;
    return true;
}

static int emrtd_read_file(uint8_t *dataout, size_t *dataoutlen, uint8_t *kenc, uint8_t *kmac, uint8_t *ssc, bool use_secure) {
    uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t tempresponse[500] = { 0x00 };
    size_t tempresplen = 0;
    int toread = 4;
    int offset = 0;

    if (use_secure) {
        if (_emrtd_secure_read_binary_decrypt(kenc, kmac, ssc, offset, toread, response, &resplen) == false) {
            return false;
        }
    } else {
        if (_emrtd_read_binary(offset, toread, response, sizeof(response), &resplen) == false) {
            return false;
        }
    }

    int datalen = emrtd_get_asn1_data_length(response, resplen, 1);
    int readlen = datalen - (3 - emrtd_get_asn1_field_length(response, resplen, 1));
    offset = 4;

    uint8_t lnbreak = 32;
    PrintAndLogEx(INFO, "." NOLF);
    while (readlen > 0) {
        toread = readlen;
        if (readlen > 118) {
            toread = 118;
        }

        if (use_secure) {
            if (_emrtd_secure_read_binary_decrypt(kenc, kmac, ssc, offset, toread, tempresponse, &tempresplen) == false) {
                PrintAndLogEx(NORMAL, "");
                return false;
            }
        } else {
            if (_emrtd_read_binary(offset, toread, tempresponse, sizeof(tempresponse), &tempresplen) == false) {
                PrintAndLogEx(NORMAL, "");
                return false;
            }
        }

        memcpy(response + resplen, tempresponse, tempresplen);
        offset += toread;
        readlen -= toread;
        resplen += tempresplen;

        PrintAndLogEx(NORMAL, "." NOLF);
        fflush(stdout);
        lnbreak--;
        if (lnbreak == 0) {
            PrintAndLogEx(NORMAL, "");
            PrintAndLogEx(INFO, "." NOLF);
            lnbreak = 32;
        }
    }
    PrintAndLogEx(NORMAL, "");

    memcpy(dataout, &response, resplen);
    *dataoutlen = resplen;
    return true;
}

static int emrtd_lds_determine_tag_length(uint8_t tag) {
    if ((tag == 0x5F) || (tag == 0x7F)) {
        return 2;
    }
    return 1;
}

static bool emrtd_lds_get_data_by_tag(uint8_t *datain, size_t datainlen, uint8_t *dataout, size_t *dataoutlen, int tag1, int tag2, bool twobytetag, bool entertoptag, size_t skiptagcount) {
    int offset = 0;
    int skipcounter = 0;

    if (entertoptag) {
        offset += emrtd_lds_determine_tag_length(*datain);
        offset += emrtd_get_asn1_field_length(datain, datainlen, offset);
    }

    while (offset < datainlen) {
        PrintAndLogEx(DEBUG, "emrtd_lds_get_data_by_tag, offset: %i, data: %X", offset, *(datain + offset));
        // Determine element ID length to set as offset on asn1datalength
        int e_idlen = emrtd_lds_determine_tag_length(*(datain + offset));

        // Get the length of the element
        int e_datalen = emrtd_get_asn1_data_length(datain + offset, datainlen - offset, e_idlen);

        // Get the length of the element's length
        int e_fieldlen = emrtd_get_asn1_field_length(datain + offset, datainlen - offset, e_idlen);

        PrintAndLogEx(DEBUG, "emrtd_lds_get_data_by_tag, e_idlen: %02X, e_datalen: %02X, e_fieldlen: %02X", e_idlen, e_datalen, e_fieldlen);

        // If the element is what we're looking for, get the data and return true
        if (*(datain + offset) == tag1 && (!twobytetag || *(datain + offset + 1) == tag2)) {
            if (skipcounter < skiptagcount) {
                skipcounter += 1;
            } else if (datainlen > e_datalen) {
                *dataoutlen = e_datalen;
                memcpy(dataout, datain + offset + e_idlen + e_fieldlen, e_datalen);
                return true;
            } else {
                PrintAndLogEx(ERR, "error (emrtd_lds_get_data_by_tag) e_datalen out-of-bounds");
                return false;
            }
        }
        offset += e_idlen + e_datalen + e_fieldlen;
    }
    // Return false if we can't find the relevant element
    return false;
}

static bool emrtd_pace_parse_info(uint8_t *cardaccess, size_t cardaccess_len, emrtd_pace_info_t *pace_info) {
    memset(pace_info, 0, sizeof(*pace_info));

    for (size_t set_index = 0;; set_index++) {
        uint8_t dataset[100] = { 0x00 };
        size_t datasetlen = 0;
        uint8_t datafromtag[100] = { 0x00 };
        size_t datafromtaglen = 0;

        if (emrtd_lds_get_data_by_tag(cardaccess, cardaccess_len, dataset, &datasetlen, 0x30, 0x00, false, true, set_index) == false) {
            return false;
        }

        if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x06, 0x00, false, false, 0) == false) {
            continue;
        }

        for (int pacei = 0; pacealg_table[pacei].name != NULL; pacei++) {
            if (datafromtaglen == sizeof(pacealg_table[pacei].descriptor) &&
                    memcmp(pacealg_table[pacei].descriptor, datafromtag, datafromtaglen) == 0) {
                pace_info->alg = &pacealg_table[pacei];
                pace_info->oidlen = datafromtaglen;
                memcpy(pace_info->oid, datafromtag, datafromtaglen);
                break;
            }
        }

        if (pace_info->alg == NULL) {
            continue;
        }

        if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x02, 0x00, false, false, 0) == false || datafromtaglen != 1) {
            memset(pace_info, 0, sizeof(*pace_info));
            continue;
        }
        pace_info->version = datafromtag[0];

        if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x02, 0x00, false, false, 1) == true && datafromtaglen == 1) {
            pace_info->parameter_id = datafromtag[0];
            pace_info->has_parameter_id = true;
        }

        return true;
    }
}

static bool emrtd_pace_mse_set_at(const emrtd_pace_info_t *pace_info, uint8_t password_ref) {
    uint8_t response[PM3_CMD_DATA_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t data[32] = { 0x00 };
    size_t datalen = 0;
    uint16_t sw = 0;

    data[datalen++] = 0x80;
    data[datalen++] = pace_info->oidlen;
    memcpy(data + datalen, pace_info->oid, pace_info->oidlen);
    datalen += pace_info->oidlen;

    data[datalen++] = 0x83;
    data[datalen++] = 0x01;
    data[datalen++] = password_ref;

    if (pace_info->has_parameter_id) {
        data[datalen++] = 0x84;
        data[datalen++] = 0x01;
        data[datalen++] = pace_info->parameter_id;
    }

    PrintAndLogEx(DEBUG, "PACE MSE:Set AT data... %s", sprint_hex_inrow(data, datalen));

    int res = Iso7816ExchangeEx(CC_CONTACTLESS, false, true, (sAPDU_t) {0x00, EMRTD_INS_MSE, 0xC1, 0xA4, datalen, data}, false, 0, response, sizeof(response), &resplen, &sw);
    if (res != PM3_SUCCESS || sw != ISO7816_OK) {
        PrintAndLogEx(WARNING, "PACE MSE:Set AT status.. " _YELLOW_("%04X") " (%s)", sw, GetAPDUCodeDescription(sw >> 8, sw & 0xff));
        return false;
    }
    return true;
}

static bool emrtd_pace_get_encrypted_nonce(uint8_t *nonce, size_t maxnonce_len, size_t *nonce_len) {
    uint8_t response[PM3_CMD_DATA_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t data[2] = {0x7C, 0x00};
    *nonce_len = 0;

    if (emrtd_exchange_commands((sAPDU_t) {0x10, EMRTD_INS_GENERAL_AUTH, 0x00, 0x00, sizeof(data), data}, true, 0, response, sizeof(response), &resplen, false, true) == false) {
        return false;
    }

    if (resplen < 4 || response[0] != 0x7C || response[2] != 0x80) {
        PrintAndLogEx(ERR, "PACE Get Nonce response did not contain encrypted nonce tag 80.");
        return false;
    }

    size_t len = response[3];
    if (len > maxnonce_len || len + 4 > resplen) {
        PrintAndLogEx(ERR, "PACE encrypted nonce is too large (%zu bytes).", len);
        return false;
    }

    memcpy(nonce, response + 4, len);
    *nonce_len = len;
    return true;
}

static bool emrtd_tlv_find_inner(const uint8_t *data, size_t datalen, uint16_t expected_tag, const uint8_t **value, size_t *value_len) {
    size_t offset = 0;
    uint16_t outer_tag = 0;
    const uint8_t *outer_value = NULL;
    size_t outer_len = 0;

    if (emrtd_tlv_next(data, datalen, &offset, &outer_tag, &outer_value, &outer_len) == false || outer_tag != 0x7C) {
        return false;
    }

    offset = 0;
    while (offset < outer_len) {
        uint16_t tag = 0;
        if (emrtd_tlv_next(outer_value, outer_len, &offset, &tag, value, value_len) == false) {
            return false;
        }
        if (tag == expected_tag) {
            return true;
        }
    }
    return false;
}

static bool emrtd_pace_general_auth(uint8_t cla, uint8_t send_tag, const uint8_t *send_value, size_t send_value_len,
                                    uint8_t expected_tag, uint8_t *recv_value, size_t max_recv_value_len, size_t *recv_value_len) {
    uint8_t response[PM3_CMD_DATA_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t inner[140] = { 0x00 };
    uint8_t data[150] = { 0x00 };
    size_t inner_len = 0;
    size_t datalen = 0;
    uint16_t sw = 0;

    *recv_value_len = 0;

    inner[inner_len++] = send_tag;
    inner_len += emrtd_tlv_put_len(inner + inner_len, send_value_len);
    memcpy(inner + inner_len, send_value, send_value_len);
    inner_len += send_value_len;

    data[datalen++] = 0x7C;
    datalen += emrtd_tlv_put_len(data + datalen, inner_len);
    memcpy(data + datalen, inner, inner_len);
    datalen += inner_len;

    int res = Iso7816ExchangeEx(CC_CONTACTLESS, false, true, (sAPDU_t) {cla, EMRTD_INS_GENERAL_AUTH, 0x00, 0x00, datalen, data}, true, 0, response, sizeof(response), &resplen, &sw);
    if (res != PM3_SUCCESS || sw != ISO7816_OK) {
        PrintAndLogEx(WARNING, "PACE General Authenticate tag %02X status.. " _YELLOW_("%04X") " (%s)", send_tag, sw, GetAPDUCodeDescription(sw >> 8, sw & 0xff));
        return false;
    }

    const uint8_t *value = NULL;
    size_t value_len = 0;
    if (emrtd_tlv_find_inner(response, resplen, expected_tag, &value, &value_len) == false) {
        PrintAndLogEx(ERR, "PACE General Authenticate response did not contain tag %02X.", expected_tag);
        return false;
    }
    if (value_len > max_recv_value_len) {
        PrintAndLogEx(ERR, "PACE General Authenticate tag %02X is too large (%zu bytes).", expected_tag, value_len);
        return false;
    }

    memcpy(recv_value, value, value_len);
    *recv_value_len = value_len;
    return true;
}

static bool emrtd_pace_sha256_kdf(const uint8_t *input, size_t input_len, uint32_t counter, uint8_t *key, size_t key_len) {
    uint8_t buf[128] = { 0x00 };
    uint8_t digest[32] = { 0x00 };

    if (input_len + 4 > sizeof(buf) || key_len > sizeof(digest)) {
        return false;
    }

    memcpy(buf, input, input_len);
    buf[input_len + 0] = (counter >> 24) & 0xFF;
    buf[input_len + 1] = (counter >> 16) & 0xFF;
    buf[input_len + 2] = (counter >> 8) & 0xFF;
    buf[input_len + 3] = counter & 0xFF;

    if (sha256hash(buf, input_len + 4, digest) != PM3_SUCCESS) {
        return false;
    }

    memcpy(key, digest, key_len);
    return true;
}

static bool emrtd_pace_aes256_ecb_decrypt(const uint8_t key[EMRTD_PACE_AES256_KEY_LEN], const uint8_t enc[16], uint8_t out[16]) {
    mbedtls_aes_context aes;
    int ret = 0;

    mbedtls_aes_init(&aes);
    ret = mbedtls_aes_setkey_dec(&aes, key, 256);
    if (ret == 0) {
        ret = mbedtls_aes_crypt_ecb(&aes, MBEDTLS_AES_DECRYPT, enc, out);
    }
    mbedtls_aes_free(&aes);
    return ret == 0;
}

static bool emrtd_pace_aes256_cmac8(const uint8_t key[EMRTD_PACE_AES256_KEY_LEN], const uint8_t *input, size_t input_len, uint8_t mac8[8]) {
    uint8_t mac[16] = { 0x00 };
    const mbedtls_cipher_info_t *cipher_info = mbedtls_cipher_info_from_type(MBEDTLS_CIPHER_AES_256_ECB);
    if (cipher_info == NULL || mbedtls_cipher_cmac(cipher_info, key, 256, input, input_len, mac) != 0) {
        return false;
    }
    memcpy(mac8, mac, 8);
    return true;
}

static bool emrtd_pace_export_pubkey(const mbedtls_ecp_group *grp, const mbedtls_ecp_point *point, uint8_t out[EMRTD_PACE_BP384_PUB_LEN]) {
    size_t out_len = 0;
    return mbedtls_ecp_point_write_binary(grp, point, MBEDTLS_ECP_PF_UNCOMPRESSED,
                                          &out_len, out, EMRTD_PACE_BP384_PUB_LEN) == 0 &&
           out_len == EMRTD_PACE_BP384_PUB_LEN;
}

static bool emrtd_pace_read_pubkey(const mbedtls_ecp_group *grp, const uint8_t *in, size_t in_len, mbedtls_ecp_point *point) {
    return in_len == EMRTD_PACE_BP384_PUB_LEN &&
           in[0] == 0x04 &&
           mbedtls_ecp_point_read_binary(grp, point, in, in_len) == 0 &&
           mbedtls_ecp_check_pubkey(grp, point) == 0;
}

static bool emrtd_pace_normalize_point(const mbedtls_ecp_group *grp, const mbedtls_ecp_point *in, mbedtls_ecp_point *out) {
    uint8_t encoded[EMRTD_PACE_BP384_PUB_LEN] = { 0x00 };
    return emrtd_pace_export_pubkey(grp, in, encoded) &&
           mbedtls_ecp_point_read_binary(grp, out, encoded, sizeof(encoded)) == 0;
}

static bool emrtd_pace_affine_add(const mbedtls_ecp_group *grp, const mbedtls_ecp_point *p, const mbedtls_ecp_point *q, mbedtls_ecp_point *r) {
    bool ok = false;
    mbedtls_mpi lambda;
    mbedtls_mpi numerator;
    mbedtls_mpi denominator;
    mbedtls_mpi inverse;
    mbedtls_mpi tmp;

    mbedtls_mpi_init(&lambda);
    mbedtls_mpi_init(&numerator);
    mbedtls_mpi_init(&denominator);
    mbedtls_mpi_init(&inverse);
    mbedtls_mpi_init(&tmp);

    if (mbedtls_mpi_cmp_mpi(&p->X, &q->X) == 0) {
        PrintAndLogEx(ERR, "PACE affine add hit unsupported point doubling/infinity case.");
        goto out;
    }

    if (mbedtls_mpi_sub_mpi(&numerator, &q->Y, &p->Y) != 0 ||
            mbedtls_mpi_mod_mpi(&numerator, &numerator, &grp->P) != 0 ||
            mbedtls_mpi_sub_mpi(&denominator, &q->X, &p->X) != 0 ||
            mbedtls_mpi_mod_mpi(&denominator, &denominator, &grp->P) != 0 ||
            mbedtls_mpi_inv_mod(&inverse, &denominator, &grp->P) != 0 ||
            mbedtls_mpi_mul_mpi(&lambda, &numerator, &inverse) != 0 ||
            mbedtls_mpi_mod_mpi(&lambda, &lambda, &grp->P) != 0) {
        goto out;
    }

    if (mbedtls_mpi_mul_mpi(&r->X, &lambda, &lambda) != 0 ||
            mbedtls_mpi_sub_mpi(&r->X, &r->X, &p->X) != 0 ||
            mbedtls_mpi_sub_mpi(&r->X, &r->X, &q->X) != 0 ||
            mbedtls_mpi_mod_mpi(&r->X, &r->X, &grp->P) != 0) {
        goto out;
    }

    if (mbedtls_mpi_sub_mpi(&tmp, &p->X, &r->X) != 0 ||
            mbedtls_mpi_mul_mpi(&tmp, &lambda, &tmp) != 0 ||
            mbedtls_mpi_sub_mpi(&r->Y, &tmp, &p->Y) != 0 ||
            mbedtls_mpi_mod_mpi(&r->Y, &r->Y, &grp->P) != 0 ||
            mbedtls_mpi_lset(&r->Z, 1) != 0) {
        goto out;
    }

    ok = mbedtls_ecp_check_pubkey(grp, r) == 0;

out:
    mbedtls_mpi_free(&tmp);
    mbedtls_mpi_free(&inverse);
    mbedtls_mpi_free(&denominator);
    mbedtls_mpi_free(&numerator);
    mbedtls_mpi_free(&lambda);
    return ok;
}

static bool emrtd_pace_encode_auth_token_input(const emrtd_pace_info_t *pace_info, const uint8_t pubkey[EMRTD_PACE_BP384_PUB_LEN],
                                               uint8_t *out, size_t max_out_len, size_t *out_len) {
    uint8_t inner[128] = { 0x00 };
    size_t inner_len = 0;
    size_t pos = 0;

    if (pace_info->oidlen > 32 ||
            1 + 2 + pace_info->oidlen + 1 + 2 + EMRTD_PACE_BP384_PUB_LEN > sizeof(inner)) {
        return false;
    }

    inner[inner_len++] = 0x06;
    inner_len += emrtd_tlv_put_len(inner + inner_len, pace_info->oidlen);
    memcpy(inner + inner_len, pace_info->oid, pace_info->oidlen);
    inner_len += pace_info->oidlen;

    inner[inner_len++] = 0x86;
    inner_len += emrtd_tlv_put_len(inner + inner_len, EMRTD_PACE_BP384_PUB_LEN);
    memcpy(inner + inner_len, pubkey, EMRTD_PACE_BP384_PUB_LEN);
    inner_len += EMRTD_PACE_BP384_PUB_LEN;

    if (inner_len + 4 > max_out_len) {
        return false;
    }

    out[pos++] = 0x7F;
    out[pos++] = 0x49;
    pos += emrtd_tlv_put_len(out + pos, inner_len);
    memcpy(out + pos, inner, inner_len);
    pos += inner_len;
    *out_len = pos;
    return true;
}

static bool emrtd_pace_is_supported_suite(const emrtd_pace_info_t *pace_info) {
    const uint8_t oid_ecdh_gm_aes_cmac_256[] = {0x04, 0x00, 0x7F, 0x00, 0x07, 0x02, 0x02, 0x04, 0x02, 0x04};
    return pace_info->oidlen == sizeof(oid_ecdh_gm_aes_cmac_256) &&
           memcmp(pace_info->oid, oid_ecdh_gm_aes_cmac_256, sizeof(oid_ecdh_gm_aes_cmac_256)) == 0 &&
           pace_info->has_parameter_id &&
           pace_info->parameter_id == 16;
}

static bool emrtd_pace_do_can_auth(const emrtd_pace_info_t *pace_info, const char *can,
                                   uint8_t ks_enc[EMRTD_PACE_AES256_KEY_LEN], uint8_t ks_mac[EMRTD_PACE_AES256_KEY_LEN]) {
    bool ok = false;
    uint8_t kpi[EMRTD_PACE_AES256_KEY_LEN] = { 0x00 };
    uint8_t enc_nonce[64] = { 0x00 };
    size_t enc_nonce_len = 0;
    uint8_t nonce[16] = { 0x00 };
    uint8_t pcd_map_pub[EMRTD_PACE_BP384_PUB_LEN] = { 0x00 };
    uint8_t icc_map_pub[EMRTD_PACE_BP384_PUB_LEN] = { 0x00 };
    size_t icc_map_pub_len = 0;
    uint8_t pcd_ka_pub[EMRTD_PACE_BP384_PUB_LEN] = { 0x00 };
    uint8_t icc_ka_pub[EMRTD_PACE_BP384_PUB_LEN] = { 0x00 };
    size_t icc_ka_pub_len = 0;
    uint8_t shared_secret[EMRTD_PACE_BP384_COORD_LEN] = { 0x00 };
    uint8_t token_input[140] = { 0x00 };
    size_t token_input_len = 0;
    uint8_t pcd_token[8] = { 0x00 };
    uint8_t icc_token[8] = { 0x00 };
    uint8_t expected_icc_token[8] = { 0x00 };
    size_t icc_token_len = 0;

    pcrypto_rng_t rng;
    mbedtls_ecp_group grp;
    mbedtls_ecp_group mapped_grp;
    mbedtls_mpi map_d;
    mbedtls_mpi ka_d;
    mbedtls_mpi one;
    mbedtls_ecp_point map_Q;
    mbedtls_ecp_point icc_map_Q;
    mbedtls_ecp_point H;
    mbedtls_ecp_point H_affine;
    mbedtls_ecp_point sG;
    mbedtls_ecp_point sG_affine;
    mbedtls_ecp_point mapped_G;
    mbedtls_ecp_point ka_Q;
    mbedtls_ecp_point icc_ka_Q;
    mbedtls_ecp_point shared_point;

    pcrypto_rng_init(&rng, (const uint8_t *)"emrtd-pace", strlen("emrtd-pace"));
    mbedtls_ecp_group_init(&grp);
    mbedtls_ecp_group_init(&mapped_grp);
    mbedtls_mpi_init(&map_d);
    mbedtls_mpi_init(&ka_d);
    mbedtls_mpi_init(&one);
    mbedtls_ecp_point_init(&map_Q);
    mbedtls_ecp_point_init(&icc_map_Q);
    mbedtls_ecp_point_init(&H);
    mbedtls_ecp_point_init(&H_affine);
    mbedtls_ecp_point_init(&sG);
    mbedtls_ecp_point_init(&sG_affine);
    mbedtls_ecp_point_init(&mapped_G);
    mbedtls_ecp_point_init(&ka_Q);
    mbedtls_ecp_point_init(&icc_ka_Q);
    mbedtls_ecp_point_init(&shared_point);

    if (rng.seeded == false) {
        PrintAndLogEx(ERR, "PACE RNG initialization failed.");
        goto out;
    }

    if (emrtd_pace_sha256_kdf((const uint8_t *)can, strlen(can), 3, kpi, sizeof(kpi)) == false) {
        PrintAndLogEx(ERR, "PACE CAN key derivation failed.");
        goto out;
    }

    if (emrtd_pace_get_encrypted_nonce(enc_nonce, sizeof(enc_nonce), &enc_nonce_len) == false || enc_nonce_len != 16) {
        PrintAndLogEx(ERR, "PACE Get Nonce failed.");
        goto out;
    }
    PrintAndLogEx(SUCCESS, "PACE encrypted nonce.... " _YELLOW_("%s"), sprint_hex_inrow(enc_nonce, enc_nonce_len));

    if (emrtd_pace_aes256_ecb_decrypt(kpi, enc_nonce, nonce) == false) {
        PrintAndLogEx(ERR, "PACE nonce decrypt failed.");
        goto out;
    }
    PrintAndLogEx(SUCCESS, "PACE nonce decrypted.... " _YELLOW_("%s"), sprint_hex_inrow(nonce, sizeof(nonce)));

    if (mbedtls_ecp_group_load(&grp, MBEDTLS_ECP_DP_BP384R1) != 0 ||
            mbedtls_ecp_group_copy(&mapped_grp, &grp) != 0 ||
            mbedtls_mpi_lset(&one, 1) != 0) {
        PrintAndLogEx(ERR, "PACE BrainpoolP384r1 setup failed.");
        goto out;
    }

    if (mbedtls_ecp_gen_keypair(&grp, &map_d, &map_Q, mbedtls_ctr_drbg_random, &rng.ctr_drbg) != 0 ||
            emrtd_pace_export_pubkey(&grp, &map_Q, pcd_map_pub) == false) {
        PrintAndLogEx(ERR, "PACE mapping key generation failed.");
        goto out;
    }

    if (emrtd_pace_general_auth(0x10, 0x81, pcd_map_pub, sizeof(pcd_map_pub), 0x82,
                                icc_map_pub, sizeof(icc_map_pub), &icc_map_pub_len) == false ||
            emrtd_pace_read_pubkey(&grp, icc_map_pub, icc_map_pub_len, &icc_map_Q) == false) {
        PrintAndLogEx(ERR, "PACE mapping public-key exchange failed.");
        goto out;
    }
    PrintAndLogEx(SUCCESS, "PACE mapping exchange... " _YELLOW_("ok"));

    if (mbedtls_ecp_mul(&grp, &H, &map_d, &icc_map_Q, mbedtls_ctr_drbg_random, &rng.ctr_drbg) != 0 ||
            emrtd_pace_normalize_point(&grp, &H, &H_affine) == false ||
            mbedtls_mpi_read_binary(&map_d, nonce, sizeof(nonce)) != 0 ||
            mbedtls_ecp_mul(&grp, &sG, &map_d, &grp.G, mbedtls_ctr_drbg_random, &rng.ctr_drbg) != 0 ||
            emrtd_pace_normalize_point(&grp, &sG, &sG_affine) == false ||
            emrtd_pace_affine_add(&grp, &sG_affine, &H_affine, &mapped_G) == false) {
        PrintAndLogEx(ERR, "PACE generic mapping failed.");
        goto out;
    }
    PrintAndLogEx(SUCCESS, "PACE generic mapping.... " _YELLOW_("ok"));

    if (mbedtls_ecp_gen_keypair_base(&grp, &mapped_G, &ka_d, &ka_Q, mbedtls_ctr_drbg_random, &rng.ctr_drbg) != 0 ||
            emrtd_pace_export_pubkey(&grp, &ka_Q, pcd_ka_pub) == false) {
        PrintAndLogEx(ERR, "PACE mapped key generation failed.");
        goto out;
    }

    if (emrtd_pace_general_auth(0x10, 0x83, pcd_ka_pub, sizeof(pcd_ka_pub), 0x84,
                                icc_ka_pub, sizeof(icc_ka_pub), &icc_ka_pub_len) == false ||
            emrtd_pace_read_pubkey(&grp, icc_ka_pub, icc_ka_pub_len, &icc_ka_Q) == false) {
        PrintAndLogEx(ERR, "PACE mapped public-key exchange failed.");
        goto out;
    }
    PrintAndLogEx(SUCCESS, "PACE key agreement...... " _YELLOW_("ok"));

    if (mbedtls_ecp_mul(&grp, &shared_point, &ka_d, &icc_ka_Q, mbedtls_ctr_drbg_random, &rng.ctr_drbg) != 0 ||
            mbedtls_mpi_write_binary(&shared_point.X, shared_secret, sizeof(shared_secret)) != 0 ||
            emrtd_pace_sha256_kdf(shared_secret, sizeof(shared_secret), 1, ks_enc, EMRTD_PACE_AES256_KEY_LEN) == false ||
            emrtd_pace_sha256_kdf(shared_secret, sizeof(shared_secret), 2, ks_mac, EMRTD_PACE_AES256_KEY_LEN) == false) {
        PrintAndLogEx(ERR, "PACE session key derivation failed.");
        goto out;
    }

    if (emrtd_pace_encode_auth_token_input(pace_info, icc_ka_pub, token_input, sizeof(token_input), &token_input_len) == false ||
            emrtd_pace_aes256_cmac8(ks_mac, token_input, token_input_len, pcd_token) == false) {
        PrintAndLogEx(ERR, "PACE terminal token calculation failed.");
        goto out;
    }

    if (emrtd_pace_general_auth(0x00, 0x85, pcd_token, sizeof(pcd_token), 0x86,
                                icc_token, sizeof(icc_token), &icc_token_len) == false ||
            icc_token_len != sizeof(icc_token)) {
        PrintAndLogEx(ERR, "PACE mutual authentication token exchange failed.");
        goto out;
    }

    if (emrtd_pace_encode_auth_token_input(pace_info, pcd_ka_pub, token_input, sizeof(token_input), &token_input_len) == false ||
            emrtd_pace_aes256_cmac8(ks_mac, token_input, token_input_len, expected_icc_token) == false) {
        PrintAndLogEx(ERR, "PACE card token calculation failed.");
        goto out;
    }

    if (memcmp(icc_token, expected_icc_token, sizeof(expected_icc_token)) != 0) {
        PrintAndLogEx(ERR, "PACE card authentication token mismatch.");
        PrintAndLogEx(DEBUG, "PACE card token......... %s", sprint_hex_inrow(icc_token, sizeof(icc_token)));
        PrintAndLogEx(DEBUG, "PACE expected token..... %s", sprint_hex_inrow(expected_icc_token, sizeof(expected_icc_token)));
        goto out;
    }

    PrintAndLogEx(SUCCESS, "PACE mutual auth........ " _GREEN_("ok"));
    ok = true;

out:
    mbedtls_ecp_point_free(&shared_point);
    mbedtls_ecp_point_free(&icc_ka_Q);
    mbedtls_ecp_point_free(&ka_Q);
    mbedtls_ecp_point_free(&mapped_G);
    mbedtls_ecp_point_free(&sG_affine);
    mbedtls_ecp_point_free(&sG);
    mbedtls_ecp_point_free(&H_affine);
    mbedtls_ecp_point_free(&H);
    mbedtls_ecp_point_free(&icc_map_Q);
    mbedtls_ecp_point_free(&map_Q);
    mbedtls_mpi_free(&one);
    mbedtls_mpi_free(&ka_d);
    mbedtls_mpi_free(&map_d);
    mbedtls_ecp_group_free(&mapped_grp);
    mbedtls_ecp_group_free(&grp);
    pcrypto_rng_free(&rng);
    memset(kpi, 0x00, sizeof(kpi));
    memset(shared_secret, 0x00, sizeof(shared_secret));
    memset(nonce, 0x00, sizeof(nonce));
    if (ok == false) {
        memset(ks_enc, 0x00, EMRTD_PACE_AES256_KEY_LEN);
        memset(ks_mac, 0x00, EMRTD_PACE_AES256_KEY_LEN);
    }
    return ok;
}

static bool emrtd_probe_pace(uint8_t *cardaccess, size_t cardaccess_len, const char *can, bool mrz_available, const char *phase,
                             uint8_t *ssc, uint8_t *ks_enc, uint8_t *ks_mac) {
    emrtd_pace_info_t pace_info;

    if (emrtd_pace_parse_info(cardaccess, cardaccess_len, &pace_info) == false) {
        PrintAndLogEx(INFO, "PACE is advertised, but no supported PACEInfo was parsed.");
        return false;
    }

    PrintAndLogEx(INFO, "PACE probe phase........ " _YELLOW_("%s"), phase);
    PrintAndLogEx(INFO, "PACE candidate.......... " _YELLOW_("%s"), pace_info.alg->name);
    if (pace_info.has_parameter_id) {
        PrintAndLogEx(INFO, "PACE parameter id....... " _YELLOW_("%u"), pace_info.parameter_id);
    }

    uint8_t password_ref = EMRTD_PACE_PASSWORD_MRZ;
    if (can != NULL && strlen(can) > 0) {
        password_ref = EMRTD_PACE_PASSWORD_CAN;
        PrintAndLogEx(INFO, "PACE password ref....... " _YELLOW_("CAN"));
    } else if (mrz_available) {
        PrintAndLogEx(INFO, "PACE password ref....... " _YELLOW_("MRZ (key derivation is not implemented yet)"));
    } else {
        PrintAndLogEx(INFO, "PACE password ref....... " _YELLOW_("MRZ (not available)"));
    }

    if (emrtd_pace_is_supported_suite(&pace_info) == false) {
        PrintAndLogEx(ERR, "PACE crypto currently supports only ECDH-GM-AES-CMAC-256 with BrainpoolP384r1.");
        return false;
    }

    if (password_ref != EMRTD_PACE_PASSWORD_CAN) {
        PrintAndLogEx(ERR, "PACE crypto currently requires `" _YELLOW_("--can <CAN>") "`.");
        return false;
    }

    if (emrtd_pace_mse_set_at(&pace_info, password_ref) == false) {
        PrintAndLogEx(ERR, "PACE MSE:Set AT failed.");
        if ((can == NULL || strlen(can) == 0) && mrz_available) {
            PrintAndLogEx(HINT, "Hint: This card may require CAN-based PACE. Retry with `" _YELLOW_("--can <CAN>") "`.");
        }
        return false;
    }

    if (emrtd_pace_do_can_auth(&pace_info, can, ks_enc, ks_mac) == false) {
        return false;
    }

    memset(ssc, 0x00, EMRTD_PACE_SSC_LEN);
    g_emrtd_sm_type = EMRTD_SM_PACE_AES;
    return true;
}

static bool emrtd_select_and_read(uint8_t *dataout, size_t *dataoutlen, uint16_t file, uint8_t *ks_enc, uint8_t *ks_mac, uint8_t *ssc, bool use_secure) {
    if (use_secure) {
        if (emrtd_secure_select_file_by_ef(ks_enc, ks_mac, ssc, file) == false) {
            PrintAndLogEx(ERR, "Failed to secure select %04X", file);
            return false;
        }
    } else {
        if (emrtd_select_file_by_ef(file) == false) {
            PrintAndLogEx(ERR, "Failed to select %04X", file);
            return false;
        }
    }

    if (emrtd_read_file(dataout, dataoutlen, ks_enc, ks_mac, ssc, use_secure) == false) {
        PrintAndLogEx(ERR, "Failed to read %04X", file);
        return false;
    }
    return true;
}

static const uint8_t jpeg_header[4] = { 0xFF, 0xD8, 0xFF, 0xE0 };
static const uint8_t jpeg2k_header[6] = { 0x00, 0x00, 0x00, 0x0C, 0x6A, 0x50 };
static const uint8_t jpeg2k_cs_header[4] = { 0xFF, 0x4F, 0xFF, 0x51 };

static int emrtd_dump_ef_dg2(uint8_t *file_contents, size_t file_length, const char *path) {
    size_t offset;
    int datalen = 0;
    char suffix[5] = { '\0' };

    // This is a hacky impl that just looks for the image header. I'll improve it eventually.
    // based on mrpkey.py
    // Note: Doing file_length - 6 to account for the longest data we're checking.
    // Checks first byte before the rest to reduce overhead
    for (offset = 0; offset < file_length - 6; offset++) {
        if (file_contents[offset] == 0xFF) {
            if (memcmp(jpeg_header, file_contents + offset, 4) == 0) {
                datalen = file_length - offset;
                strcpy(suffix, ".jpg");
                break;
            } else if (memcmp(jpeg2k_cs_header, file_contents + offset, 4) == 0) {
                datalen = file_length - offset;
                // no standardized extension for codestream data, using .jpc
                strcpy(suffix, ".jpc");
                break;
            }
        } else if (file_contents[offset] == 0x00 && memcmp(jpeg2k_header, file_contents + offset, 6) == 0) {
            strcpy(suffix, ".jp2");
            datalen = file_length - offset;
            break;
        }
    }
    // If we didn't get any data, return false.
    if (datalen == 0) {
        return PM3_ESOFT;
    }

    char *filepath = calloc(strlen(path) + 100, sizeof(char));
    if (filepath == NULL) {
        PrintAndLogEx(WARNING, "Failed to allocate memory");
        return PM3_EMALLOC;
    }

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_DG2].filename);

    saveFile(filepath, suffix, file_contents + offset, datalen);

    free(filepath);
    return PM3_SUCCESS;
}

static int emrtd_dump_ef_dg5(uint8_t *file_contents, size_t file_length, const char *path) {
    uint8_t data[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t datalen = 0;

    // If we can't find image in EF_DG5, return false.
    if (emrtd_lds_get_data_by_tag(file_contents, file_length, data, &datalen, 0x5F, 0x40, true, true, 0) == false) {
        return PM3_ESOFT;
    }

    if (datalen < EMRTD_MAX_FILE_SIZE) {
        char *filepath = calloc(strlen(path) + 100, sizeof(char));
        if (filepath == NULL) {
            PrintAndLogEx(WARNING, "Failed to allocate memory");
            return PM3_EMALLOC;
        }
        strcpy(filepath, path);
        strncat(filepath, PATHSEP, 2);
        strcat(filepath, dg_table[EF_DG5].filename);

        saveFile(filepath, data[0] == 0xFF ? ".jpg" : ".jp2", data, datalen);

        free(filepath);
    } else {
        PrintAndLogEx(ERR, "error (emrtd_dump_ef_dg5) datalen out-of-bounds");
        return PM3_ESOFT;
    }
    return PM3_SUCCESS;
}

static int emrtd_dump_ef_dg7(uint8_t *file_contents, size_t file_length, const char *path) {
    uint8_t data[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t datalen = 0;

    // If we can't find image in EF_DG7, return false.
    if (emrtd_lds_get_data_by_tag(file_contents, file_length, data, &datalen, 0x5F, 0x42, true, true, 0) == false) {
        return PM3_ESOFT;
    }

    if (datalen < EMRTD_MAX_FILE_SIZE) {
        char *filepath = calloc(strlen(path) + 100, sizeof(char));
        if (filepath == NULL) {
            PrintAndLogEx(WARNING, "Failed to allocate memory");
            return PM3_EMALLOC;
        }
        strcpy(filepath, path);
        strncat(filepath, PATHSEP, 2);
        strcat(filepath, dg_table[EF_DG7].filename);

        saveFile(filepath, data[0] == 0xFF ? ".jpg" : ".jp2", data, datalen);

        free(filepath);
    } else {
        PrintAndLogEx(ERR, "error (emrtd_dump_ef_dg7) datalen out-of-bounds");
        return PM3_ESOFT;
    }
    return PM3_SUCCESS;
}

static int emrtd_dump_ef_sod(uint8_t *file_contents, size_t file_length, const char *path) {
    int fieldlen = emrtd_get_asn1_field_length(file_contents, file_length, 1);
    int datalen = emrtd_get_asn1_data_length(file_contents, file_length, 1);

    if (fieldlen + 1 > EMRTD_MAX_FILE_SIZE) {
        PrintAndLogEx(ERR, "error (emrtd_dump_ef_sod) fieldlen out-of-bounds");
        return PM3_EOUTOFBOUND;
    }

    char *filepath = calloc(strlen(path) + 100, sizeof(char));
    if (filepath == NULL) {
        PrintAndLogEx(WARNING, "Failed to allocate memory");
        return PM3_EMALLOC;
    }

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_SOD].filename);

    saveFile(filepath, ".p7b", file_contents + fieldlen + 1, datalen);
    free(filepath);
    return PM3_ESOFT;
}

static bool emrtd_dump_file(uint8_t *ks_enc, uint8_t *ks_mac, uint8_t *ssc, uint16_t file, const char *name, bool use_secure, const char *path) {
    uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t resplen = 0;

    if (emrtd_select_and_read(response, &resplen, file, ks_enc, ks_mac, ssc, use_secure) == false) {
        return false;
    }

    char *filepath = calloc(strlen(path) + 100, sizeof(char));
    if (filepath == NULL) {
        PrintAndLogEx(WARNING, "Failed to allocate memory");
        return false;
    }

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, name);

    PrintAndLogEx(INFO, "Read " _YELLOW_("%s") ", len %zu", name, resplen);
    PrintAndLogEx(DEBUG, "Contents (may be incomplete over 2k chars)");
    PrintAndLogEx(DEBUG, "------------------------------------------");
    PrintAndLogEx(DEBUG, "%s", sprint_hex_inrow(response, resplen));
    PrintAndLogEx(DEBUG, "------------------------------------------");
    saveFile(filepath, ".bin", response, resplen);

    emrtd_dg_t *dg = emrtd_fileid_to_dg(file);
    if ((dg != NULL) && (dg->dumper != NULL)) {
        dg->dumper(response, resplen, path);
    }

    free(filepath);
    return true;
}

static void rng(int length, uint8_t *dataout) {
    // Do very very secure prng operations
    //for (int i = 0; i < (length / 4); i++) {
    //    num_to_bytes(prng_successor(msclock() + i, 32), 4, &dataout[i * 4]);
    //}
    memset(dataout, 0x00, length);
}

static bool emrtd_do_bac(char *documentnumber, char *dob, char *expiry, uint8_t *ssc, uint8_t *ks_enc, uint8_t *ks_mac) {
    uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t resplen = 0;

    uint8_t rnd_ic[10] = { 0x00 }; // 8 + SW
    uint8_t kenc[50] = { 0x00 };
    uint8_t kmac[50] = { 0x00 };
    uint8_t k_icc[16] = { 0x00 };
    uint8_t S[32] = { 0x00 };

    uint8_t rnd_ifd[8], k_ifd[16];
    rng(8, rnd_ifd);
    rng(16, k_ifd);

    PrintAndLogEx(DEBUG, "doc............... " _GREEN_("%s"), documentnumber);
    PrintAndLogEx(DEBUG, "dob............... " _GREEN_("%s"), dob);
    PrintAndLogEx(DEBUG, "exp............... " _GREEN_("%s"), expiry);

    char documentnumbercd = emrtd_calculate_check_digit(documentnumber);
    char dobcd = emrtd_calculate_check_digit(dob);
    char expirycd = emrtd_calculate_check_digit(expiry);

    char kmrz[25] = { 0x00 };
    snprintf(kmrz, sizeof(kmrz), "%s%i%s%i%s%i", documentnumber, documentnumbercd, dob, dobcd, expiry, expirycd);
    PrintAndLogEx(DEBUG, "kmrz.............. " _GREEN_("%s"), kmrz);

    uint8_t kseed[20] = { 0x00 };
    sha1hash((unsigned char *)kmrz, strlen(kmrz), kseed);
    PrintAndLogEx(DEBUG, "kseed (sha1)...... %s ", sprint_hex_inrow(kseed, 16));

    emrtd_deskey(kseed, KENC_type, 16, kenc);
    emrtd_deskey(kseed, KMAC_type, 16, kmac);
    PrintAndLogEx(DEBUG, "kenc.............. %s", sprint_hex_inrow(kenc, 16));
    PrintAndLogEx(DEBUG, "kmac.............. %s", sprint_hex_inrow(kmac, 16));

    // Get Challenge
    if (emrtd_get_challenge(8, rnd_ic, sizeof(rnd_ic), &resplen) == false) {
        PrintAndLogEx(ERR, "Couldn't get challenge.");
        return false;
    }
    PrintAndLogEx(DEBUG, "rnd_ic............ %s", sprint_hex_inrow(rnd_ic, 8));

    memcpy(S, rnd_ifd, 8);
    memcpy(S + 8, rnd_ic, 8);
    memcpy(S + 16, k_ifd, 16);

    PrintAndLogEx(DEBUG, "S................. %s", sprint_hex_inrow(S, 32));

    uint8_t iv[8] = { 0x00 };
    uint8_t e_ifd[32] = { 0x00 };

    des3_encrypt_cbc(iv, kenc, S, sizeof(S), e_ifd);
    PrintAndLogEx(DEBUG, "e_ifd............. %s", sprint_hex_inrow(e_ifd, 32));

    uint8_t m_ifd[8] = { 0x00 };

    retail_mac(kmac, e_ifd, 32, m_ifd);
    PrintAndLogEx(DEBUG, "m_ifd............. %s", sprint_hex_inrow(m_ifd, 8));

    uint8_t cmd_data[40];
    memcpy(cmd_data, e_ifd, 32);
    memcpy(cmd_data + 32, m_ifd, 8);

    // Do external authentication
    if (emrtd_external_authenticate(cmd_data, sizeof(cmd_data), response, sizeof(response), &resplen) == false) {
        PrintAndLogEx(ERR, "Couldn't do external authentication. Did you supply the correct MRZ info?");
        return false;
    }
    PrintAndLogEx(INFO, "External authentication with BAC successful");

    uint8_t dec_output[32] = { 0x00 };
    des3_decrypt_cbc(iv, kenc, response, 32, dec_output);
    PrintAndLogEx(DEBUG, "dec_output........ %s", sprint_hex_inrow(dec_output, 32));

    if (memcmp(rnd_ifd, dec_output + 8, 8) != 0) {
        PrintAndLogEx(ERR, "Challenge failed, rnd_ifd does not match.");
        return false;
    }

    memcpy(k_icc, dec_output + 16, 16);

    // Calculate session keys
    for (int x = 0; x < 16; x++) {
        kseed[x] = k_ifd[x] ^ k_icc[x];
    }

    PrintAndLogEx(DEBUG, "kseed............ %s", sprint_hex_inrow(kseed, 16));

    emrtd_deskey(kseed, KENC_type, 16, ks_enc);
    emrtd_deskey(kseed, KMAC_type, 16, ks_mac);

    PrintAndLogEx(DEBUG, "ks_enc........ %s", sprint_hex_inrow(ks_enc, 16));
    PrintAndLogEx(DEBUG, "ks_mac........ %s", sprint_hex_inrow(ks_mac, 16));

    memcpy(ssc, rnd_ic + 4, 4);
    memcpy(ssc + 4, rnd_ifd + 4, 4);

    PrintAndLogEx(DEBUG, "ssc........... %s", sprint_hex_inrow(ssc, 8));

    return true;
}

static bool emrtd_connect(void) {
    int res = Iso7816Connect(CC_CONTACTLESS);
    return res == PM3_SUCCESS;
}

static bool emrtd_do_auth(char *documentnumber, char *dob, char *expiry, const char *can, bool BAC_available, uint8_t *cardaccess, size_t cardaccess_len, bool *BAC, uint8_t *ssc, uint8_t *ks_enc, uint8_t *ks_mac) {

    if (cardaccess_len > 0) {
        PrintAndLogEx(INFO, "PACE is available, probing PACE before selecting MRTD app");
        if (emrtd_probe_pace(cardaccess, cardaccess_len, can, BAC_available, "MF / pre-application select", ssc, ks_enc, ks_mac)) {
            *BAC = true;
            uint8_t aid[] = EMRTD_AID_MRTD;
            if (emrtd_secure_select_file_by_name(ks_enc, ks_mac, ssc, sizeof(aid), aid) == false) {
                PrintAndLogEx(ERR, "PACE authentication succeeded, but protected MRTD application select failed.");
                return false;
            }
            PrintAndLogEx(SUCCESS, "PACE secure messaging.. " _GREEN_("started"));
            return true;
        }
    }

    // Select MRTD applet
    uint8_t aid[] = EMRTD_AID_MRTD;
    if (emrtd_select_file_by_name(sizeof(aid), aid) == false) {
        PrintAndLogEx(ERR, "Couldn't select the MRTD application.");
        return false;
    }

    // Select EF_COM
    if (emrtd_select_file_by_ef(dg_table[EF_COM].fileid) == false) {
        *BAC = true;
        PrintAndLogEx(INFO, "Authentication is enforced");
        PrintAndLogEx(INFO, "Switching to external authentication");
    } else {
        *BAC = false;
        // Select EF_DG1
        emrtd_select_file_by_ef(dg_table[EF_DG1].fileid);

        size_t resplen = 0;
        uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
        if (emrtd_read_file(response, &resplen, NULL, NULL, NULL, false) == false) {
            *BAC = true;
            PrintAndLogEx(INFO, "Authentication is enforced");
            PrintAndLogEx(INFO, "Switching to external authentication");
        } else {
            *BAC = false;
        }
    }

    // Do Basic Access Control
    if (*BAC) {
        if (cardaccess_len > 0) {
            PrintAndLogEx(INFO, "PACE is available, probing PACE before BAC");
            if (emrtd_probe_pace(cardaccess, cardaccess_len, can, BAC_available, "MRTD application selected", ssc, ks_enc, ks_mac)) {
                PrintAndLogEx(SUCCESS, "PACE secure messaging.. " _GREEN_("started"));
                return true;
            } else {
                PrintAndLogEx(HINT, "Hint: This card likely requires PACE; BAC external authentication is expected to fail.");
            }
            PrintAndLogEx(ERR, "PACE probe failed; not falling back to BAC because EF.CardAccess advertises PACE.");
            return false;
        }

        // If BAC isn't available, exit out and warn user.
        if (BAC_available == false) {
            PrintAndLogEx(ERR, "This eMRTD enforces authentication, but you didn't supply MRZ data. Cannot proceed.");
            PrintAndLogEx(HINT, "Hint: Check out `" _YELLOW_("hf emrtd info/dump --h") "`, supply data with `-n` `-d` and `-e`");
            return false;
        }

        if (emrtd_do_bac(documentnumber, dob, expiry, ssc, ks_enc, ks_mac) == false) {
            return false;
        }
        g_emrtd_sm_type = EMRTD_SM_BAC;
    }
    return true;
}

int dumpHF_EMRTD(char *documentnumber, char *dob, char *expiry, const char *can, bool BAC_available, const char *path) {
    uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t cardaccess[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t cardaccess_len = 0;
    uint8_t ssc[EMRTD_PACE_SSC_LEN] = { 0x00 };
    uint8_t ks_enc[EMRTD_PACE_AES256_KEY_LEN] = { 0x00 };
    uint8_t ks_mac[EMRTD_PACE_AES256_KEY_LEN] = { 0x00 };
    g_emrtd_sm_type = EMRTD_SM_NONE;
    bool BAC = false;

    // Select the eMRTD
    if (emrtd_connect() == false) {
        DropField();
        return PM3_ESOFT;
    }

    // Dump EF_CardAccess (if available)
    if (emrtd_select_and_read(cardaccess, &cardaccess_len, dg_table[EF_CardAccess].fileid, ks_enc, ks_mac, ssc, BAC) == false) {
        PrintAndLogEx(INFO, "Couldn't dump EF_CardAccess, card does not support PACE");
        PrintAndLogEx(HINT, "Hint: This is expected behavior for cards without PACE and isn't something to be worried about");
    } else {
        char *filepath = calloc(strlen(path) + 100, sizeof(char));
        if (filepath == NULL) {
            PrintAndLogEx(WARNING, "Failed to allocate memory");
            DropField();
            return PM3_EMALLOC;
        }

        strcpy(filepath, path);
        strncat(filepath, PATHSEP, 2);
        strcat(filepath, dg_table[EF_CardAccess].filename);

        PrintAndLogEx(INFO, "Read " _YELLOW_("%s") ", len %zu", dg_table[EF_CardAccess].filename, cardaccess_len);
        PrintAndLogEx(DEBUG, "Contents (may be incomplete over 2k chars)");
        PrintAndLogEx(DEBUG, "------------------------------------------");
        PrintAndLogEx(DEBUG, "%s", sprint_hex_inrow(cardaccess, cardaccess_len));
        PrintAndLogEx(DEBUG, "------------------------------------------");
        saveFile(filepath, ".bin", cardaccess, cardaccess_len);
        free(filepath);
    }

    // Authenticate with the eMRTD
    if (emrtd_do_auth(documentnumber, dob, expiry, can, BAC_available, cardaccess, cardaccess_len, &BAC, ssc, ks_enc, ks_mac) == false) {
        DropField();
        return PM3_ESOFT;
    }

    // Select EF_COM
    if (emrtd_select_and_read(response, &resplen, dg_table[EF_COM].fileid, ks_enc, ks_mac, ssc, BAC) == false) {
        PrintAndLogEx(ERR, "Failed to read EF_COM");
        DropField();
        return PM3_ESOFT;
    }


    char *filepath = calloc(strlen(path) + 100, sizeof(char));
    if (filepath == NULL) {
        PrintAndLogEx(WARNING, "Failed to allocate memory");
        return PM3_EMALLOC;
    }

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_COM].filename);

    PrintAndLogEx(INFO, "Read EF_COM, len %zu", resplen);
    PrintAndLogEx(DEBUG, "Contents (may be incomplete over 2k chars)... %s", sprint_hex_inrow(response, resplen));
    saveFile(filepath, ".bin", response, resplen);

    free(filepath);

    uint8_t filelist[50];
    size_t filelistlen = 0;

    if (emrtd_lds_get_data_by_tag(response, resplen, filelist, &filelistlen, 0x5c, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_COM");
        DropField();
        return PM3_ESOFT;
    }

    PrintAndLogEx(DEBUG, "File List... %s", sprint_hex_inrow(filelist, filelistlen));
    // Add EF_SOD to the list
    filelist[filelistlen++] = 0x77;
    // Dump all files in the file list
    for (int i = 0; i < filelistlen; i++) {
        emrtd_dg_t *dg = emrtd_tag_to_dg(filelist[i]);
        if (dg == NULL) {
            PrintAndLogEx(INFO, "File tag not found, skipping... %02X", filelist[i]);
            continue;
        }
        PrintAndLogEx(DEBUG, "Current file... %s", dg->filename);
        if (!dg->pace && !dg->eac) {
            emrtd_dump_file(ks_enc, ks_mac, ssc, dg->fileid, dg->filename, BAC, path);
        }
    }
    DropField();
    return PM3_SUCCESS;
}

static bool emrtd_compare_check_digit(char *datain, int datalen, char expected_check_digit) {
    char tempdata[90] = { 0x00 };
    memcpy(tempdata, datain, datalen);

    uint8_t check_digit = emrtd_calculate_check_digit(tempdata) + 0x30;
    bool res = check_digit == expected_check_digit;
    PrintAndLogEx(DEBUG, "emrtd_compare_check_digit, expected %c == %c calculated ( %s )"
                  , expected_check_digit
                  , check_digit
                  , (res) ? _GREEN_("ok") : _RED_("fail"));
    return res;
}

static bool emrtd_mrz_verify_check_digit(char *mrz, int offset, int datalen) {
    char tempdata[90] = { 0x00 };
    memcpy(tempdata, mrz + offset, datalen);
    return emrtd_compare_check_digit(tempdata, datalen, mrz[offset + datalen]);
}

static void emrtd_print_legal_sex(char *legal_sex) {
    char sex[12] = { 0x00 };
    switch (*legal_sex) {
        case 'M':
            strncpy(sex, "Male", 5);
            break;
        case 'F':
            strncpy(sex, "Female", 7);
            break;
        case '<':
            strncpy(sex, "Unspecified", 12);
            break;
    }
    PrintAndLogEx(SUCCESS, "Legal Sex Marker......... " _YELLOW_("%s"), sex);
}

static int emrtd_mrz_determine_length(const char *mrz, int offset, int max_length) {
    int i;
    for (i = max_length; i >= 1; i--) {
        if (mrz[offset + i - 1] != '<') {
            return i;
        }
    }

    return 0;
}

static int emrtd_mrz_determine_separator(const char *mrz, int offset, int max_length) {
    // Note: this function does not account for len=0
    int i;
    for (i = max_length - 1; i > 0; i--) {
        if (mrz[offset + i] == '<' && mrz[offset + i + 1] == '<') {
            break;
        }
    }
    return i;
}

static void emrtd_mrz_replace_pad(char *data, int datalen, char newchar) {
    for (int i = 0; i < datalen; i++) {
        if (data[i] == '<') {
            data[i] = newchar;
        }
    }
}

static void emrtd_print_optional_elements(char *mrz, int offset, int length, bool verify_check_digit) {
    int i = emrtd_mrz_determine_length(mrz, offset, length);
    if (i == 0) {
        return;
    }

    PrintAndLogEx(SUCCESS, "Optional elements........ " _YELLOW_("%.*s"), i, mrz + offset);

    if (verify_check_digit && !emrtd_mrz_verify_check_digit(mrz, offset, length)) {
        PrintAndLogEx(SUCCESS, _RED_("Optional element check digit is invalid."));
    }
}

static void emrtd_print_document_number(char *mrz, int offset) {
    int i = emrtd_mrz_determine_length(mrz, offset, 9);
    if (i == 0) {
        return;
    }

    PrintAndLogEx(SUCCESS, "Document Number.......... " _YELLOW_("%.*s"), i, mrz + offset);

    if (!emrtd_mrz_verify_check_digit(mrz, offset, 9)) {
        PrintAndLogEx(SUCCESS, _RED_("Document number check digit is invalid."));
    }
}

static void emrtd_print_name(char *mrz, int offset, int max_length, bool localized) {
    char final_name[100] = { 0x00 };
    int namelen = emrtd_mrz_determine_length(mrz, offset, max_length);
    if (namelen == 0) {
        return;
    }
    int sep = emrtd_mrz_determine_separator(mrz, offset, namelen);

    // Account for mononyms
    if (sep != 0) {
        int firstnamelen = (namelen - (sep + 2));

        memcpy(final_name, mrz + offset + sep + 2, firstnamelen);
        final_name[firstnamelen] = ' ';
        memcpy(final_name + firstnamelen + 1, mrz + offset, sep);
    } else {
        memcpy(final_name, mrz + offset, namelen);
    }

    // Replace < characters with spaces
    emrtd_mrz_replace_pad(final_name, namelen, ' ');

    if (localized) {
        PrintAndLogEx(SUCCESS, "Legal Name (Localized)... " _YELLOW_("%s"), final_name);
    } else {
        PrintAndLogEx(SUCCESS, "Legal Name............... " _YELLOW_("%s"), final_name);
    }
}

static void emrtd_mrz_convert_date(char *mrz, int offset, char *final_date, bool is_expiry, bool is_full, bool is_ascii) {
    char work_date[9] = { 0x00 };
    int len = is_full ? 8 : 6;

    // Copy the data to a working array in the right format
    if (!is_ascii) {
        memcpy(work_date, sprint_hex_inrow((uint8_t *)mrz + offset, len / 2), len);
    } else {
        memcpy(work_date, mrz + offset, len);
    }

    // Set offset to 0 as we've now copied data.
    offset = 0;

    if (is_full) {
        // If we get the full date, use the first two characters from that for year
        memcpy(final_date, work_date, 2);
        // and do + 2 on offset so that rest of code uses the right data
        offset += 2;
    } else {
        char temp_year[3] = { 0x00 };
        memcpy(temp_year, work_date, 2);
        // If it's > 20, assume 19xx.
        if (strtol(temp_year, NULL, 10) < 20 || is_expiry) {
            final_date[0] = '2';
            final_date[1] = '0';
        } else {
            final_date[0] = '1';
            final_date[1] = '9';
        }
    }

    memcpy(final_date + 2, work_date + offset, 2);
    final_date[4] = '-';
    memcpy(final_date + 5, work_date + offset + 2, 2);
    final_date[7] = '-';
    memcpy(final_date + 8, work_date + offset + 4, 2);
}

static void emrtd_print_dob(char *mrz, int offset, bool full, bool ascii) {
    char final_date[12] = { 0x00 };
    emrtd_mrz_convert_date(mrz, offset, final_date, false, full, ascii);

    PrintAndLogEx(SUCCESS, "Date of birth............ " _YELLOW_("%s"), final_date);

    if (!full && !emrtd_mrz_verify_check_digit(mrz, offset, 6)) {
        PrintAndLogEx(SUCCESS, _RED_("Date of Birth check digit is invalid."));
    }
}

static void emrtd_print_expiry(char *mrz, int offset) {
    char final_date[12] = { 0x00 };
    emrtd_mrz_convert_date(mrz, offset, final_date, true, false, true);

    PrintAndLogEx(SUCCESS, "Date of expiry........... " _YELLOW_("%s"), final_date);

    if (!emrtd_mrz_verify_check_digit(mrz, offset, 6)) {
        PrintAndLogEx(SUCCESS, _RED_("Date of expiry check digit is invalid."));
    }
}

static void emrtd_print_issuance(char *data, bool ascii) {
    char final_date[12] = { 0x00 };
    emrtd_mrz_convert_date(data, 0, final_date, true, true, ascii);

    PrintAndLogEx(SUCCESS, "Date of issue............ " _YELLOW_("%s"), final_date);
}

static void emrtd_print_personalization_timestamp(uint8_t *data, size_t datalen) {
    if (datalen < 7) {
        return;
    }

    char str_date[0x0F] = { 0x00 };
    strncpy(str_date, sprint_hex_inrow(data, 0x07), sizeof(str_date) - 1);

    char final_date[20] = { 0x00 };
    snprintf(final_date, sizeof(final_date), "%.4s-%.2s-%.2s %.2s:%.2s:%.2s"
             , str_date
             , str_date + 4
             , str_date + 6
             , str_date + 8
             , str_date + 10
             , str_date + 12
            );

    PrintAndLogEx(SUCCESS, "Personalization at....... " _YELLOW_("%s"), final_date);
}

static void emrtd_print_unknown_timestamp_5f85(uint8_t *data, size_t datalen) {
    if (datalen < 14) {
        return;
    }
    char final_date[20] = { 0x00 };
    snprintf(final_date, sizeof(final_date), "%.4s-%.2s-%.2s %.2s:%.2s:%.2s"
             , data
             , data + 4
             , data + 6
             , data + 8
             , data + 10
             , data + 12
            );

    PrintAndLogEx(SUCCESS, "Unknown timestamp 5F85... " _YELLOW_("%s"), final_date);
    PrintAndLogEx(HINT, "Hint: This is very likely the personalization timestamp but it is using an undocumented tag.");
}

static int emrtd_print_ef_com_info(uint8_t *data, size_t datalen) {
    uint8_t filelist[50];
    size_t filelistlen = 0;
    bool res = emrtd_lds_get_data_by_tag(data, datalen, filelist, &filelistlen, 0x5c, 0x00, false, true, 0);
    if (res == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_COM.");
        return PM3_ESOFT;
    }

    // List files in the file list
    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "------------------------ " _CYAN_("EF_COM") " ------------------------");
    for (int i = 0; i < filelistlen; i++) {
        emrtd_dg_t *dg = emrtd_tag_to_dg(filelist[i]);
        if (dg == NULL) {
            PrintAndLogEx(INFO, "File tag not found, skipping: %02X", filelist[i]);
            continue;
        }
        int n = 25 - strlen(dg->filename);
        PrintAndLogEx(SUCCESS, "%s%.*s " _YELLOW_("%s"), dg->filename, n, pad, dg->desc);

    }
    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg1_info(uint8_t *data, size_t datalen) {
    int td_variant = 0;

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "------------------------ " _CYAN_("EF_DG1") " ------------------------");

    // MRZ on TD1 is 90 characters, 30 on each row.
    // MRZ on TD3 is 88 characters, 44 on each row.
    char mrz[90] = { 0x00 };
    size_t mrzlen = 0;

    if (emrtd_lds_get_data_by_tag(data, datalen, (uint8_t *) mrz, &mrzlen, 0x5f, 0x1f, true, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read MRZ from EF_DG1.");
        return PM3_ESOFT;
    }

    // Determine and print the document type
    if (mrz[0] == 'I' && mrz[1] == 'P') {
        PrintAndLogEx(SUCCESS, "Document Type............ " _YELLOW_("Passport Card"));
    } else if (mrz[0] == 'I') {
        PrintAndLogEx(SUCCESS, "Document Type............ " _YELLOW_("ID Card"));
    } else if (mrz[0] == 'P') {
        PrintAndLogEx(SUCCESS, "Document Type............ " _YELLOW_("Passport"));
    } else if (mrz[0] == 'A') {
        PrintAndLogEx(SUCCESS, "Document Type............ " _YELLOW_("Residency Permit"));
    } else {
        PrintAndLogEx(SUCCESS, "Document Type............ " _YELLOW_("Unknown"));
    }

    if (mrzlen == 90) {
        td_variant = 1;
    } else if (mrzlen == 88) {
        td_variant = 3;
    } else {
        PrintAndLogEx(ERR, "MRZ length (%zu) is wrong.", mrzlen);
        return PM3_ESOFT;
    }

    PrintAndLogEx(SUCCESS, "Document Form Factor..... " _YELLOW_("TD%i"), td_variant);

    // Print the MRZ
    if (td_variant == 1) {
        PrintAndLogEx(DEBUG, "MRZ Row 1... " _YELLOW_("%.30s"), mrz);
        PrintAndLogEx(DEBUG, "MRZ Row 2... " _YELLOW_("%.30s"), mrz + 30);
        PrintAndLogEx(DEBUG, "MRZ Row 3... " _YELLOW_("%.30s"), mrz + 60);
    } else if (td_variant == 3) {
        PrintAndLogEx(DEBUG, "MRZ Row 1... " _YELLOW_("%.44s"), mrz);
        PrintAndLogEx(DEBUG, "MRZ Row 2... " _YELLOW_("%.44s"), mrz + 44);
    }

    PrintAndLogEx(SUCCESS, "Issuing state............ " _YELLOW_("%.3s"), mrz + 2);

    if (td_variant == 3) {
        // Passport form factor
        PrintAndLogEx(SUCCESS, "Nationality.............. " _YELLOW_("%.3s"), mrz + 44 + 10);
        emrtd_print_name(mrz, 5, 38, false);
        emrtd_print_document_number(mrz, 44);
        emrtd_print_dob(mrz, 44 + 13, false, true);
        emrtd_print_legal_sex(&mrz[44 + 20]);
        emrtd_print_expiry(mrz, 44 + 21);
        emrtd_print_optional_elements(mrz, 44 + 28, 14, true);

        // Calculate and verify composite check digit
        char composite_check_data[50] = { 0x00 };
        memcpy(composite_check_data, mrz + 44, 10);
        memcpy(composite_check_data + 10, mrz + 44 + 13, 7);
        memcpy(composite_check_data + 17, mrz + 44 + 21, 23);

        if (emrtd_compare_check_digit(composite_check_data, 39, mrz[87]) == false) {
            PrintAndLogEx(SUCCESS, _RED_("Composite check digit is invalid."));
        }
    } else if (td_variant == 1) {
        // ID form factor
        PrintAndLogEx(SUCCESS, "Nationality.............. " _YELLOW_("%.3s"), mrz + 30 + 15);
        emrtd_print_name(mrz, 60, 30, false);
        emrtd_print_document_number(mrz, 5);
        emrtd_print_dob(mrz, 30, false, true);
        emrtd_print_legal_sex(&mrz[30 + 7]);
        emrtd_print_expiry(mrz, 30 + 8);
        emrtd_print_optional_elements(mrz, 15, 15, false);
        emrtd_print_optional_elements(mrz, 30 + 18, 11, false);

        // Calculate and verify composite check digit
        if (emrtd_compare_check_digit(mrz, 59, mrz[59]) == false) {
            PrintAndLogEx(SUCCESS, _RED_("Composite check digit is invalid."));
        }
    }

    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg2_info(uint8_t *data, size_t datalen) {

    int offset = 0;

    // This is a hacky impl that just looks for the image header. I'll improve it eventually.
    // based on mrpkey.py
    // Note: Doing datalen - 6 to account for the longest data we're checking.
    // Checks first byte before the rest to reduce overhead
    for (offset = 0; offset < datalen - 6; offset++) {
        if ((data[offset] == 0xFF && memcmp(jpeg_header, data + offset, 4) == 0) ||
                (data[offset] == 0x00 && memcmp(jpeg2k_header, data + offset, 6) == 0)) {
            datalen = datalen - offset;
            break;
        }
    }

    // If we didn't get any data, return false.
    if (datalen == 0) {
        return PM3_ESOFT;
    }

    ShowPictureWindow(data + offset, datalen);
    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg5_info(uint8_t *data, size_t datalen) {

    int offset = 0;

    // This is a hacky impl that just looks for the image header. I'll improve it eventually.
    // based on mrpkey.py
    // Note: Doing datalen - 6 to account for the longest data we're checking.
    // Checks first byte before the rest to reduce overhead
    for (offset = 0; offset < datalen - 6; offset++) {
        if ((data[offset] == 0xFF && memcmp(jpeg_header, data + offset, 4) == 0) ||
                (data[offset] == 0x00 && memcmp(jpeg2k_header, data + offset, 6) == 0)) {
            datalen = datalen - offset;
            break;
        }
    }

    // If we didn't get any data, return false.
    if (datalen == 0) {
        return PM3_ESOFT;
    }

    ShowPictureWindow(data + offset, datalen);
    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg7_info(uint8_t *data, size_t datalen) {

    int offset = 0;

    // This is a hacky impl that just looks for the image header. I'll improve it eventually.
    // based on mrpkey.py
    // Note: Doing datalen - 6 to account for the longest data we're checking.
    // Checks first byte before the rest to reduce overhead
    for (offset = 0; offset < datalen - 6; offset++) {
        if ((data[offset] == 0xFF && memcmp(jpeg_header, data + offset, 4) == 0) ||
                (data[offset] == 0x00 && memcmp(jpeg2k_header, data + offset, 6) == 0)) {
            datalen = datalen - offset;
            break;
        }
    }

    // If we didn't get any data, return false.
    if (datalen == 0) {
        return PM3_ESOFT;
    }

    ShowPictureWindow(data + offset, datalen);
    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg11_info(uint8_t *data, size_t datalen) {
    uint8_t taglist[100] = { 0x00 };
    size_t taglistlen = 0;
    uint8_t tagdata[1000] = { 0x00 };
    size_t tagdatalen = 0;

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "------------------------ " _CYAN_("EF_DG11") " -----------------------");

    if (emrtd_lds_get_data_by_tag(data, datalen, taglist, &taglistlen, 0x5c, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_DG11.");
        return PM3_ESOFT;
    }

    for (int i = 0; i < taglistlen; i++) {
        bool res = emrtd_lds_get_data_by_tag(data, datalen, tagdata, &tagdatalen, taglist[i], taglist[i + 1], taglist[i] == 0x5f, true, 0);
        (void)res;
        // Don't bother with empty tags
        if (tagdatalen == 0) {
            continue;
        }
        // Special behavior for two char tags
        if (taglist[i] == 0x5f) {
            switch (taglist[i + 1]) {
                case 0x0e:
                    emrtd_print_name((char *) tagdata, 0, tagdatalen, true);
                    break;
                case 0x0f:
                    emrtd_print_name((char *) tagdata, 0, tagdatalen, false);
                    break;
                case 0x10:
                    PrintAndLogEx(SUCCESS, "Personal Number.......... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x11:
                    // TODO: acc for < separation
                    PrintAndLogEx(SUCCESS, "Place of Birth........... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x42:
                    // TODO: acc for < separation
                    PrintAndLogEx(SUCCESS, "Permanent Address........ " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x12:
                    PrintAndLogEx(SUCCESS, "Telephone................ " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x13:
                    PrintAndLogEx(SUCCESS, "Profession............... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x14:
                    PrintAndLogEx(SUCCESS, "Title.................... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x15:
                    PrintAndLogEx(SUCCESS, "Personal Summary......... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x16:
                    saveFile("ProofOfCitizenship", tagdata[0] == 0xFF ? ".jpg" : ".jp2", tagdata, tagdatalen);
                    break;
                case 0x17:
                    // TODO: acc for < separation
                    PrintAndLogEx(SUCCESS, "Other valid TDs nums..... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x18:
                    PrintAndLogEx(SUCCESS, "Custody Information...... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x2b:
                    emrtd_print_dob((char *) tagdata, 0, true, tagdatalen != 4);
                    break;
                default:
                    PrintAndLogEx(SUCCESS, "Unknown Field %02X%02X....... %s", taglist[i], taglist[i + 1], sprint_hex_inrow(tagdata, tagdatalen));
                    break;
            }

            i += 1;
        } else {
            // TODO: Account for A0
            PrintAndLogEx(SUCCESS, "Unknown Field %02X......... %s", taglist[i], sprint_hex_inrow(tagdata, tagdatalen));
        }
    }
    return PM3_SUCCESS;
}

static int emrtd_print_ef_dg12_info(uint8_t *data, size_t datalen) {
    uint8_t taglist[100] = { 0x00 };
    size_t taglistlen = 0;
    uint8_t tagdata[1000] = { 0x00 };
    size_t tagdatalen = 0;

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "------------------------ " _CYAN_("EF_DG12") " -----------------------");

    if (emrtd_lds_get_data_by_tag(data, datalen, taglist, &taglistlen, 0x5c, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_DG12.");
        return PM3_ESOFT;
    }

    for (int i = 0; i < taglistlen; i++) {
        bool res = emrtd_lds_get_data_by_tag(data, datalen, tagdata, &tagdatalen, taglist[i], taglist[i + 1], taglist[i] == 0x5f, true, 0);
        (void)res;
        // Don't bother with empty tags
        if (tagdatalen == 0) {
            continue;
        }
        // Special behavior for two char tags
        if (taglist[i] == 0x5f) {
            // Several things here are longer than the rest but I can't think of a way to shorten them
            // ...and I doubt many states are using them.
            switch (taglist[i + 1]) {
                case 0x19:
                    PrintAndLogEx(SUCCESS, "Issuing Authority........ " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x26:
                    emrtd_print_issuance((char *) tagdata, tagdatalen != 4);
                    break;
                case 0x1b:
                    PrintAndLogEx(SUCCESS, "Endorsements & Observations... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x1c:
                    PrintAndLogEx(SUCCESS, "Tax/Exit Requirements.... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x1d:
                    saveFile("FrontOfDocument", tagdata[0] == 0xFF ? ".jpg" : ".jp2", tagdata, tagdatalen);
                    break;
                case 0x1e:
                    saveFile("BackOfDocument", tagdata[0] == 0xFF ? ".jpg" : ".jp2", tagdata, tagdatalen);
                    break;
                case 0x55:
                    emrtd_print_personalization_timestamp(tagdata, tagdatalen);
                    break;
                case 0x56:
                    PrintAndLogEx(SUCCESS, "Serial of Personalization System... " _YELLOW_("%.*s"), (int)tagdatalen, tagdata);
                    break;
                case 0x85:
                    emrtd_print_unknown_timestamp_5f85(tagdata, tagdatalen);
                    break;
                default:
                    PrintAndLogEx(SUCCESS, "Unknown Field %02X%02X....... %s", taglist[i], taglist[i + 1], sprint_hex_inrow(tagdata, tagdatalen));
                    break;
            }

            i += 1;
        } else {
            // TODO: Account for A0
            PrintAndLogEx(SUCCESS, "Unknown Field %02X......... %s", taglist[i], sprint_hex_inrow(tagdata, tagdatalen));
        }
    }
    return PM3_SUCCESS;
}

static int emrtd_ef_sod_extract_signatures(uint8_t *data, size_t datalen, uint8_t *dataout, size_t *dataoutlen) {
    uint8_t top[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t signeddata[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t emrtdsigcontainer[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t emrtdsig[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t emrtdsigtext[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t toplen, signeddatalen, emrtdsigcontainerlen, emrtdsiglen, emrtdsigtextlen = 0;

    if (emrtd_lds_get_data_by_tag(data, datalen, top, &toplen, 0x30, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read top from EF_SOD.");
        return false;
    }

    PrintAndLogEx(DEBUG, "top: %s.", sprint_hex_inrow(top, toplen));

    if (emrtd_lds_get_data_by_tag(top, toplen, signeddata, &signeddatalen, 0xA0, 0x00, false, false, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read signedData from EF_SOD.");
        return false;
    }

    PrintAndLogEx(DEBUG, "signeddata: %s.", sprint_hex_inrow(signeddata, signeddatalen));

    // Do true on reading into the tag as it's a "sequence"
    if (emrtd_lds_get_data_by_tag(signeddata, signeddatalen, emrtdsigcontainer, &emrtdsigcontainerlen, 0x30, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read eMRTDSignature container from EF_SOD.");
        return false;
    }

    PrintAndLogEx(DEBUG, "emrtdsigcontainer: %s.", sprint_hex_inrow(emrtdsigcontainer, emrtdsigcontainerlen));

    if (emrtd_lds_get_data_by_tag(emrtdsigcontainer, emrtdsigcontainerlen, emrtdsig, &emrtdsiglen, 0xA0, 0x00, false, false, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read eMRTDSignature from EF_SOD.");
        return false;
    }

    PrintAndLogEx(DEBUG, "emrtdsig: %s.", sprint_hex_inrow(emrtdsig, emrtdsiglen));

    // TODO: Not doing memcpy here, it didn't work, fix it somehow
    if (emrtd_lds_get_data_by_tag(emrtdsig, emrtdsiglen, emrtdsigtext, &emrtdsigtextlen, 0x04, 0x00, false, false, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read eMRTDSignature (text) from EF_SOD.");
        return false;
    }
    memcpy(dataout, emrtdsigtext, emrtdsigtextlen);
    *dataoutlen = emrtdsigtextlen;
    return PM3_SUCCESS;
}

static int emrtd_parse_ef_sod_hash_algo(uint8_t *data, size_t datalen, int *hashalgo) {
    uint8_t hashalgoset[64] = { 0x00 };
    size_t hashalgosetlen = 0;

    // We'll return hash algo -1 if we can't find anything
    *hashalgo = -1;

    if (emrtd_lds_get_data_by_tag(data, datalen, hashalgoset, &hashalgosetlen, 0x30, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read hash algo set from EF_SOD.");
        return false;
    }

    PrintAndLogEx(DEBUG, "hash algo set: %s", sprint_hex_inrow(hashalgoset, hashalgosetlen));

    // If last two bytes are 05 00, ignore them.
    // https://wf.lavatech.top/ave-but-random/emrtd-data-quirks#EF_SOD
    if (hashalgoset[hashalgosetlen - 2] == 0x05 && hashalgoset[hashalgosetlen - 1] == 0x00) {
        hashalgosetlen -= 2;
    }

    for (int hashi = 0; hashalg_table[hashi].name != NULL; hashi++) {
        PrintAndLogEx(DEBUG, "trying: %s", hashalg_table[hashi].name);
        // We're only interested in checking if the length matches to avoid memory shenanigans
        if (hashalg_table[hashi].descriptorlen != hashalgosetlen) {
            PrintAndLogEx(DEBUG, "len mismatch: %zu", hashalgosetlen);
            continue;
        }

        if (memcmp(hashalg_table[hashi].descriptor, hashalgoset, hashalgosetlen) == 0) {
            *hashalgo = hashi;
            return PM3_SUCCESS;
        }
    }

    PrintAndLogEx(ERR, "Failed to parse hash list (Unknown algo: %s). Hash verification won't be available.", sprint_hex_inrow(hashalgoset, hashalgosetlen));
    return PM3_ESOFT;
}

static int emrtd_parse_ef_sod_hashes(uint8_t *data, size_t datalen, uint8_t *hashes, int *hashalgo) {
    uint8_t emrtdsig[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t hashlist[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    uint8_t hash[64] = { 0x00 };
    size_t hashlen = 0;

    uint8_t hashidstr[4] = { 0x00 };
    size_t hashidstrlen = 0;

    size_t emrtdsiglen = 0;
    size_t hashlistlen = 0;
    size_t offset = 0;

    if (emrtd_ef_sod_extract_signatures(data, datalen, emrtdsig, &emrtdsiglen) != PM3_SUCCESS) {
        return false;
    }

    PrintAndLogEx(DEBUG, "hash data... %s", sprint_hex_inrow(emrtdsig, emrtdsiglen));

    emrtd_parse_ef_sod_hash_algo(emrtdsig, emrtdsiglen, hashalgo);

    if (emrtd_lds_get_data_by_tag(emrtdsig, emrtdsiglen, hashlist, &hashlistlen, 0x30, 0x00, false, true, 1) == false) {
        PrintAndLogEx(ERR, "Failed to read hash list from EF_SOD");
        return false;
    }

    PrintAndLogEx(DEBUG, "hash list... %s", sprint_hex_inrow(hashlist, hashlistlen));

    while (offset < hashlistlen) {
        // Get the length of the element
        int e_datalen = emrtd_get_asn1_data_length(hashlist + offset, hashlistlen - offset, 1);

        // Get the length of the element's length
        int e_fieldlen = emrtd_get_asn1_field_length(hashlist + offset, hashlistlen - offset, 1);

        switch (hashlist[offset]) {
            case 0x30: {
                // iceman:  if these two calls fails,  feels like we should have a better check in place
                bool res = emrtd_lds_get_data_by_tag(hashlist + offset + e_fieldlen + 1, e_datalen, hashidstr, &hashidstrlen, 0x02, 0x00, false, false, 0);
                (void)res;
                res = emrtd_lds_get_data_by_tag(hashlist + offset + e_fieldlen + 1, e_datalen, hash, &hashlen, 0x04, 0x00, false, false, 0);
                (void)res;
                if (hashlen <= 64) {
                    memcpy(hashes + (hashidstr[0] * 64), hash, hashlen);
                } else {
                    PrintAndLogEx(ERR, "error (emrtd_parse_ef_sod_hashes) hashlen out-of-bounds");
                }
                break;
            }
        }
        // + 1 for length of ID
        offset += 1 + e_datalen + e_fieldlen;
    }

    return PM3_SUCCESS;
}

static int emrtd_print_ef_sod_info(uint8_t *dg_hashes_calc, uint8_t *dg_hashes_sod, int hash_algo, bool fastdump) {
    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "------------------------ " _CYAN_("EF_SOD") " ------------------------");
    PrintAndLogEx(INFO, "Document Security Object");
    PrintAndLogEx(INFO, "contains the digital signatures of the passport data");
    PrintAndLogEx(INFO, "");

    if (hash_algo == -1) {
        PrintAndLogEx(SUCCESS, "Hash algorithm... " _YELLOW_("Unknown"));
    } else {

        PrintAndLogEx(SUCCESS, "Hash algorithm... " _YELLOW_("%s"), hashalg_table[hash_algo].name);

        uint8_t all_zeroes[64] = { 0x00 };

        for (int i = 1; i <= 16; i++) {

            bool calc_all_zero = (memcmp(dg_hashes_calc + (i * 64), all_zeroes, hashalg_table[hash_algo].hashlen) == 0);
            bool sod_all_zero = (memcmp(dg_hashes_sod + (i * 64), all_zeroes, hashalg_table[hash_algo].hashlen) == 0);
            bool hash_matches = (memcmp(dg_hashes_sod + (i * 64), dg_hashes_calc + (i * 64), hashalg_table[hash_algo].hashlen) == 0);

            // Ignore files we don't haven't read and lack hashes to
            if (calc_all_zero == true && sod_all_zero == true) {
                continue;
            }

            // silly padding thingy
            int n = 40 - strlen(dg_table[i].desc);

            if (calc_all_zero == true) {

                if (fastdump && !dg_table[i].fastdump && !dg_table[i].pace && !dg_table[i].eac) {
                    PrintAndLogEx(SUCCESS, _YELLOW_("EF_DG%-2i") " %s%.*s File was skipped, but is in EF_SOD", i, dg_table[i].desc, n, pad);
                } else {
                    PrintAndLogEx(SUCCESS, _YELLOW_("EF_DG%-2i") " %s%.*s File couldn't be read, but is in EF_SOD", i, dg_table[i].desc, n, pad);
                }

            } else if (sod_all_zero == true) {
                PrintAndLogEx(SUCCESS, _YELLOW_("EF_DG%-2i") " %s%.*s " _RED_("File is not in EF_SOD"), i, dg_table[i].desc, n, pad);
            } else if (hash_matches == false) {
                PrintAndLogEx(SUCCESS, _YELLOW_("EF_DG%-2i") " %s%.*s " _RED_("Invalid"), i, dg_table[i].desc, n, pad);
            } else {
                PrintAndLogEx(SUCCESS, _YELLOW_("EF_DG%-2i") " %s%.*s " _GREEN_("Valid"), i, dg_table[i].desc, n, pad);
            }
        }
    }

    return PM3_SUCCESS;
}

static int emrtd_print_ef_cardaccess_info(uint8_t *data, size_t datalen) {
    uint8_t dataset[100] = { 0x00 };
    size_t datasetlen = 0;
    uint8_t datafromtag[100] = { 0x00 };
    size_t datafromtaglen = 0;
    uint8_t parsednum = 0;

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "--------------------- " _CYAN_("EF_CardAccess") " --------------------");

    if (emrtd_lds_get_data_by_tag(data, datalen, dataset, &datasetlen, 0x30, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read set from EF_CardAccess.");
        return PM3_ESOFT;
    }

    // Get PACE version
    if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x02, 0x00, false, false, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read PACE version from EF_CardAccess.");
        return PM3_ESOFT;
    }
    // TODO: hack!!!
    memcpy(&parsednum, datafromtag, datafromtaglen);
    PrintAndLogEx(SUCCESS, "PACE version............. " _YELLOW_("%i"), parsednum);

    // Get PACE algorithm
    if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x06, 0x00, false, false, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read PACE algorithm from EF_CardAccess.");
        return PM3_ESOFT;
    }

    for (int pacei = 0; pacealg_table[pacei].name != NULL; pacei++) {
        PrintAndLogEx(DEBUG, "Trying: %s", pacealg_table[pacei].name);

        if (memcmp(pacealg_table[pacei].descriptor, datafromtag, datafromtaglen) == 0) {
            PrintAndLogEx(SUCCESS, "PACE algorithm........... " _YELLOW_("%s"), pacealg_table[pacei].name);
        }
    }

    // Get PACE parameter ID
    if (emrtd_lds_get_data_by_tag(dataset, datasetlen, datafromtag, &datafromtaglen, 0x02, 0x00, false, false, 1) == false) {
        PrintAndLogEx(ERR, "Failed to read PACE parameter ID from EF_CardAccess.");
        return PM3_ESOFT;
    }

    // TODO: hack!!!
    memcpy(&parsednum, datafromtag, datafromtaglen);
    for (int pacepari = 0; pacesdp_table[pacepari].id != 32; pacepari++) {
        PrintAndLogEx(DEBUG, "Trying: %s", pacesdp_table[pacepari].name);

        if (pacesdp_table[pacepari].id == parsednum) {
            PrintAndLogEx(SUCCESS, "PACE parameter........... " _YELLOW_("%s"), pacesdp_table[pacepari].name);
        }
        // TODO: account for RFU
    }

    return PM3_SUCCESS;
}

int infoHF_EMRTD(char *documentnumber, char *dob, char *expiry, const char *can, bool BAC_available, bool only_fast) {
    uint8_t response[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t resplen = 0;
    uint8_t cardaccess[EMRTD_MAX_FILE_SIZE] = { 0x00 };
    size_t cardaccess_len = 0;
    uint8_t ssc[EMRTD_PACE_SSC_LEN] = { 0x00 };
    uint8_t ks_enc[EMRTD_PACE_AES256_KEY_LEN] = { 0x00 };
    uint8_t ks_mac[EMRTD_PACE_AES256_KEY_LEN] = { 0x00 };
    g_emrtd_sm_type = EMRTD_SM_NONE;
    bool BAC = false;
    bool PACE_available = true;

    // Select the eMRTD
    if (emrtd_connect() == false) {
        DropField();
        return PM3_ESOFT;
    }
    bool use14b = (GetISODEPState() == ISODEP_NFCB);

    // Read EF_CardAccess
    if (emrtd_select_and_read(response, &resplen, dg_table[EF_CardAccess].fileid, ks_enc, ks_mac, ssc, BAC) == false) {
        PACE_available = false;
        PrintAndLogEx(HINT, "Hint: The error above this is normal. It just means that your eMRTD lacks PACE.");
    } else {
        memcpy(cardaccess, response, resplen);
        cardaccess_len = resplen;
    }

    // Select and authenticate with the eMRTD
    bool auth_result = emrtd_do_auth(documentnumber, dob, expiry, can, BAC_available, cardaccess, cardaccess_len, &BAC, ssc, ks_enc, ks_mac);

    PrintAndLogEx(NORMAL, "");
    PrintAndLogEx(INFO, "---------------------- " _CYAN_("Basic Info") " ----------------------");
    PrintAndLogEx(SUCCESS, "Communication standard... %s", use14b ? _YELLOW_("ISO/IEC 14443(B)") : _YELLOW_("ISO/IEC 14443(A)"));
    PrintAndLogEx(SUCCESS, "Authentication........... %s", BAC ? _GREEN_("Enforced") : _RED_("Not enforced"));
    PrintAndLogEx(SUCCESS, "PACE..................... %s", PACE_available ? _GREEN_("Available") : _YELLOW_("Not available"));
    PrintAndLogEx(SUCCESS, "Authentication result.... %s", auth_result ? _GREEN_("Successful") : _RED_("Failed"));

    if (PACE_available) {
        emrtd_print_ef_cardaccess_info(response, resplen);
    }

    if (auth_result == false) {
        DropField();
        return PM3_ESOFT;
    }

    // Read EF_COM to get file list
    if (emrtd_select_and_read(response, &resplen, dg_table[EF_COM].fileid, ks_enc, ks_mac, ssc, BAC) == false) {
        PrintAndLogEx(ERR, "Failed to read EF_COM");
        DropField();
        return PM3_ESOFT;
    }

    int res = emrtd_print_ef_com_info(response, resplen);
    if (res != PM3_SUCCESS) {
        DropField();
        return res;
    }

    uint8_t filelist[50];
    size_t filelistlen = 0;

    if (emrtd_lds_get_data_by_tag(response, resplen, filelist, &filelistlen, 0x5c, 0x00, false, true, 0) == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_COM.");
        DropField();
        return PM3_ESOFT;
    }

    // Grab the hash list from EF_SOD
    uint8_t dg_hashes_sod[17][64] = { { 0 } };
    uint8_t dg_hashes_calc[17][64] = { { 0 } };
    int hash_algo = 0;

    if (!emrtd_select_and_read(response, &resplen, dg_table[EF_SOD].fileid, ks_enc, ks_mac, ssc, BAC)) {
        PrintAndLogEx(ERR, "Failed to read EF_SOD.");
        DropField();
        return PM3_ESOFT;
    }

    res = emrtd_parse_ef_sod_hashes(response, resplen, *dg_hashes_sod, &hash_algo);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(ERR, "Failed to read hash list from EF_SOD. Hash checks will fail");
    }

    // Dump all files in the file list
    for (int i = 0; i < filelistlen; i++) {

        emrtd_dg_t *dg = emrtd_tag_to_dg(filelist[i]);
        if (dg == NULL) {
            PrintAndLogEx(INFO, "File tag not found, skipping... %02X", filelist[i]);
            continue;
        }

        if (((dg->fastdump && only_fast) || !only_fast) && !dg->pace && !dg->eac) {
            if (emrtd_select_and_read(response, &resplen, dg->fileid, ks_enc, ks_mac, ssc, BAC)) {
                if (dg->parser != NULL)
                    dg->parser(response, resplen);

                PrintAndLogEx(DEBUG, "EF_DG%i hash algo... %i", dg->dgnum, hash_algo);
                // Check file hash
                if (hash_algo != -1) {
                    PrintAndLogEx(DEBUG, "EF_DG%i hash on EF_SOD... %s", dg->dgnum, sprint_hex_inrow(dg_hashes_sod[dg->dgnum], hashalg_table[hash_algo].hashlen));
                    hashalg_table[hash_algo].hasher(response, resplen, dg_hashes_calc[dg->dgnum]);
                    PrintAndLogEx(DEBUG, "EF_DG%i hash calc........ %s", dg->dgnum, sprint_hex_inrow(dg_hashes_calc[dg->dgnum], hashalg_table[hash_algo].hashlen));
                }
            }
        }
    }
    DropField();

    emrtd_print_ef_sod_info(*dg_hashes_calc, *dg_hashes_sod, hash_algo, true);
    PrintAndLogEx(NORMAL, "");
    return PM3_SUCCESS;
}

int infoHF_EMRTD_offline(const char *path) {
    uint8_t *data;
    size_t datalen = 0;
    char *filepath = calloc(strlen(path) + 100, sizeof(char));
    if (filepath == NULL) {
        PrintAndLogEx(WARNING, "Failed to allocate memory");
        return PM3_EMALLOC;
    }
    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_COM].filename);

    if ((loadFile_safeEx(filepath, ".BIN", (void **)&data, (size_t *)&datalen, false) != PM3_SUCCESS) &&
            (loadFile_safeEx(filepath, ".bin", (void **)&data, (size_t *)&datalen, false) != PM3_SUCCESS)) {
        PrintAndLogEx(ERR, "Failed to read EF_COM");
        free(filepath);
        return PM3_ESOFT;
    }

    int res = emrtd_print_ef_com_info(data, datalen);
    if (res != PM3_SUCCESS) {
        free(data);
        free(filepath);
        return res;
    }

    uint8_t filelist[50];
    size_t filelistlen = 0;
    res = emrtd_lds_get_data_by_tag(data, datalen, filelist, &filelistlen, 0x5c, 0x00, false, true, 0);
    if (res == false) {
        PrintAndLogEx(ERR, "Failed to read file list from EF_COM");
        free(data);
        free(filepath);
        return PM3_ESOFT;
    }
    free(data);

    // Grab the hash list
    uint8_t dg_hashes_sod[17][64] = { { 0 } };
    uint8_t dg_hashes_calc[17][64] = { { 0 } };
    int hash_algo = 0;

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_CardAccess].filename);

    if ((loadFile_safeEx(filepath, ".BIN", (void **)&data, (size_t *)&datalen, false) == PM3_SUCCESS) ||
            (loadFile_safeEx(filepath, ".bin", (void **)&data, (size_t *)&datalen, false) == PM3_SUCCESS)) {
        emrtd_print_ef_cardaccess_info(data, datalen);
        free(data);
    } else {
        PrintAndLogEx(HINT, "Hint: The error above this is normal. It just means that your eMRTD lacks PACE");
    }

    strcpy(filepath, path);
    strncat(filepath, PATHSEP, 2);
    strcat(filepath, dg_table[EF_SOD].filename);

    if ((loadFile_safeEx(filepath, ".BIN", (void **)&data, (size_t *)&datalen, false) != PM3_SUCCESS) &&
            (loadFile_safeEx(filepath, ".bin", (void **)&data, (size_t *)&datalen, false) != PM3_SUCCESS)) {
        PrintAndLogEx(ERR, "Failed to read EF_SOD");
        free(filepath);
        return PM3_ESOFT;
    }

    // coverity scan CID 395630,
    if (data == NULL) {
        free(filepath);
        return PM3_ESOFT;
    }

    res = emrtd_parse_ef_sod_hashes(data, datalen, *dg_hashes_sod, &hash_algo);
    if (res != PM3_SUCCESS) {
        PrintAndLogEx(ERR, "Failed to read hash list from EF_SOD. Hash checks will fail");
    }
    free(data);

    // Read files in the file list
    for (int i = 0; i < filelistlen; i++) {

        emrtd_dg_t *dg = emrtd_tag_to_dg(filelist[i]);
        if (dg == NULL) {
            PrintAndLogEx(INFO, "File tag not found, skipping... %02X", filelist[i]);
            continue;
        }

        if (!dg->pace && !dg->eac) {
            strcpy(filepath, path);
            strncat(filepath, PATHSEP, 2);
            strcat(filepath, dg->filename);
            if ((loadFile_safeEx(filepath, ".BIN", (void **)&data, (size_t *)&datalen, false) == PM3_SUCCESS) ||
                    (loadFile_safeEx(filepath, ".bin", (void **)&data, (size_t *)&datalen, false) == PM3_SUCCESS)) {
                // we won't halt on parsing errors
                if (dg->parser != NULL) {
                    dg->parser(data, datalen);
                }

                PrintAndLogEx(DEBUG, "EF_DG%i hash algo... %i", dg->dgnum, hash_algo);
                // Check file hash
                if (hash_algo != -1) {
                    PrintAndLogEx(DEBUG, "EF_DG%i hash on EF_SOD... %s", dg->dgnum, sprint_hex_inrow(dg_hashes_sod[dg->dgnum], hashalg_table[hash_algo].hashlen));
                    hashalg_table[hash_algo].hasher(data, datalen, dg_hashes_calc[dg->dgnum]);
                    PrintAndLogEx(DEBUG, "EF_DG%i hash calc........ %s", dg->dgnum, sprint_hex_inrow(dg_hashes_calc[dg->dgnum], hashalg_table[hash_algo].hashlen));
                }
                free(data);
            }
        }
    }
    free(filepath);

    emrtd_print_ef_sod_info(*dg_hashes_calc, *dg_hashes_sod, hash_algo, false);
    PrintAndLogEx(NORMAL, "");
    return PM3_SUCCESS;
}

static bool validate_date(uint8_t *data, int datalen) {
    // Date has to be 6 chars
    if (datalen != 6) {
        return false;
    }

    // Check for valid date and month numbers
    char temp[4] = { 0x00 };
    memcpy(temp, data + 2, 2);
    int month = (int) strtol(temp, NULL, 10);
    memcpy(temp, data + 4, 2);
    int day = (int) strtol(temp, NULL, 10);

    return !(day <= 0 || day > 31 || month <= 0 || month > 12);
}

static bool emrtd_extract_access_data_from_mrz(uint8_t *mrz, int mrzlen, uint8_t *docnum, uint8_t *dob, uint8_t *expiry) {
    strn_upper((char *)mrz, mrzlen);

    if (mrzlen == 44) {
        memcpy(docnum, &mrz[0], 9);
        memcpy(dob,    &mrz[13], 6);
        memcpy(expiry, &mrz[21], 6);
        return true;
    }

    if (mrzlen == 90) {
        memcpy(docnum, &mrz[5], 9);
        memcpy(dob,    &mrz[30], 6);
        memcpy(expiry, &mrz[38], 6);
        return true;
    }

    return false;
}

static int CmdHFeMRTDDump(const char *Cmd) {
    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf emrtd dump",
                  "Dump all files on an eMRTD",
                  "hf emrtd dump\n"
                  "hf emrtd dump --dir ../dump\n"
                  "hf emrtd dump -n 123456789 -d 890101 -e 250401"
                 );

    void *argtable[] = {
        arg_param_begin,
        arg_str0("n", "doc", "<alphanum>", "document number, up to 9 chars"),
        arg_str0("d", "date", "<YYMMDD>", "date of birth in YYMMDD format"),
        arg_str0("e", "expiry", "<YYMMDD>", "expiry in YYMMDD format"),
        arg_str0("m", "mrz", "<[0-9A-Z<]>", "TD3 passport MRZ line 2 (44 chars) or full TD1 ID card MRZ (90 chars)"),
        arg_str0("c", "can", "<digits>", "card access number for PACE"),
        arg_str0(NULL, "dir", "<str>", "save dump to the given dirpath"),
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, true);

    uint8_t mrz[91] = { 0x00 };
    uint8_t docnum[10] = { 0x00 };
    uint8_t dob[7] = { 0x00 };
    uint8_t expiry[7] = { 0x00 };
    uint8_t can[16] = { 0x00 };
    bool BAC = true;
    bool error = false;
    int slen = 0;
    // Go through all args, if even one isn't supplied, mark BAC as unavailable
    if (CLIParamStrToBuf(arg_get_str(ctx, 1), docnum, 9, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        strn_upper((char *)docnum, slen);
        if (slen != 9) {
            // Pad to 9 with <
            memset(docnum + slen, '<', 9 - slen);
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 2), dob, 6, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        if (!validate_date(dob, slen)) {
            PrintAndLogEx(ERR, "Date of birth date format is incorrect, cannot continue.");
            PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
            error = true;
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 3), expiry, 6, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        if (!validate_date(expiry, slen)) {
            PrintAndLogEx(ERR, "Expiry date format is incorrect, cannot continue.");
            PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
            error = true;
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 4), mrz, sizeof(mrz) - 1, &slen) == 0 && slen != 0) {
        if (emrtd_extract_access_data_from_mrz(mrz, slen, docnum, dob, expiry) == false) {
            PrintAndLogEx(ERR, "MRZ length is incorrect, it should be 44 (TD3 line 2) or 90 (full TD1), not %i", slen);
            error = true;
        } else {
            BAC = true;
            // TODO check MRZ checksums?
            if (!validate_date(dob, 6)) {
                PrintAndLogEx(ERR, "Date of birth date format is incorrect, cannot continue.");
                PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
                error = true;
            }
            if (!validate_date(expiry, 6)) {
                PrintAndLogEx(ERR, "Expiry date format is incorrect, cannot continue.");
                PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
                error = true;
            }
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 5), can, sizeof(can) - 1, &slen) == 0 && slen != 0) {
        strn_upper((char *)can, slen);
    }

    uint8_t path[FILENAME_MAX] = { 0x00 };
    if (CLIParamStrToBuf(arg_get_str(ctx, 6), path, sizeof(path), &slen) != 0 || slen == 0) {
        path[0] = '.';
    }

    CLIParserFree(ctx);
    if (error) {
        return PM3_ESOFT;
    }
    bool restore_apdu_logging = GetAPDULogging();
    if (g_debugMode >= 2) {
        SetAPDULogging(true);
    }

    uint64_t t1 = msclock();

    int res = dumpHF_EMRTD((char *)docnum, (char *)dob, (char *)expiry, (const char *)can, BAC, (const char *)path);

    PrintAndLogEx(SUCCESS, "time: %" PRIu64 " seconds\n", (msclock() - t1) / 1000);

    SetAPDULogging(restore_apdu_logging);
    return res;
}

static int CmdHFeMRTDInfo(const char *Cmd) {
    CLIParserContext *ctx;
    CLIParserInit(&ctx, "hf emrtd info",
                  "Display info about an eMRTD",
                  "hf emrtd info\n"
                  "hf emrtd info --dir ../dumps\n"
                  "hf emrtd info -n 123456789 -d 890101 -e 250401\n"
                  "hf emrtd info -n 123456789 -d 890101 -e 250401 -i"
                 );

    void *argtable[] = {
        arg_param_begin,
        arg_str0("n", "doc", "<alphanum>", "document number, up to 9 chars"),
        arg_str0("d", "date", "<YYMMDD>", "date of birth in YYMMDD format"),
        arg_str0("e", "expiry", "<YYMMDD>", "expiry in YYMMDD format"),
        arg_str0("m", "mrz", "<[0-9A-Z<]>", "TD3 passport MRZ line 2 (44 chars) or full TD1 ID card MRZ (90 chars)"),
        arg_str0("c", "can", "<digits>", "card access number for PACE"),
        arg_str0(NULL, "dir", "<str>", "display info from offline dump stored in dirpath"),
        arg_lit0("i", "images", "show images"),
        arg_param_end
    };
    CLIExecWithReturn(ctx, Cmd, argtable, true);

    uint8_t mrz[91] = { 0x00 };
    uint8_t docnum[10] = { 0x00 };
    uint8_t dob[7] = { 0x00 };
    uint8_t expiry[7] = { 0x00 };
    uint8_t can[16] = { 0x00 };
    bool BAC = true;
    bool error = false;
    int slen = 0;
    // Go through all args, if even one isn't supplied, mark BAC as unavailable
    if (CLIParamStrToBuf(arg_get_str(ctx, 1), docnum, 9, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        strn_upper((char *)docnum, slen);
        if (slen != 9) {
            memset(docnum + slen, '<', 9 - slen);
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 2), dob, 6, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        if (!validate_date(dob, slen)) {
            PrintAndLogEx(ERR, "Date of birth date format is incorrect, cannot continue.");
            PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
            error = true;
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 3), expiry, 6, &slen) != 0 || slen == 0) {
        BAC = false;
    } else {
        if (!validate_date(expiry, slen)) {
            PrintAndLogEx(ERR, "Expiry date format is incorrect, cannot continue.");
            PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
            error = true;
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 4), mrz, sizeof(mrz) - 1, &slen) == 0 && slen != 0) {
        if (emrtd_extract_access_data_from_mrz(mrz, slen, docnum, dob, expiry) == false) {
            PrintAndLogEx(ERR, "MRZ length is incorrect, it should be 44 (TD3 line 2) or 90 (full TD1), not %i", slen);
            error = true;
        } else {
            BAC = true;
            // TODO check MRZ checksums?
            if (!validate_date(dob, 6)) {
                PrintAndLogEx(ERR, "Date of birth date format is incorrect, cannot continue.");
                PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
                error = true;
            }
            if (!validate_date(expiry, 6)) {
                PrintAndLogEx(ERR, "Expiry date format is incorrect, cannot continue.");
                PrintAndLogEx(HINT, "Hint: Use the format YYMMDD.");
                error = true;
            }
        }
    }

    if (CLIParamStrToBuf(arg_get_str(ctx, 5), can, sizeof(can) - 1, &slen) == 0 && slen != 0) {
        strn_upper((char *)can, slen);
    }

    uint8_t path[FILENAME_MAX] = { 0x00 };
    bool is_offline = CLIParamStrToBuf(arg_get_str(ctx, 6), path, sizeof(path), &slen) == 0 && slen > 0;
    bool show_images = arg_get_lit(ctx, 7);
    CLIParserFree(ctx);

    if ((IfPm3Iso14443() == false) && (is_offline == false)) {
        PrintAndLogEx(WARNING, "Only offline mode is available");
        error = true;
    }

    if (error) {
        return PM3_ESOFT;
    }

    if (is_offline) {
        return infoHF_EMRTD_offline((const char *)path);
    } else {
        bool restore_apdu_logging = GetAPDULogging();
        if (g_debugMode >= 2) {
            SetAPDULogging(true);
        }
        int res = infoHF_EMRTD((char *)docnum, (char *)dob, (char *)expiry, (const char *)can, BAC, !show_images);
        SetAPDULogging(restore_apdu_logging);
        return res;
    }
}

static int CmdHFeMRTDList(const char *Cmd) {
    return CmdTraceListAlias(Cmd, "hf emrtd", "7816");
}

static command_t CommandTable[] = {
    {"help",    CmdHelp,           AlwaysAvailable, "This help"},
    {"-----------", CmdHelp,           IfPm3Iso14443,   "------------------- " _CYAN_("Operations") " -------------------"},
    {"dump",    CmdHFeMRTDDump,    IfPm3Iso14443,   "Dump eMRTD files to binary files"},
    {"info",        CmdHFeMRTDInfo,    AlwaysAvailable, "Tag information"},
    {"list",    CmdHFeMRTDList,    AlwaysAvailable, "List ISO 14443A/7816 history"},
    {NULL, NULL, NULL, NULL}
};

static int CmdHelp(const char *Cmd) {
    (void)Cmd; // Cmd is not used so far
    CmdsHelp(CommandTable);
    return PM3_SUCCESS;
}

int CmdHFeMRTD(const char *Cmd) {
    clearCommandBuffer();
    return CmdsParse(CommandTable, Cmd);
}
