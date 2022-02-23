/*
 *  Copyright (C) 2019 - This file is part of x509-parser project
 *
 *  Author:
 *      Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
 *
 *  This software is licensed under a dual GPLv2/BSD license. See
 *  LICENSE file at the root folder of the project.
 */
#ifndef __X509_PARSER_H__
#define __X509_PARSER_H__

#include <stdint.h>
#include <unistd.h>
#include <string.h>

#if defined(__FRAMAC__)
#define ATTRIBUTE_UNUSED
#else
#define ATTRIBUTE_UNUSED __attribute__((unused))
#endif

typedef uint8_t	  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

/*
 * FIXME: document error values
 */

typedef enum {
	X509_PARSER_ERROR_VERSION_ABSENT            = -1,
	X509_PARSER_ERROR_VERSION_UNEXPECTED_LENGTH = -2,
	X509_PARSER_ERROR_VERSION_NOT_3             = -3,
} x509_parser_errors;


/* Knob to skip over currently unknown RDN elements */
#define TEMPORARY_LAXIST_HANDLE_ALL_REMAINING_RDN_OIDS

/*
 * Each certificate extension is made of an OID and an associated data value
 * for which we need a specific parsing function to validate the structure
 * of the data. This means that by default a certificate will be rejected if
 * an extensions is unknown. We define two macros to allow parsing to continue
 * when encoutering unsupported extensions (for which we do not have a specific
 * parsing function for data value)
 *
 * The first (TEMPORARY_LAXIST_HANDLE_COMMON_UNSUPPORTED_EXT_OIDS) handles
 * common extensions found in certificates which we know of but currently
 * have no parsing functions. Those extensions OID are explicitly referenced
 * in known_ext_oids table. When the knob is defined, the extensions data is
 * skipped to continue parsing, i.e. the structure of the data it carries is
 * NOT VERIFIED AT ALL. The check that the extension only appear once in the
 * certificate is performed.
 *
 * The second (TEMPORARY_LAXIST_HANDLE_ALL_REMAINING_EXT_OIDS) is used as a
 * catch-all for extensions that are not known. When the knob is defined:
 *
 *  - unknown extensions data structure is NOT VERIFIED AT ALL
 *  - NO CHECK is performed to verify that the extension appears only once
 *    in the certificate.
 */
#define TEMPORARY_LAXIST_HANDLE_COMMON_UNSUPPORTED_EXT_OIDS
#define TEMPORARY_LAXIST_HANDLE_ALL_REMAINING_EXT_OIDS

/*
 * Double the defined upper upper bound value of on common RDN components
 * (CN, O and OU) length from 64 to 128.
 */
#define TEMPORARY_LAXIST_RDN_UPPER_BOUND

/* Allow CA certificates w/o SKI. */
#define TEMPORARY_LAXIST_CA_WO_SKI

/* Allow emailAddress using UTF-8 encoding instead for IA5String. */
#define TEMPORARY_LAXIST_EMAILADDRESS_WITH_UTF8_ENCODING

/* Allow weak/bad algs w/o to parse more certificate fields from our set. */
#define TEMPORARY_BADALGS

/*
 * Same for otherwise unsupported extensions but for which we have an
 * internal reference to the OID
 */
#define TEMPORARY_BAD_EXT_OIDS

/*
 * Same for otherwise unsupported RDN but for which we have an internal
 * reference to the OID
 */
#define TEMPORARY_BAD_OID_RDN

/* Allow certificates w/ full directoryString . */
#define TEMPORARY_LAXIST_DIRECTORY_STRING

/*
 * Allow negative serial value
 */
#define TEMPORARY_LAXIST_SERIAL_NEGATIVE

/*
 * Allow large serial value. Limit is 20 bytes but some implementation
 * use larger serial.
 */
#define TEMPORARY_LAXIST_SERIAL_LENGTH

/*
 * Serial value is not expected to be 0. This knob make such certificate
 * valid.
 */
#define TEMPORARY_LAXIST_SERIAL_NULL

/*
 * Allow certificates w/ full basic constraints boolean explicitly set to false.
 * As this is the DEFAULT value, DER forbids encoding of that value.
 */
#define TEMPORARY_LAXIST_CA_BASIC_CONSTRAINTS_BOOLEAN_EXPLICIT_FALSE

/*
 * Allow certificates w/ extension's critical flag explicitly set to false.
 * As this is the DEFAULT value, DER forbids encoding of that value.
 */
#define TEMPORARY_LAXIST_EXTENSION_CRITICAL_FLAG_BOOLEAN_EXPLICIT_FALSE

/*
 * Allow certificates w/ SKI extension critical flag set. Section 4.2.1.1. of
 * RFC 5280 forbids that with a MUST.
 */
#define TEMPORARY_LAXIST_SKI_CRITICAL_FLAG_SET

/*
 * Allow serial DN component encoded as an IA5String whereas RFC 5280
 * requires such element to be encoded using printable string.
 */
#define TEMPORARY_LAXIST_SERIAL_RDN_AS_IA5STRING

/*
 * The following can be defined to enable an error trace to be
 * printed on standard output. The error path is made of the
 * lines in the representing the call graph leading to the
 * error.
 */
// #define ERROR_TRACE_ENABLE

/*
 * Max allowed buffer size for ASN.1 structures. Also note that
 * the type used for length in the whole code is an u16, so it
 * is pointless to set something higher than 65535.
 */
#define ASN1_MAX_BUFFER_SIZE 65534

typedef struct {
	/* Positions/length of various elements in cert */
	u16 tbs_start;
	u16 tbs_len;
	u16 issuer_start;
	u16 issuer_len;
	u16 serial_start;
	u16 serial_len;
	u16 subject_start;
	u16 subject_len;
	u16 spki_start;
	u16 spki_len;
	u16 spki_alg_oid_start;
	u16 spki_alg_oid_len;
	u16 spki_pub_key_start;
	u16 spki_pub_key_len;
	u16 sig_alg_start;
	u16 sig_alg_len;
	u16 sig_start;
	u16 sig_len;

	/* Info we grabbed while parsing */
	int version;
	u64 not_before;
	u64 not_after;
	int empty_subject;
	int san_empty;
	int san_critical;
	int ca_true;
	int bc_critical;
	int has_ski;
	int has_keyUsage;
	int keyCertSign_set;
	int cRLSign_set;
	int pathLenConstraint_set;
	int has_name_constraints;
	int has_crldp;
	int one_crldp_has_all_reasons;
	int aki_has_keyIdentifier;
	int subject_issuer_identical;
} cert_parsing_ctx;

/*
 * Return 0 if parsing went OK, a non zero value otherwise.
 * 'len' must exactly match the size of the certificate
 * in the buffer 'buf' (i.e. nothing is expected behind).
 */
int parse_x509_cert(cert_parsing_ctx *ctx, const u8 *buf, u16 len);

/*
 * This wrapper around parse_x509_cert() does not expect the buffer
 * to exactly contain a DER-encoded certificate, but to start with
 * one. It returns the length of the first sequence found in the
 * buffer, no matter if the certificate (this sequence) is valid
 * or not. It only requires the buffer to start with a sequence.
 * A value of 1 is returned in 'remain' if the buffer does not
 * start with a sequence.
 */
int parse_x509_cert_relaxed(const u8 *buf, u16 len, u16 *eaten);


int parse_sig_ecdsa_export_r_s(const u8 *buf, u16 len,
			       u16 *r_start_off, u16 *r_len,
			       u16 *s_start_off, u16 *s_len,
			       u16 *eaten);

int parse_sig_eddsa_export_r_s(const u8 *buf, u16 len,
			       u16 *r_start_off, u16 *r_len,
			       u16 *s_start_off, u16 *s_len,
			       u16 *eaten);

#endif /* __X509_PARSER_H__ */
