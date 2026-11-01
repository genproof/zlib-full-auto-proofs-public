// Law rt_gzip_header: For any gzip header given to deflateSetHeader (text, os, hcrc: any ints; time below 2^32; an
// extra field of up to 65535 bytes, a name and a comment of any length up to 2^32 - 2 nonzero bytes, as much as
// inflateGetHeader's buffers take with the zero, each present or not), after deflateInit2 with any windowBits
// 16 + 9..15 and any level, memLevel and strategy it accepts and deflate(Z_FINISH) into deflateBound_z bytes, in pieces
// of at most 2^32 - 1 bytes (the run ends unless these succeed), inflate(Z_FINISH) with inflateGetHeader (buffers of
// exactly the fields' sizes) fed the compressed bytes in pieces of at most 2^32 - 1 bytes reports the header complete
// with the same fields as copies made before compression hold, and Z_NULL for an absent one (Z_MEM_ERROR ends the
// run).
#include "laws_common.h"

static unsigned char *any_string(size_t len) {
	unsigned char *string = alloc_any_bytes(len + 1);
	if (string == NULL)
		return NULL;
	for (size_t i = 0; i < len; i++)
		gp_assume(string[i] != 0);
	string[len] = 0;
	return string;
}

static int same_field(int present, unsigned char *got, unsigned char *given, size_t len) {
	if (!present)
		return got == Z_NULL;                        // zlib.h: absent fields are "set to Z_NULL"
	return got != Z_NULL && bytes_eq(got, given, len);
}

int main(void) {
	// RFC 1952 2.3: MTIME is 4 bytes, OS 1, XLEN 2; the name and the comment are "zero-terminated"
	size_t extra_len = upto(65535);
	size_t name_len = upto(UINT_MAX - 1);
	size_t comment_len = upto(UINT_MAX - 1);
	unsigned char present = nondet_u8();
	int text = (int) nondet_u32();
	uLong time = nondet_u32();
	int os = (int) nondet_u32();
	int hcrc = (int) nondet_u32();
	unsigned char *extra = alloc_any_bytes(extra_len);
	unsigned char *name = any_string(name_len);
	unsigned char *comment = any_string(comment_len);
	if (!extra || !name || !comment)
		return 0;
	unsigned char *extra_copy = copy_of(extra, extra_len);
	unsigned char *name_copy = copy_of(name, name_len + 1);
	unsigned char *comment_copy = copy_of(comment, comment_len + 1);
	gz_header head;
	head.text = text;
	head.time = time;
	head.os = os;
	head.hcrc = hcrc;
	head.extra = (present & 1) ? extra : Z_NULL;
	head.extra_len = (uInt) extra_len;
	head.name = (present & 2) ? name : Z_NULL;
	head.comment = (present & 4) ? comment : Z_NULL;
	int level = (int) nondet_u32();
	int window_bits = 16 + 9 + (int) upto(6);
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gz_header got;
	got.extra = malloc(extra_len);
	got.extra_max = (uInt) extra_len;
	got.name = malloc(name_len + 1);
	got.name_max = (uInt) (name_len + 1);
	got.comment = malloc(comment_len + 1);
	got.comm_max = (uInt) (comment_len + 1);
	if (!extra_copy || !name_copy || !comment_copy || !got.extra || !got.name || !got.comment)
		return 0;
	z_stream compressor;
	new_stream(&compressor);
	if (deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy) != Z_OK)
		return 0;
	if (deflateSetHeader(&compressor, &head) != Z_OK)
		return 0;
	size_t out_size = deflateBound_z(&compressor, 0);
	unsigned char *compressed = malloc(out_size);
	if (compressed == NULL)
		return 0;
	compressor.next_out = compressed;
	int code;
	do {
		compressor.avail_out = clip(out_size - (size_t) (compressor.next_out - compressed));

		code = deflate(&compressor, Z_FINISH);
	} while (code == Z_OK);
	if (code != Z_STREAM_END)
		return 0;
	size_t compressed_len = (size_t) (compressor.next_out - compressed);
	z_stream decompressor;
	new_stream(&decompressor);
	if (inflateInit2(&decompressor, window_bits) != Z_OK || inflateGetHeader(&decompressor, &got) != Z_OK)
		return 0;
	unsigned char room[1];
	set_buffer(&decompressor, compressed, 0, room, 1);
	do {
		decompressor.avail_in = clip(compressed_len - (size_t) (decompressor.next_in - compressed));

		code = inflate(&decompressor, Z_FINISH);

		if (code == Z_MEM_ERROR)
			return 0;
	} while (code == Z_BUF_ERROR && decompressor.next_in != compressed + compressed_len);
	// zlib.h, inflateGetHeader: "head->done is set to one" once the header is complete; "If any of extra, name, or
	// comment are not present in the header, then that field's pointer is set to Z_NULL"
	gp_assert(got.done == 1 && got.text == (text != 0) && got.hcrc == (hcrc != 0));
	gp_assert(got.os == (os & 255) && got.time == time);
	gp_assert(same_field(present & 1, got.extra, extra_copy, extra_len));
	gp_assert(!(present & 1) || got.extra_len == extra_len);
	gp_assert(same_field(present & 2, got.name, name_copy, name_len + 1));
	gp_assert(same_field(present & 4, got.comment, comment_copy, comment_len + 1));
	return 0;
}
