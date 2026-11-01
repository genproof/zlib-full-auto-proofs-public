// Law rt_session: For any level, windowBits, memLevel and strategy in zlib.h's ranges for deflateInit2 (raw, zlib or
// gzip wrapper), with or without, after it, deflateSetDictionary of any dictionary (1 to 2^32 - 1 bytes; zlib or raw
// wrapper) or deflateSetHeader of any gzip header (text, os, hcrc: any ints; time below 2^32; an extra field of up to
// 65535 bytes, a name and a comment of up to 2^32 - 2 nonzero bytes, each present or not; gzip wrapper), and any data
// (any length the allocator provides) given to deflate() in any pieces (at most 2^32 - 1 bytes per call), with any
// output space (at most 2^32 - 1 bytes per call, none included, from a buffer of any size; running out of it ends the
// run) and any flush Z_NO_FLUSH..Z_BLOCK per call (Z_FINISH coming with the rest of the data once one call can take it,
// and repeated until Z_STREAM_END), then inflateInit2 with the matching windowBits, inflateGetHeader with buffers of
// exactly the fields' sizes (if a header was set), inflateSetDictionary of a copy of the dictionary (raw wrapper: after
// inflateInit2; zlib wrapper: when inflate() returns Z_NEED_DICT), and inflate() fed the compressed bytes followed by
// any bytes (any number up to PTRDIFF_MAX minus the stream's length) in any pieces, empty ones included, with any
// output space, none included, and any flush: deflateInit2, deflateSetDictionary, deflateSetHeader, inflateInit2,
// inflateGetHeader and inflateSetDictionary return Z_OK; every call moves next_in and next_out exactly as far as it
// lowers avail_in and avail_out; a deflate() call offered no output space returns Z_BUF_ERROR and moves no pointer and
// no counter; inflate() returns only Z_OK, Z_BUF_ERROR or Z_NEED_DICT until Z_STREAM_END, Z_NEED_DICT exactly once when
// a dictionary was set with the zlib wrapper and never otherwise, a call offered neither input nor output space does
// not return Z_OK and moves no pointer and no counter, and at Z_STREAM_END it has read exactly the compressed bytes,
// none of the bytes after them, written exactly the data, as a copy made before compression holds it, and reported the
// header complete with the fields that copies made before compression hold, and Z_NULL for an absent one (Z_MEM_ERROR
// ends the run).
#include "laws_common.h"
#include "laws_session.h"

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
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	unsigned char choice = nondet_u8();
	int with_dict = window_bits <= 15 && (choice & 1);
	int with_head = window_bits > 15 && (choice & 1);
	// RFC 1952 2.3: MTIME is 4 bytes, OS 1, XLEN 2; the name and the comment are "zero-terminated"
	size_t dict_len = 1 + upto(UINT_MAX - 1);
	size_t extra_len = upto(65535);
	size_t name_len = upto(UINT_MAX - 1);
	size_t comment_len = upto(UINT_MAX - 1);
	size_t data_len = upto(PTRDIFF_MAX);
	size_t out_size = upto(PTRDIFF_MAX);
	int text = (int) nondet_u32();
	uLong time = nondet_u32();
	int os = (int) nondet_u32();
	int hcrc = (int) nondet_u32();
	unsigned char *dict = alloc_any_bytes(dict_len);
	unsigned char *extra = alloc_any_bytes(extra_len);
	unsigned char *name = any_string(name_len);
	unsigned char *comment = any_string(comment_len);
	unsigned char *data = alloc_any_bytes(data_len);
	if (!dict || !extra || !name || !comment || !data)
		return 0;
	unsigned char *dict_copy = copy_of(dict, dict_len);
	unsigned char *extra_copy = copy_of(extra, extra_len);
	unsigned char *name_copy = copy_of(name, name_len + 1);
	unsigned char *comment_copy = copy_of(comment, comment_len + 1);
	unsigned char *expected = copy_of(data, data_len);
	unsigned char *compressed = malloc(out_size);
	unsigned char *out = malloc(data_len);
	gz_header head;
	head.text = text;
	head.time = time;
	head.os = os;
	head.hcrc = hcrc;
	head.extra = (choice & 2) ? extra : Z_NULL;
	head.extra_len = (uInt) extra_len;
	head.name = (choice & 4) ? name : Z_NULL;
	head.comment = (choice & 8) ? comment : Z_NULL;
	gz_header got;
	got.extra = malloc(extra_len);
	got.extra_max = (uInt) extra_len;
	got.name = malloc(name_len + 1);
	got.name_max = (uInt) (name_len + 1);
	got.comment = malloc(comment_len + 1);
	got.comm_max = (uInt) (comment_len + 1);
	if (!dict_copy || !extra_copy || !name_copy || !comment_copy || !expected || !compressed || !out)
		return 0;
	if (!got.extra || !got.name || !got.comment)
		return 0;
	z_stream compressor;
	new_stream(&compressor);
	int code = deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	// zlib.h, deflateSetDictionary and deflateSetHeader: "returns Z_OK if success"
	if (with_dict)
		gp_assert(deflateSetDictionary(&compressor, dict, (uInt) dict_len) == Z_OK);
	if (with_head)
		gp_assert(deflateSetHeader(&compressor, &head) == Z_OK);
	compressor.next_in = data;
	compressor.next_out = compressed;
	size_t offered = 0;
	int flush = Z_NO_FLUSH;
	struct position at;
	do {
		size_t read = (size_t) (compressor.next_in - data);
		if (flush != Z_FINISH) {
			offered += upto(data_len - offered);
			flush = (int) upto(Z_BLOCK);
			if (flush == Z_FINISH && data_len - read > UINT_MAX)
				flush = Z_NO_FLUSH;
			if (flush == Z_FINISH)
				offered = data_len;
		}
		compressor.avail_in = clip(offered - read);
		compressor.avail_out = clip(upto(out_size - (size_t) (compressor.next_out - compressed)));
		position_of(&compressor, &at);

		code = deflate(&compressor, flush);

		// zlib.h, deflate: "Compress more input starting at next_in and update next_in and avail_in accordingly";
		// "Z_BUF_ERROR if no progress is possible (for example avail_in or avail_out was zero)"
		gp_assert(accounted(&compressor, &at));
		if (at.avail_out == 0)
			gp_assert(code == Z_BUF_ERROR && unmoved(&compressor, &at));
		if (code != Z_STREAM_END && compressor.next_out == compressed + out_size)
			return 0;
	} while (code != Z_STREAM_END);
	size_t compressed_len = (size_t) (compressor.next_out - compressed);
	// RFC 1950 2.2: "Any data which may appear after ADLER32 are not part of the zlib stream." zlib.h,
	// inflateInit2: "inflate() will return Z_STREAM_END at the end of the gzip member."
	size_t after = upto(PTRDIFF_MAX - compressed_len);
	unsigned char *input = alloc_any_bytes(compressed_len + after);
	if (input == NULL)
		return 0;
	for (size_t i = 0; i < compressed_len; i++)
		input[i] = compressed[i];
	z_stream decompressor;
	new_stream(&decompressor);
	// zlib.h, deflateInit2: "a request for 8 will result in 9"; "use 9 with inflateInit2()"
	if (window_bits == 8)
		window_bits = 9;
	code = inflateInit2(&decompressor, window_bits);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	if (with_head)
		gp_assert(inflateGetHeader(&decompressor, &got) == Z_OK);
	// zlib.h, inflateSetDictionary: "For raw inflate, this function can be called at any time to set the
	// dictionary."; "This function must be called immediately after a call of inflate, if that call returned
	// Z_NEED_DICT."
	if (with_dict && window_bits < 0) {
		code = inflateSetDictionary(&decompressor, dict_copy, (uInt) dict_len);
		if (code == Z_MEM_ERROR)
			return 0;
		gp_assert(code == Z_OK);
	}
	int asked = 0;
	decompressor.next_in = input;
	decompressor.next_out = out;
	do {
		decompressor.avail_in = clip(upto(compressed_len + after - (size_t) (decompressor.next_in - input)));
		decompressor.avail_out = clip(upto(data_len - (size_t) (decompressor.next_out - out)));
		position_of(&decompressor, &at);

		code = inflate(&decompressor, (int) nondet_u32());

		if (code == Z_MEM_ERROR)
			return 0;
		gp_assert(code == Z_OK || code == Z_BUF_ERROR || code == Z_STREAM_END || code == Z_NEED_DICT);
		gp_assert(accounted(&decompressor, &at));
		// zlib.h, inflate() "returns Z_OK if some progress has been made (more input processed or more output
		// produced)"
		if (at.avail_in == 0 && at.avail_out == 0)
			gp_assert(code != Z_OK && unmoved(&decompressor, &at));
		if (code == Z_NEED_DICT) {
			gp_assert(with_dict && window_bits > 0 && !asked);
			asked = 1;
			code = inflateSetDictionary(&decompressor, dict_copy, (uInt) dict_len);
			if (code == Z_MEM_ERROR)
				return 0;
			gp_assert(code == Z_OK);
		}
	} while (code != Z_STREAM_END);
	gp_assert(asked == (with_dict && window_bits > 0));
	gp_assert(decompressor.next_in == input + compressed_len);
	gp_assert(decompressor.next_out == out + data_len && bytes_eq(out, expected, data_len));
	if (!with_head)
		return 0;
	// zlib.h, inflateGetHeader: "head->done is set to one" once the header is complete; "If any of extra, name, or
	// comment are not present in the header, then that field's pointer is set to Z_NULL"
	gp_assert(got.done == 1 && got.text == (text != 0) && got.hcrc == (hcrc != 0));
	gp_assert(got.os == (os & 255) && got.time == time);
	gp_assert(same_field(choice & 2, got.extra, extra_copy, extra_len));
	gp_assert(!(choice & 2) || got.extra_len == extra_len);
	gp_assert(same_field(choice & 4, got.name, name_copy, name_len + 1));
	gp_assert(same_field(choice & 8, got.comment, comment_copy, comment_len + 1));
	return 0;
}
