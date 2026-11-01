// Law res_bound: After deflateInit2 with any level, windowBits, memLevel and strategy in zlib.h's ranges (it returns
// Z_OK; Z_MEM_ERROR ends the run) and, or not, deflateSetDictionary with any dictionary (zlib or raw; up to 2^32 - 1
// bytes, as much as it takes) or deflateSetHeader with any gzip header (text, time, os, hcrc; an extra field up to
// 65535 bytes, a name and a comment up to 2^32 - 2 bytes, each present or not), one deflate(Z_FINISH) offered any data
// and exactly deflateBound bytes of output space (zlib.h's guarantee is for that one call: data and bound below 2^32)
// returns Z_STREAM_END, having read all of the data (avail_in 0, next_in at its end, total_in up by its length) and
// written at most deflateBound bytes (total_out as many).
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

int main(void) {
	int level = (int) nondet_u32();
	int window_bits = (int) nondet_u32();
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	gp_assume(deflate_params_ok(level, window_bits, mem_level, strategy));
	size_t data_len = nondet_u32();
	unsigned char *data = alloc_any_bytes(data_len);
	unsigned char choice = nondet_u8();
	size_t dict_len = nondet_u32();
	size_t extra_len = upto(65535);
	size_t name_len = upto(UINT_MAX - 1);
	size_t comment_len = upto(UINT_MAX - 1);
	unsigned char *dict = alloc_any_bytes(dict_len);
	unsigned char *extra = alloc_any_bytes(extra_len);
	unsigned char *name = any_string(name_len);
	unsigned char *comment = any_string(comment_len);
	if (!data || !dict || !extra || !name || !comment)
		return 0;
	gz_header head;
	head.text = (int) nondet_u32();
	head.time = nondet_u32();
	head.os = (int) nondet_u32();
	head.hcrc = (int) nondet_u32();
	head.extra = (choice & 2) ? extra : Z_NULL;
	head.extra_len = (uInt) extra_len;
	head.name = (choice & 4) ? name : Z_NULL;
	head.comment = (choice & 8) ? comment : Z_NULL;
	z_stream strm;
	new_stream(&strm);
	int code = deflateInit2(&strm, level, Z_DEFLATED, window_bits, mem_level, strategy);
	if (code == Z_MEM_ERROR)
		return 0;
	gp_assert(code == Z_OK);
	if ((choice & 1) && window_bits > 15)
		gp_assert(deflateSetHeader(&strm, &head) == Z_OK);
	if ((choice & 1) && window_bits <= 15)
		gp_assert(deflateSetDictionary(&strm, dict, (uInt) dict_len) == Z_OK);
	uLong bound = deflateBound(&strm, data_len);
	gp_assume(bound <= UINT_MAX);
	unsigned char *compressed = malloc(bound);
	if (compressed == NULL)
		return 0;
	set_buffer(&strm, data, data_len, compressed, bound);
	uLong total_in = strm.total_in;
	// zlib.h, deflateBound: "If that first deflate() call is provided the sourceLen input bytes, an output buffer
	// allocated to the size returned by deflateBound(), and the flush value Z_FINISH, then deflate() is guaranteed
	// to return Z_STREAM_END."

	code = deflate(&strm, Z_FINISH);

	gp_assert(code == Z_STREAM_END);
	size_t wrote = (size_t) (strm.next_out - compressed);
	gp_assert(wrote <= bound && strm.avail_in == 0 && strm.next_in == data + data_len);
	gp_assert(strm.total_in == total_in + data_len && strm.total_out == wrote);
	return 0;
}
