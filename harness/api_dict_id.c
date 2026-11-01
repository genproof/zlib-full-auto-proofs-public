// Law api_dict_id: For any dictionary (1 to 2^32 - 1 bytes, as much as deflateSetDictionary takes) and any data (any
// length the allocator provides) compressed with it (deflateInit2 with any windowBits 8..15 and any level, memLevel
// and strategy it accepts, deflateSetDictionary, then deflate: all of the data, in pieces of at most 2^32 - 1 bytes,
// Z_FINISH with the last, into deflateBound_z bytes; the run ends unless these succeed), inflate() offered the
// compressed bytes (at most 2^32 - 1 of them), room for the data (as much) and any flush returns Z_NEED_DICT with
// adler set to the Adler-32 of the dictionary, as a copy made before compression holds it.
#include "laws_common.h"

int main(void) {
	size_t dict_len = 1 + upto(UINT_MAX - 1);
	size_t data_len = upto(PTRDIFF_MAX);
	unsigned char *dict = alloc_any_bytes(dict_len);
	unsigned char *data = alloc_any_bytes(data_len);
	if (dict == NULL || data == NULL)
		return 0;
	unsigned char *dict_copy = copy_of(dict, dict_len);
	unsigned char *out = malloc(data_len);
	int level = (int) nondet_u32();
	int window_bits = 8 + (int) upto(7);
	int mem_level = (int) nondet_u32();
	int strategy = (int) nondet_u32();
	if (dict_copy == NULL || out == NULL)
		return 0;
	z_stream compressor;
	new_stream(&compressor);
	if (deflateInit2(&compressor, level, Z_DEFLATED, window_bits, mem_level, strategy) != Z_OK)
		return 0;
	if (deflateSetDictionary(&compressor, dict, (uInt) dict_len) != Z_OK)
		return 0;
	size_t out_size = deflateBound_z(&compressor, data_len);
	unsigned char *compressed = malloc(out_size);
	if (compressed == NULL)
		return 0;
	compressor.next_in = data;
	compressor.next_out = compressed;
	int code;
	do {
		size_t rest = data_len - (size_t) (compressor.next_in - data);
		int flush = Z_NO_FLUSH;
		if (rest <= UINT_MAX)
			flush = Z_FINISH;
		compressor.avail_in = clip(rest);
		compressor.avail_out = clip(out_size - (size_t) (compressor.next_out - compressed));

		code = deflate(&compressor, flush);
	} while (code == Z_OK);
	if (code != Z_STREAM_END)
		return 0;
	size_t compressed_len = (size_t) (compressor.next_out - compressed);
	z_stream decompressor;
	new_stream(&decompressor);
	// zlib.h, deflateInit2: "a request for 8 will result in 9"; "use 9 with inflateInit2()"
	if (window_bits == 8)
		window_bits = 9;
	if (inflateInit2(&decompressor, window_bits) != Z_OK)
		return 0;
	set_buffer(&decompressor, compressed, clip(compressed_len), out, clip(data_len));

	code = inflate(&decompressor, (int) nondet_u32());

	// RFC 1950 2.2, FDICT: "DICT is the Adler-32 checksum of this sequence of bytes". zlib.h, inflate: "If a preset
	// dictionary is needed after this call (see inflateSetDictionary below), inflate sets strm->adler to the
	// Adler-32 checksum of the dictionary chosen by the compressor and returns Z_NEED_DICT"
	gp_assert(code == Z_NEED_DICT && decompressor.adler == adler32_z(1, dict_copy, dict_len));
	return 0;
}
