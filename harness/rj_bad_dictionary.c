// Law rj_bad_dictionary: For a zlib stream that starts with any header asking for a dictionary (FDICT set, any DICTID,
// any CINFO the windowBits 8..15 allow, any FLEVEL), followed by any bytes (any length the allocator provides): once
// inflate() offered the stream (at most 2^32 - 1 bytes of it), with any output space and any flush, has returned
// Z_NEED_DICT, inflateSetDictionary with any bytes (up to 2^32 - 1, as many as it takes) whose Adler-32 is not DICTID
// returns Z_DATA_ERROR.
#include "laws_common.h"

int main(void) {
	int window_bits = 8 + (int) upto(7);
	size_t stream_len = 6 + upto(PTRDIFF_MAX - 6);
	size_t room = nondet_u32();
	size_t dict_len = nondet_u32();
	unsigned char *stream = alloc_any_bytes(stream_len);
	unsigned char *out = malloc(room);
	unsigned char *dict = alloc_any_bytes(dict_len);
	if (stream == NULL || out == NULL || dict == NULL)
		return 0;
	// RFC 1950 2.2: CMF = CINFO << 4 | CM 8; FLG = FLEVEL, FDICT, FCHECK, with (CMF*256 + FLG) a multiple of 31;
	// "If FDICT is set, a DICT dictionary identifier is present immediately after the FLG byte" (4 bytes, MSB
	// first)
	unsigned cinfo = (unsigned) upto(window_bits - 8);
	stream[0] = (unsigned char) (cinfo << 4 | 8);
	stream[1] = (unsigned char) ((stream[1] & 0xc0) | 0x20);
	stream[1] = (unsigned char) (stream[1] + (31 - (stream[0] * 256 + stream[1]) % 31) % 31);
	uLong dictid = (uLong) stream[2] << 24 | (uLong) stream[3] << 16 | (uLong) stream[4] << 8 | stream[5];
	gp_assume(adler32_z(1, dict, dict_len) != dictid);
	z_stream strm;
	new_stream(&strm);
	if (inflateInit2(&strm, window_bits) != Z_OK)
		return 0;
	set_buffer(&strm, stream, clip(stream_len), out, room);

	gp_assert(inflate(&strm, (int) nondet_u32()) == Z_NEED_DICT);

	// RFC 1950 2.3: "A compliant decompressor must give an error indication if FDICT is set and DICTID is not the
	// identifier of a known preset dictionary." zlib.h, inflateSetDictionary: "Z_DATA_ERROR if the given dictionary
	// doesn't match the expected one (incorrect Adler-32 value)"

	gp_assert(inflateSetDictionary(&strm, dict, (uInt) dict_len) == Z_DATA_ERROR);

	return 0;
}
