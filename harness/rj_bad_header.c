// Law rj_bad_header: For any windowBits that selects the zlib wrapper (0, 8..15, or those plus 32, when the input does
// not start with the gzip magic 1f 8b) and any input (2 bytes to 2^32 - 1) whose first two bytes CMF and FLG break RFC
// 1950 2.2 (CMF*256 + FLG not a multiple of 31, or CM not 8, or CINFO above 7, or CINFO + 8 above windowBits when that
// is not 0 or 32), one inflate() call with any output space and any flush refuses it before any output: it returns
// Z_DATA_ERROR with total_out 0 and the output space unchanged.
#include "laws_common.h"

int main(void) {
	int window_bits = (int) upto(47);
	int low = window_bits & 15;
	gp_assume((window_bits & 16) == 0 && (low == 0 || low >= 8));
	size_t input_len = 2 + upto(UINT_MAX - 2);
	size_t room = nondet_u32();
	unsigned char *input = alloc_any_bytes(input_len);
	unsigned char *out = alloc_any_bytes(room);
	if (input == NULL || out == NULL)
		return 0;
	unsigned char *before = copy_of(out, room);
	if (before == NULL)
		return 0;
	// RFC 1950 2.2: "The FCHECK value must be such that CMF and FLG, when viewed as a 16-bit unsigned integer
	// stored in MSB order (CMF*256 + FLG), is a multiple of 31"; "CM = 8 denotes the "deflate" compression method";
	// "Values of CINFO above 7 are not allowed". zlib.h, inflateInit2: "If a compressed stream with a larger window
	// size is given as input, inflate() will return with the error code Z_DATA_ERROR"
	unsigned cmf = input[0];
	unsigned flg = input[1];
	unsigned cinfo = cmf >> 4;
	int bad_check = (cmf * 256 + flg) % 31 != 0;
	int bad_method = (cmf & 15) != 8;
	int bad_window = cinfo > 7 || (low != 0 && cinfo + 8 > (unsigned) low);
	gp_assume(bad_check || bad_method || bad_window);
	gp_assume(window_bits < 32 || cmf != 0x1f || flg != 0x8b);
	z_stream strm;
	new_stream(&strm);
	if (inflateInit2(&strm, window_bits) != Z_OK)
		return 0;
	set_buffer(&strm, input, input_len, out, room);

	int code = inflate(&strm, (int) nondet_u32());

	// RFC 1950 2.3: "A compliant decompressor must check CMF, FLG, and ADLER32, and provide an error indication if
	// any of these have incorrect values."
	gp_assert(code == Z_DATA_ERROR && strm.total_out == 0 && bytes_eq(out, before, room));
	return 0;
}
