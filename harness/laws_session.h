// laws_session.h: helpers of the laws that drive a z_stream, included after laws_common.h. No models, no algorithms.
static int deflate_params_ok(int level, int window_bits, int mem_level, int strategy) {
	// zlib.h, deflateInit2: level "Z_DEFAULT_COMPRESSION, or between 0 and 9"; memLevel 1..MAX_MEM_LEVEL (9,
	// zconf.h); strategy Z_DEFAULT_STRATEGY (0) .. Z_FIXED (4); windowBits 8..15, "-8..-15 for raw deflate", "Add 16
	// to windowBits to write a simple gzip header", but "For raw deflate or gzip encoding, a request for a 256-byte
	// window is rejected as invalid"
	int zlib_window = window_bits >= 8 && window_bits <= 15;
	int raw_window = window_bits >= -15 && window_bits <= -9;
	int gzip_window = window_bits >= 16 + 9 && window_bits <= 16 + 15;
	int valid = level >= -1 && level <= 9 && mem_level >= 1 && mem_level <= 9 && strategy >= 0 && strategy <= Z_FIXED;
	return valid && (zlib_window || raw_window || gzip_window);
}
static int inflate_window_ok(int window_bits) {
	// zlib.h, inflateInit2: windowBits "should be in the range 8..15", "can also be zero to request that inflate
	// use the window size in the zlib header", "can also be -8..-15 for raw inflate", "Add 32 to windowBits to
	// enable zlib and gzip decoding with automatic header detection, or add 16 to decode only the gzip format"
	int low = window_bits & 15;
	int raw = window_bits >= -15 && window_bits <= -8;
	int wrapped = window_bits >= 0 && window_bits < 48 && (low == 0 || low >= 8);
	return raw || wrapped;
}
struct position {
	unsigned char *next_in;
	uInt avail_in;
	unsigned char *next_out;
	uInt avail_out;
	uLong total_in;
	uLong total_out;
};
static void position_of(z_stream *strm, struct position *at) {
	at->next_in = strm->next_in;
	at->avail_in = strm->avail_in;
	at->next_out = strm->next_out;
	at->avail_out = strm->avail_out;
	at->total_in = strm->total_in;
	at->total_out = strm->total_out;
}
static int unmoved(z_stream *strm, struct position *at) {
	int in = strm->next_in == at->next_in && strm->avail_in == at->avail_in && strm->total_in == at->total_in;
	int out = strm->next_out == at->next_out && strm->avail_out == at->avail_out && strm->total_out == at->total_out;
	return in && out;
}
static int accounted(z_stream *strm, struct position *at) {
	int in = strm->avail_in <= at->avail_in && strm->next_in + strm->avail_in == at->next_in + at->avail_in;
	int out = strm->avail_out <= at->avail_out && strm->next_out + strm->avail_out == at->next_out + at->avail_out;
	return in && out;
}
static int counted(z_stream *strm, struct position *at) {
	int in = strm->total_in == at->total_in + (at->avail_in - strm->avail_in);
	int out = strm->total_out == at->total_out + (at->avail_out - strm->avail_out);
	return in && out;
}
