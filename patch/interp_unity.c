/* patch/interp_unity.c: the zlib units as one translation unit, for CompCert's interpreter only (quickproof.conf
 * INTERP_UNITS, read by quickproof/tools/interp.sh only).  interp.sh renames the struct tags a unit's .c file
 * defines (trees.c: struct static_tree_desc_s), which breaks deflate.h's typedef of it; included here in one
 * unit, the names stay as they are.  zutil.c comes last: its gzguts.h defines COPY and GZIP, names that
 * inflate.h's enum and deflate.c use.  The proofs (tools/clight.sh) and native runs use the units one by one. */
#include "inflate.c"
#include "inffast.c"
#include "inftrees.c"
#include "uncompr.c"
#include "adler32.c"
#include "crc32.c"
#include "deflate.c"
#include "trees.c"
#include "compress.c"
#include "zutil.c"
