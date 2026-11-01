#!/usr/bin/env bash
# patch/difftest.sh, run in the patched tree (`tools/qp tree zlib`): the quickproof patch (patch/PATCH.md).
#  1. The idiom edits (I1-I5) change no behaviour: patch/difftest_drv.c is built against the unmodified zlib ($ORIG,
#     default: the tree of `tools/qp tree zlib --orig`) and against the idiom-patched zlib (zlibpatch.py --no-fix,
#     built here from $ORIG), by gcc -O2, gcc -O1 with ASan/UBSan, and CompCert's ccomp (when on PATH, e.g. after
#     `eval $(opam env --switch=liblzma)`); every pair must print the same bytes for $N cases per seed.
#  2. The fixes change only what they fix: F1 strm->total_in after Z_NEED_DICT, F2 adler32 with a Z_NULL buffer and
#     length 1 (which zlib itself and the driver never do), F3 deflateBound for Z_FIXED at levels 1-3 with windowBits
#     15 and memLevel 8, F5 the result of deflate(Z_FINISH) when the last block of a raw stream exactly fills the
#     output space, F4 inflate_fast's rewind of next_in after inflatePrime leaves 8+ bits buffered (a
#     deterministic inflateprime_probe runs every case), and F6 the window of a stream that inflateSync made raw
#     while its windowBits asked for the header's window size (a deterministic sync_window_probe runs every case).
#     Every run sets GP_NO_F6_SYNC=1: the driver does not call inflateSync for such streams, where the unmodified
#     code can overflow the window after an inflateReset2 (F6: undefined behaviour, nothing to compare).
#     The idiom-patched and the fully patched (this tree) builds print the same bytes when these are hidden
#     (GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_HIDE_F6=1); with one fix shown and
#     the others hidden, they differ exactly when that fix's cases occur (some stream returned Z_NEED_DICT; some F3
#     or F5 case was probed; the F4 and F6 probes always run).
# Usage: [N=1500] [SEEDS="1 2 3"] patch/difftest.sh
set -euo pipefail
cd "$(dirname "$0")/.."
ORIG=${ORIG:-$HOME/zlib-1.3.2-orig}
N=${N:-1500}
SEEDS=${SEEDS:-"1 2 3"}
B=build/difftest; rm -rf $B; mkdir -p $B/nofix
cp "$ORIG"/*.c "$ORIG"/*.h $B/nofix/
(cd $B/nofix && python3 ../../../patch/zlibpatch.py --no-fix)
LIB="adler32.c crc32.c deflate.c trees.c inflate.c inffast.c inftrees.c zutil.c compress.c uncompr.c"
ok=1
build() {   # $1 out, $2 dir, $3.. compiler and flags
  local out=$1 dir=$2; shift 2
  local srcs=(); for f in $LIB; do srcs+=("$dir/$f"); done
  "$@" -DZ_TESTW= -I"$dir" "${srcs[@]}" patch/difftest_drv.c -o "$out"
}
hash_of() {   # $1 binary, $2 seed, [env]
  local exe=$1 s=$2
  (set -o pipefail; ASAN_OPTIONS=detect_leaks=0 "$exe" "$s" "$N" 2>"$B/summary" | sha256sum | cut -c1-16)
}
run() {   # $1 label, $2.. compiler and flags
  local label=$1; shift
  build $B/orig "$ORIG" "$@" || { echo "$label: build failed (orig)"; ok=0; return; }
  build $B/nofix_exe $B/nofix "$@" || { echo "$label: build failed (idiom patch)"; ok=0; return; }
  build $B/full . "$@" || { echo "$label: build failed (patched)"; ok=0; return; }
  for s in $SEEDS; do
    local h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    h1=$(GP_NO_F6_SYNC=1 hash_of $B/orig $s) || { echo "$label seed $s: orig FAILED"; ok=0; continue; }
    h2=$(GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { echo "$label seed $s: idiom-patched FAILED"; ok=0; continue; }
    local summary; summary=$(cat $B/summary)
    if [ "$h1" = "$h2" ]; then echo "$label seed $s: orig = idiom-patched ($h1), $summary"
    else echo "$label seed $s: orig and idiom-patched DIFFER"; ok=0; fi
    h3=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { ok=0; continue; }
    h4=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/full $s) \
      || { echo "$label seed $s: patched FAILED"; ok=0; continue; }
    if [ "$h3" = "$h4" ]; then echo "$label seed $s: idiom-patched = patched with the fixed values hidden ($h3)"
    else echo "$label seed $s: idiom-patched and patched DIFFER beyond the fixed values"; ok=0; fi
    # F1 alone: deflate's fixes, F4 and F6 hidden
    h5=$(GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { ok=0; continue; }
    h6=$(GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/full $s) || { ok=0; continue; }
    if grep -q ' 0 streams with Z_NEED_DICT' $B/summary; then
      [ "$h5" = "$h6" ] || { echo "$label seed $s: patched differs without Z_NEED_DICT"; ok=0; }
    else
      [ "$h5" != "$h6" ] && echo "$label seed $s: F1 visible: total_in differs after Z_NEED_DICT" \
        || { echo "$label seed $s: F1 not visible"; ok=0; }
    fi
    # F3 and F5 alone: total_in hidden after Z_NEED_DICT, F4 and F6 hidden
    h7=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { ok=0; continue; }
    h8=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_F4=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/full $s) || { ok=0; continue; }
    if grep -q ' 0 F3 bounds, 0 F5 exact finishes' $B/summary; then
      [ "$h7" = "$h8" ] || { echo "$label seed $s: patched differs without F3/F5 cases"; ok=0; }
    else
      [ "$h7" != "$h8" ] && echo "$label seed $s: F3/F5 visible: $(sed 's/.*Z_NEED_DICT, //' $B/summary)" \
        || { echo "$label seed $s: F3/F5 not visible"; ok=0; }
    fi
    # F4 alone: total_in, deflate's fixes and F6 hidden (the inflatePrime probe runs every case, so F4 is always
    # shown)
    h9=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { ok=0; continue; }
    h10=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F6=1 GP_NO_F6_SYNC=1 hash_of $B/full $s) || { ok=0; continue; }
    [ "$h9" != "$h10" ] && echo "$label seed $s: F4 visible: inflate_fast rewind after inflatePrime" \
      || { echo "$label seed $s: F4 not visible"; ok=0; }
    # F6 alone: total_in, deflate's fixes and F4 hidden (the sync window probe runs every case, so F6 is always
    # shown)
    h11=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_NO_F6_SYNC=1 hash_of $B/nofix_exe $s) || { ok=0; continue; }
    h12=$(GP_NO_TOTAL_IN_AFTER_NEED_DICT=1 GP_HIDE_DEFLATE_FIXES=1 GP_HIDE_F4=1 GP_NO_F6_SYNC=1 hash_of $B/full $s) || { ok=0; continue; }
    [ "$h11" != "$h12" ] && echo "$label seed $s: F6 visible: the window of a raw stream after inflateSync" \
      || { echo "$label seed $s: F6 not visible"; ok=0; }
  done
}
run "gcc -O2" gcc -O2 -w
run "gcc -O1 ASan/UBSan" gcc -O1 -g -w -fsanitize=address,undefined -fno-sanitize-recover=all
if command -v ccomp > /dev/null; then
  N=$((N / 5)) run "ccomp" ccomp -fstruct-passing
else
  echo "ccomp: not on PATH, skipped"
fi
rm -rf $B
[ $ok = 1 ] && echo "patch/difftest.sh: idiom edits change no behaviour; the fixes change only total_in after Z_NEED_DICT (F1), deflateBound for Z_FIXED at levels 1-3 (F3), inflate_fast's next_in after inflatePrime (F4), deflate's result at an exact raw finish (F5) and the window of a raw stream after inflateSync (F6)" \
  || { echo "patch/difftest.sh: FAILED"; exit 1; }
