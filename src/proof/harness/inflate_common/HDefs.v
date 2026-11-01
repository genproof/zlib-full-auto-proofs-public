(* Pure definitions of the inflate harnesses' helper functions (harness/zlib_common.h), shared by the
   inflate laws: the values the helpers compute. *)
From Coq Require Import ZArith List Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.inflate_api.ApiModel.
Import ListNotations.
Local Open Scope Z_scope.

(* be32(p): the 4 bytes p[0..4), big-endian *)
Definition be32 (l: list Z) : Z :=
  Znth 0 l * 2 ^ 24 + Znth 1 l * 2 ^ 16 + Znth 2 l * 2 ^ 8 + Znth 3 l.

(* inflate_code_ok(r): one of inflate()'s documented return codes *)
Definition code_okb (r: Z) : bool :=
  (r =? Z_OK) || (r =? Z_STREAM_END) || (r =? Z_NEED_DICT) || (r =? Z_DATA_ERROR) || (r =? Z_STREAM_ERROR) ||
  (r =? Z_MEM_ERROR) || (r =? Z_BUF_ERROR).

(* inflate_wbits_ok(w) is ApiModel.wbits_ok w *)

(* the harness's zlib_ok: windowBits with which a zlib wrapper is accepted *)
Definition zlib_okb (w: Z) : bool := (0 <=? w) && ((w <? 16) || (32 <=? w)).
