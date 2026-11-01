(* The helpers of harness/laws_session.h (deflate_params_ok, inflate_window_ok, position_of, unmoved, accounted,
   counted): THE specifications, one per function, shared by every law that includes the header (api_deflate_any,
   api_deterministic, api_inflate_any, api_inflate_deterministic, api_untouched_output, res_bound,
   res_memory_deflate, res_memory_inflate, rfc_trailing_bytes, rj_any_input, rt_stream, rt_stream_trailing,
   rt_session).

   Each helper is the same Clight term in every harness unit that keeps it (identifiers are name-based; a unit drops
   the helpers its main does not call).  No harness keeps all six: deflate_params_ok and unmoved are taken from
   harness/rt_stream.c's unit, the four others from harness/api_inflate_any.c's.

   The compspecs [CS_session] are those of the two structs the helpers use, struct z_stream_s (zlib.h) and struct
   position (laws_session.h), as the harnesses' Clight defines them; every program that includes the header has both
   composites unchanged, so QuickProof.Assembly's entry_shared moves a body proved here into the law's program
   ([cspecs_sub CS_session <law's CS>] holds by computation), and a main at its own compspecs calls these
   specifications through [change_composite_env CS_session <law's CS>] (make_cs_preserve), as it calls laws_common's
   offer/new_stream at the compress unit's compspecs.

   The six members a position records are given as a [posz] (next_in, avail_in, total_in, next_out, avail_out,
   total_out; the integers by value), for the z_stream ([zs_of c r], [r] its eight other members) as for the struct
   position ([pos_of a]); [posz_ok] says they are well typed (C reads them).  The pointer comparisons of unmoved and
   accounted are defined in C only between null pointers or (weakly) valid pointers, and accounted's sums
   next + avail only for non-null pointers: the caller lends, as the last SEP item, memory [B] (typically its input
   and output objects with their malloc tokens) in the form [B && unmoved_cmp c a] / [B && accounted_cmp c a], i.e.
   it proves [B |-- denote_tc_test_eq x y] for the compared values (VST's condition for [x == y]: both null, or one
   null and the other weakly valid, or two pointers of one block both weakly valid, or two pointers of different
   blocks both valid), and gets [B] back.  Because [B : mpred] is in their WITH, these two are dependent
   specifications (TYPE ... WITH, with their non-expansiveness proved below). *)
Require Import VST.floyd.proofauto.
Require Zlib.harness.rt_stream.code.
Require Zlib.harness.api_inflate_any.code.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.units.Adler32.
Module RS := Zlib.harness.rt_stream.code.
Module AI := Zlib.harness.api_inflate_any.code.

(* The compspecs of struct z_stream_s and struct position, as the harnesses define them. *)
Definition session_cprog : Clight.program := Clightdefs.mkprogram AI.composites nil nil 1%positive Logic.I.
Definition CS_session : compspecs. make_compspecs session_cprog. Defined.

(* No composite: the compspecs of the two range tests, which touch no memory.  The programs that call only them
   (api_deterministic, res_bound, res_memory_deflate, rfc_trailing_bytes, api_inflate_deterministic,
   res_memory_inflate) have no struct position, so their bodies are proved at the compspecs of the adler32 unit (no
   struct; laws_common's byte helpers use it too), which every law's compspecs contain. *)
Definition CS_none : compspecs := Zlib.units.Adler32.CS.

(* deflate_params_ok's test (the harness's [valid] of rj_deflate_params with method = Z_DEFLATED): level -1..9,
   memLevel 1..9, strategy 0..4, windowBits 8..15, -15..-9 or 25..31.  Facts.v: it is deflate/LawFacts.params_ok
   level 8 windowBits memLevel strategy. *)
Definition deflate_params_valid (level wbits mem strategy : Z) : bool :=
  (-1 <=? level) && (level <=? 9) && (1 <=? mem) && (mem <=? 9) && (0 <=? strategy) && (strategy <=? 4) &&
  ((8 <=? wbits) && (wbits <=? 15) || (-15 <=? wbits) && (wbits <=? -9) || (25 <=? wbits) && (wbits <=? 31)).

(* inflate_window_ok's test (rj_inflate_params' [raw || wrapped]): -15..-8, or 0..47 with the low four bits 0 or
   8..15.  Facts.v: it is inflate_api/ApiModel.wbits_ok, the windowBits inflateInit2 accepts. *)
Definition inflate_window_valid (w : Z) : bool :=
  ((-15 <=? w) && (w <=? -8)) || ((0 <=? w) && (w <? 48) && ((Z.land w 15 =? 0) || (8 <=? Z.land w 15))).

(* equality of two pointer values, as [==] computes it on comparable values *)
Definition ptr_eqb (x y : val) : bool := if Val.eq x y then true else false.

(* The six members a position records, by value: next_in, avail_in (uInt), total_in (uLong), next_out, avail_out
   (uInt), total_out (uLong).  Used both for a z_stream's members and for a struct position's. *)
Record posz : Type := mk_posz {
  pz_next_in : val; pz_avail_in : Z; pz_total_in : Z;
  pz_next_out : val; pz_avail_out : Z; pz_total_out : Z }.

(* the members are well typed: next_* pointers or null, the integers in range (C reads them) *)
Definition posz_ok (c : posz) : Prop :=
  is_pointer_or_null (pz_next_in c) /\ is_pointer_or_null (pz_next_out c) /\
  0 <= pz_avail_in c <= Int.max_unsigned /\ 0 <= pz_total_in c <= Int64.max_unsigned /\
  0 <= pz_avail_out c <= Int.max_unsigned /\ 0 <= pz_total_out c <= Int64.max_unsigned.

(* unmoved(strm, at): the six members of strm [c] equal those of at [a] *)
Definition unmoved_b (c a : posz) : bool :=
  ptr_eqb (pz_next_in c) (pz_next_in a) && (pz_avail_in c =? pz_avail_in a) && (pz_total_in c =? pz_total_in a) &&
  (ptr_eqb (pz_next_out c) (pz_next_out a) && (pz_avail_out c =? pz_avail_out a) &&
   (pz_total_out c =? pz_total_out a)).

(* accounted(strm, at): avail_in <= at.avail_in and next_in + avail_in == at.next_in + at.avail_in; the same for
   the output *)
Definition accounted_b (c a : posz) : bool :=
  (pz_avail_in c <=? pz_avail_in a) &&
  ptr_eqb (offset_val (pz_avail_in c) (pz_next_in c)) (offset_val (pz_avail_in a) (pz_next_in a)) &&
  ((pz_avail_out c <=? pz_avail_out a) &&
   ptr_eqb (offset_val (pz_avail_out c) (pz_next_out c)) (offset_val (pz_avail_out a) (pz_next_out a))).

(* counted(strm, at): total_in == at.total_in + (at.avail_in - avail_in) in C's arithmetic (the uInt difference
   modulo 2^32, the uLong sum modulo 2^64); the same for the output *)
Definition counted_b (c a : posz) : bool :=
  (pz_total_in c =? (pz_total_in a + (pz_avail_in a - pz_avail_in c) mod Int.modulus) mod Int64.modulus) &&
  (pz_total_out c =? (pz_total_out a + (pz_avail_out a - pz_avail_out c) mod Int.modulus) mod Int64.modulus).

(* the eight members of a z_stream the helpers do not touch: msg, state, zalloc, zfree, opaque, data_type, adler,
   reserved (any values) *)
Definition zs_rest : Type := (val * val * val * val * val * val * val * val)%type.

(* The comparability the pointer compares of unmoved and accounted need, in the memory [B] the caller lends. *)
Definition unmoved_cmp (c a : posz) : mpred :=
  denote_tc_test_eq (pz_next_in c) (pz_next_in a) && denote_tc_test_eq (pz_next_out c) (pz_next_out a).

Definition accounted_cmp (c a : posz) : mpred :=
  denote_tc_test_eq (offset_val (pz_avail_in c) (pz_next_in c)) (offset_val (pz_avail_in a) (pz_next_in a)) &&
  denote_tc_test_eq (offset_val (pz_avail_out c) (pz_next_out c)) (offset_val (pz_avail_out a) (pz_next_out a)).

(* The non-expansiveness of the pre- and postconditions of unmoved and accounted (their WITH holds the lent
   memory [B], so they are dependent specifications): only [B] is approximated. *)
Ltac ls_pre_ne :=
  let x := fresh "x" in intros ? ? x ?; destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl;
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp;
  f_equal; f_equal; rewrite !approx_sepcon, !approx_andp, !approx_idem; reflexivity.
Ltac ls_post_ne :=
  let x := fresh "x" in intros ? ? x ?; destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl;
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp;
  f_equal; f_equal; rewrite !approx_sepcon, !approx_idem; reflexivity.

Section Specs.
#[local] Existing Instance CS_session.

Definition t_pos : type := Tstruct AI._position noattr.

(* struct position's six members in declaration order: next_in, avail_in, next_out, avail_out, total_in,
   total_out *)
Definition pos_val (next_in avail_in next_out avail_out total_in total_out : val) : reptype t_pos :=
  (next_in, (avail_in, (next_out, (avail_out, (total_in, total_out))))).

(* a z_stream with the members [c] and the eight others [r] (laws_common's zs_val) *)
Definition zs_of (c : posz) (r : zs_rest) : reptype t_zs :=
  match r with (msg, st, za, zf, op, dt, ad, rs) =>
    zs_val (pz_next_in c) (Vint (Int.repr (pz_avail_in c))) (Vlong (Int64.repr (pz_total_in c)))
           (pz_next_out c) (Vint (Int.repr (pz_avail_out c))) (Vlong (Int64.repr (pz_total_out c)))
           msg st za zf op dt ad rs end.

(* a struct position holding [a] *)
Definition pos_of (a : posz) : reptype t_pos :=
  pos_val (pz_next_in a) (Vint (Int.repr (pz_avail_in a))) (pz_next_out a) (Vint (Int.repr (pz_avail_out a)))
          (Vlong (Int64.repr (pz_total_in a))) (Vlong (Int64.repr (pz_total_out a))).

(* deflate_params_ok(level, window_bits, mem_level, strategy): 1 when the parameters are in zlib.h's ranges for
   deflateInit2 (with method Z_DEFLATED), 0 otherwise *)
Definition deflate_params_ok_spec :=
  DECLARE RS._deflate_params_ok
  WITH level : Z, wbits : Z, mem : Z, strategy : Z
  PRE [ tint, tint, tint, tint ]
    PROP (Int.min_signed <= level <= Int.max_signed; Int.min_signed <= wbits <= Int.max_signed;
          Int.min_signed <= mem <= Int.max_signed; Int.min_signed <= strategy <= Int.max_signed)
    PARAMS (Vint (Int.repr level); Vint (Int.repr wbits); Vint (Int.repr mem); Vint (Int.repr strategy))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Val.of_bool (deflate_params_valid level wbits mem strategy))
    SEP ().

(* inflate_window_ok(window_bits): 1 when windowBits is one of zlib.h's values for inflateInit2, 0 otherwise *)
Definition inflate_window_ok_spec :=
  DECLARE AI._inflate_window_ok
  WITH w : Z
  PRE [ tint ]
    PROP (Int.min_signed <= w <= Int.max_signed)
    PARAMS (Vint (Int.repr w))
    SEP ()
  POST [ tint ]
    PROP ()
    RETURN (Val.of_bool (inflate_window_valid w))
    SEP ().

(* position_of(strm, at): at := strm's next_in, avail_in, next_out, avail_out, total_in, total_out; strm
   unchanged *)
Definition position_of_spec :=
  DECLARE AI._position_of
  WITH sp : val, shs : share, c : posz, r : zs_rest, ap : val, sha : share
  PRE [ tptr t_zs, tptr t_pos ]
    PROP (readable_share shs; writable_share sha; posz_ok c)
    PARAMS (sp; ap)
    SEP (data_at shs t_zs (zs_of c r) sp; data_at_ sha t_pos ap)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of c) ap).

(* unmoved(strm, at): 1 when strm's six members equal at's, 0 otherwise.  The caller lends memory [B] in which
   next_in and next_out are comparable with at's (it gets [B] back). *)
Program Definition unmoved_spec :=
  DECLARE RS._unmoved
  TYPE (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType
          (rmaps.ConstType val) (rmaps.ConstType share)) (rmaps.ConstType posz)) (rmaps.ConstType zs_rest)) (rmaps.ConstType val))
          (rmaps.ConstType share)) (rmaps.ConstType posz)) rmaps.Mpred)
  WITH sp : val, shs : share, c : posz, r : zs_rest, ap : val, sha : share, a : posz, B : mpred
  PRE [ tptr t_zs, tptr t_pos ]
    PROP (readable_share shs; readable_share sha; posz_ok c; posz_ok a)
    PARAMS (sp; ap)
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap; B && unmoved_cmp c a)
  POST [ tint ]
    PROP ()
    RETURN (Val.of_bool (unmoved_b c a))
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap; B).
Next Obligation. ls_pre_ne. Qed.
Next Obligation. ls_post_ne. Qed.

(* accounted(strm, at): 1 when avail_in <= at.avail_in and next_in + avail_in == at.next_in + at.avail_in and the
   same for the output, 0 otherwise.  The four next_* are pointers (not null; C's pointer + integer), and the
   caller lends memory [B] in which the two sums of each side are comparable (it gets [B] back). *)
Program Definition accounted_spec :=
  DECLARE AI._accounted
  TYPE (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ProdType
          (rmaps.ConstType val) (rmaps.ConstType share)) (rmaps.ConstType posz)) (rmaps.ConstType zs_rest)) (rmaps.ConstType val))
          (rmaps.ConstType share)) (rmaps.ConstType posz)) rmaps.Mpred)
  WITH sp : val, shs : share, c : posz, r : zs_rest, ap : val, sha : share, a : posz, B : mpred
  PRE [ tptr t_zs, tptr t_pos ]
    PROP (readable_share shs; readable_share sha; posz_ok c; posz_ok a;
          isptr (pz_next_in c); isptr (pz_next_out c); isptr (pz_next_in a); isptr (pz_next_out a))
    PARAMS (sp; ap)
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap; B && accounted_cmp c a)
  POST [ tint ]
    PROP ()
    RETURN (Val.of_bool (accounted_b c a))
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap; B).
Next Obligation. ls_pre_ne. Qed.
Next Obligation. ls_post_ne. Qed.

(* counted(strm, at): 1 when total_in == at.total_in + (at.avail_in - avail_in) and the same for the output (C's
   unsigned arithmetic), 0 otherwise *)
Definition counted_spec :=
  DECLARE AI._counted
  WITH sp : val, shs : share, c : posz, r : zs_rest, ap : val, sha : share, a : posz
  PRE [ tptr t_zs, tptr t_pos ]
    PROP (readable_share shs; readable_share sha; posz_ok c; posz_ok a)
    PARAMS (sp; ap)
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap)
  POST [ tint ]
    PROP ()
    RETURN (Val.of_bool (counted_b c a))
    SEP (data_at shs t_zs (zs_of c r) sp; data_at sha t_pos (pos_of a) ap).

End Specs.

(* The contexts of the bodies: the helpers call no function. *)
Definition Vprog_ls : varspecs := [].
Definition Gprog_ls : funspecs := [].

(* The bodies of the six helpers against their specifications (the range tests at [CS_none], the others at
   [CS_session]): a law's assembly takes this as its hypothesis (src/proof/harness/laws_session/Bodies.v proves it)
   and moves each body its program contains with entry_shared. *)
Definition laws_session_ok : Prop :=
  @semax_body Vprog_ls Gprog_ls CS_none RS.f_deflate_params_ok deflate_params_ok_spec /\
  @semax_body Vprog_ls Gprog_ls CS_none AI.f_inflate_window_ok inflate_window_ok_spec /\
  @semax_body Vprog_ls Gprog_ls CS_session AI.f_position_of position_of_spec /\
  @semax_body Vprog_ls Gprog_ls CS_session RS.f_unmoved unmoved_spec /\
  @semax_body Vprog_ls Gprog_ls CS_session AI.f_accounted accounted_spec /\
  @semax_body Vprog_ls Gprog_ls CS_session AI.f_counted counted_spec.
