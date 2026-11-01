(* Specifications of the framework's libc functions that zlib calls through zutil.h's macros:
   zmemcpy = memcpy, zmemzero(d, n) = memset(d, 0, n) (quickproof/libc/libc.c, a unit of every law that links
   zutil.c, inflate.c or deflate.c).  Shared by the inflate and deflate proofs.

   The specifications take the exact slices: data_at of tarray tuchar len at the two pointers (a caller that
   holds a larger object splits it, e.g. with split3_data_at_Tarray_tuchar; two slices of one object are
   disjoint by separation).  A byte is a Z in 0..255 stored as Vint (Int.repr b) (byte_vals; the
   representation of nondet_bytes).

   memcpy(d, s, len): s holds the bytes data (len of them), d any contents (also undefined); afterwards d
   holds data, s is unchanged.  memset(p, c, len): p any contents; afterwards len times the byte c mod 256.

   Both are stated for ANY compspecs (byte arrays are the same in every one); memcpy_spec_sub and
   memset_spec_sub move a unit's specification to a law's. *)
Require Import VST.floyd.proofauto.
Require Import QuickProof.Assembly.
Require Zlib.libc.code.
Import Zlib.libc.code.

Definition byte_vals (l: list Z) : list val := map (fun b => Vint (Int.repr b)) l.
Definition bytes_ok (l: list Z) : Prop := Forall (fun b => 0 <= b <= Byte.max_unsigned) l.

Lemma Zlength_byte_vals l: Zlength (byte_vals l) = Zlength l.
Proof. unfold byte_vals. apply Zlength_map. Qed.

Lemma Znth_byte_vals l i: 0 <= i < Zlength l -> Znth i (byte_vals l) = Vint (Int.repr (Znth i l)).
Proof. intros. unfold byte_vals. rewrite Znth_map by lia. reflexivity. Qed.

Lemma sublist_byte_vals lo hi l: sublist lo hi (byte_vals l) = byte_vals (sublist lo hi l).
Proof. unfold byte_vals. apply sublist_map. Qed.

Lemma byte_vals_app l1 l2: byte_vals (l1 ++ l2) = byte_vals l1 ++ byte_vals l2.
Proof. unfold byte_vals. apply map_app. Qed.

Lemma zext8 c: Int.zero_ext 8 (Int.repr c) = Int.repr (c mod 256).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr c))).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change (two_p 8) with 256.
  symmetry. apply Znumtheory.Zmod_div_mod; [lia | reflexivity | exists 16777216; reflexivity].
Qed.

Section Specs.
Context {cs: compspecs}.

Definition memcpy_spec :=
  DECLARE _memcpy
  WITH shd: share, d: val, shs: share, s: val, data: list Z
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (writable_share shd; readable_share shs; bytes_ok data; Zlength data <= Int64.max_unsigned)
    PARAMS (d; s; Vlong (Int64.repr (Zlength data)))
    SEP (data_at_ shd (tarray tuchar (Zlength data)) d;
         data_at shs (tarray tuchar (Zlength data)) (byte_vals data) s)
  POST [ tptr tvoid ]
    PROP ()
    RETURN (d)
    SEP (data_at shd (tarray tuchar (Zlength data)) (byte_vals data) d;
         data_at shs (tarray tuchar (Zlength data)) (byte_vals data) s).

Definition memset_spec :=
  DECLARE _memset
  WITH sh: share, p: val, len: Z, c: Z
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; 0 <= len <= Int64.max_unsigned; Int.min_signed <= c <= Int.max_signed)
    PARAMS (p; Vint (Int.repr c); Vlong (Int64.repr len))
    SEP (data_at_ sh (tarray tuchar len) p)
  POST [ tptr tvoid ]
    PROP ()
    RETURN (p)
    SEP (data_at sh (tarray tuchar len) (byte_vals (repeat (c mod 256) (Z.to_nat len))) p).

Definition Vprog : varspecs := [].
Definition Gprog : funspecs := [].

Lemma body_memcpy: semax_body Vprog Gprog f_memcpy memcpy_spec.
Proof.
  start_function.
  set (len := Zlength data) in *.
  assert (LB: Zlength (byte_vals data) = len) by (apply Zlength_byte_vals).
  forward. forward.
  forward_for_simple_bound len
    (EX i: Z,
     PROP ()
     LOCAL (temp _dest d; temp _d d; temp _s s; temp _n (Vlong (Int64.repr len)))
     SEP (data_at shd (tarray tuchar len)
            (sublist 0 i (byte_vals data) ++ Zrepeat Vundef (len - i)) d;
          data_at shs (tarray tuchar len) (byte_vals data) s)).
  - entailer!. rewrite sublist_nil, app_nil_l. apply derives_refl.
  - assert (B: 0 <= Znth i data <= Byte.max_unsigned). {
      match goal with H: bytes_ok _ |- _ =>
        unfold bytes_ok in H; rewrite Forall_forall in H; apply H, Znth_In; lia end. }
    forward.
    { entailer!. rewrite Znth_byte_vals by lia. simpl. rewrite Int.unsigned_repr by rep_lia. lia. }
    rewrite Znth_byte_vals by lia.
    forward.
    entailer!.
    apply derives_refl'. f_equal.
    rewrite (sublist_split 0 i (i + 1)) by lia.
    rewrite (sublist_one i (i + 1)) by lia. rewrite Znth_byte_vals by lia.
    list_solve.
  - forward. entailer!. rewrite Z.sub_diag. simpl. rewrite app_nil_r.
    rewrite sublist_same by lia. auto.
Qed.

Lemma body_memset: semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound len
    (EX i: Z,
     PROP ()
     LOCAL (temp _s p; temp _p p; temp _c (Vint (Int.repr c)); temp _n (Vlong (Int64.repr len)))
     SEP (data_at sh (tarray tuchar len)
            (byte_vals (repeat (c mod 256) (Z.to_nat i)) ++ Zrepeat Vundef (len - i)) p)).
  - entailer!. apply derives_refl.
  - forward. entailer!.
    apply derives_refl'. f_equal.
    rewrite !zext8, Zmod_mod.
    rewrite Z2Nat.inj_add by lia. rewrite repeat_app. rewrite byte_vals_app.
    unfold byte_vals. simpl. list_solve.
  - forward. entailer!. rewrite Z.sub_diag. simpl. rewrite app_nil_r. auto.
Qed.

End Specs.

(* A law's specification (cs2) is a subspecification of a unit's (cs1): byte arrays are the same. *)
Lemma memcpy_spec_sub (cs1 cs2: compspecs): funspec_sub (snd (@memcpy_spec cs2)) (snd (@memcpy_spec cs1)).
Proof.
  do_funspec_sub. destruct w as [[[[shd d] shs] s] data].
  Exists (shd, d, shs, s, data) emp. simpl.
  rewrite (data_at__tuchar_cs cs1 cs2), (data_at_tuchar_cs cs1 cs2).
  entailer!. intros. rewrite !(data_at_tuchar_cs cs2 cs1). entailer!.
Qed.

Lemma memset_spec_sub (cs1 cs2: compspecs): funspec_sub (snd (@memset_spec cs2)) (snd (@memset_spec cs1)).
Proof.
  do_funspec_sub. destruct w as [[[sh p] len] c].
  Exists (sh, p, len, c) emp. simpl.
  rewrite (data_at__tuchar_cs cs1 cs2).
  entailer!. intros. rewrite !(data_at_tuchar_cs cs2 cs1). entailer!.
Qed.
