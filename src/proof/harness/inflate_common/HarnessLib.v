(* The helpers of harness/zlib_common.h used by the inflate laws: THE specifications (one per function, shared
   by every inflate law whose harness keeps them) and their bodies.

   The Clight of each helper is the same term in every harness unit that keeps it (identifiers are name-based);
   the bodies are taken from harness/inflate_codes.c's unit.  Specified here: be32, exact_copy, exact_space,
   inflate_wbits_ok, inflate_code_ok (at the compspecs of the adler32 unit, like bytes_copy / ref_adler32), and
   stream_defaults (at the compspecs of the inflate unit: struct z_stream).  Already specified elsewhere (reuse):
   bytes_copy, bytes_same (src/proof/adler32/HarnessBytes.v), ref_adler32 (src/proof/adler32/HarnessRef.v).
   Byte slices are given as in those files: [cbuf_ok false buf sh p lo n len contents data] (adler32/Bytes.v):
   buf = p + lo, the object at p has n bytes [contents], and the slice [lo, lo + len) holds [data]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes.
Require Import Zlib.proof.harness.inflate_common.HDefs.
Require Zlib.units.Adler32 Zlib.units.Inflate.
Require Zlib.proof.inflate.Rep.
Require Zlib.harness.x_inflate_codes.code.
Module HI := Zlib.harness.x_inflate_codes.code.

Section ByteHelpers.
#[local] Existing Instance Zlib.units.Adler32.CS.

(* be32(p): the 4 bytes p[0..4), big-endian *)
Definition be32_spec :=
  DECLARE HI._be32
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, data : list Z
  PRE [ tptr tuchar ]
    PROP (cbuf_ok false buf sh p lo n 4 contents data)
    PARAMS (buf)
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (be32 data)))
    SEP (data_at sh (tarray tuchar n) contents p).

(* exact_copy(src, n): a new object of exactly n bytes holding the slice (NULL when malloc fails) *)
Definition exact_copy_spec :=
  DECLARE HI._exact_copy
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, len : Z, data : list Z,
       gv : globals
  PRE [ tptr tuchar, tuint ]
    PROP (0 <= len <= Int.max_unsigned; cbuf_ok false buf sh p lo n len contents data)
    PARAMS (buf; Vint (Int.repr len)) GLOBALS (gv)
    SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)
  POST [ tptr tuchar ]
    EX q : val,
    PROP () RETURN (q)
    SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p;
         if eq_dec q nullval then emp
         else (malloc_token Ews (tarray tuchar len) q * data_at Ews (tarray tuchar len) (bytes_rep data) q)).

(* exact_space(n, snap): two new objects of exactly n bytes with the same arbitrary contents, the second one
   in *snap; NULL (and *snap = NULL) when an allocation fails *)
Definition exact_space_spec :=
  DECLARE HI._exact_space
  WITH n : Z, snapp : val, ssh : share, gv : globals
  PRE [ tuint, tptr (tptr tuchar) ]
    PROP (0 <= n <= Int.max_unsigned; writable_share ssh)
    PARAMS (Vint (Int.repr n); snapp) GLOBALS (gv)
    SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp)
  POST [ tptr tuchar ]
    EX r : val, EX q : val, EX bs : list Z,
    PROP (Zlength bs = n; is_bytes bs; r = nullval -> q = nullval)
    RETURN (r)
    SEP (mem_mgr gv; data_at ssh (tptr tuchar) q snapp;
         if eq_dec r nullval then emp
         else (malloc_token Ews (tarray tuchar n) r * data_at Ews (tarray tuchar n) (bytes_rep bs) r *
               malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (bytes_rep bs) q)).

(* inflate_wbits_ok(w): inflateInit2's windowBits test (ApiModel.wbits_ok) *)
Definition inflate_wbits_ok_spec :=
  DECLARE HI._inflate_wbits_ok
  WITH w : Z
  PRE [ tint ]
    PROP (Int.min_signed <= w <= Int.max_signed)
    PARAMS (Vint (Int.repr w))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if wbits_ok w then 1 else 0))) SEP ().

(* inflate_code_ok(r) *)
Definition inflate_code_ok_spec :=
  DECLARE HI._inflate_code_ok
  WITH r : Z
  PRE [ tint ]
    PROP (Int.min_signed <= r <= Int.max_signed)
    PARAMS (Vint (Int.repr r))
    SEP ()
  POST [ tint ]
    PROP () RETURN (Vint (Int.repr (if code_okb r then 1 else 0))) SEP ().

End ByteHelpers.

Section StreamHelpers.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* stream_defaults(s): zalloc, zfree, opaque, next_in, next_out Z_NULL, avail_in, avail_out 0, and arbitrary
   total_in, total_out, adler, data_type, reserved (pick); msg and state untouched *)
Definition stream_defaults_spec :=
  DECLARE HI._stream_defaults
  WITH sp : val, sh : share, msg : val, st : val
  PRE [ tptr Zlib.proof.inflate.Rep.t_strm ]
    PROP (writable_share sh)
    PARAMS (sp)
    SEP (data_at sh Zlib.proof.inflate.Rep.t_strm
           (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (msg, (st,
            (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))) sp)
  POST [ tvoid ]
    EX tin : Z, EX tout : Z, EX adler : Z, EX dt : Z, EX rs : Z,
    PROP (0 <= tin <= Int64.max_unsigned; 0 <= tout <= Int64.max_unsigned; 0 <= adler <= Int64.max_unsigned;
          Int.min_signed <= dt <= Int.max_signed; 0 <= rs <= Int64.max_unsigned)
    RETURN ()
    SEP (data_at sh Zlib.proof.inflate.Rep.t_strm
           (nullval, (Vint (Int.repr 0), (Vlong (Int64.repr tin), (nullval, (Vint (Int.repr 0),
            (Vlong (Int64.repr tout), (msg, (st, (nullval, (nullval, (nullval, (Vint (Int.repr dt),
            (Vlong (Int64.repr adler), Vlong (Int64.repr rs)))))))))))))) sp).

End StreamHelpers.

(* The contexts of the bodies (callees only). *)
Definition Vprog_hl : varspecs := [].
Definition Gprog_be32 : funspecs := [].
Definition Gprog_exact_copy : funspecs := [(_quickproof_malloc, @malloc_spec' Zlib.units.Adler32.CS); bytes_copy_spec].
Definition Gprog_exact_space : funspecs :=
  [(_quickproof_malloc, @malloc_spec' Zlib.units.Adler32.CS); (_quickproof_free, @free_spec' Zlib.units.Adler32.CS); @nondet_bytes_spec Zlib.units.Adler32.CS; bytes_copy_spec].
Definition Gprog_wbits : funspecs := [].
Definition Gprog_code : funspecs := [].
Definition Gprog_stream_defaults : funspecs := [@nondet_bytes_spec Zlib.units.Inflate.CS].

Definition harness_bytes_ok : Prop :=
  @semax_body Vprog_hl Gprog_be32 Zlib.units.Adler32.CS HI.f_be32 be32_spec /\
  @semax_body Vprog_hl Gprog_exact_copy Zlib.units.Adler32.CS HI.f_exact_copy exact_copy_spec /\
  @semax_body Vprog_hl Gprog_exact_space Zlib.units.Adler32.CS HI.f_exact_space exact_space_spec /\
  @semax_body Vprog_hl Gprog_wbits Zlib.units.Adler32.CS HI.f_inflate_wbits_ok inflate_wbits_ok_spec /\
  @semax_body Vprog_hl Gprog_code Zlib.units.Adler32.CS HI.f_inflate_code_ok inflate_code_ok_spec.

Definition harness_stream_ok : Prop :=
  @semax_body Vprog_hl Gprog_stream_defaults Zlib.units.Inflate.CS HI.f_stream_defaults stream_defaults_spec.

Lemma hl_lor_low x y k: 0 <= k -> 0 <= y < 2 ^ k -> Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof.
  intros Hk Hy. rewrite <- Z.add_lor_land. replace (Z.land (x * 2 ^ k) y) with 0; [lia | ].
  symmetry. apply Z.bits_inj_0. intros m.
  rewrite Z.land_spec. destruct (Z.lt_ge_cases m 0) as [Hm | Hm].
  - rewrite Z.testbit_neg_r by lia. reflexivity.
  - destruct (Z.lt_ge_cases m k) as [Hm' | Hm'].
    + rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite <- (Z.mod_small y (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r.
Qed.

Lemma hl_be32_or a b c d:
  0 <= a <= 255 -> 0 <= b <= 255 -> 0 <= c <= 255 -> 0 <= d <= 255 ->
  Int64.or (Int64.or (Int64.or (Int64.shl (Int64.repr a) (Int64.repr 24)) (Int64.shl (Int64.repr b) (Int64.repr 16)))
    (Int64.shl (Int64.repr c) (Int64.repr 8))) (Int64.repr d) =
  Int64.repr (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d).
Proof.
  intros Ha Hb Hc Hd.
  assert (S: forall x k, 0 <= x <= 255 -> 0 <= k <= 24 -> Int64.shl (Int64.repr x) (Int64.repr k) = Int64.repr (x * 2 ^ k)).
  { intros x k Hx Hk. unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia.
    rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (O: forall x y, 0 <= x <= Int64.max_unsigned -> 0 <= y <= Int64.max_unsigned ->
    Int64.or (Int64.repr x) (Int64.repr y) = Int64.repr (Z.lor x y)).
  { intros x y Hx Hy. unfold Int64.or. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  rewrite (S a 24), (S b 16), (S c 8) by lia.
  assert (P: forall k, 0 <= k <= 24 -> 2 ^ k <= 2 ^ 24) by (intros; apply Z.pow_le_mono_r; lia).
  pose proof (P 16 ltac:(lia)). pose proof (P 8 ltac:(lia)).
  rewrite O by (simpl; rep_lia).
  rewrite hl_lor_low by (simpl; lia).
  rewrite O by (simpl; rep_lia).
  replace (a * 2 ^ 24 + b * 2 ^ 16) with ((a * 2 ^ 8 + b) * 2 ^ 16) by ring.
  rewrite hl_lor_low by (simpl; lia).
  rewrite O by (simpl; rep_lia).
  replace ((a * 2 ^ 8 + b) * 2 ^ 16 + c * 2 ^ 8) with ((a * 2 ^ 16 + b * 2 ^ 8 + c) * 2 ^ 8) by ring.
  rewrite hl_lor_low by (simpl; lia).
  f_equal; ring.
Qed.

Lemma hl_int_eq r c: Int.min_signed <= r <= Int.max_signed -> Int.min_signed <= c <= Int.max_signed ->
  Int.eq (Int.repr r) (Int.repr c) = (r =? c).
Proof.
  intros. destruct (Z.eqb_spec r c) as [E | E].
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro X. apply E. apply repr_inj_signed; auto.
Qed.

Ltac hl_code_step r t c :=
  match goal with
  | |- semax _ (PROP () LOCAL (temp _ (Vint (Int.repr 1)); _) _) _ _ =>
      forward_if (PROP () LOCAL (temp t (Vint (Int.repr 1)); temp HI._r (Vint (Int.repr r))) SEP ());
      [ forward; entailer!
      | match goal with H: Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero H) end
      | ]
  | |- semax _ (PROP () LOCAL (temp _ (Vint (Int.repr 0)); _) _) _ _ =>
      forward_if (PROP () LOCAL (temp t (Vint (Int.repr (if r =? c then 1 else 0))); temp HI._r (Vint (Int.repr r))) SEP ());
      [ match goal with H: 0 <> 0 |- _ => contradiction end
      | forward; entailer!; rewrite hl_int_eq by rep_lia; cbn [Z.opp]; destruct (r =? c); reflexivity
      | destruct (r =? c) eqn:? ]
  end.

Ltac hl_absurd := exfalso; match goal with
  | H: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | _ => solve [discriminate | auto]
  end.

Section BytesBodies.
#[local] Existing Instance Zlib.units.Adler32.CS.

Lemma body_be32: @semax_body Vprog_hl Gprog_be32 Zlib.units.Adler32.CS HI.f_be32 be32_spec.
Proof.
  start_function.
  match goal with H: cbuf_ok false _ _ _ _ _ _ _ _ |- _ => destruct H as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub) end.
  subst buf.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  assert_PROP (Zlength contents = n) by (entailer!; rewrite Zlength_correct in *; auto).
  assert (Hb: forall i, 0 <= i < 4 -> @Znth val Vundef (lo + i) contents = Vint (Int.repr (Znth i data))) by
    (intros; apply (Znth_cbuf lo 4); auto; lia).
  assert (Hr: forall i, 0 <= i < 4 -> 0 <= Znth i data <= Byte.max_unsigned) by (intros; apply is_bytes_Znth; auto; lia).
  assert (E: forall i, 0 <= i < 4 -> force_val (sem_add_ptr_int tuchar Signed (offset_val lo p) (Vint (Int.repr i))) =
    field_address (tarray tuchar n) [ArraySubsc (lo + i)] p) by
    (intros; apply Zlib.proof.adler32.Ptr.add_ptr_c; auto; rep_lia).
  pose proof (E 0 ltac:(lia)) as E0. pose proof (E 1 ltac:(lia)) as E1.
  pose proof (E 2 ltac:(lia)) as E2. pose proof (E 3 ltac:(lia)) as E3.
  rewrite Z.add_0_r in E0.
  assert (B: forall i, 0 <= i < 4 -> Int.unsigned (Int.repr (Znth i data)) = Znth i data) by
    (intros i Hi; pose proof (Hr i Hi); rewrite Int.unsigned_repr by rep_lia; reflexivity).
  pose proof (Hb 0 ltac:(lia)) as B0. rewrite Z.add_0_r in B0.
  forward. { entailer!. rewrite B0. simpl. rewrite (B 0) by lia. pose proof (Hr 0 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 1) by lia. simpl. rewrite (B 1) by lia. pose proof (Hr 1 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 2) by lia. simpl. rewrite (B 2) by lia. pose proof (Hr 2 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 3) by lia. simpl. rewrite (B 3) by lia. pose proof (Hr 3 ltac:(lia)). rep_lia. }
  rewrite B0, !Hb by lia.
  forward.
  entailer!. simpl. rewrite !B by lia.
  rewrite hl_be32_or by (apply Hr; lia).
  reflexivity.
Qed.

Lemma body_code_ok: @semax_body Vprog_hl Gprog_code Zlib.units.Adler32.CS HI.f_inflate_code_ok inflate_code_ok_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp HI._t'1 (Vint (Int.repr (if orb (r =? 0) (r =? 1) then 1 else 0))); temp HI._r (Vint (Int.repr r))) SEP ()).
  { forward. entailer!. }
  { forward. entailer!. rewrite hl_int_eq by rep_lia. rewrite (proj2 (Z.eqb_neq r 0)) by auto. simpl. destruct (r =? 1); reflexivity. }
  destruct (orb (r =? 0) (r =? 1)) eqn:B1.
  all: hl_code_step r HI._t'2 2.
  all: hl_code_step r HI._t'3 (-3).
  all: hl_code_step r HI._t'4 (-2).
  all: hl_code_step r HI._t'5 (-4).
  all: hl_code_step r HI._t'6 (-5).
  all: forward; entailer!; unfold code_okb; cbv [Z_OK Z_STREAM_END Z_NEED_DICT Z_DATA_ERROR Z_STREAM_ERROR Z_MEM_ERROR Z_BUF_ERROR].
  all: repeat match goal with H: ?x = ?b |- context [?x] => rewrite H end; reflexivity.
Qed.

Lemma body_wbits_ok: @semax_body Vprog_hl Gprog_wbits Zlib.units.Adler32.CS HI.f_inflate_wbits_ok inflate_wbits_ok_spec.
Proof.
  start_function.
  forward_if (PROP (0 <= w) LOCAL (temp HI._w (Vint (Int.repr w))) SEP ()).
  { forward_if (PROP () LOCAL (temp HI._t'1 (Vint (Int.repr (if andb (-15 <=? w) (w <=? -8) then 1 else 0)))) SEP ()).
    - forward. entailer!.
      rewrite Int.signed_repr in * by rep_lia. unfold Int.lt. rewrite !Int.signed_repr by rep_lia.
      destruct (Z.leb_spec (-15) w); [ | lia]. destruct (Z.leb_spec w (-8)), (zlt (-(8)) w); simpl; try reflexivity; lia.
    - forward. entailer!. rewrite Int.signed_repr in * by rep_lia. destruct (Z.leb_spec (-15) w); [lia | reflexivity].
    - forward. entailer!. unfold wbits_ok, reset2_wb.
      destruct (Z.ltb_spec w 0); [ | lia]. destruct (Z.ltb_spec w (-15)).
      + destruct (Z.leb_spec (-15) w); [lia | reflexivity].
      + destruct (Z.leb_spec (-15) w); [ | lia]. simpl andb.
        destruct (Z.leb_spec w (-8)), (Z.leb_spec 8 (- w)), (Z.leb_spec (- w) 15); simpl; try reflexivity; lia. }
  { forward. entailer!. }
  Intros.
  forward_if (PROP (w < 48) LOCAL (temp HI._w (Vint (Int.repr w))) SEP ()).
  { forward. entailer!. unfold wbits_ok, reset2_wb.
    rewrite ?Int.signed_repr in * by rep_lia.
    destruct (Z.ltb_spec w 0); [lia | ]. destruct (Z.ltb_spec w 48); [lia | ].
    destruct (Z.eqb_spec w 0), (Z.leb_spec 8 w), (Z.leb_spec w 15); simpl; try reflexivity; lia. }
  { forward. entailer!. }
  Intros.
  assert (L: 0 <= Z.land w 15 <= 15).
  { assert (LE: Z.land w 15 = w mod 16) by (apply (Z.land_ones w 4); lia).
    rewrite LE. pose proof (Z.mod_pos_bound w 16). lia. }
  assert (A: Int.and (Int.repr w) (Int.repr 15) = Int.repr (Z.land w 15)) by
    (unfold Int.and; rewrite !Int.unsigned_repr by rep_lia; reflexivity).
  forward. rewrite A.
  forward_if (PROP () LOCAL (temp HI._t'2 (Vint (Int.repr (if orb (Z.land w 15 =? 0) (andb (8 <=? Z.land w 15) (Z.land w 15 <=? 15)) then 1 else 0)))) SEP ()).
  { forward. entailer!. rewrite H2. reflexivity. }
  { forward_if.
    - forward. forward. entailer!.
      destruct (Z.eqb_spec (Z.land w 15) 0), (Z.leb_spec 8 (Z.land w 15)), (Z.leb_spec (Z.land w 15) 15),
        (zlt 15 (Z.land w 15)); simpl; try reflexivity; lia.
    - forward. entailer!.
      destruct (Z.eqb_spec (Z.land w 15) 0), (Z.leb_spec 8 (Z.land w 15)); simpl; try reflexivity; lia. }
  forward. entailer!. unfold wbits_ok, reset2_wb.
  destruct (Z.ltb_spec w 0); [lia | ]. destruct (Z.ltb_spec w 48); [ | lia].
  destruct (_ || _)%bool; reflexivity.
Qed.

Lemma body_exact_copy: @semax_body Vprog_hl Gprog_exact_copy Zlib.units.Adler32.CS HI.f_exact_copy exact_copy_spec.
Proof.
  start_function.
  pose proof H0 as C.
  destruct H0 as (Hbuf & Hsh & Hlo & Hn & Hlen & Hby & Hsub).
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  forward_call (tarray tuchar len, gv).
  { simpl. rep_lia. }
  Intros q.
  destruct (eq_dec q nullval) as [Eq | Nq].
  - subst q.
    forward_if (PROP () LOCAL (temp HI._p nullval) SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)).
    + exfalso. discriminate.
    + forward. entailer!.
    + forward. Exists nullval. entailer!.
  - Intros.
    forward_if (PROP () LOCAL (temp HI._p q)
      SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p;
           malloc_token Ews (tarray tuchar len) q; data_at Ews (tarray tuchar len) (bytes_rep data) q)).
    + forward_call (q, Ews, buf, sh, p, lo, n, contents, len, data).
      entailer!.
    + exfalso. auto.
    + forward. Exists q. entailer!. rewrite if_false by auto. cancel.
Qed.

Lemma body_exact_space: @semax_body Vprog_hl Gprog_exact_space Zlib.units.Adler32.CS HI.f_exact_space exact_space_spec.
Proof.
  start_function.
  forward_call (tarray tuchar n, gv).
  { simpl. rep_lia. }
  Intros p.
  forward_call (tarray tuchar n, gv).
  { simpl. rep_lia. }
  Intros q.
  assert (Z0: Zlength (Zrepeat 0 n) = n) by (rewrite Zlength_Zrepeat; lia).
  assert (B0: is_bytes (Zrepeat 0 n)) by (apply Forall_forall; intros x Hx; unfold Zrepeat in Hx; apply repeat_spec in Hx; subst x; rep_lia).
  destruct (eq_dec p nullval) as [Ep | Np]; destruct (eq_dec q nullval) as [Eq | Nq]; Intros.
  - subst p q.
    forward_if (PROP () LOCAL (temp HI._t'3 (Vint (Int.repr 1)); temp HI._p nullval; temp HI._q nullval; gvars gv;
                               temp HI._snap snapp)
                SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp)).
    + forward. entailer!.
    + hl_absurd.
    + forward_if.
      2: { hl_absurd. }
      forward_call (tarray tuchar n, nullval, gv).
      { rewrite if_true by auto. cancel. }
      forward_call (tarray tuchar n, nullval, gv).
      { rewrite if_true by auto. cancel. }
      forward. forward.
      Exists nullval nullval (Zrepeat 0 n). entailer!.
  - subst p.
    forward_if (PROP () LOCAL (temp HI._t'3 (Vint (Int.repr 1)); temp HI._p nullval; temp HI._q q; gvars gv;
                               temp HI._snap snapp)
                SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp;
                     malloc_token Ews (tarray tuchar n) q; data_at_ Ews (tarray tuchar n) q)).
    + forward. entailer!.
    + hl_absurd.
    + forward_if.
      2: { hl_absurd. }
      forward_call (tarray tuchar n, nullval, gv).
      { rewrite if_true by auto. cancel. }
      forward_call (tarray tuchar n, q, gv).
      { rewrite if_false by auto. cancel. }
      forward. forward.
      Exists nullval nullval (Zrepeat 0 n). entailer!.
  - subst q.
    forward_if (PROP () LOCAL (temp HI._t'3 (Vint (Int.repr 1)); temp HI._p p; temp HI._q nullval; gvars gv;
                               temp HI._snap snapp)
                SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp;
                     malloc_token Ews (tarray tuchar n) p; data_at_ Ews (tarray tuchar n) p)).
    + hl_absurd.
    + forward. entailer!.
    + forward_if.
      2: { hl_absurd. }
      forward_call (tarray tuchar n, p, gv).
      { rewrite if_false by auto. cancel. }
      forward_call (tarray tuchar n, nullval, gv).
      { rewrite if_true by auto. cancel. }
      forward. forward.
      Exists nullval nullval (Zrepeat 0 n). entailer!.
  - forward_if (PROP () LOCAL (temp HI._t'3 (Vint (Int.repr 0)); temp HI._p p; temp HI._q q; gvars gv;
                               temp HI._n (Vint (Int.repr n)); temp HI._snap snapp)
                SEP (mem_mgr gv; data_at_ ssh (tptr tuchar) snapp;
                     malloc_token Ews (tarray tuchar n) p; data_at_ Ews (tarray tuchar n) p;
                     malloc_token Ews (tarray tuchar n) q; data_at_ Ews (tarray tuchar n) q)).
    + hl_absurd.
    + forward. entailer!.
      match goal with H: field_compatible (tarray tuchar n) [] q |- _ => destruct H as [Hq _] end.
      destruct q; try contradiction. reflexivity.
    + forward_if.
      { hl_absurd. }
      forward_call (p, n, Ews).
      { rewrite if_false by auto. cancel. }
      Intros bs.
      rewrite if_false by auto.
      assert_PROP (isptr p) as Pp by entailer!.
      fold (bytes_rep bs).
      assert (C: cbuf_ok false p Ews p 0 n n (bytes_rep bs) bs).
      { subst n. apply cbuf_ok_whole; auto. }
      forward_call (q, Ews, p, Ews, p, 0, n, bytes_rep bs, n, bs).
      forward. forward.
      Exists p q bs. entailer!.
      rewrite !if_false by auto. cancel.
Qed.

End BytesBodies.

Theorem harness_bytes_bodies : harness_bytes_ok.
Proof.
  split; [exact body_be32 | ].
  split; [exact body_exact_copy | ].
  split; [exact body_exact_space | ].
  split; [exact body_wbits_ok | exact body_code_ok].
Qed.

(* pick(s->f) on a field of struct z_stream: its bytes for nondet_bytes, and back to a value of the field *)
Require QuickProof.Pick.
Section StreamPick.
#[local] Existing Instance Zlib.units.Inflate.CS.

Lemma hl_field_bytes sh gfs p n v:
  sizeof (nested_field_type Zlib.proof.inflate.Rep.t_strm gfs) = n -> n < Ptrofs.modulus ->
  v = default_val (nested_field_type Zlib.proof.inflate.Rep.t_strm gfs) ->
  field_at sh Zlib.proof.inflate.Rep.t_strm gfs v p |--
  data_at_ sh (tarray tuchar n) (field_address Zlib.proof.inflate.Rep.t_strm gfs p).
Proof.
  intros E L ->. fold (field_at_ sh Zlib.proof.inflate.Rep.t_strm gfs p).
  rewrite field_at__memory_block. rewrite E.
  apply memory_block_data_at__tarray_tuchar.
  pose proof (sizeof_pos (nested_field_type Zlib.proof.inflate.Rep.t_strm gfs)). lia.
Qed.

Lemma hl_field_ulong sh gfs p bs:
  nested_field_type Zlib.proof.inflate.Rep.t_strm gfs = tulong ->
  field_compatible Zlib.proof.inflate.Rep.t_strm gfs p ->
  Zlength bs = 8 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) bs)
    (field_address Zlib.proof.inflate.Rep.t_strm gfs p) |--
  EX z : Z, !! (0 <= z <= Int64.max_unsigned) &&
    data_at sh tulong (Vlong (Int64.repr z)) (field_address Zlib.proof.inflate.Rep.t_strm gfs p).
Proof.
  intros T FC L B.
  pose proof (field_compatible_app [] _ gfs p FC) as FC'. rewrite T in FC'.
  sep_apply (QuickProof.Pick.pick_tulong sh bs _ L B FC'). Intros v.
  Exists (Int64.unsigned v). rewrite Int64.repr_unsigned.
  entailer!; rep_lia.
Qed.

Lemma hl_field_int sh gfs p bs:
  nested_field_type Zlib.proof.inflate.Rep.t_strm gfs = tint ->
  field_compatible Zlib.proof.inflate.Rep.t_strm gfs p ->
  Zlength bs = 4 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 4) (map (fun b => Vint (Int.repr b)) bs)
    (field_address Zlib.proof.inflate.Rep.t_strm gfs p) |--
  EX z : Z, !! (Int.min_signed <= z <= Int.max_signed) &&
    data_at sh tint (Vint (Int.repr z)) (field_address Zlib.proof.inflate.Rep.t_strm gfs p).
Proof.
  intros T FC L B.
  pose proof (field_compatible_app [] _ gfs p FC) as FC'. rewrite T in FC'.
  sep_apply (QuickProof.Pick.pick_tint sh bs _ L B FC'). Intros v.
  Exists (Int.signed v). rewrite Int.repr_signed.
  entailer!; rep_lia.
Qed.

Lemma hl_fa_nonnull t gfs p: field_compatible t gfs p -> field_address t gfs p <> nullval.
Proof.
  intros FC. rewrite field_compatible_field_address by auto.
  destruct FC as [Hp _]. destruct p; try contradiction. discriminate.
Qed.

Lemma hl_stream_body :
  semax_body Vprog_hl Gprog_stream_defaults HI.f_stream_defaults stream_defaults_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward. forward. forward.
  unfold_data_at (data_at _ _ _ sp).
  assert_PROP (field_compatible Zlib.proof.inflate.Rep.t_strm (DOT HI._total_in) sp /\ field_compatible Zlib.proof.inflate.Rep.t_strm (DOT HI._total_out) sp /\
               field_compatible Zlib.proof.inflate.Rep.t_strm (DOT HI._adler) sp /\ field_compatible Zlib.proof.inflate.Rep.t_strm (DOT HI._data_type) sp /\
               field_compatible Zlib.proof.inflate.Rep.t_strm (DOT HI._reserved) sp) as FF by entailer!.
  destruct FF as (F1 & F2 & F3 & F4 & F5).
  sep_apply (hl_field_bytes sh (DOT HI._total_in) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address Zlib.proof.inflate.Rep.t_strm (DOT HI._total_in) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HI._total_in) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros tin. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HI._total_out) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address Zlib.proof.inflate.Rep.t_strm (DOT HI._total_out) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HI._total_out) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros tout. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HI._adler) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address Zlib.proof.inflate.Rep.t_strm (DOT HI._adler) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HI._adler) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros adler. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HI._data_type) sp 4 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address Zlib.proof.inflate.Rep.t_strm (DOT HI._data_type) sp, 4, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_int sh (DOT HI._data_type) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros dt. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HI._reserved) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address Zlib.proof.inflate.Rep.t_strm (DOT HI._reserved) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HI._reserved) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros rs. clear bs H H0.
  Exists tin tout adler dt rs.
  pose proof (@field_at_data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm (DOT HI._total_in) (Vlong (Int64.repr tin)) sp) as E.
  simpl nested_field_type in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm (DOT HI._total_out) (Vlong (Int64.repr tout)) sp) as E.
  simpl nested_field_type in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm (DOT HI._adler) (Vlong (Int64.repr adler)) sp) as E.
  simpl nested_field_type in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm (DOT HI._data_type) (Vint (Int.repr dt)) sp) as E.
  simpl nested_field_type in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm (DOT HI._reserved) (Vlong (Int64.repr rs)) sp) as E.
  simpl nested_field_type in E. rewrite <- E. clear E.
  entailer!.
  unfold_data_at (data_at _ _ _ sp). simpl. cancel.
Qed.

End StreamPick.

Theorem harness_stream_body : harness_stream_ok.
Proof.
  exact hl_stream_body.
Qed.
