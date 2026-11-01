(** * The harness helpers of zlib_common.h / deflate_common.h used by the deflate laws: THE specifications
    (one per function, shared by every law whose harness uses them) and their bodies

    The Clight of each helper is the same term in every harness unit that keeps it (identifiers are
    name-based); the bodies are taken from harness/deflate_api.c's unit.  Specified here: be32, le32,
    exact_copy, exact_space, stream_defaults, deflate_params_ok, draw_nonzero_bytes.  Already specified
    elsewhere (reuse them): bytes_copy, bytes_same (src/proof/adler32/HarnessBytes.v), ref_adler32
    (src/proof/adler32/HarnessRef.v), ref_crc32, ref_crc_byte (src/proof/crc32/HarnessRef.v).
    Byte slices are given as in those files: [cbuf_ok false buf sh p lo n len contents data] (Bytes.v):
    buf = p + lo, the object at p has n bytes [contents], and the slice [lo, lo + len) holds [data]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.harness.x_deflate_api.code.
Module HD := Zlib.harness.x_deflate_api.code.
#[local] Existing Instance DCS.CS.

(** be32(p) / le32(p): the 4 bytes p[0..4) *)
Definition be32_spec :=
  DECLARE HD._be32
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, data : list Z
  PRE [ tptr tuchar ]
    PROP (cbuf_ok false buf sh p lo n 4 contents data)
    PARAMS (buf)
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (be32 data)))
    SEP (data_at sh (tarray tuchar n) contents p).

Definition le32_spec :=
  DECLARE HD._le32
  WITH buf : val, sh : share, p : val, lo : Z, n : Z, contents : list val, data : list Z
  PRE [ tptr tuchar ]
    PROP (cbuf_ok false buf sh p lo n 4 contents data)
    PARAMS (buf)
    SEP (data_at sh (tarray tuchar n) contents p)
  POST [ tulong ]
    PROP () RETURN (Vlong (Int64.repr (le32 data)))
    SEP (data_at sh (tarray tuchar n) contents p).

(** exact_copy(src, n): a new object of exactly n bytes holding the slice (NULL when malloc fails). *)
Definition exact_copy_spec :=
  DECLARE HD._exact_copy
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

(** exact_space(n, snap): two new objects of exactly n bytes with the same arbitrary contents, the second one
    in *snap; NULL (and *snap = NULL) when an allocation fails. *)
Definition exact_space_spec :=
  DECLARE HD._exact_space
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

(** stream_defaults(s): zalloc, zfree, opaque, next_in, next_out Z_NULL, avail_in, avail_out 0, and
    arbitrary total_in, total_out, adler, data_type, reserved; msg and state untouched. *)
Definition stream_defaults_spec :=
  DECLARE HD._stream_defaults
  WITH sp : val, sh : share, msg : val, st : val
  PRE [ tptr t_strm ]
    PROP (writable_share sh)
    PARAMS (sp)
    SEP (data_at sh t_strm (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (msg, (st,
           (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))) sp)
  POST [ tvoid ]
    EX tin : Z, EX tout : Z, EX adler : Z, EX dt : Z, EX rs : Z,
    PROP (u64r tin; u64r tout; u64r adler; s32 dt; u64r rs)
    RETURN ()
    SEP (data_at sh t_strm (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (msg, (st,
           (nullval, (nullval, (nullval, (vi dt, (vl adler, vl rs))))))))))))) sp).

(** deflate_params_ok(level, method, wbits, mem, strategy) *)
Definition deflate_params_ok_spec :=
  DECLARE HD._deflate_params_ok
  WITH level : Z, method : Z, wbits : Z, mem : Z, strategy : Z
  PRE [ tint, tint, tint, tint, tint ]
    PROP (s32 level; s32 method; s32 wbits; s32 mem; s32 strategy)
    PARAMS (vi level; vi method; vi wbits; vi mem; vi strategy)
    SEP ()
  POST [ tint ]
    PROP () RETURN (vi (if params_ok level method wbits mem strategy then 1 else 0)) SEP ().

(** draw_nonzero_bytes(buf, n): n arbitrary non-zero bytes. *)
Definition draw_nonzero_bytes_spec :=
  DECLARE HD._draw_nonzero_bytes
  WITH buf : val, n : Z, sh : share
  PRE [ tptr tuchar, tuint ]
    PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
    PARAMS (buf; Vint (Int.repr n))
    SEP (data_at_ sh (tarray tuchar n) buf)
  POST [ tvoid ]
    EX bs : list Z,
    PROP (Zlength bs = n; Forall (fun b => 0 < b < 256) bs)
    RETURN ()
    SEP (data_at sh (tarray tuchar n) (bytes_rep bs) buf).

(** The contexts of the bodies (callees only). *)
Definition Vprog_hl : varspecs := [].
Definition Gprog_be32 : funspecs := [].
Definition Gprog_le32 : funspecs := [].
Definition Gprog_exact_copy : funspecs := [(_quickproof_malloc, malloc_spec'); bytes_copy_spec].
Definition Gprog_exact_space : funspecs :=
  [(_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec'); nondet_bytes_spec; bytes_copy_spec].
Definition Gprog_stream_defaults : funspecs := [nondet_bytes_spec].
Definition Gprog_deflate_params_ok : funspecs := [].
Definition Gprog_draw_nonzero_bytes : funspecs := [nondet_bytes_spec; gp_assume_spec].

Definition harness_lib_ok : Prop :=
  semax_body Vprog_hl Gprog_be32 HD.f_be32 be32_spec /\
  semax_body Vprog_hl Gprog_le32 HD.f_le32 le32_spec /\
  semax_body Vprog_hl Gprog_exact_copy HD.f_exact_copy exact_copy_spec /\
  semax_body Vprog_hl Gprog_exact_space HD.f_exact_space exact_space_spec /\
  semax_body Vprog_hl Gprog_stream_defaults HD.f_stream_defaults stream_defaults_spec /\
  semax_body Vprog_hl Gprog_deflate_params_ok HD.f_deflate_params_ok deflate_params_ok_spec /\
  semax_body Vprog_hl Gprog_draw_nonzero_bytes HD.f_draw_nonzero_bytes draw_nonzero_bytes_spec.

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

Ltac hl_absurd := exfalso; match goal with
  | H: Int.repr 1 = Int.zero |- _ => exact (Int.one_not_zero H)
  | H: Int.repr 0 <> Int.zero |- _ => apply H; reflexivity
  | H: ?x <> ?x |- _ => apply H; reflexivity
  | _ => solve [discriminate | auto]
  end.

Ltac hl_to_acs := rewrite ?(QuickProof.Assembly.data_at__tuchar_cs DCS.CS Zlib.units.Adler32.CS),
  ?(QuickProof.Assembly.data_at_tuchar_cs DCS.CS Zlib.units.Adler32.CS).
Ltac hl_to_dcs := rewrite ?(QuickProof.Assembly.data_at__tuchar_cs Zlib.units.Adler32.CS DCS.CS),
  ?(QuickProof.Assembly.data_at_tuchar_cs Zlib.units.Adler32.CS DCS.CS).

Lemma body_be32: semax_body Vprog_hl Gprog_be32 HD.f_be32 be32_spec.
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

Lemma body_le32: semax_body Vprog_hl Gprog_le32 HD.f_le32 le32_spec.
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
  forward. { entailer!. rewrite (Hb 3) by lia. simpl. rewrite (B 3) by lia. pose proof (Hr 3 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 2) by lia. simpl. rewrite (B 2) by lia. pose proof (Hr 2 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite (Hb 1) by lia. simpl. rewrite (B 1) by lia. pose proof (Hr 1 ltac:(lia)). rep_lia. }
  forward. { entailer!. rewrite B0. simpl. rewrite (B 0) by lia. pose proof (Hr 0 ltac:(lia)). rep_lia. }
  rewrite B0, !Hb by lia.
  forward.
  entailer!. simpl. rewrite !B by lia.
  rewrite hl_be32_or by (apply Hr; lia).
  reflexivity.
Qed.

Lemma body_draw_nonzero_bytes:
  semax_body Vprog_hl Gprog_draw_nonzero_bytes HD.f_draw_nonzero_bytes draw_nonzero_bytes_spec.
Proof.
  start_function.
  assert_PROP (isptr buf) as Pb by entailer!.
  forward_call (buf, n, sh).
  { rewrite if_false by (intro; subst; contradiction). cancel. }
  Intros bs. rewrite if_false by (intro; subst; contradiction).
  forward_for_simple_bound n (EX i: Z,
     PROP (Forall (fun b => 0 < b < 256) (sublist 0 i bs))
     LOCAL (temp HD._buf buf; temp HD._n (Vint (Int.repr n)))
     SEP (data_at sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) buf)).
  - entailer!.
  - Intros.
    assert (Bi: 0 <= Znth i bs <= Byte.max_unsigned) by (apply (proj1 (Forall_Znth _ _) H1); lia).
    forward.
    { entailer!. simpl. rep_lia. }
    forward_call (if Int.eq (Int.repr (Znth i bs)) Int.zero then Int.zero else Int.one).
    { entailer!. destruct (Int.eq _ _); reflexivity. }
    entailer!.
    assert (NZ: Znth i bs <> 0).
    { intro Z0. rewrite Z0 in *. rewrite Int.eq_true in *. contradiction. }
    rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
    apply Forall_app; split; auto. constructor; [ rep_lia | constructor ].
  - Exists bs. entailer!. rewrite sublist_same in * by lia. auto.
Qed.

Ltac hl_ints := cbn [Z.opp] in *; repeat match goal with
  | H: Int.repr ?a = Int.repr ?b |- _ => apply repr_inj_signed in H; [ | rep_lia | rep_lia ]
  | H: Int.repr ?a <> Int.repr ?b |- _ => assert (a <> b) by (intro; subst; contradiction); clear H
  end.

Ltac hl_bsolve :=
  unfold bool2val, vi;
  repeat match goal with
  | H: context [if ?b then 1 else 0] |- _ => destruct b; simpl in H
  end;
  rewrite ?hl_int_eq by rep_lia;
  repeat match goal with
  | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  | |- context [zlt ?a ?b] => destruct (zlt a b)
  | |- context [zeq ?a ?b] => destruct (zeq a b)
  end; simpl; try reflexivity; try lia; hl_absurd.

Lemma body_deflate_params_ok:
  semax_body Vprog_hl Gprog_deflate_params_ok HD.f_deflate_params_ok deflate_params_ok_spec.
Proof.
  start_function.
  unfold s32 in *.
  forward.
  forward_if (PROP ()
    LOCAL (temp HD._wrap (vi 1); temp HD._level (vi (if level =? -1 then 6 else level));
           temp HD._method (vi method); temp HD._wbits (vi wbits); temp HD._mem (vi mem);
           temp HD._strategy (vi strategy)) SEP ()).
  - forward. entailer!. hl_ints. subst. reflexivity.
  - forward. entailer!. hl_ints. rewrite (proj2 (Z.eqb_neq level (-1))) by lia. reflexivity.
  - set (lv := if level =? -1 then 6 else level).
    forward_if (PROP (-15 <= wbits)
      LOCAL (temp HD._wrap (vi (wrap_of wbits)); temp HD._level (vi lv);
             temp HD._method (vi method); temp HD._wbits (vi (wb_of wbits)); temp HD._mem (vi mem);
             temp HD._strategy (vi strategy)) SEP ()).
    + forward_if (PROP (-15 <= wbits)
        LOCAL (temp HD._wrap (vi 1); temp HD._level (vi lv);
               temp HD._method (vi method); temp HD._wbits (vi wbits); temp HD._mem (vi mem);
               temp HD._strategy (vi strategy)) SEP ()).
      * forward. rewrite Int.signed_repr in * by rep_lia. apply prop_right.
        unfold params_ok. rewrite (proj2 (Z.ltb_lt wbits (-15))) by lia. reflexivity.
      * forward. entailer!. rewrite Int.signed_repr in * by rep_lia. lia.
      * Intros. forward. forward. { entailer!. rewrite Int.signed_zero. rep_lia. }
        entailer!. unfold wrap_of, wb_of. rewrite (proj2 (Z.ltb_lt wbits 0)) by lia. auto.
    + forward_if (PROP (-15 <= wbits)
        LOCAL (temp HD._wrap (vi (wrap_of wbits)); temp HD._level (vi lv);
               temp HD._method (vi method); temp HD._wbits (vi (wb_of wbits)); temp HD._mem (vi mem);
               temp HD._strategy (vi strategy)) SEP ()).
      * forward. forward. entailer!. unfold wrap_of, wb_of.
        rewrite (proj2 (Z.ltb_ge wbits 0)) by lia. rewrite (proj2 (Z.gtb_lt wbits 15)) by lia. auto.
      * forward. entailer!. unfold wrap_of, wb_of. rewrite (proj2 (Z.ltb_ge wbits 0)) by lia.
        rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge 15 wbits)) by lia. auto.
    + Intros. set (w := wb_of wbits). set (wr := wrap_of wbits).
      assert (Wr: -15 <= w <= Int.max_signed) by (unfold w, wb_of;
        destruct (Z.ltb_spec wbits 0); [rep_lia | ]; rewrite Z.gtb_ltb; destruct (Z.ltb_spec 15 wbits); rep_lia).
      assert (WRr: 0 <= wr <= 2) by (unfold wr, wrap_of;
        destruct (Z.ltb_spec wbits 0); [lia | ]; rewrite Z.gtb_ltb; destruct (Z.ltb_spec 15 wbits); lia).
      assert (Lr: Int.min_signed <= lv <= Int.max_signed) by (unfold lv; destruct (level =? -1); rep_lia).
      assert (Ew: w = wb_of wbits) by reflexivity. assert (Ewr: wr = wrap_of wbits) by reflexivity.
      assert (Elv: lv = if level =? -1 then 6 else level) by reflexivity.
      clearbody w wr lv.
      forward_if (PROP () LOCAL (temp HD._t'1 (vi (if andb (1 <=? mem) (mem <=? 9) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'2 (vi (if andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'3 (vi (if andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'4 (vi (if andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'5 (vi (if andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'6 (vi (if andb (andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv)) (lv <=? 9) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'7 (vi (if andb (andb (andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv)) (lv <=? 9)) (0 <=? strategy) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'8 (vi (if andb (andb (andb (andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv)) (lv <=? 9)) (0 <=? strategy)) (strategy <=? 4) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      1,2: forward; entailer!; hl_bsolve.
      forward_if (PROP () LOCAL (temp HD._t'9 (vi (if andb (andb (andb (andb (andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv)) (lv <=? 9)) (0 <=? strategy)) (strategy <=? 4)) (orb (negb (w =? 8)) (wr =? 1)) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
      * forward_if (PROP () LOCAL (temp HD._t'9 (vi (if andb (andb (andb (andb (andb (andb (andb (andb (andb (1 <=? mem) (mem <=? 9)) (method =? 8)) (8 <=? w)) (w <=? 15)) (0 <=? lv)) (lv <=? 9)) (0 <=? strategy)) (strategy <=? 4)) (orb (negb (w =? 8)) (wr =? 1)) then 1 else 0)); temp HD._wrap (vi wr); temp HD._level (vi lv); temp HD._method (vi method); temp HD._wbits (vi w); temp HD._mem (vi mem); temp HD._strategy (vi strategy)) SEP ()).
        1: forward; entailer!; hl_bsolve.
        1: forward; forward; entailer!; hl_bsolve.
      * forward; entailer!; hl_bsolve.
      * forward. entailer!. unfold params_ok.
        rewrite (proj2 (Z.ltb_ge wbits (-15))) by lia. simpl andb.
        destruct (_ && _)%bool; reflexivity.
Qed.

Lemma body_exact_copy: semax_body Vprog_hl Gprog_exact_copy HD.f_exact_copy exact_copy_spec.
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
    forward_if (PROP () LOCAL (temp HD._p nullval) SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p)).
    + exfalso. discriminate.
    + forward. entailer!.
    + forward. Exists nullval. entailer!.
  - Intros.
    forward_if (PROP () LOCAL (temp HD._p q)
      SEP (mem_mgr gv; data_at sh (tarray tuchar n) contents p;
           malloc_token Ews (tarray tuchar len) q; data_at Ews (tarray tuchar len) (bytes_rep data) q)).
    + hl_to_acs. forward_call (q, Ews, buf, sh, p, lo, n, contents, len, data).
      hl_to_dcs. entailer!.
    + exfalso. auto.
    + forward. Exists q. entailer!. rewrite if_false by auto. cancel.
Qed.

Lemma body_exact_space: semax_body Vprog_hl Gprog_exact_space HD.f_exact_space exact_space_spec.
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
    forward_if (PROP () LOCAL (temp HD._t'3 (Vint (Int.repr 1)); temp HD._p nullval; temp HD._q nullval; gvars gv;
                               temp HD._snap snapp)
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
    forward_if (PROP () LOCAL (temp HD._t'3 (Vint (Int.repr 1)); temp HD._p nullval; temp HD._q q; gvars gv;
                               temp HD._snap snapp)
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
    forward_if (PROP () LOCAL (temp HD._t'3 (Vint (Int.repr 1)); temp HD._p p; temp HD._q nullval; gvars gv;
                               temp HD._snap snapp)
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
  - forward_if (PROP () LOCAL (temp HD._t'3 (Vint (Int.repr 0)); temp HD._p p; temp HD._q q; gvars gv;
                               temp HD._n (Vint (Int.repr n)); temp HD._snap snapp)
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
      hl_to_acs. forward_call (q, Ews, p, Ews, p, 0, n, bytes_rep bs, n, bs).
      hl_to_dcs. forward. forward.
      Exists p q bs. entailer!.
      rewrite !if_false by auto. cancel.
Qed.


Require QuickProof.Pick.

Lemma hl_field_bytes sh gfs p n v:
  sizeof (nested_field_type t_strm gfs) = n -> n < Ptrofs.modulus ->
  v = default_val (nested_field_type t_strm gfs) ->
  field_at sh t_strm gfs v p |--
  data_at_ sh (tarray tuchar n) (field_address t_strm gfs p).
Proof.
  intros E L ->. fold (field_at_ sh t_strm gfs p).
  rewrite field_at__memory_block. rewrite E.
  apply memory_block_data_at__tarray_tuchar.
  pose proof (sizeof_pos (nested_field_type t_strm gfs)). lia.
Qed.

Lemma hl_field_ulong sh gfs p bs:
  nested_field_type t_strm gfs = tulong ->
  field_compatible t_strm gfs p ->
  Zlength bs = 8 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 8) (map (fun b => Vint (Int.repr b)) bs)
    (field_address t_strm gfs p) |--
  EX z : Z, !! (0 <= z <= Int64.max_unsigned) &&
    data_at sh tulong (Vlong (Int64.repr z)) (field_address t_strm gfs p).
Proof.
  intros T FC L B.
  pose proof (field_compatible_app [] _ gfs p FC) as FC'. rewrite T in FC'.
  sep_apply (QuickProof.Pick.pick_tulong sh bs _ L B FC'). Intros v.
  Exists (Int64.unsigned v). rewrite Int64.repr_unsigned.
  entailer!; rep_lia.
Qed.

Lemma hl_field_int sh gfs p bs:
  nested_field_type t_strm gfs = tint ->
  field_compatible t_strm gfs p ->
  Zlength bs = 4 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  data_at sh (tarray tuchar 4) (map (fun b => Vint (Int.repr b)) bs)
    (field_address t_strm gfs p) |--
  EX z : Z, !! (Int.min_signed <= z <= Int.max_signed) &&
    data_at sh tint (Vint (Int.repr z)) (field_address t_strm gfs p).
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

Lemma body_stream_defaults:
  semax_body Vprog_hl Gprog_stream_defaults HD.f_stream_defaults stream_defaults_spec.
Proof.
  start_function.
  forward. forward. forward. forward. forward. forward. forward.
  unfold_data_at (data_at _ _ _ sp).
  assert_PROP (field_compatible t_strm (DOT HD._total_in) sp /\ field_compatible t_strm (DOT HD._total_out) sp /\
               field_compatible t_strm (DOT HD._adler) sp /\ field_compatible t_strm (DOT HD._data_type) sp /\
               field_compatible t_strm (DOT HD._reserved) sp) as FF by entailer!.
  destruct FF as (F1 & F2 & F3 & F4 & F5).
  sep_apply (hl_field_bytes sh (DOT HD._total_in) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address t_strm (DOT HD._total_in) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HD._total_in) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros tin. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HD._total_out) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address t_strm (DOT HD._total_out) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HD._total_out) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros tout. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HD._adler) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address t_strm (DOT HD._adler) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HD._adler) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros adler. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HD._data_type) sp 4 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address t_strm (DOT HD._data_type) sp, 4, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_int sh (DOT HD._data_type) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros dt. clear bs H H0.
  sep_apply (hl_field_bytes sh (DOT HD._reserved) sp 8 Vundef eq_refl ltac:(rep_lia) eq_refl).
  forward_call (field_address t_strm (DOT HD._reserved) sp, 8, sh).
  { rewrite if_false by (apply hl_fa_nonnull; auto). cancel. }
  Intros bs. rewrite if_false by (apply hl_fa_nonnull; auto).
  sep_apply (hl_field_ulong sh (DOT HD._reserved) sp bs eq_refl ltac:(auto) ltac:(auto) ltac:(auto)).
  Intros rs. clear bs H H0.
  Exists tin tout adler dt rs.
  unfold u64r, s32.
  pose proof (@field_at_data_at DCS.CS sh t_strm (DOT HD._total_in) (Vlong (Int64.repr tin)) sp) as E.
  change (nested_field_type t_strm (DOT HD._total_in)) with tulong in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at DCS.CS sh t_strm (DOT HD._total_out) (Vlong (Int64.repr tout)) sp) as E.
  change (nested_field_type t_strm (DOT HD._total_out)) with tulong in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at DCS.CS sh t_strm (DOT HD._adler) (Vlong (Int64.repr adler)) sp) as E.
  change (nested_field_type t_strm (DOT HD._adler)) with tulong in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at DCS.CS sh t_strm (DOT HD._data_type) (Vint (Int.repr dt)) sp) as E.
  change (nested_field_type t_strm (DOT HD._data_type)) with tint in E. rewrite <- E. clear E.
  pose proof (@field_at_data_at DCS.CS sh t_strm (DOT HD._reserved) (Vlong (Int64.repr rs)) sp) as E.
  change (nested_field_type t_strm (DOT HD._reserved)) with tulong in E. rewrite <- E. clear E.
  entailer!.
  unfold_data_at (data_at _ _ _ sp). simpl. cancel.
Qed.


Theorem harness_lib_bodies : harness_lib_ok.
Proof.
  split; [exact body_be32 | ].
  split; [exact body_le32 | ].
  split; [exact body_exact_copy | ].
  split; [exact body_exact_space | ].
  split; [exact body_stream_defaults | ].
  split; [exact body_deflate_params_ok | exact body_draw_nonzero_bytes].
Qed.
