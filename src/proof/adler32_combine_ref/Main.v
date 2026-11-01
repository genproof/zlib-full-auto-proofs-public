(* The main of harness/adler32_combine_ref.c, proved against main_core_spec (memory manager only: adler32.c has
   no globals), and the harness's own helper `valid`. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Zlib.contracts.x_adler32_combine_ref.
Require Import Zlib.harness.x_adler32_combine_ref.code.
Require Import Zlib.proof.adler32.Spec Zlib.proof.adler32.Facts2 Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib Zlib.proof.adler32.Ptr.
Require Import Zlib.proof.adler32_combine_ref.Algebra.

Definition p := Zlib.contracts.x_adler32_combine_ref.whole_prog.
Definition comps := ltac:(let x := eval vm_compute in (prog_composites p) in exact x).
Definition cprog : Clight.program := Clightdefs.mkprogram comps nil nil 1%positive Logic.I.
#[export] Instance CS : compspecs. make_compspecs cprog. Defined.
#[export] Instance CC2 : change_composite_env Zlib.units.Adler32.CS CS. make_cs_preserve Zlib.units.Adler32.CS CS. Defined.

Ltac tok_cs :=
  match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end;
  cancel.

Ltac tok_norm :=
  repeat match goal with |- context [@malloc_token Zlib.units.Adler32.CS ?sh ?t] =>
    rewrite (@malloc_token_change_composite Zlib.units.Adler32.CS CS CC2 sh t) by reflexivity end.

Ltac side := try (solve [cancel | tok_cs | entailer!; arg_cmp]).

Definition R (gv: globals) : mpred := emp.

(* ---------------------------------------------------------------------- *)
(* valid(a): a <= 0xffffffff && (a & 0xffff) < 65521 && (a >> 16) < 65521  *)
(* ---------------------------------------------------------------------- *)

Definition valid_b (a: Z) : bool := andb (andb (a <=? 4294967295) (adler_lo a <? 65521)) (a / 65536 <? 65521).

Lemma valid_b_spec a: 0 <= a -> valid_b a = true <-> adler_valid a.
Proof.
  intros Ha. unfold valid_b, adler_valid, ADLER_BASE.
  rewrite !andb_true_iff, Z.leb_le, !Z.ltb_lt.
  assert (a <= 4294967295 -> adler_hi a = a / 65536).
  { intros. unfold adler_hi. apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  change (2 ^ 32) with 4294967296.
  split; intros [[A B] C]; [ | split; [split | ]]; try rewrite H in *; try lia.
Qed.

Definition valid_spec :=
  DECLARE _valid
  WITH a: Z
  PRE [ tulong ] PROP (0 <= a <= Int64.max_unsigned) PARAMS (Vlong (Int64.repr a)) SEP ()
  POST [ tint ] PROP () RETURN (Vint (Int.repr (if valid_b a then 1 else 0))) SEP ().

Lemma land_lo a: 0 <= a -> Z.land a 65535 = adler_lo a.
Proof. intros. unfold adler_lo. change 65535 with (Z.ones 16). apply Z.land_ones. lia. Qed.

Ltac vcmp a :=
  pose proof (adler_lo_range a);
  unfold valid_b in *;
  try change (Int.unsigned (Int.repr (-1))) with 4294967295 in *;
  rewrite ?adler_lo_int2 in * by lia;
  simpl; unfold Int64.ltu, Int64.shru, Int.eq, Int64.eq in *;
  rewrite ?Int64.unsigned_repr in * by rep_lia;
  rewrite ?land_lo in * by lia; rewrite ?Int64.Z_mod_modulus_eq in *; rewrite ?land_lo in * by lia;
  rewrite ?(Z.mod_small (adler_lo a)) in * by rep_lia;
  try change (Int64.unsigned (Int64.repr 16)) with 16 in *;
  rewrite ?Z.shiftr_div_pow2 in * by lia; try change (2 ^ 16) with 65536 in *;
  try (rewrite Int64.unsigned_repr in * by (split; [apply Z.div_pos; lia | apply (Z.le_trans _ a); [apply Z.div_le_upper_bound; lia | rep_lia]]));
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with H: context [zlt ?a ?b] |- _ => destruct (zlt a b) end;
  repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  repeat match goal with H: context [Z.ltb ?a ?b] |- _ => destruct (Z.ltb_spec a b) end;
  repeat match goal with H: context [Z.leb ?a ?b] |- _ => destruct (Z.leb_spec a b) end;
  simpl in *;
  rewrite ?Int64.Z_mod_modulus_eq in *;
  rewrite ?(Z.mod_small (adler_lo a)) in * by (change Int64.modulus with 18446744073709551616; lia);
  try (match goal with H: ?x <> ?y |- _ => assert (x = y) by reflexivity; contradiction end);
  try lia; try reflexivity; try discriminate.

Lemma body_valid: semax_body [] [] f_valid valid_spec.
Proof.
  start_function.
  forward_if (PROP () LOCAL (temp _t'1 (Vint (Int.repr (if andb (a <=? 4294967295) (adler_lo a <? 65521) then 1 else 0)));
                             temp _a (Vlong (Int64.repr a))) SEP ()).
  - forward. entailer!. vcmp a.
  - forward. entailer!. vcmp a.
  - forward_if (PROP () LOCAL (temp _t'2 (Vint (Int.repr (if valid_b a then 1 else 0)))) SEP ()).
    + forward. entailer!.
      assert (S: Int64.shru (Int64.repr a) (Int64.repr 16) = Int64.repr (a / 65536)).
      { unfold Int64.shru. rewrite (Int64.unsigned_repr a) by rep_lia. change (Int64.unsigned (Int64.repr 16)) with 16.
        rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
      assert (0 <= a / 65536 <= a) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      rewrite S. unfold valid_b. destruct (andb (a <=? 4294967295) (adler_lo a <? 65521)); [ | contradiction H0'; reflexivity].
      unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt (a / 65536) 65521), (Z.ltb_spec (a / 65536) 65521); simpl; try lia; reflexivity.
    + forward. entailer!. unfold valid_b.
      destruct (andb (a <=? 4294967295) (adler_lo a <? 65521)); [ discriminate | reflexivity].
    + forward.
Qed.

(* The harness's second check, as VST leaves it. *)
Lemma combine_check x y z: adler_valid x -> adler_valid y -> 0 <= z <= Int64.max_signed ->
  Int64.eq (Int64.repr (adler32_combine_result x y z))
    (Int64.or
       (Int64.shl
          (Int64.modu
             (Int64.add
                (Int64.add (Int64.shru (Int64.repr x) (Int64.repr 16)) (Int64.shru (Int64.repr y) (Int64.repr 16)))
                (Int64.mul (Int64.modu (Int64.repr z) (Int64.repr 65521))
                   (Int64.modu (Int64.repr (Z.land x 65535 + 65521 - 1)) (Int64.repr 65521))))
             (Int64.repr 65521)) (Int64.repr 16))
       (Int64.modu (Int64.repr (Z.land x 65535 + Z.land y 65535 + 65521 - 1)) (Int64.repr 65521))) = true.
Proof.
  intros Vx Vy Hz.
  assert (SH: forall a, adler_valid a -> Int64.shru (Int64.repr a) (Int64.repr 16) = Int64.repr (adler_hi a)).
  { intros a (Ra & _ & _). unfold Int64.shru. rewrite (Int64.unsigned_repr a) by rep_lia.
    change (Int64.unsigned (Int64.repr 16)) with 16. rewrite Z.shiftr_div_pow2 by lia. f_equal.
    unfold adler_hi. symmetry. apply Z.mod_small. change (2 ^ 16) with 65536.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; change (2 ^ 32) with 4294967296 in Ra; lia]. }
  pose proof Vx as (_ & Hx1 & Hx2). pose proof Vy as (_ & Hy1 & Hy2).
  pose proof (adler_lo_range x). pose proof (adler_hi_range x).
  pose proof (adler_lo_range y). pose proof (adler_hi_range y).
  unfold ADLER_BASE in *.
  rewrite (SH x Vx), (SH y Vy).
  rewrite !land_lo by (destruct Vx, Vy; lia).
  set (x1 := adler_lo x) in *. set (x2 := adler_hi x) in *.
  set (y1 := adler_lo y) in *. set (y2 := adler_hi y) in *.
  rewrite (modu65521 z) by rep_lia.
  rewrite (modu65521 (x1 + 65521 - 1)) by rep_lia.
  rewrite (modu65521 (x1 + y1 + 65521 - 1)) by rep_lia.
  assert (0 <= z mod 65521 < 65521) by (apply Z.mod_pos_bound; lia).
  assert (0 <= (x1 + 65521 - 1) mod 65521 < 65521) by (apply Z.mod_pos_bound; lia).
  assert (0 <= (x1 + y1 + 65521 - 1) mod 65521 < 65521) by (apply Z.mod_pos_bound; lia).
  rewrite add64_repr, mul64_repr, add64_repr.
  rewrite modu65521 by (unfold ADLER_BASE in *;
    assert (0 <= z mod 65521 * ((x1 + 65521 - 1) mod 65521) <= 65521 * 65521) by nia; rep_lia).
  set (s2 := (x2 + y2 + z mod ADLER_BASE * ((x1 + 65521 - 1) mod ADLER_BASE)) mod ADLER_BASE).
  assert (0 <= s2 < 65521) by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  change (Int64.repr 16) with (Int64.repr (Int.unsigned (Int.repr 16))).
  rewrite or_pack_int by (unfold ADLER_BASE in *; lia).
  unfold adler32_combine_result. destruct (Z.ltb_spec z 0); [lia | ].
  rewrite adler32_combine_impl_val by auto.
  unfold adler32_combine_val. fold x1 x2 y1 y2. unfold ADLER_BASE in *. fold s2.
  apply Int64.eq_true.
Qed.

Definition Gmain : funspecs := [adler32_z_spec; adler32_combine_spec; ref_adler32_spec; valid_spec;
  (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
  nondet_u32_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

(* pick(x) of an unsigned long local variable. *)
Ltac pick_ulong v :=
  let FC := fresh "FC" in let P := fresh "P" in let N := fresh "N" in
  assert_PROP (field_compatible tulong [] v) as FC by entailer!;
  sep_apply (data_at_ulong_bytes Tsh v);
  assert_PROP (isptr v) as P by entailer!;
  assert (N: v <> nullval) by (destruct v; try contradiction; discriminate);
  forward_call (v, 8, Tsh);
  [ rewrite if_false by auto; cancel | ];
  let bs := fresh "bs" in
  Intros bs; rewrite if_false by auto;
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tulong Tsh bs v H1 H2 FC) end.

Ltac pick_long v :=
  let FC := fresh "FC" in let P := fresh "P" in let N := fresh "N" in
  assert_PROP (field_compatible tlong [] v) as FC by entailer!;
  sep_apply (data_at_long_bytes Tsh v);
  assert_PROP (isptr v) as P by entailer!;
  assert (N: v <> nullval) by (destruct v; try contradiction; discriminate);
  forward_call (v, 8, Tsh);
  [ rewrite if_false by auto; cancel | ];
  let bs := fresh "bs" in
  Intros bs; rewrite if_false by auto;
  match goal with H1: Zlength bs = 8, H2: Forall _ bs |- _ => sep_apply (pick_tlong Tsh bs v H1 H2 FC) end.

Lemma body_main: semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  start_function.
  unfold R. Intros.
  pick_ulong v_a0. Intros va0.
  pick_ulong v_x. Intros vx.
  pick_ulong v_y. Intros vy.
  pick_long v_z. Intros vz.
  assert (E1: Vlong va0 = Vlong (Int64.repr (Int64.unsigned va0))) by (rewrite Int64.repr_unsigned; auto).
  assert (E2: Vlong vx = Vlong (Int64.repr (Int64.unsigned vx))) by (rewrite Int64.repr_unsigned; auto).
  assert (E3: Vlong vy = Vlong (Int64.repr (Int64.unsigned vy))) by (rewrite Int64.repr_unsigned; auto).
  assert (E4: Vlong vz = Vlong (Int64.repr (Int64.signed vz))) by (rewrite Int64.repr_signed; auto).
  rewrite E1, E2, E3, E4. clear E1 E2 E3 E4.
  assert (Ha0: 0 <= Int64.unsigned va0 <= Int64.max_unsigned) by rep_lia.
  assert (Hx: 0 <= Int64.unsigned vx <= Int64.max_unsigned) by rep_lia.
  assert (Hy: 0 <= Int64.unsigned vy <= Int64.max_unsigned) by rep_lia.
  assert (Hz: Int64.min_signed <= Int64.signed vz <= Int64.max_signed) by rep_lia.
  remember (Int64.unsigned va0) as a0 eqn:Ea0. clear Ea0.
  remember (Int64.unsigned vx) as x eqn:Ex. clear Ex.
  remember (Int64.unsigned vy) as y eqn:Ey. clear Ey.
  remember (Int64.signed vz) as z eqn:Ez. clear Ez.
  forward_call tt. Intros na.
  forward_call tt. Intros nb.
  forward.
  forward_call a0.
  forward_call (Int.repr (if valid_b a0 then 1 else 0)).
  assumed. apply valid_b_spec in E; [ | lia]. rename E into Va0.
  ifpost _t'4 (Int.repr (if andb (na <=? 2 ^ 20) (nb <=? 2 ^ 20) then 1 else 0)).
  { forward. entailer!. change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20))) with (2 ^ 20) in *. arg_cmp. }
  { forward. entailer!. change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20))) with (2 ^ 20) in *. arg_cmp. }
  forward_call (Int.repr (if andb (na <=? 2 ^ 20) (nb <=? 2 ^ 20) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [Ena Enb]. apply Z.leb_le in Ena, Enb.
  forward_call (tarray tuchar (na + nb), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ab.
  destruct (eq_dec ab nullval) as [PB|PB].
  { subst ab. forward_if False. { ret0. } { first [contradiction | discriminate]. } }
  Intros.
  forward_if (PROP () LOCAL (temp _ab ab; temp _nb (Vint (Int.repr nb)); temp _na (Vint (Int.repr na));
                             lvar _z tlong v_z; lvar _y tulong v_y; lvar _x tulong v_x; lvar _a0 tulong v_a0; gvars gv)
    SEP (mem_mgr gv; malloc_token Ews (tarray tuchar (na + nb)) ab; data_at_ Ews (tarray tuchar (na + nb)) ab;
         data_at Tsh tlong (Vlong (Int64.repr z)) v_z; data_at Tsh tulong (Vlong (Int64.repr y)) v_y;
         data_at Tsh tulong (Vlong (Int64.repr x)) v_x; data_at Tsh tulong (Vlong (Int64.repr a0)) v_a0)).
  { contradiction. }
  { forward. entailer!. }
  (* the buffer A B: na + nb arbitrary bytes *)
  forward_call (ab, na + nb, Ews).
  { rewrite if_false by auto. cancel. }
  Intros data. rewrite if_false by auto.
  match goal with H: Zlength data = _ |- _ => rename H into Hdn end.
  match goal with H: Forall _ data |- _ => rename H into Hdb end.
  assert (Hby: is_bytes data) by exact Hdb.
  assert_PROP (isptr ab) as Pab by entailer!.
  fold (bytes_rep data).
  set (A := sublist 0 na data). set (B := sublist na (na + nb) data).
  assert (CBA: cbuf_ok false ab Ews ab 0 (na + nb) na (bytes_rep data) A)
    by (rewrite <- Hdn; apply cbuf_ok_prefix; auto; lia).
  assert (CBB: cbuf_ok false (offset_val na ab) Ews ab na (na + nb) nb (bytes_rep data) B).
  { assert (C := cbuf_ok_slice Ews ab data na nb ltac:(auto) Pab Hby ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite Hdn in C. exact C. }
  assert (CBW: cbuf_ok false ab Ews ab 0 (na + nb) (na + nb) (bytes_rep data) data)
    by (rewrite <- Hdn; apply cbuf_ok_whole; auto).
  (* aa = adler32_z(a0, ab, na) *)
  forward.
  forward_call (a0, ab, na, false, Ews, ab, 0, na + nb, bytes_rep data, A, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by auto.
  forward.
  (* bb = adler32_z(1, ab + na, nb) *)
  forward_call (1, offset_val na ab, nb, false, Ews, ab, na, na + nb, bytes_rep data, B, true, Ews).
  all: side.
  tok_norm. rewrite adler32_z_val_ref by apply adler_valid_1.
  (* want = ref_adler32(a0, ab, na + nb) *)
  forward.
  forward_call (a0, ab, Ews, ab, 0, na + nb, bytes_rep data, na + nb, data).
  all: side.
  forward.
  (* adler32_combine(aa, bb, nb) == want *)
  pose proof (ref_adler32_valid a0 A Va0) as VA.
  pose proof (ref_adler32_valid 1 B adler_valid_1) as VB.
  assert (RA: 0 <= ref_adler32 a0 A <= Int64.max_unsigned) by (destruct VA; rep_lia).
  assert (RB: 0 <= ref_adler32 1 B <= Int64.max_unsigned) by (destruct VB; rep_lia).
  forward_call (ref_adler32 a0 A, ref_adler32 1 B, nb).
  all: side.
  assert (CMB: adler32_combine_result (ref_adler32 a0 A) (ref_adler32 1 B) nb = ref_adler32 a0 data).
  { replace nb with (Zlength B) by (unfold B; rewrite Zlength_sublist; lia).
    rewrite adler32_combine_app by auto. unfold A, B. rewrite <- sublist_split by lia.
    rewrite sublist_same by lia. reflexivity. }
  rewrite CMB.
  forward_call (Int.repr 1).
  { entailer!. simpl. rewrite Int64.eq_true. reflexivity. }
  (* r = adler32_combine(x, y, z) *)
  forward. forward. forward.
  forward_call (x, y, z).
  forward.
  forward.
  ifsame.
  { (* z < 0 *)
    assert (Hzn: z < 0)
      by (match goal with H: Int64.signed (Int64.repr z) < _ |- _ => rewrite !Int64.signed_repr in H by rep_lia; lia end).
    forward_call (Int.repr 1).
    { entailer!. unfold adler32_combine_result. destruct (Z.ltb_spec z 0); [ | lia]. arg_cmp. }
    entailer!. }
  { (* z >= 0 *)
    assert (Hz0: 0 <= z)
      by (match goal with H: Int64.signed (Int64.repr z) >= _ |- _ => rewrite !Int64.signed_repr in H by rep_lia; lia end).
    forward.
    forward_call x.
    ifpost _t'12 (Int.repr (if andb (valid_b x) (valid_b y) then 1 else 0)).
    { forward. forward_call y. forward. entailer!.
      destruct (valid_b x); [ | simpl in *; lia]. destruct (valid_b y); reflexivity. }
    { forward. entailer!. destruct (valid_b x); [ | reflexivity].
      match goal with H: Int.repr 1 = Int.zero |- _ => apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end. }
    ifsame.
    { destruct (valid_b x) eqn:Vx; [ | simpl in *; lia]. destruct (valid_b y) eqn:Vy; [ | simpl in *; lia].
      apply valid_b_spec in Vx; [ | lia]. apply valid_b_spec in Vy; [ | lia].
      forward. forward. forward. forward. forward. forward. forward. forward. forward. forward.
      forward. forward.
      forward_call (Int.repr 1).
      { entailer!. rewrite combine_check by (auto; rep_lia). reflexivity. }
      entailer!. }
    { forward. entailer!. }
    entailer!. }
  (* free(ab) *)
  forward_call (tarray tuchar (na + nb), ab, gv).
  { rewrite if_false by auto. sep_apply (data_at_data_at_ Ews (tarray tuchar (na + nb)) (bytes_rep data) ab).
    cancel. }
  ret0.
Qed.
