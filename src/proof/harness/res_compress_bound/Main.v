(* Law res_compress_bound: main's body (harness/res_compress_bound.c) against MainLib.main_core_spec R under
   Gmain: the laws_common.h helpers upto / any_bytes (laws_common/Spec.v), compress.c's compressBound_z
   (CSpec.v), compress2_z for any sizes (RTCSpecW.v, POST = RTC2.c2_res), malloc and gp_assert.  The model fact:
   RTC2W.c2w_bound_stmt (for data of at most PTRDIFF_MAX bytes, a level -1..9 and destLen = compressBound_z(n),
   compress2_z's run exists for every allocation outcome and ends with Z_OK or Z_MEM_ERROR); with Z_OK, main's
   compressed_len <= bound follows from compress2_z's postcondition (the output fits in destLen).  main computes
   compressBound's formula itself and asserts it equal to compressBound_z(n) (BoundFormula.cb_formula_i64: no
   wrap-around for n <= PTRDIFF_MAX); the source is any_bytes' object, or Z_NULL when it has no bytes
   (null_if_empty), which compress2_z's specification accepts as its source resource [c2_src]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW Zlib.proof.roundtrip.RTC2W.
Require Import Zlib.proof.compress.BoundFormula.
Require Import Zlib.proof.harness.res_compress_bound.LawCS Zlib.proof.harness.res_compress_bound.Globals.
Require Import Zlib.harness.res_compress_bound.code.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Definition Gmain : funspecs :=
  [upto_spec; Zlib.proof.compress.CSpec.compressBound_z_spec; any_bytes_spec;
   (_quickproof_malloc, malloc_spec'); compress2_z_spec_w; gp_assert_spec].

(* compressBound_z of a size an object can have (at most PTRDIFF_MAX): no wrap-around, at least 13 *)
Lemma rcb_cb_range n : 0 <= n <= 9223372036854775807 -> 13 <= compressBound_z n <= Int64.max_unsigned.
Proof.
  intros Hn. unfold compressBound_z.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096. change (2 ^ 14) with 16384. change (2 ^ 25) with 33554432.
  assert (0 <= n / 4096 <= 2251799813685248) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= n / 16384 <= n / 4096) by (split; [apply Z.div_pos | apply Z.div_le_compat_l]; lia).
  assert (0 <= n / 33554432 <= n / 4096) by (split; [apply Z.div_pos | apply Z.div_le_compat_l]; lia).
  unfold Zlib.proof.huffman.Model.u64. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (n + n / 4096 + n / 16384 + n / 33554432 + 13) n); rep_lia.
Qed.

(* moves between the units' compspecs and the law's *)
Lemma rcb_bytes_compress sh n (v: list val) q:
  @data_at Zlib.units.Compress.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma rcb_ulong_compress sh (v: val) q:
  @data_at Zlib.units.Compress.CS sh tulong v q = @data_at CS sh tulong v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_compress); [apply JMeq_refl | reflexivity]. Qed.
Lemma rcb_bytes_adler sh n (v: list val) q:
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = @data_at CS sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.
Lemma rcb_tok_adler sh n q:
  @malloc_token Zlib.units.Adler32.CS sh (tarray tuchar n) q = @malloc_token CS sh (tarray tuchar n) q.
Proof. apply equal_f; apply (@malloc_token_change_composite _ _ CC_adler32). reflexivity. Qed.

(* forward_call's frame when the spec's SEP list is a definition [d] (RTCSpecW.c2w_sep_pre) *)
Ltac rcb_sep_cancel d :=
  unfold d;
  repeat (eapply syntactic_cancel_cons_succeed;
          [find_nth ecancel_local_tac | cbv iota; unfold delete_nth; cbv zeta iota ]);
  apply syntactic_cancel_nil.

(* compress2_z's precondition for destLen = compressBound_z(n), from c2w_bound_stmt *)
Lemma rcb_c2_pre (CB: c2w_bound_stmt) lvl gv dp dlp sp src :
  isptr dp -> is_pointer_or_null sp -> is_bytes src -> Zlength src <= 9223372036854775807 -> -1 <= lvl <= 9 ->
  fold_right_and True
    (c2w_pre lvl gv dp (Zrepeat Vundef (compressBound_z (Zlength src))) (compressBound_z (Zlength src)) dlp Ews
       sp src).
Proof.
  intros Hd Hs Hb Hn Hl. assert (0 <= Zlength src) by apply Zlength_nonneg.
  pose proof (rcb_cb_range (Zlength src) ltac:(lia)) as Hcb.
  assert (Hrb: rbytes src) by (eapply Forall_impl; [ | exact Hb]; simpl; intros; rep_lia).
  unfold c2w_pre. simpl. unfold Zrepeat. rewrite Zlength_repeat by rep_lia.
  split; [exact Hd | ]. split; [reflexivity | ]. split; [rep_lia | ]. split; [lia | ]. split; [auto | ].
  split; [exact Hs | ]. split; [rep_lia | ]. split; [exact Hrb | ]. split; [unfold rs32; lia | ]. split; [ | exact I].
  intros. apply (proj1 (CB src lvl a1 a2 a3 a4 a5 _ Hrb Hn Hl)).
Qed.

(* the outcome: Z_OK or Z_MEM_ERROR *)
Lemma rcb_c2_post (CB: c2w_bound_stmt) src lvl a1 a2 a3 a4 a5 r out :
  is_bytes src -> Zlength src <= 9223372036854775807 -> -1 <= lvl <= 9 ->
  c2_res src (compressBound_z (Zlength src)) lvl a1 a2 a3 a4 a5 Zlib.proof.deflate.DSpec9.zrst0 r out ->
  r = Z_OK \/ r = Z_MEM_ERROR.
Proof.
  intros Hb Hn Hl Hr.
  assert (Hrb: rbytes src) by (eapply Forall_impl; [ | exact Hb]; simpl; intros; rep_lia).
  exact (proj1 (proj2 (CB src lvl a1 a2 a3 a4 a5 _ Hrb Hn Hl) r out Hr)).
Qed.

(* a branch the values exclude *)
Ltac rcb_absurd :=
  first [ contradiction
        | exfalso; apply Int.one_not_zero; assumption
        | match goal with H: ?x <> ?x |- _ => contradiction (H eq_refl) end ].

(* the test data == NULL on any_bytes' object (of any size, 0 included) *)
Ltac rcb_tc_data :=
  match goal with |- _ |-- denote_tc_test_eq ?q _ =>
    match goal with |- context [@data_at _ _ (tarray tuchar ?n) ?v q] =>
      apply (@malloc_test_eq CS _ n); [rep_lia | sep_apply (data_at_data_at_ Ews (tarray tuchar n) v q); cancel]
    end
  end.

(* main's source (any_bytes' object, or Z_NULL with no bytes) as compress2_z's source resource [c2_src], with
   the object's malloc token aside *)
Lemma rcb_src_c2 sp bs :
  (sp = nullval -> bs = []) ->
  (if eq_dec sp nullval then emp
   else malloc_token Ews (tarray tuchar (Zlength bs)) sp * data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) sp)
  |-- c2_src Ews sp bs *
      (if eq_dec sp nullval then emp else malloc_token Ews (tarray tuchar (Zlength bs)) sp).
Proof.
  intros E. unfold c2_src. destruct (eq_dec sp nullval) as [P | P].
  - rewrite (E P). entailer!.
  - rewrite <- rcb_bytes_compress. cancel.
Qed.

(* Floyd's simplify_remove_localdef_temp (simpl on rlt_ident_eq of the large $"..." identifiers) does not end
   after a call that stores into a temp of this main: remove the temp by rewriting instead *)
Lemma rcb_rlt_nil i: remove_localdef_temp i [] = [].
Proof. reflexivity. Qed.
Lemma rcb_rlt_gvars i g l: remove_localdef_temp i (gvars g :: l) = gvars g :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rcb_rlt_lvar i j t v l: remove_localdef_temp i (lvar j t v :: l) = lvar j t v :: remove_localdef_temp i l.
Proof. reflexivity. Qed.
Lemma rcb_rlt_same i v l: remove_localdef_temp i (temp i v :: l) = remove_localdef_temp i l.
Proof. simpl. unfold rlt_ident_eq. rewrite if_true by auto. reflexivity. Qed.
Lemma rcb_rlt_cons i j v l: i <> j -> remove_localdef_temp i (temp j v :: l) = temp j v :: remove_localdef_temp i l.
Proof. intros. simpl. unfold rlt_ident_eq. rewrite if_false by auto. reflexivity. Qed.

Ltac simplify_remove_localdef_temp ::=
  repeat first [ rewrite rcb_rlt_nil | rewrite rcb_rlt_gvars | rewrite rcb_rlt_lvar | rewrite rcb_rlt_same
               | rewrite rcb_rlt_cons by (let X := fresh in intro X; discriminate X) ].

Lemma body_main : c2w_bound_stmt -> semax_body (QPvarspecs p) Gmain f_main (_main, main_core_spec R).
Proof.
  intros CB.
  start_function.
  unfold R. Intros.
  forward_call 10.
  Intros lv.
  forward.
  { entailer!. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. rewrite Int.signed_repr by rep_lia.
    rep_lia. }
  replace (Int.add (Int.neg (Int.repr 1)) (Int.repr (Int64.unsigned (Int64.repr lv)))) with (Int.repr (lv - 1))
    by (rewrite Int64.unsigned_repr by rep_lia; rewrite Int.add_signed, Int.signed_repr by rep_lia; f_equal; 
        change (Int.signed (Int.neg (Int.repr 1))) with (-1); lia).
  forward_call 9223372036854775807.
  Intros n.
  pose proof (rcb_cb_range n ltac:(lia)) as Hcb.
  forward_call 1.
  Intros ne.
  forward.
  change (Int64.repr (Int.unsigned (Int.repr 12))) with (Int64.repr 12).
  change (Int64.repr (Int.unsigned (Int.repr 14))) with (Int64.repr 14).
  change (Int64.repr (Int.unsigned (Int.repr 25))) with (Int64.repr 25).
  change (Int64.repr (Int.signed (Int.repr 13))) with (Int64.repr 13).
  rewrite (cb_formula_i64 n H0).
  set (cb := compressBound_z n) in *.
  rewrite <- !seq_assoc.
  forward_call n.
  (* the formula computed by main is compressBound_z(original_len) *)
  forward_call (Int.repr 1).
  { entailer!. unfold Int64.eq. rewrite zeq_true. reflexivity. }
  forward.
  forward.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  ifpost _t'6 (if orb (0 <? n) (ne =? 0) then Int.one else Int.zero).
  { forward. rewrite !Int64.unsigned_repr in H2 by rep_lia. rewrite (proj2 (Z.ltb_lt 0 n)) by rep_lia. entailer!. }
  { forward. rewrite !Int64.unsigned_repr in H2 by rep_lia. rewrite (proj2 (Z.ltb_ge 0 n)) by rep_lia. entailer!.
    destruct (Z.eqb_spec ne 0); [subst; reflexivity | assert (ne = 1) by lia; subst; reflexivity]. }
  (* the source: any_bytes' object (NULL when malloc fails), or Z_NULL for an empty source *)
  match goal with |- semax _ (PROPx _ (LOCALx (?t6 :: temp _original _ :: ?Q) (SEPx ?Rs))) _ _ =>
    forward_if (EX q : val, EX bs : list Z,
      PROPx [Zlength bs = n; is_bytes bs]
      (LOCALx (t6 :: temp _original q :: Q)
      (SEPx (Rs ++ [if eq_dec q nullval then emp
                    else (malloc_token Ews (tarray tuchar n) q * data_at Ews (tarray tuchar n) (bytes_rep bs) q)]))))
  end.
  { forward_call (n, gv).
    Intros vret. destruct vret as [q bs]. simpl fst in *; simpl snd in *.
    forward.
    Exists q bs. entailer!. simpl app. simpl fold_right_sepcon.
    destruct (eq_dec q nullval) as [Pq | Pq]; [rewrite !if_true by exact Pq; cancel
      | rewrite !if_false by exact Pq; rewrite rcb_tok_adler, rcb_bytes_adler; cancel]. }
  { forward.
    assert (n = 0).
    { destruct (Z.ltb_spec 0 n); [discriminate | lia]. }
    subst n. Exists nullval (@nil Z). entailer!.
    { constructor. }
    simpl app. try rewrite if_true by reflexivity. simpl. cancel. }
  Intros datap bs.
  simpl app.
  forward_call (tarray tuchar cb, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros destp.
  (* main returns unless the output object exists and the source is an object or Z_NULL with no bytes *)
  ifpost _t'8 (if eq_dec datap nullval then (if zlt 0 n then Int.one else Int.zero) else Int.zero).
  { destruct (eq_dec datap nullval) as [PS | PS].
    { subst datap. entailer!. }
    rewrite (if_false (datap = nullval)) by exact PS. rcb_tc_data. }
  { forward. entailer!. rewrite if_true by reflexivity. unfold Int64.cmpu, Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt 0 (Zlength bs)); reflexivity. }
  { forward. entailer!. rewrite (if_false (datap = nullval)) by assumption. reflexivity. }
  ifpost _t'9 (if eq_dec datap nullval
               then (if zlt 0 n then Int.one else if eq_dec destp nullval then Int.one else Int.zero)
               else if eq_dec destp nullval then Int.one else Int.zero).
  { forward. entailer!.
    destruct (eq_dec datap nullval) as [E | E];
      [rewrite (if_true (datap = nullval)) in * by exact E; destruct (zlt 0 (Zlength bs))
      | rewrite (if_false (datap = nullval)) in * by exact E]; try reflexivity; rcb_absurd. }
  { destruct (eq_dec destp nullval) as [PD | PD].
    { subst destp. forward. entailer!. destruct (eq_dec datap nullval); [destruct (zlt 0 (Zlength bs)) | ]; reflexivity. }
    try rewrite (if_false (destp = nullval)) by exact PD. Intros.
    forward.
    entailer!.
    assert (Pd: isptr destp) by (eapply field_compatible_isptr; eassumption).
    destruct destp; try contradiction.
    destruct (eq_dec datap nullval) as [E | E]; [ | reflexivity].
    rewrite (if_true (datap = nullval)) in * by exact E.
    destruct (zlt 0 (Zlength bs)); [rcb_absurd | reflexivity]. }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx [destp <> nullval; datap = nullval -> n = 0] (LOCALx Q (SEPx Rs))) end.
  { ret0. }
  { forward. entailer!.
    match goal with Hh: (if _ then _ else _) = Int.zero |- _ => rename Hh into H9 end.
    split; intro E; [subst destp | subst datap];
      repeat match type of H9 with context [if ?c then _ else _] => destruct c end; try rcb_absurd; lia. }
  Intros.
  rewrite !(if_false (destp = nullval)) by assumption. Intros.
  assert_PROP (isptr destp) as Pdest by entailer!.
  assert_PROP (is_pointer_or_null datap) as Pdata.
  { destruct (eq_dec datap nullval) as [E | E]; [subst datap; entailer! | ].
    rewrite (if_false (datap = nullval)) by exact E. entailer!. }
  subst n.
  assert (Hsrc: datap = nullval -> bs = []) by (intro E; apply Zlength_nil_inv; auto).
  change (EqDec_val datap nullval) with (eq_dec datap nullval).
  sep_apply (rcb_src_c2 datap bs Hsrc). Intros.
  replace (data_at_ Ews (tarray tuchar cb) destp) with (data_at Ews (tarray tuchar cb) (Zrepeat Vundef cb) destp)
    by reflexivity.
  subst cb.
  rewrite <- seq_assoc.
  rewrite <- (rcb_bytes_compress Ews (compressBound_z (Zlength bs)) _ destp),
    <- (rcb_ulong_compress Tsh _ v_compressed_len).
  forward_call (gv, destp, Zrepeat Vundef (compressBound_z (Zlength bs)), compressBound_z (Zlength bs),
                v_compressed_len, Ews, datap, bs, lv - 1).
  { rcb_sep_cancel c2w_sep_pre. }
  { apply (rcb_c2_pre CB); [exact Pdest | exact Pdata | exact H3 | lia | lia]. }
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out]. simpl fst in *; simpl snd in *.
  unfold c2w_sep_post. simpl app.
  rewrite rcb_bytes_compress, rcb_ulong_compress.
  match goal with H: c2_res _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hres end.
  pose proof (rcb_c2_post CB bs (lv - 1) a1 a2 a3 a4 a5 r out H3 ltac:(lia) ltac:(lia) Hres) as Hr.
  forward_if.
  { ret0. }
  assert (r = Z_OK) as Hok.
  { unfold Z_OK, Z_MEM_ERROR in *. destruct Hr as [-> | ->]; [reflexivity | ].
    match goal with Hn: Int.repr (-4) <> _ |- _ => exfalso; apply Hn; reflexivity end. }
  subst r.
  rewrite <- seq_assoc.
  (* code == Z_OK: compressed_len <= bound, by compress2_z's postcondition (the output fits in destLen) *)
  ifpost _t'11 Int.one.
  { forward. forward.
    assert (Hle: Int64.cmpu Cle (Int64.repr (Zlength out)) (Int64.repr (compressBound_z (Zlength bs))) = true).
    { pose proof (Zlength_nonneg out). unfold Int64.cmpu, Int64.ltu.
      rewrite !Int64.unsigned_repr by rep_lia. rewrite zlt_false by lia. reflexivity. }
    rewrite Hle. entailer!. }
  { rcb_absurd. }
  forward_call (Int.repr 1).
  ret0.
Qed.
