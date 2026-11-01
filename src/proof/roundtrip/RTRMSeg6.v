(* Law deflate_roundtrip, main (kit: RTRMKit.v): positions 6-7 of b0 without a gzip header
   (R.head_set = 0: the inflateGetHeader block is skipped; head_mem of init_live is emp), then the raw dictionary
   block `if (R.wrap == 0 && R.dict_set) { r = inflateSetDictionary(&t, R.dict, R.dlen); if (r == Z_MEM_ERROR)
   return 0; gp_assert(r == Z_OK); }` (Spec5.inflateSetDictionary_spec; first_facts gives Z_OK or Z_MEM_ERROR and
   first_ok of the new live part); establishes A8 with first_ok. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* rm_dside opened at the fields positions 6-7 read (R.head_set, R.wrap, R.dict_set, R.dict, R.dlen) and the
   dictionary object *)
Definition rm6_rest (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in let Rp := vR in
  field_at Ews t_drun (DOT _level) (vi (rs_level rs)) Rp *
  field_at Ews t_drun (DOT _method) (vi (rs_method rs)) Rp *
  field_at Ews t_drun (DOT _wbits) (vi (rs_wbits rs)) Rp *
  field_at Ews t_drun (DOT _mem) (vi (rs_mem rs)) Rp *
  field_at Ews t_drun (DOT _strategy) (vi (rs_strategy rs)) Rp *
  field_at Ews t_drun (DOT _init) (vi 0) Rp *
  field_at Ews t_drun (DOT _wb) (vi (wb_of (rs_wbits rs))) Rp *
  field_at Ews t_drun (DOT _data) (rs_datap rs) Rp *
  field_at Ews t_drun (DOT _n) (vi (Zlength (rs_data rs))) Rp *
  field_at Ews t_drun (DOT _nf) (vi (rf_nf rf)) Rp *
  field_at Ews t_drun (DOT _xf) (rs_xfp rs) Rp *
  field_at Ews t_drun (DOT _nf_) (rs_nfp rs) Rp *
  field_at Ews t_drun (DOT _cf) (rs_cfp rs) Rp *
  field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) Rp *
  field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) Rp *
  field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) Rp *
  field_at Ews t_drun (DOT _comp) (rs_compp rs) Rp *
  field_at Ews t_drun (DOT _clen) (vl (Zlength (rf_O rf))) Rp *
  field_at Ews t_drun (DOT _ended) (vi 1) Rp *
  field_at Ews t_drun (DOT _api_ok) (vi 1) Rp *
  drun_pad Rp *
  hpart (rf_hset rf) vR * hdr_at (Some (rf_s rf)) (rf_ghp rf) (hx_of rs) *
  obj (rs_datap rs) (rs_data rs) * comp_at (rf_O rf) (rs_compp rs) *
  data_at_ (Share.comp Ews) t_drun vR.

Definition rm6_open (rf : rfinal) (vR : val) : mpred :=
  let rs := rf_rs rf in
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp rs) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict rs))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR *
  malloc_token Ews (tarray tuchar (Zlength (rs_dict rs))) (rs_dictp rs) *
  data_at Ews (tarray tuchar (Zlength (rs_dict rs))) (map vi (rs_dict rs)) (rs_dictp rs) *
  rm6_rest rf vR.

Lemma rm6_open_eq rf vR : rm_dside rf vR = rm6_open rf vR.
Proof. unfold rm_dside, drun_rest, rm6_open, rm6_rest, obj. apply pred_ext; cancel. Qed.

Lemma rm6_close rf vR :
  field_at Ews t_drun (DOT _wrap) (vi (rf_wrap rf)) vR *
  field_at Ews t_drun (DOT _dict) (rs_dictp (rf_rs rf)) vR *
  field_at Ews t_drun (DOT _dlen) (vi (Zlength (rs_dict (rf_rs rf)))) vR *
  field_at Ews t_drun (DOT _dict_set) (vi (rf_dset rf)) vR *
  field_at Ews t_drun (DOT _head_set) (vi (rf_hset rf)) vR *
  malloc_token Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (rs_dictp (rf_rs rf)) *
  data_at Ews (tarray tuchar (Zlength (rs_dict (rf_rs rf)))) (map vi (rs_dict (rf_rs rf))) (rs_dictp (rf_rs rf)) *
  rm6_rest rf vR |-- rm_dside rf vR.
Proof. rewrite rm6_open_eq. unfold rm6_open. apply derives_refl. Qed.

Lemma rm6_wrap rf : rf_wrap rf = 0 \/ rf_wrap rf = 1 \/ rf_wrap rf = 2.
Proof. unfold rf_wrap, wrap_of. destruct (_ <? 0); [ | destruct (_ >? 15)]; auto. Qed.

Lemma rm6_head_init sp w : head_mem (init_live sp w) = emp.
Proof. unfold head_mem, init_live. destruct (reset2_wb w) as [[? ?] | ]; reflexivity. Qed.

Lemma rm6_ihead_init sp w : i_head (l_s (init_live sp w)) = false.
Proof. unfold init_live. destruct (reset2_wb w) as [[? ?] | ]; reflexivity. Qed.

Lemma rm6_iopt gv sh p z st : isptr p -> istream_opt gv sh p z st = istream gv sh p z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec p nullval); [subst; contradiction | reflexivity]. Qed.

Lemma rm6_on_live p z L f : isptr p ->
  on_live p z (Some L) f = (fst3 (f z L), snd3 (f z L), Some (thd3 (f z L))).
Proof.
  intros P. unfold on_live, is_live. destruct (eq_dec p nullval); [subst; contradiction | ].
  destruct (f z L) as [[? ?] ?]; reflexivity.
Qed.

Lemma rm6_head_uw s d : i_head (updatewindow s d) = i_head s.
Proof.
  unfold updatewindow. cbv zeta.
  destruct (i_wsize s =? 0);
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma rm6_head_sd dict aok winp z L :
  i_head (l_s (thd3 (setdict_f dict aok winp z L))) = i_head (l_s L).
Proof.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [ | destruct aok]; simpl; try apply rm6_head_uw; reflexivity.
Qed.

Lemma rm6_head_sd_init dict aok winp z sp w :
  head_mem (thd3 (setdict_f dict aok winp z (init_live sp w))) = emp.
Proof. unfold head_mem. rewrite rm6_head_sd, rm6_ihead_init. reflexivity. Qed.

Lemma rm6_z_sd dict aok winp z L : snd3 (setdict_f dict aok winp z L) = z.
Proof.
  unfold setdict_f. destruct (setdict_check (l_s L) dict); try reflexivity.
  destruct (i_win (l_s L)); [ | destruct aok]; reflexivity.
Qed.

Lemma rm_seg6 {Espec : OracleKind} I Iend rf vR vs vt vih gv z sp :
  rf_hset rf = 0 -> first_facts rf ->
  (forall L, semax (Delta_m I Iend) (A8 Iend rf vR vs vt vih gv z L) seg8 POST_b) ->
  semax (Delta_m I Iend) (A6 Iend rf vR vs vt vih gv z sp) seg6 POST_b.
Proof.
  intros Hh FF K.
  unfold seg6. apply seq_assoc.
  apply semax_seq with (Q := EX L, A8 Iend rf vR vs vt vih gv z L);
    [ | apply extract_exists_pre; intro L; apply K].
  unfold Delta_m, A6, POST_b, POST_m. simplify_func_tycontext.
  rewrite rm6_open_eq. unfold rm6_open.
  Intros.
  assert (WR := rm6_wrap rf).
  assert (DS: (rf_dset rf = 1 /\ rf_dict rf = rs_dict (rf_rs rf) /\ rs_dict (rf_rs rf) <> []) \/
              (rf_dset rf = 0 /\ rf_dict rf = []))
    by (destruct H as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (RS: rs_ok (rf_rs rf)) by (destruct H; auto).
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx Q (SEPx R))) end.
  { rewrite Hh in *. contradiction. }
  { forward. entailer!. }
  forward.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'13 (Vint (if ((rf_wrap rf =? 0) && (rf_dset rf =? 1))%bool then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { forward. forward. entailer!. rewrite H1. destruct DS as [[D _] | [D _]]; rewrite D; reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity. }
  forward_if.
  { assert (WD: rf_wrap rf = 0 /\ rf_dset rf = 1).
    { destruct (rf_wrap rf =? 0) eqn:E1; destruct (rf_dset rf =? 1) eqn:E2; simpl in H1;
        try (contradiction H1; reflexivity).
      apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. auto. }
    destruct WD as [W D].
    destruct DS as [[_ [ED NE]] | [D' _]]; [ | lia].
    destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DL & _ & _ & _ & _ &
                    BD & _ & _ & _ & _ & PD & _).
    forward. forward.
    assert_PROP (isptr vt) as Pvt by entailer!.
    assert_PROP (live_ok (init_live sp (rm_iw rf))) as LOK by (unfold istream; entailer!).
    rewrite (bytes_cs CS Zlib.units.Inflate.CS Ews).
    forward_call (gv, Tsh, vt, z, Some (init_live sp (rm_iw rf)), Ews, rs_dictp (rf_rs rf), 0,
                  Zlength (rs_dict (rf_rs rf)), map vi (rs_dict (rf_rs rf)), rs_dict (rf_rs rf), false).
    { rewrite rm6_iopt by auto. cancel. }
    { split; [apply Zlength_map | ].
      split; [intros E; apply Zlength_nil_inv in E; contradiction | ].
      split; [rewrite sublist_same by (rewrite ?Zlength_map; lia); reflexivity | ].
      eapply Forall_impl; [ | exact BD]. intros b Hb; simpl in *; rep_lia. }
    Intros vret. destruct vret as [aok winp]. simpl fst; simpl snd.
    rewrite rm6_iopt by auto. rewrite !rm6_on_live by auto.
    pose proof (proj2 (FF sp) W D LOK aok winp z) as SD. cbv zeta in SD. rewrite ED in SD.
    pose proof (rm6_z_sd (rs_dict (rf_rs rf)) aok winp z (init_live sp (rm_iw rf))) as ZS.
    pose proof (rm6_head_sd_init (rs_dict (rf_rs rf)) aok winp z sp (rm_iw rf)) as HS.
    destruct (setdict_f (rs_dict (rf_rs rf)) aok winp z (init_live sp (rm_iw rf))) as [[r z'] L'] eqn:E.
    unfold fst3, snd3, thd3 in *; simpl fst in *; simpl snd in *. subst z'.
    rewrite (bytes_cs Zlib.units.Inflate.CS CS Ews).
    destruct SD as [Hr HOK].
    forward.
    forward_if.
    { sep_apply (rm6_close rf vR). sep_apply (rm_dside_ret Iend vR rf H). sep_apply rm_istream_ret.
      forward. Exists (Int.repr 0). entailer!. }
    assert (r = Z_OK) by (destruct Hr; auto; subst; contradiction). subst r.
    forward_call (Int.repr 1).
    Exists L'. unfold A8. rewrite HS, rm6_open_eq. unfold rm6_open. entailer!. }
  { assert (NB: ~ (rf_wrap rf = 0 /\ rf_dset rf = 1)).
    { intros [W D]. rewrite W, D in H1. simpl in H1. apply Int.one_not_zero; exact H1. }
    forward. Exists (init_live sp (rm_iw rf)). unfold A8. rewrite rm6_head_init, rm6_open_eq. unfold rm6_open.
    entailer!. apply (proj1 (FF sp) NB). }
Qed.
