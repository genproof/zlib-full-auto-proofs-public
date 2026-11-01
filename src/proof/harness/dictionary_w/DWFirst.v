(* Laws rt_dictionary and api_dict_id, main (DWKit.v): the first half of statement 28 (rt_dictionary's numbers; 27 in api_dict_id), the flush draw and the first inflate() (A25 -> A26, DWIFacts.di_first), in each program's context (the same proof). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

(* the stream inflateInit2_ makes keeps no gzip header *)
Lemma dwf_init_head (sp : val) (w : Z) : i_head (l_s (init_live sp w)) = false.
Proof.
  unfold init_live. destruct (Zlib.proof.inflate_api.ApiModel.reset2_wb w) as [[? ?] | ]; reflexivity.
Qed.

(* the globals main keeps while it lends inflate() its tables and crc32.c's table *)
Definition dwf_rest (vlit : ident) (gv : globals) : mpred :=
  Zlib.proof.trees.TRep.trees_globals gv * Zlib.proof.deflate.DRep.errmsg_at gv *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray Zlib.proof.deflate.DSpec.t_config 10)
    (Zlib.proof.deflate.DSpec.config_vals gv)
    (gv Zlib.deflate.code._configuration_table) *
  @data_at Zlib.proof.deflate.DCS.CS Ers (tarray tschar 6) (map Zlib.proof.deflate.Rep.vi [49; 46; 51; 46; 50; 0])
    (gv Zlib.deflate.code._my_version) *
  Zlib.proof.deflate.GlobalsInit.version_at gv vlit * Zlib.proof.inflate_api.Spec5.version_lit gv.

Lemma dwf_R_split (vlit : ident) (gv : globals) :
  R_of vlit gv = Zlib.proof.inflate.Rep.tables_rep Ers gv * Zlib.proof.crc32.Spec.crc_table_at Ers gv *
                 dwf_rest vlit gv.
Proof. unfold R_of, dwf_rest, Zlib.proof.deflate.DSpec.deflate_globals. apply pred_ext; cancel. Qed.

(* the output object, nothing written, as inflate()'s output buffer holds it *)
Lemma dwf_out_empty (op : val) (n : Z) :
  data_at_ Ews (tarray tuchar n) op = data_at Ews (tarray tuchar n) (rtl_oc n []) op.
Proof.
  unfold data_at_, rtl_oc. simpl. rewrite Z.sub_0_r. reflexivity.
Qed.

(* the live stream as istreamA_opt with its (empty) gzip header *)
Lemma dwf_istream_opt gv (vs : val) z av L : isptr vs -> i_head (l_s L) = false ->
  istreamA gv Tsh vs z av (Some L) |-- istreamA_opt gv Tsh vs z av (Some L) * head_opt (is_live vs (Some L)).
Proof.
  intros Pv Hh. rewrite rtl_head_none, rtl_istreamA_opt_ptr by auto. rewrite sepcon_emp. apply derives_refl.
Qed.

(* deflate's and inflate's clip are the same function *)
Lemma dwf_clipz (x : Z) : DFacts.clipz x = IFacts.clipz x.
Proof. unfold DFacts.clipz, IFacts.clipz. reflexivity. Qed.

(* rt_dictionary *)
Lemma seg_first_drt_ok : seg_first_drt_stmt.
Proof.
  intros Espec Q P gv vc vd wbits n b D O dict dp op ddp cp z sp DI.
  unfold A25, seg_first_drt, POST_drt, Delta_drt. abbreviate_semax.
  Intros. pose proof H as HF.
  destruct H as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdict & Idict & Pddp & Hw).
  destruct H0 as (Wok & Psp & Zo & Zm & Zt & Zto & Lo).
  unfold max_size in Hn.
  assert_PROP (isptr vd) as Pvd by entailer!.
  set (L := init_live sp (iwb wbits)) in *.
  assert (Hh : i_head (l_s L) = false) by apply dwf_init_head.
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ai := clipz (Zlength O)). set (ao := clipz n).
  assert (Hai: 0 <= ai <= Zlength O /\ ai <= Int.max_unsigned) by (unfold ai, clipz, umax; rep_lia).
  assert (Hao: 0 <= ao <= n /\ ao <= Int.max_unsigned) by (unfold ao, clipz, umax; rep_lia).
  assert (Eai: ai = IFacts.clipz (Zlength O)) by reflexivity.
  clearbody ai ao.
  set (inp := sublist 0 (0 + ai) O).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := rtl_ib cp b 0 O). set (o := rtl_ob op n []).
  replace (offer_z z cp ai op ao) with (offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao)
    by (unfold ib, o, rtl_ib, rtl_ob; simpl; rewrite !isptr_offset_val_zero by auto; reflexivity).
  sep_apply (dwf_istream_opt gv vd (offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao) Vundef L); auto.
  rewrite dwf_out_empty.
  change (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) with (rtl_oc b O).
  sep_apply (rtl_bufs_pre vd L cp b 0 O op n []); auto; try (rewrite ?Zlength_nil; lia). fold ib o.
  rewrite dwf_R_split. Intros.
  assert (INOK: in_ok ib inp) by (apply rtl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply rtl_out_ok; auto; rewrite ?Zlength_nil; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (rtl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  (* the decode theory: the first call asks for the dictionary *)
  assert (CP: call_pre O 0 z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj Lo (conj Zo (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, rtl_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel flush vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  (* deflate's clip in di_first's statement, inflate's in A25: bridged by an equation, not by conversion *)
  pose proof (eq_trans Hinp (eq_trans Eai (eq_sym (dwf_clipz (Zlength O))))) as Ecl.
  assert (H64: Zlength O <= 2 ^ 64 - 1) by (unfold Ptrofs.max_unsigned in Hb; simpl in Hb; lia).
  destruct (di_first Q P DI wbits dict D O z sp vd flush ib inp o ao r z' st' ow DF Hdict H64
              (conj Wok (conj Psp (conj Zo (conj Zm (conj Zt (conj Zto Lo)))))) CP Ecl REL' Zo')
    as (Er & Had & L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & H6 & Eow & Hh' & Hwr & HQ).
  subst st' ow r.
  rewrite rtl_istreamA_opt_ptr by auto. rewrite (rtl_head_none vd L') by auto.
  unfold ib, o. sep_apply (rtl_bufs_post vd L cp b 0 O op n [] []); auto; try (rewrite ?Zlength_nil; lia).
  rewrite <- dwf_out_empty.
  destruct (POST_of DRT.f_main); cbv beta iota.
  Exists z' L'. unfold A26. rewrite dwf_R_split.
  assert (Eni: zf_ni z' = offset_val 6 cp) by (rewrite Hni', H6; reflexivity).
  assert (Eno: zf_no z' = op)
    by (rewrite Hno'; rewrite Zlength_nil in How; unfold rtl_ob; simpl; rewrite <- How;
        apply isptr_offset_val_zero; auto).
  unfold rtl_oc. entailer!.
Qed.

(* api_dict_id: the same proof with its own statement, context and literal *)
Lemma seg_first_dai_ok : seg_first_dai_stmt.
Proof.
  intros Espec Q P gv vc vd wbits n b D O dict dp op ddp cp z sp DI.
  unfold A25, seg_first_dai, POST_dai, Delta_dai. abbreviate_semax.
  Intros. pose proof H as HF.
  destruct H as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdict & Idict & Pddp & Hw).
  destruct H0 as (Wok & Psp & Zo & Zm & Zt & Zto & Lo).
  unfold max_size in Hn.
  assert_PROP (isptr vd) as Pvd by entailer!.
  set (L := init_live sp (iwb wbits)) in *.
  assert (Hh : i_head (l_s L) = false) by apply dwf_init_head.
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (ai := clipz (Zlength O)). set (ao := clipz n).
  assert (Hai: 0 <= ai <= Zlength O /\ ai <= Int.max_unsigned) by (unfold ai, clipz, umax; rep_lia).
  assert (Hao: 0 <= ao <= n /\ ao <= Int.max_unsigned) by (unfold ao, clipz, umax; rep_lia).
  assert (Eai: ai = IFacts.clipz (Zlength O)) by reflexivity.
  clearbody ai ao.
  set (inp := sublist 0 (0 + ai) O).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := rtl_ib cp b 0 O). set (o := rtl_ob op n []).
  replace (offer_z z cp ai op ao) with (offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao)
    by (unfold ib, o, rtl_ib, rtl_ob; simpl; rewrite !isptr_offset_val_zero by auto; reflexivity).
  sep_apply (dwf_istream_opt gv vd (offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao) Vundef L); auto.
  rewrite dwf_out_empty.
  change (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) with (rtl_oc b O).
  sep_apply (rtl_bufs_pre vd L cp b 0 O op n []); auto; try (rewrite ?Zlength_nil; lia). fold ib o.
  rewrite dwf_R_split. Intros.
  assert (INOK: in_ok ib inp) by (apply rtl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply rtl_out_ok; auto; rewrite ?Zlength_nil; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (rtl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  (* the decode theory: the first call asks for the dictionary *)
  assert (CP: call_pre O 0 z L vd flush ib inp o ao).
  { unfold call_pre.
    refine (conj Lo (conj Zo (conj _ (conj Hfl (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - unfold ib, rtl_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel flush vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  (* deflate's clip in di_first's statement, inflate's in A25: bridged by an equation, not by conversion *)
  pose proof (eq_trans Hinp (eq_trans Eai (eq_sym (dwf_clipz (Zlength O))))) as Ecl.
  assert (H64: Zlength O <= 2 ^ 64 - 1) by (unfold Ptrofs.max_unsigned in Hb; simpl in Hb; lia).
  destruct (di_first Q P DI wbits dict D O z sp vd flush ib inp o ao r z' st' ow DF Hdict H64
              (conj Wok (conj Psp (conj Zo (conj Zm (conj Zt (conj Zto Lo)))))) CP Ecl REL' Zo')
    as (Er & Had & L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & H6 & Eow & Hh' & Hwr & HQ).
  subst st' ow r.
  rewrite rtl_istreamA_opt_ptr by auto. rewrite (rtl_head_none vd L') by auto.
  unfold ib, o. sep_apply (rtl_bufs_post vd L cp b 0 O op n [] []); auto; try (rewrite ?Zlength_nil; lia).
  rewrite <- dwf_out_empty.
  destruct (POST_of DAI.f_main); cbv beta iota.
  Exists z' L'. unfold A26. rewrite dwf_R_split.
  assert (Eni: zf_ni z' = offset_val 6 cp) by (rewrite Hni', H6; reflexivity).
  assert (Eno: zf_no z' = op)
    by (rewrite Hno'; rewrite Zlength_nil in How; unfold rtl_ob; simpl; rewrite <- How;
        apply isptr_offset_val_zero; auto).
  unfold rtl_oc. entailer!.
Qed.

Lemma seg_first_ok : seg_first_drt_stmt /\ seg_first_dai_stmt.
Proof. exact (conj seg_first_drt_ok seg_first_dai_ok). Qed.
