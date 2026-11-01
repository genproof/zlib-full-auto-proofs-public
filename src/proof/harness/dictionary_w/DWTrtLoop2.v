(* Law rt_dictionary, main (DWKit.v), statement 32 (DWTrtLoop1.v): (5), the call
   code = inflate(&decompressor, Z_FINISH) on the stream offered clip(|O| - pos) bytes of O from pos on and
   clip(n - |out|) bytes of the output object after out, then `return 0` on Z_MEM_ERROR; DWIFacts.di_call gives
   the loop's test state trt_cont. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
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
Require Import Zlib.proof.harness.dictionary_w.DWTrtLoop1.
Import DWKit.DRT.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

Lemma trt_call_ok {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp pos out z L (X Y : environ -> mpred) :
  dict_ifacts Q P -> dw_hf wbits n b D O dict dp op ddp cp -> 6 <= Zlength O ->
  P wbits dict D O pos out z L -> swfW (l_s L) -> zf_ok z -> live_ok L ->
  semax Delta_drt (trt_mid1 n b D O dict dp op ddp cp gv vc vd pos out z L) trt_call
    (loop1_ret_assert (trt_cont P wbits n b D O dict dp op ddp cp gv vc vd)
       (overridePost X (overridePost Y POST_drt))).
Proof.
  intros PF HF H6O HP Hsw Zo Lo.
  pose proof HF as HF'. destruct HF' as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdl & IDd & Pddp & Hw).
  unfold max_size in Hn.
  unfold trt_call, trt_mid1, Delta_drt, POST_drt. abbreviate_semax.
  assert_PROP (isptr vd) as Pvd by entailer!.
  destruct (di_ok _ _ PF _ _ _ _ _ _ _ _ HP) as (Hhd & Hwr & Hpos & rest & Erest).
  assert (Hout: Zlength out <= n) by (rewrite <- HD, Erest, Zlength_app; pose proof (Zlength_nonneg rest); lia).
  clear Erest rest.
  set (ai := Z.min (Zlength O - pos) Int.max_unsigned).
  set (ao := Z.min (n - Zlength out) Int.max_unsigned).
  assert (Hai: 0 <= ai <= Zlength O - pos /\ ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  assert (Hao: 0 <= ao <= n - Zlength out /\ ao <= Int.max_unsigned) by (unfold ao; rep_lia).
  assert (Cai: ai = DFacts.clipz (Zlength O - pos)) by (unfold ai; apply trt_clipz).
  assert (Cao: ao = DFacts.clipz (Zlength D - Zlength out)) by (unfold ao; rewrite <- HD; apply trt_clipz).
  clearbody ai ao.
  set (inp := sublist pos (pos + ai) O).
  assert (Hinp: Zlength inp = ai) by (unfold inp; rewrite Zlength_sublist; lia).
  set (ib := rtl_ib cp b pos O). set (o := rtl_ob op n out).
  replace (offset_val pos cp) with (in_ptr ib 0) by (unfold ib, rtl_ib; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) op) with (out_ptr o 0)
    by (unfold o, rtl_ob; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (rtl_offer_fold gv vd z L ib o ai ao); auto; try lia.
  change (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) with (rtl_oc b O).
  change (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) with (rtl_oc n out).
  sep_apply (rtl_bufs_pre vd L cp b pos O op n out); auto; try lia. fold ib o.
  unfold R_of, Zlib.proof.deflate.DSpec.deflate_globals. Intros.
  assert (INOK: in_ok ib inp) by (apply rtl_in_ok; auto; lia).
  assert (OUTOK: out_ok o ao) by (apply rtl_out_ok; auto; rep_lia).
  forward_call (gv, Tsh, vd, offer_z z (in_ptr ib 0) ai (out_ptr o 0) ao, Vundef, Some L, ib, inp, Some o,
                4, Ers, Ers, true, true).
  { split; [exact INOK | simpl; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hs: match st' with Some _ => _ | None => _ end |- _ => rename Hs into Hsw' end.
  assert_PROP (zf_ok z') as Zo'.
  { sep_apply (rtl_zf_ok gv Tsh vd z' Vundef st'); auto. entailer!. }
  forward_if.
  { (* Z_MEM_ERROR ends the run *)
    forward. Exists (Int.repr 0). sep_apply (rtl_a_frame_opt gv Tsh vd z' Vundef st'); auto. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (CP: call_pre O pos z L vd 4 ib inp o ao).
  { unfold call_pre.
    refine (conj Lo (conj Zo (conj _ (conj _ (conj _ (conj INOK (conj OUTOK (conj _ (conj _ _))))))))).
    - intro E; subst vd; contradiction.
    - rep_lia.
    - unfold ib, rtl_ib; discriminate.
    - unfold umax; rep_lia.
    - unfold umax; rep_lia.
    - rewrite Hinp. reflexivity. }
  assert (REL': inflate_rel Z_FINISH vd (offer_z z (in_ptr ib 0) (Zlength inp) (out_ptr o 0) ao) (Some L) ib inp
                  (Some o) r z' st' ow) by (rewrite Hinp; exact REL).
  destruct (di_call _ _ PF wbits dict D O pos out z L vd ib inp o ao r z' st' ow HP CP
              (eq_trans Hinp Cai) Cao REL' Hr Zo')
    as (L' & (Est & Hai' & Hao' & Hni' & Hno' & How) & Hcode & Hend & Hbuf).
  subst st'.
  rewrite rtl_istreamA_opt_ptr by auto.
  rewrite (rtl_is_live_ptr vd (Some L')) by auto.
  unfold ib, o. sep_apply (rtl_bufs_post vd L cp b pos O op n out ow); auto; try lia. fold ib o.
  assert (Eni: zf_ni z' = offset_val (pos + (Zlength inp - zf_ai z')) cp)
    by (rewrite Hni'; unfold ib, rtl_ib; reflexivity).
  assert (Eno: zf_no z' = offset_val (Zlength (out ++ ow)) op)
    by (rewrite Hno'; unfold o, rtl_ob; simpl; f_equal; rewrite Zlength_app; lia).
  assert (HPR: (r = 1 /\ pos + (Zlength inp - zf_ai z') = Zlength O /\ out ++ ow = D) \/
               (r = -5 /\ (4294967295 < Zlength O - pos \/ 4294967295 < n - Zlength out) /\
                P wbits dict D O (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L' /\ swfW (l_s L'))).
  { destruct Hcode as [E|E].
    - left. destruct (Hend E) as [E1 E2]. split; [exact E | split; auto].
    - right. destruct (Hbuf E) as [E1 E2]. rewrite <- HD. unfold RTDIface.umax in E1. split; [exact E | split; [exact E1 | split; auto]]. }
  clear Hcode Hend Hbuf.
  forward.
  unfold trt_cont. Exists r (pos + (Zlength inp - zf_ai z')) (out ++ ow) z' L' (Zlength O - pos) (n - Zlength out).
  change (head_opt (Some L')) with (head_mem L').
  unfold rtl_oc, R_of, Zlib.proof.deflate.DSpec.deflate_globals. rewrite Eni, Eno.
  entailer!.
Qed.
