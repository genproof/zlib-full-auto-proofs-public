(* Law rt_session, main's inflate loop with a header (SMLoopI9.v): position_of(&decompressor, &at), then
   code = inflate(&decompressor, (int) nondet_u32()) (RTH9Spec.inflate_spec9) and the test
   if (code == Z_MEM_ERROR) return 0, from the offer state OI9 (avail_in = take, avail_out = room) to ICr9: at holds
   the position before the call, the call consumed some of the bytes offered, wrote some of the data, returned
   Z_OK, Z_BUF_ERROR or Z_STREAM_END (SLI9Kit.call_step9), and moved next_in and next_out exactly as far as it
   lowered avail_in and avail_out. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Zlib.proof.harness.rt_stream.ULoopIKit.
Require Import Zlib.proof.harness.rt_session.SLI9Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.
Module R8 := Zlib.proof.roundtrip.RTH8Spec.
Module R9 := Zlib.proof.roundtrip.RTH9Spec.
Module UK := Zlib.proof.harness.rt_stream.ULoopIKit.

(* position_of(&decompressor, &at): the decompressor's struct lent at laws_session's compspecs *)
Lemma pos9_ok {Espec : OracleKind} gv vh vg vc va vd u O c src ip pos out asked L z take room :
  su_ok u -> isptr ip -> zf_ok z -> 0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  semax Delta_9
    (OI9 gv vh vg vc va vd u O c src ip [] pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))
    posI9
    (normal_ret_assert
      (OI9 gv vh vg vc va vd u O c src ip [] pos out asked z L (vi take) (vi room)
         (data_at Tsh t_p (LS.pos_of (opos9 ip u pos out z take room)) va))).
Proof.
  intros SU Pip Zo Ht Hr.
  unfold Delta_9; simplify_func_tycontext.
  unfold posI9, OI9, i9_locals, lvs, lv_locals. simpl app.
  pose proof (opos9_ok ip u pos out z take room Pip SU Zo Ht Hr) as OK.
  rewrite oS9_session, at_cs9.
  forward_call (vd, Tsh, opos9 ip u pos out z take room, zrest gv z (vl (zf_adler z)) (l_sp L), va, Tsh).
  all: try solve [auto].
  rewrite <- oS9_session. entailer!.
Qed.

(* got, whatever inflate() returned (Z_MEM_ERROR included), back to the stack frame: the stream keeps the
   gz_header pointer and its share *)
Lemma head_frame9 flush vd z L ib inp o r z' st' ow u vg :
  isptr vd -> inflate_rel flush vd z (Some L) ib inp (Some o) r z' st' ow -> got_at u vg L ->
  R9.head_opt9 (is_live vd st') |-- data_at_ Tsh t_g vg * TT.
Proof.
  intros Pvd REL (Ehp & Ehs & _).
  rewrite is_live_ptr9 by exact Pvd.
  destruct REL as [(_ & _ & _ & -> & _) | (_ & L0 & o0 & res & winp & EL & _ & _ & _ & _ & _ & _ & _ & ->)].
  - apply head_mem9_frame; assumption.
  - injection EL as <-. apply head_mem9_frame; assumption.
Qed.

(* the call and its Z_MEM_ERROR test *)
Lemma call_mem9_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip pos out asked L z take room :
  ses_ifacts (fun _ => True) P PN -> su_ok u -> with_head u = true -> sc_ok (scase_of u) (su_data u) O ->
  Zlength O <= su_cap u -> rbytes O -> SIFacts.src_ok O src -> isptr ip ->
  il_ok P u O src ip (mkIL pos out asked L z) -> got_at u vg L ->
  0 <= take <= Zlength src - pos -> take <= Int.max_unsigned -> zf_ok z -> R8.live_ok8 L -> isptr vd ->
  0 <= room <= Zlength (su_data u) - Zlength out -> room <= Int.max_unsigned ->
  semax Delta_9
    (OI9 gv vh vg vc va vd u O c src ip [] pos out asked z L (vi take) (vi room)
       (data_at Tsh t_p (LS.pos_of (opos9 ip u pos out z take room)) va))
    (Ssequence callI9 memI9)
    (overridePost (EX r : Z, EX l : ils, ICr9 gv vh vg vc va vd P u O c src ip r l (opos9 ip u pos out z take room))
       (RI9 gv vh vg vc va vd P u O c src ip)).
Proof.
  intros PF SU HH SC HO BO SO Pip IL GA Htake Htake' Zo Lo Pvd Hroom Hroom'.
  unfold Delta_9; simplify_func_tycontext.
  abbreviate_semax.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold callI9, memI9, OI9, oS9, RI9, i9_locals, lvs, lv_locals. simpl app.
  forward_call tt. Intros fl.
  assert (Efl : Int.repr fl = Int.repr (Int.signed (Int.repr fl))) by (rewrite Int.repr_signed; auto).
  rewrite Efl. clear Efl. set (flush := Int.signed (Int.repr fl)).
  assert (Hfl : Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (inp := sublist pos (pos + take) src).
  replace (offset_val pos ip) with (in_ptr (ib9 src ip pos) 0)
    by (unfold ib9; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) (su_op u)) with (out_ptr (ob9 u out) 0)
    by (unfold ob9; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (offer_fold9 gv vd z L (in_ptr (ib9 src ip pos) 0) take (out_ptr (ob9 u out) 0) room);
    auto; try rep_lia.
  replace (R9.head_mem9 L) with (R9.head_opt9 (is_live vd (Some L))) by (rewrite is_live_ptr9; auto).
  sep_apply (bufs_pre9 vd L u src ip pos out); auto; try lia.
  unfold Rm, deflate_globals. Intros.
  assert (INOK : in_ok (ib9 src ip pos) inp) by (apply (in_ok9 O); auto; lia).
  assert (OUTOK : out_ok (ob9 u out) room) by (apply out_ok9; auto; lia).
  assert (HD9 : R9.hd9_ok (Some L)).
  { split; [ | exact Hsw]. rewrite (si_shape _ _ _ PF _ _ _ _ _ _ _ _ _ I HP). cbn. rewrite sgh_head by exact HH.
    reflexivity. }
  forward_call (gv, Tsh, vd, zoff9 z (in_ptr (ib9 src ip pos) 0) take (out_ptr (ob9 u out) 0) room,
                Some L, ib9 src ip pos, inp, Some (ob9 u out), flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; unfold inp; rewrite Zlength_sublist; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr : inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hd : R9.hd9_ok st' |- _ => rename Hd into HD9' end.
  forward.
  unfold memI9.
  forward_if.
  { (* Z_MEM_ERROR: return 0 *)
    forward. Exists (Int.repr 0).
    sep_apply (head_frame9 flush vd _ L (ib9 src ip pos) inp (ob9 u out) r z' st' ow u vg Pvd REL GA).
    sep_apply (istream8_frame gv Tsh vd z' st' Pvd). sep_apply (cstream_frame9 gv vc (ghp vh u) c).
    sep_apply (data_at_data_at_ Tsh t_p (LS.pos_of (opos9 ip u pos out z take room)) va).
    unfold hobj. sep_apply (data_at_data_at_ Tsh t_g (hvals u) vh).
    entailer!. }
  assert (Hr : r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  destruct (call_step9 P PN u O src ip (mkIL pos out asked L z) vd take room flush r z' st' ow PF SU HH SC SO Pip IL
              Lo Zo ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia) ltac:(lia) Pvd REL
              ltac:(intros L' E; subst st'; exact (proj2 HD9')) Hr)
    as (l' & Est & Ez & Eout & Eask & Ehp & Ehs & Exb & Enb & Ecb & Hc & Hlen & Hmem & Hok & Hend & Hidle & Hacc).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  subst st' z'.
  rewrite istream8_opt_ptr, is_live_ptr9 by auto.
  sep_apply (bufs_post9 vd L u src ip pos out ow); auto.
  rewrite <- Eout. Intros.
  assert (GA' : got_at u vg (il_L l')).
  { destruct GA as (G1 & G2 & G3 & G4 & G5). unfold got_at. rewrite Ehp, Ehs, Exb, Enb, Ecb. auto. }
  assert (Hpok : LS.posz_ok (opos9 ip u pos out z take room)) by (apply opos9_ok; auto; lia).
  forward.
  unfold ICr9. Exists r l'. unfold Rm, deflate_globals, i9_locals, lvs, lv_locals. simpl app. rewrite Eask.
  entailer!. apply derives_refl.
Qed.
