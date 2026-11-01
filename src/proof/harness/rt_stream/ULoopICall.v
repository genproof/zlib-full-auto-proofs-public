(* Law rt_stream (data of any length), main's inflate loop: position_of(&decompressor, &at), then
   code = inflate(&decompressor, (int) nondet_u32()) and the test if (code == Z_MEM_ERROR) return 0, from the offer
   state OI (avail_in = take, avail_out = room) to ICr: at holds the position before the call, the call consumed
   some of the bytes offered, wrote some of the data, and returned a documented code (not Z_OK, the position
   unchanged, when it was offered neither input nor output space). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.rt_stream.UIFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.harness.rt_stream.code.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_stream.ULoopIKit.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

(* position_of(&decompressor, &at): the decompressor's struct lent at laws_session's compspecs *)
Lemma pos_ok {Espec : OracleKind} gv vc vd va u O c pos out L z take room :
  su_ok u -> zf_ok z -> 0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  semax Delta_m
    (OI [] gv vc vd va u O c pos out z L (vi take) (vi room) (data_at_ Tsh t_p va))
    posI
    (normal_ret_assert
      (OI [] gv vc vd va u O c pos out z L (vi take) (vi room)
         (@data_at LawCS.CS Tsh t_p (LS.pos_of (opos u pos out z take room)) va))).
Proof.
  intros SU Zo Ht Hr.
  unfold Delta_m; simplify_func_tycontext.
  unfold posI, OI, su_locals, lv_locals. simpl app.
  pose proof (opos_ok u pos out z take room SU Zo Ht Hr) as OK.
  pose proof OK as (Hni & Hno & _).
  rewrite oS_session, at_cs.
  forward_call (vd, Tsh, opos u pos out z take room,
                zrest gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L), va, Tsh).
  all: try solve [auto].
  rewrite <- oS_session, <- at_pos_cs. entailer!.
Qed.

Lemma call_mem_ok {Espec : OracleKind} P gv vc vd va u O c pos out L z take room :
  urts_ifacts P -> su_ok u -> Zlength O <= su_cap u -> Zlib.proof.roundtrip.RTDIface.rbytes O ->
  il_ok P u O (mkIL pos out L z) ->
  0 <= take <= Zlength O - pos -> take <= Int.max_unsigned -> zf_ok z -> live_ok L -> isptr vd ->
  0 <= room <= Zlength (su_data u) - Zlength out -> room <= Int.max_unsigned ->
  semax Delta_m
    (OI [] gv vc vd va u O c pos out z L (vi take) (vi room)
       (@data_at LawCS.CS Tsh t_p (LS.pos_of (opos u pos out z take room)) va))
    (Ssequence callI memI)
    (overridePost (EX r : Z, EX l : ils, ICr gv vc vd va P u O c r l (opos u pos out z take room))
       (RI gv vc vd va P u O c)).
Proof.
  intros PF SU HO BO IL Htake Htake' Zo Lo Pvd Hroom Hroom'.
  unfold Delta_m; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  pose proof SU as (_ & _ & _ & _ & Hn & _ & Hcap & Pdp & Pcp & Pop).
  cbn [il_pos il_out il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold callI, memI, OI, oS, RI, su_locals, lv_locals. simpl app.
  forward_call tt. Intros fl.
  assert (Efl : Int.repr fl = Int.repr (Int.signed (Int.repr fl))) by (rewrite Int.repr_signed; auto).
  rewrite Efl. clear Efl. set (flush := Int.signed (Int.repr fl)).
  assert (Hfl : Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (inp := sublist pos (pos + take) O).
  replace (offset_val pos (su_cp u)) with (in_ptr (ib_of u O pos) 0)
    by (unfold ib_of; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) (su_op u)) with (out_ptr (ob_of u out) 0)
    by (unfold ob_of; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (offer_fold gv vd z L (in_ptr (ib_of u O pos) 0) take (out_ptr (ob_of u out) 0) room); auto; try rep_lia.
  replace (head_opt (Some L)) with (head_opt (is_live vd (Some L))) by (rewrite is_live_ptr; auto).
  sep_apply (bufs_pre vd L u O pos out); auto; try lia.
  unfold Rm, deflate_globals. Intros.
  assert (INOK : in_ok (ib_of u O pos) inp) by (apply in_ok_of; auto; lia).
  assert (OUTOK : out_ok (ob_of u out) room) by (apply out_ok_of; auto; lia).
  forward_call (gv, Tsh, vd, zoff z (in_ptr (ib_of u O pos) 0) take (out_ptr (ob_of u out) 0) room, Vundef,
                Some L, ib_of u O pos, inp, Some (ob_of u out), flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; unfold inp; rewrite Zlength_sublist; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr : inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hs : match st' with Some _ => _ | None => True end |- _ => rename Hs into Hsw' end.
  forward.
  apply semax_seq_skip.
  forward_if.
  { (* Z_MEM_ERROR: return 0 *)
    forward. Exists (Int.repr 0).
    sep_apply (a_frame_opt gv Tsh vd z' Vundef st'); auto. sep_apply (cstream_frame gv vc c).
    sep_apply (@data_at_data_at_ LawCS.CS Tsh t_p (LS.pos_of (opos u pos out z take room)) va). entailer!. }
  assert (Hr : r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  destruct (call_step P u O (mkIL pos out L z) vd take room flush r z' st' ow PF SU ltac:(assumption) IL
              ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia) ltac:(lia) Pvd REL
              ltac:(intros L' E; subst st'; exact Hsw') Hr)
    as (l' & Est & Ez & Eout & Hc & Hlen & IL' & Hend & Hidle).
  cbn [il_pos il_out il_L il_z] in *.
  subst st' z'.
  rewrite istreamA_opt_ptr, is_live_ptr by auto.
  sep_apply (bufs_post vd L u O pos out ow); auto.
  rewrite <- Eout. Intros.
  assert (Hok : LS.posz_ok (opos u pos out z take room)) by (apply opos_ok; auto; lia).
  forward.
  unfold ICr. Exists r l'. unfold Rm, deflate_globals, su_locals, lv_locals. simpl app. entailer!.
Qed.
