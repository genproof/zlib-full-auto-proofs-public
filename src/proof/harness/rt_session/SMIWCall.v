(* Law rt_session, main's inflate loop without a header (SMLoopIW.v): position_of(&decompressor, &at), then
   code = inflate(&decompressor, (int) nondet_u32()) and the test if (code == Z_MEM_ERROR) return 0, from the offer
   state OI_w (avail_in = take, avail_out = room) to ICr_w: at holds the position before the call, the call
   consumed some of the bytes offered, wrote some of the data, returned one of the four documented codes with the
   facts SIFacts.si_call gives (SMIWKit.cfacts), and moved next_in and next_out exactly as far as it lowered
   avail_in and avail_out (not Z_OK, the position unchanged, when it was offered neither input nor output space). *)
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
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Facts.
Require Import Zlib.proof.harness.rt_stream.ULoopIPos.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.proof.harness.rt_session.SMIWKit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* a call that did not run out of memory: one of the four documented codes with the facts [cfacts] at the new
   position (pos + bytes consumed) with the new output (out ++ bytes written) and the same flag asked;
   accounted holds of the position recorded before the call; offered neither input nor output space, not Z_OK
   and the stream's position unchanged *)
Lemma call_step_w P PN u O src ip l vd take room flush r z' st' ow :
  ses_ifacts (fun _ => True) P PN -> su_ok u -> with_head u = false -> sc_ok (scase_of u) (su_data u) O ->
  src_ok O src -> isptr ip -> il_ok P u O src ip l -> live_ok (il_L l) ->
  zf_ok (il_z l) -> 0 <= take <= Int.max_unsigned -> il_pos l + take <= Zlength src ->
  0 <= room <= Zlength (su_data u) - Zlength (il_out l) -> room <= Int.max_unsigned -> isptr vd ->
  inflate_rel flush vd
    (zoff (il_z l) (in_ptr (ib_w src ip (il_pos l)) 0) take (out_ptr (ob_w u (il_out l)) 0) room)
    (Some (il_L l)) (ib_w src ip (il_pos l)) (sublist (il_pos l) (il_pos l + take) src)
    (Some (ob_w u (il_out l))) r z' st' ow ->
  (forall L', st' = Some L' -> swfW (l_s L')) ->
  r <> Z_MEM_ERROR ->
  exists l', st' = Some (il_L l') /\ il_z l' = z' /\ il_out l' = il_out l ++ ow /\ il_asked l' = il_asked l /\
    (r = Z_OK \/ r = Z_BUF_ERROR \/ r = Z_STREAM_END \/ r = Z_NEED_DICT) /\
    Zlength (il_out l) + Zlength ow <= Zlength (su_data u) /\
    cfacts P PN u O src ip r l' /\
    (take = 0 -> room = 0 -> r <> Z_OK /\ zpos z' = opos_w ip u (il_pos l) (il_out l) (il_z l) take room) /\
    acc_ok_w src ip u l' (opos_w ip u (il_pos l) (il_out l) (il_z l) take room).
Proof.
  intros PF SU NH SC SO Pip IL LO ZO Ht Hpt Hroom Hroom' Pvd REL Hsw' Hr.
  destruct l as [pos out asked L z]; simpl in *.
  destruct IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  pose proof SU as (_ & _ & _ & _ & _ & _ & _ & Pop & _).
  destruct REL as [(Hbad & _) | (_ & L0 & o0 & res & winp & EL & Eo & Hrun & Hsnx & Er & Eow & Ez & _ & Est)].
  { exfalso. unfold inflate_bad, is_live in Hbad. destruct (eq_dec vd nullval) as [E|_]; [subst; contradiction | ].
    destruct Hbad as [H|[H|[H _]]]; discriminate. }
  injection EL as <-. injection Eo as <-.
  set (inp := sublist pos (pos + take) src) in *.
  assert (Hinp : Zlength inp = take) by (unfold inp; rewrite Zlength_sublist; lia).
  set (zo := zoff z (in_ptr (ib_w src ip pos) 0) take (out_ptr (ob_w u out) 0) room) in *.
  assert (HD : Zlength (su_data u) = Zlength out + Zlength rest) by (rewrite Erest, Zlength_app; lia).
  assert (LC : live_c (scase_of u) L) by (unfold live_c; rewrite (sgh_none u NH); exact LO).
  destruct (si_call _ _ _ PF (scase_of u) (su_data u) O src pos out asked L zo inp flush res winp)
    as [Hm | (Hc & Hsnx' & Hsow & Hao & (rest' & Erest') & HOK & HND & Hend & Hidle)].
  - exact I.
  - exact SC.
  - exact SO.
  - exact HP.
  - exact LC.
  - exact Hsw.
  - unfold zf_ok in *; simpl. pose proof (Zlength_nonneg rest). rep_lia.
  - simpl. rep_lia.
  - rep_lia.
  - lia.
  - lia.
  - rewrite Hinp. reflexivity.
  - exact Hrun.
  - subst r. contradiction.
  - set (m := r_m res) in *.
    set (L' := Live (l_sp L) winp (m_s m) (m_h m) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L)).
    assert (HDl : Zlength (su_data u) = Zlength out + Zlength ow + Zlength rest')
      by (subst ow; rewrite Erest', !Zlength_app; lia).
    pose proof (Zlength_nonneg rest').
    pose proof (run2_inp _ _ _ _ _ Hrun) as Ei0. fold m in Ei0.
    exists (mkIL (pos + m_snx m) (out ++ ow) asked L' z'). simpl.
    split; [exact Est | ]. split; [reflexivity | ]. split; [reflexivity | ]. split; [reflexivity | ].
    split; [subst r; exact Hc | ]. split; [lia | ].
    split; [ | split].
    + assert (Etout : zf_tout z' = m_tout m) by (subst z'; reflexivity).
      unfold cfacts, il_geo; cbn [il_pos il_out il_asked il_L il_z].
      rewrite Etout. subst r.
      split; [ | split; [ | split]].
      * split; [lia | ]. split; [exists rest'; rewrite <- app_assoc; subst ow; exact Erest' | ].
        subst z'. split; [reflexivity | ].
        simpl. f_equal. rewrite Zlength_app. subst ow. fold m. lia.
      * intros E. split; [subst ow; exact (HOK E) | exact (Hsw' L' Est)].
      * intros E. destruct (HND E) as (HZ & HA & HPN). subst ow. auto.
      * intros E. destruct (Hend E) as (E1 & E2 & E3 & _). subst ow. auto.
    + intros Ht0 Hr0.
      destruct (Hidle ltac:(lia) ltac:(unfold zo; simpl; exact Hr0)) as (Hok & Eow0 & Etin & Etout).
      assert (Es0 : m_snx m = 0) by lia.
      split; [subst r; exact Hok | ].
      subst z'. unfold zo, zpos, opos_w, z_after, ib_w, ob_w. fold m. simpl.
      rewrite Etin, Etout, Es0, Hsow, Eow0, Ei0, Hao, Hinp. simpl.
      rewrite !Z.add_0_r, Zlength_nil, !Z.sub_0_r. reflexivity.
    + (* accounted: next_in' + avail_in' = ip + pos + take, next_out' + avail_out' = out + |out| + room *)
      subst z'. unfold acc_ok_w, zpos, opos_w, z_after, ib_w, ob_w, LS.accounted_b. fold m.
      cbn [il_z zf_ni zf_ai zf_no zf_ao in_ptr out_ptr LS.pz_next_in LS.pz_avail_in LS.pz_next_out
           LS.pz_avail_out].
      rewrite Ei0, Hinp, Hao. unfold zo; cbn [zoff zf_ao].
      rewrite !offset_offset.
      pose proof (Zlength_nonneg (m_ow m)).
      rewrite ?Z.add_0_r, ?Z.add_0_l.
      replace (pos + m_snx m + (take - m_snx m)) with (pos + take) by lia.
      replace (Zlength out + m_sow m + (room - m_sow m)) with (Zlength out + room) by lia.
      rewrite !ptr_eqb_refl.
      assert (Hle1 : (take - m_snx m <=? take) = true) by (apply Z.leb_le; lia).
      assert (Hle2 : (room - m_sow m <=? room) = true) by (apply Z.leb_le; lia).
      rewrite Hle1, Hle2. simpl.
      split; [reflexivity | ].
      split; [rewrite isptr_offset_val; exact Pip | ].
      split; [rewrite isptr_offset_val; exact Pop | ].
      exists (pos + take), (Zlength out + room). pose proof (Zlength_nonneg out).
      split; [lia | ]. split; [lia | ]. split; reflexivity.
Qed.

(* position_of(&decompressor, &at): the decompressor's struct lent at laws_session's compspecs *)
Lemma pos_w_ok {Espec : OracleKind} gv vh vg vc va vd u O c src ip pos out asked L z take room :
  su_ok u -> isptr ip -> zf_ok z -> 0 <= take <= Int.max_unsigned -> 0 <= room <= Int.max_unsigned ->
  semax Delta_W
    (OI_w gv vh vg vc va vd [] u O c src ip pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))
    posI_w
    (normal_ret_assert
      (OI_w gv vh vg vc va vd [] u O c src ip pos out asked z L (vi take) (vi room)
         (data_at Tsh t_p (LS.pos_of (opos_w ip u pos out z take room)) va))).
Proof.
  intros SU Pip Zo Ht Hr.
  unfold Delta_W; simplify_func_tycontext.
  unfold posI_w, OI_w, iw_locals, iw_rest, lvs, lv_locals. simpl app.
  pose proof (opos_w_ok ip u pos out z take room Pip SU Zo Ht Hr) as OK.
  rewrite oS_w_session, at_cs.
  forward_call (vd, Tsh, opos_w ip u pos out z take room,
                zrest gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L), va, Tsh).
  all: try solve [auto].
  rewrite <- oS_w_session. entailer!.
Qed.

(* the call and its Z_MEM_ERROR test, from the recorded position *)
Lemma call_mem_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip pos out asked L z take room :
  ses_ifacts (fun _ => True) P PN -> su_ok u -> with_head u = false -> sc_ok (scase_of u) (su_data u) O ->
  Zlength O <= su_cap u -> rbytes O -> src_ok O src -> isptr ip ->
  il_ok P u O src ip (mkIL pos out asked L z) ->
  0 <= take <= Zlength src - pos -> take <= Int.max_unsigned -> zf_ok z -> live_ok L -> isptr vd ->
  0 <= room <= Zlength (su_data u) - Zlength out -> room <= Int.max_unsigned ->
  semax Delta_W
    (OI_w gv vh vg vc va vd [] u O c src ip pos out asked z L (vi take) (vi room)
       (data_at Tsh t_p (LS.pos_of (opos_w ip u pos out z take room)) va))
    (Ssequence callI_w memI_w)
    (overridePost
       (EX r : Z, EX l : ils, ICr_w gv vh vg vc va vd P PN u O c src ip r l (opos_w ip u pos out z take room))
       (RI_w gv vh vg vc va vd P PN u O c src ip)).
Proof.
  intros PF SU NH SC HO BO SO Pip IL Htake Htake' Zo Lo Pvd Hroom Hroom'.
  unfold Delta_W; simplify_func_tycontext.
  pose proof IL as (HP & Hsw & Hpos & (rest & Erest) & Eni & Eno).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  assert (Hout : Zlength out + Zlength rest = Zlength (su_data u)) by (rewrite Erest, Zlength_app; lia).
  pose proof (Zlength_nonneg rest).
  unfold callI_w, memI_w, OI_w, oS_w, RI_w, iw_locals, iw_rest, lvs, lv_locals. simpl app.
  forward_call tt. Intros fl.
  assert (Efl : Int.repr fl = Int.repr (Int.signed (Int.repr fl))) by (rewrite Int.repr_signed; auto).
  rewrite Efl. clear Efl. set (flush := Int.signed (Int.repr fl)).
  assert (Hfl : Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  set (inp := sublist pos (pos + take) src).
  replace (offset_val pos ip) with (in_ptr (ib_w src ip pos) 0)
    by (unfold ib_w; simpl; rewrite Z.add_0_r; reflexivity).
  replace (offset_val (Zlength out) (su_op u)) with (out_ptr (ob_w u out) 0)
    by (unfold ob_w; simpl; rewrite Z.add_0_r; reflexivity).
  sep_apply (offer_fold gv vd z L (in_ptr (ib_w src ip pos) 0) take (out_ptr (ob_w u out) 0) room);
    auto; try rep_lia.
  change (head_mem L) with (head_opt (Some L)).
  replace (head_opt (Some L)) with (head_opt (is_live vd (Some L))) by (rewrite is_live_ptr; auto).
  sep_apply (bufs_pre_w vd L u src ip pos out); auto; try lia.
  unfold Rm, deflate_globals. Intros.
  assert (INOK : in_ok (ib_w src ip pos) inp) by (apply (in_ok_w O); auto; lia).
  assert (OUTOK : out_ok (ob_w u out) room) by (apply out_ok_w; auto; lia).
  forward_call (gv, Tsh, vd, zoff z (in_ptr (ib_w src ip pos) 0) take (out_ptr (ob_w u out) 0) room,
                Vundef, Some L, ib_w src ip pos, inp, Some (ob_w u out), flush, Ers, Ers, true, true).
  { split; [exact INOK | simpl; unfold inp; rewrite Zlength_sublist; lia]. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr : inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hs : match st' with Some _ => _ | None => True end |- _ => rename Hs into Hsw' end.
  forward.
  apply semax_seq_skip.
  forward_if.
  { (* Z_MEM_ERROR: return 0 *)
    forward. Exists (Int.repr 0).
    sep_apply (a_frame_opt gv Tsh vd z' Vundef st'); auto. sep_apply (cstream_frame gv vc (ghp vh u) c).
    sep_apply (hobj_frame vh u). sep_apply (graw_frame vg u).
    sep_apply (data_at_data_at_ Tsh t_p (LS.pos_of (opos_w ip u pos out z take room)) va). entailer!. }
  assert (Hr : r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  destruct (call_step_w P PN u O src ip (mkIL pos out asked L z) vd take room flush r z' st' ow PF SU NH SC SO Pip IL
              ltac:(assumption) ltac:(assumption) ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia) ltac:(lia) Pvd REL
              ltac:(intros L' E; subst st'; exact Hsw') Hr)
    as (l' & Est & Ez & Eout & Eask & Hc & Hlen & CF & Hidle & Hacc).
  cbn [il_pos il_out il_asked il_L il_z] in *.
  subst st' z'.
  rewrite istreamA_opt_ptr, is_live_ptr by auto.
  sep_apply (bufs_post_w vd L u src ip pos out ow); auto.
  rewrite <- Eout. Intros.
  assert (Hok : LS.posz_ok (opos_w ip u pos out z take room)) by (apply opos_w_ok; auto; lia).
  forward.
  unfold ICr_w. Exists r l'. rewrite Eask.
  unfold Rm, deflate_globals, iw_props, iw_locals, iw_rest, lvs, lv_locals. simpl app. entailer!.
  apply derives_refl.
Qed.

Lemma call_w_ok {Espec : OracleKind} P PN gv vh vg vc va vd u O c src ip pos out asked L z take room :
  ses_ifacts (fun _ => True) P PN -> su_ok u -> with_head u = false -> sc_ok (scase_of u) (su_data u) O ->
  Zlength O <= su_cap u -> rbytes O -> src_ok O src -> isptr ip ->
  il_ok P u O src ip (mkIL pos out asked L z) ->
  0 <= take <= Zlength src - pos -> take <= Int.max_unsigned -> zf_ok z -> live_ok L -> isptr vd ->
  0 <= room <= Zlength (su_data u) - Zlength out -> room <= Int.max_unsigned ->
  semax Delta_W
    (OI_w gv vh vg vc va vd [] u O c src ip pos out asked z L (vi take) (vi room) (data_at_ Tsh t_p va))
    (Ssequence (Ssequence posI_w callI_w) memI_w)
    (overridePost
       (EX r : Z, EX l : ils, ICr_w gv vh vg vc va vd P PN u O c src ip r l (opos_w ip u pos out z take room))
       (RI_w gv vh vg vc va vd P PN u O c src ip)).
Proof.
  intros PF SU NH SC HO BO SO Pip IL Htake Htake' Zo Lo Pvd Hroom Hroom'.
  apply seq_assoc.
  eapply semax_seq'.
  - apply pos_w_ok; auto; lia.
  - eapply call_mem_w_ok; eauto.
Qed.
