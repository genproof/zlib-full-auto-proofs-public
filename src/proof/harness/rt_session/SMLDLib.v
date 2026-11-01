(* Law rt_session (harness/rt_session.c), main's deflate loop (SMKit.loopD): the facts the proofs of its pieces use.

   The loop is rt_stream_trailing's; its facts are rt_stream's (rt_stream/ULoopDLib.v, ULoopDPos.v,
   ULoopDCallLib.v), restated for this law: the compressor here may hold a gzip header (its gzhead pointer [g] is
   SMKit.ghp: &head or Z_NULL), main's objects are SMKit's, and main is at the law's compspecs SCS.CS.
   - the compressor lent to position_of / unmoved / accounted as one z_stream ([cstream_lend_s], from
     ULoopDPos.zs_fields for any gzhead pointer), its six members ([cpos_s]) well typed;
   - the struct position at laws_session's compspecs and at the law's ([at_cs_s], [at_free_s], [at_law_s]);
   - the fields main reads and writes, at deflate.c's compspecs and at the law's; cstream folded back
     ([cstream_fold_s]) and given back to the stack frame at a return ([cstream_frame_s]);
   - the invariant's facts after the draws ([dl_redraw_s]);
   - the header part of the state depends only on the state's gzhead ([hdr_at_gz], [hclose_gz]);
   - main's byte objects as rt_stream's: [tu u] is rt_stream's setup with the same data and objects, and
     SMKit.dobj / cobj are rt_stream's UMainKit.dobj / cobj of [tu u] ([dobj_tu], [cobj_tu]), so the cuts of
     ULoopDCallLib (dobj_split, out_ok_ex) apply; byte objects compare their pointers ([test_eq_s]). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.DCS.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.harness.rt_stream.LawCS.
Require Zlib.proof.harness.rt_stream.UMainKit.
Require Zlib.proof.harness.rt_stream.ULoopDPos.
Require Zlib.proof.harness.rt_stream.ULoopDLib.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SDFacts.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Import Zlib.harness.rt_session.code.
Require Zlib.deflate.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module LS := Zlib.proof.harness.laws_session.Spec.
Module DC := Zlib.deflate.code.
Module UK := Zlib.proof.harness.rt_stream.UMainKit.
Module UP := Zlib.proof.harness.rt_stream.ULoopDPos.

(* the six members of the compressor that position_of records *)
Definition cpos_s (c : cst) : LS.posz :=
  LS.mk_posz (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c).

(** ** The compressor lent as one z_stream *)
Section DCSView.
#[local] Existing Instance Zlib.proof.deflate.DCS.CS.

(* a live compressor between deflate() calls with the gzhead pointer [g], with the complement of Ews and the
   padding (rt_stream's ULoopDPos.dstrm is the case g = Z_NULL) *)
Definition dstrm_g (gv : globals) (p g : val) (s : dstate) (ni : val) (ain tin : Z) (no : val) (aout tout : Z)
    (msgv : val) (adler : Z) : mpred :=
  dstream 2 (Some s) p g gv * api_fields p ni ain tin no aout tout msgv adler *
  data_at_ BoundKit.Ecomp t_strm p * BoundKit.strm_pad p.

Lemma strm_lend_g (gv : globals) (p g : val) (s : dstate) (ni : val) (ain tin : Z) (no : val) (aout tout : Z)
    (msgv : val) (adler : Z) :
  dstrm_g gv p g s ni ain tin no aout tout msgv adler |--
  EX r : LS.zs_rest,
    @data_at LS.CS_session Ews t_zs (LS.zs_of (LS.mk_posz ni ain tin no aout tout) r) p *
    (@data_at LS.CS_session Ews t_zs (LS.zs_of (LS.mk_posz ni ain tin no aout tout) r) p -*
     dstrm_g gv p g s ni ain tin no aout tout msgv adler).
Proof.
  unfold dstrm_g at 1, dstream at 1. Intros p0.
  unfold dstate_at'. simpl Z.eqb. cbv iota.
  unfold dstate_at at 1, trees_at at 1, dtype_at at 1, api_fields at 1. Intros. subst p.
  Exists (msgv, p_s p0, gv DC._zcalloc, gv DC._zcfree, nullval, vi (tr_data_type (fst (d_trm s))), vl adler, Vundef).
  apply (UP.lend_frame _ _ _ (UP.dstrm_rest gv (p_strm p0) s p0)).
  - unfold UP.dstrm_rest, UP.trees_nodt. rewrite UP.zs_fields.
    cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
    unfold field_at_. simpl default_val.
    cancel.
  - unfold UP.dstrm_rest, UP.trees_nodt. rewrite UP.zs_fields.
    cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out LS.pz_avail_out LS.pz_total_out].
    unfold dstrm_g, dstream, api_fields, dstate_at', dstate_at, trees_at, dtype_at. simpl Z.eqb. cbv iota.
    Exists p0. unfold field_at_. simpl default_val. entailer!.
Qed.

End DCSView.

(* SMKit's compressor is such a compressor *)
Lemma cstream_dstrm_s (gv : globals) (vc g : val) (c : cst) :
  cstream gv vc g c =
  dstrm_g gv vc g (cs_s c) (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c) (cs_aout c) (cs_tout c) (cs_msgv c)
    (cs_adler c).
Proof.
  unfold cstream, dstrm_g, srest.
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS SCS.CS CC_dcs BoundKit.Ecomp t_strm)
    by reflexivity.
  apply pred_ext; cancel.
Qed.

Lemma cstream_lend_s (gv : globals) (vc g : val) (c : cst) :
  cstream gv vc g c |--
  EX r : LS.zs_rest,
    @data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s c) r) vc *
    (@data_at LS.CS_session Ews t_zs (LS.zs_of (cpos_s c) r) vc -* cstream gv vc g c).
Proof. rewrite cstream_dstrm_s. apply strm_lend_g. Qed.

(* the six members of the compressor are well typed *)
Lemma cstream_posz_ok_s (gv : globals) (vc g : val) (c : cst) :
  is_pointer_or_null (cs_ni c) -> is_pointer_or_null (cs_no c) ->
  cstream gv vc g c |-- !! LS.posz_ok (cpos_s c).
Proof.
  intros Hi Ho. unfold cstream, api_fields. Intros. apply prop_right.
  unfold LS.posz_ok, cpos_s, u32_ok, u64_ok in *; cbn [LS.pz_next_in LS.pz_avail_in LS.pz_total_in LS.pz_next_out
    LS.pz_avail_out LS.pz_total_out]. repeat split; auto; rep_lia.
Qed.

(** ** main's struct position *)
Lemma at_cs_s (va : val) : @data_at_ SCS.CS Tsh t_p va = @data_at_ LS.CS_session Tsh LS.t_pos va.
Proof. symmetry. apply equal_f. apply (@data_at__change_composite _ _ CC_session). reflexivity. Qed.

Lemma at_free_s (a : LS.posz) (va : val) :
  @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va |-- @data_at_ SCS.CS Tsh t_p va.
Proof. rewrite at_cs_s. apply data_at_data_at_. Qed.

(* at, as position_of wrote it, at the law's compspecs where main reads at.avail_out *)
Lemma at_law_s (a : LS.posz) (va : val) :
  @data_at LS.CS_session Tsh LS.t_pos (LS.pos_of a) va = @data_at SCS.CS Tsh t_p (LS.pos_of a) va.
Proof. apply equal_f. apply (@data_at_change_composite _ _ CC_session); [apply JMeq_refl | reflexivity]. Qed.

(** ** The fields of the compressor main reads and writes *)
Lemma next_in_s (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_in) v p = @field_at SCS.CS Ews t_z (DOT _next_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma avail_in_s (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_in) v p = @field_at SCS.CS Ews t_z (DOT _avail_in) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma next_out_s (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._next_out) v p = @field_at SCS.CS Ews t_z (DOT _next_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Lemma avail_out_s (v : val) (p : val) :
  @field_at Zlib.proof.deflate.DCS.CS Ews t_strm (DOT DC._avail_out) v p =
  @field_at SCS.CS Ews t_z (DOT _avail_out) v p.
Proof. apply equal_f. apply (@field_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity]. Qed.

Section DCSView2.
#[local] Existing Instance Zlib.proof.deflate.DCS.CS.

(* the compressor's fields, as main read them, back into cstream *)
Lemma cstream_fold_s gv vc g s ni ain tin no aout tout msgv adler :
  u32_ok ain -> u64_ok tin -> u32_ok aout -> u64_ok tout -> u64_ok adler ->
  dstream 2 (Some s) vc g gv * field_at Ews t_strm (DOT DC._next_in) ni vc *
  field_at Ews t_strm (DOT DC._avail_in) (vi ain) vc * field_at Ews t_strm (DOT DC._total_in) (vl tin) vc *
  field_at Ews t_strm (DOT DC._next_out) no vc * field_at Ews t_strm (DOT DC._avail_out) (vi aout) vc *
  field_at Ews t_strm (DOT DC._total_out) (vl tout) vc * field_at Ews t_strm (DOT DC._msg) msgv vc *
  field_at Ews t_strm (DOT DC._adler) (vl adler) vc * srest vc
  |-- cstream gv vc g (mkCS s ni ain tin no aout tout msgv adler).
Proof. intros. unfold cstream, api_fields. simpl. entailer!. Qed.

End DCSView2.

(* at a return: the compressor's struct back to the stack frame *)
Lemma cstream_frame_s gv vc g c : cstream gv vc g c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc g gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS SCS.CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(** ** The invariant after the draws *)
(* the draws of offered and flush when flush was not Z_FINISH: the invariant's facts hold for the new values
   (fin is None, since a Z_FINISH would have stayed); Z_FINISH comes only with all the data offered and a rest
   that one call can take *)
Lemma dl_redraw_s J u l off fl :
  dl_ok J u l -> dl_flush l <> Z_FINISH -> dl_off l <= off <= Zlength (su_data u) -> 0 <= fl <= 5 ->
  (fl = Z_FINISH -> off = Zlength (su_data u) /\ Zlength (su_data u) - Zlength (dl_D l) <= 4294967295) ->
  dl_ok J u (mkDL (dl_D l) (dl_O l) (dl_fin l) off fl (dl_msg l) (dl_c l)).
Proof.
  intros (HJ & ED & HDoff & Hfl & Hfin4 & Hfin & HO & BO & Hmsg & Eni & Eno) Hnf Hoff Hfl' Hfin4'.
  unfold dl_ok; cbn [dl_D dl_O dl_fin dl_off dl_flush dl_msg dl_c].
  repeat split; auto; try lia;
    match goal with
    | E : dl_fin l = Some ?R |- _ => destruct (Hfin R E); contradiction
    | E : fl = _ |- _ => destruct (Hfin4' E); auto
    end.
Qed.

(** ** The header part of the state *)
Lemma hdr_at_gz (s s' : dstate) (g : val) (hx : share * val * val * val) :
  d_gzhead s' = d_gzhead s -> hdr_at (Some s') g hx = hdr_at (Some s) g hx.
Proof. intros E. unfold hdr_at. rewrite E. reflexivity. Qed.

Lemma hclose_gz (vh : val) (u : setup) (s s' : dstate) (hx : share * val * val * val) (Hr : mpred) :
  d_gzhead s' = d_gzhead s -> hclose vh u s hx Hr -> hclose vh u s' hx Hr.
Proof. intros E H s'' E'. apply H. congruence. Qed.

(* the gzhead of the state between the calls is the session's header *)
Lemma dl_gzhead (J : ses_dinv) (u : setup) (l : dls) :
  ses_dfacts J -> dl_ok J u l -> d_gzhead (cs_s (dl_c l)) = sgh u.
Proof. intros JF (HJ & _). destruct (sd_range J JF _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & E). exact E. Qed.

(** ** main's byte objects as rt_stream's *)
(* rt_stream's setup with this one's parameters, data and objects data, expected, compressed and out *)
Definition tu (u : setup) : UK.setup :=
  UK.mkSU (su_level u) (su_wbits u) (su_mem u) (su_strategy u) (su_data u) (su_cap u)
    (su_dp u) (su_ep u) (su_cp u) (su_op u).

Lemma tok_s sh n (q : val) :
  @malloc_token SCS.CS sh (tarray tuchar n) q =
  @malloc_token Zlib.proof.harness.rt_stream.LawCS.CS sh (tarray tuchar n) q.
Proof.
  transitivity (@malloc_token Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) q).
  - symmetry. apply equal_f. apply (@malloc_token_change_composite _ _ CC_dcs). reflexivity.
  - apply equal_f. apply (@malloc_token_change_composite _ _ Zlib.proof.harness.rt_stream.LawCS.CC_dcs).
    reflexivity.
Qed.

Lemma bytes_s sh n (v : list val) (q : val) :
  @data_at SCS.CS sh (tarray tuchar n) v q = @data_at Zlib.proof.harness.rt_stream.LawCS.CS sh (tarray tuchar n) v q.
Proof.
  transitivity (@data_at Zlib.proof.deflate.DCS.CS sh (tarray tuchar n) v q).
  - symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
  - apply equal_f. apply (@data_at_change_composite _ _ Zlib.proof.harness.rt_stream.LawCS.CC_dcs);
      [apply JMeq_refl | reflexivity].
Qed.

Lemma dobj_tu (u : setup) : dobj u = UK.dobj (tu u).
Proof.
  unfold dobj, datobj, eobj, bobj, UK.dobj, UK.eobj, tu; cbn [UK.su_data UK.su_dp UK.su_ep].
  rewrite !tok_s, !bytes_s. reflexivity.
Qed.

Lemma cobj_tu (u : setup) (O : list Z) : cobj u O = UK.cobj (tu u) O.
Proof.
  unfold cobj, UK.cobj, cbytes, UK.cbytes, tu; cbn [UK.su_cap UK.su_cp].
  rewrite tok_s, bytes_s. reflexivity.
Qed.

(* two pointers into or one past a malloc'ed byte object are weakly valid, so comparing them is defined *)
Lemma test_eq_s (R : mpred) (p : val) (lo1 lo2 n : Z) (contents : list val) :
  0 <= lo1 <= n -> 0 <= lo2 <= n -> isptr p ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
  |-- denote_tc_test_eq (offset_val lo1 p) (offset_val lo2 p).
Proof.
  intros. rewrite tok_s, bytes_s. apply Zlib.proof.harness.rt_stream.ULoopDLib.ld_test_eq; auto.
Qed.
