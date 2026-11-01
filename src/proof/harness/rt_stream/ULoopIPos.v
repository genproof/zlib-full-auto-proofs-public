(* Law rt_stream: a live decompressor and laws_session.h's position_of and unmoved.

   inflate()'s shared specification (inflate_api/SpecW.v) holds a live z_stream as [istreamA]: one [data_at] of
   struct z_stream_s at the inflate unit's compspecs, and the memory behind strm->state.  position_of and unmoved
   take the struct as one [data_at] at laws_session's compspecs (laws_session/Spec.v, CS_session), its six
   members recorded by a position given as a [posz].  [istreamA_session] is that conversion, for any stream
   between inflate() calls; [zpos z] are the six members of the model's fields [z].  The law's harness drives
   inflate() as rt_stream_trailing's and rt_session's do (position_of before the call, unmoved after it), so these
   lemmas are stated for any live decompressor.

   [run2_inp]: one inflate() call of the model keeps its input (strm->avail_in after the call is the input offered
   minus the bytes consumed), whatever the mode of the state it starts in. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Zlib.proof.harness.laws_session.Spec.
Require Zlib.proof.uncompr.URunFrame.
Local Open Scope logic.
Module LS := Zlib.proof.harness.laws_session.Spec.

#[local] Instance CC_is : change_composite_env LS.CS_session Zlib.units.Inflate.CS.
  make_cs_preserve LS.CS_session Zlib.units.Inflate.CS. Defined.

(* the six members a position records, of a stream with the model's fields z *)
Definition zpos (z : zfields) : LS.posz :=
  LS.mk_posz (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z).

(* the eight other members: msg, state (sp), zalloc, zfree, opaque, data_type, adler (adv), reserved *)
Definition zrest (gv : globals) (z : zfields) (adv sp : val) : LS.zs_rest :=
  (msg_val gv (zf_msg z), sp, gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval,
   Vint (Int.repr (zf_dt z)), adv, zf_res z).

Lemma zstrm_atA_session gv shs p z adv sp :
  zstrm_atA gv shs p z adv sp = @data_at LS.CS_session shs t_zs (LS.zs_of (zpos z) (zrest gv z adv sp)) p.
Proof.
  unfold zstrm_atA. symmetry. apply equal_f.
  apply (@data_at_change_composite _ _ CC_is); [apply JMeq_refl | reflexivity].
Qed.

Lemma istreamA_session gv shs p z av L :
  istreamA gv shs p z av (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at LS.CS_session shs t_zs (LS.zs_of (zpos z) (zrest gv z (adler_v (raw_live (Some L)) z av) (l_sp L))) p *
   state_mem gv p L).
Proof.
  unfold istreamA. rewrite zstrm_atA_session. apply pred_ext; entailer!.
Qed.

(* the members are well typed when the fields are in range and the two pointers are pointers or null *)
Lemma zpos_ok z :
  zf_ok z -> is_pointer_or_null (zf_ni z) -> is_pointer_or_null (zf_no z) -> LS.posz_ok (zpos z).
Proof.
  intros Z Hi Ho. unfold zf_ok, LS.posz_ok, zpos in *; simpl. intuition.
Qed.

(* one inflate() call of the model keeps its input *)
Lemma run2_inp flush z L inp res :
  Zlib.proof.inflate.Model2.run2 flush lenfix_list distfix_list (m_init z L inp) res -> m_inp (r_m res) = inp.
Proof.
  intros Hrun.
  set (m0 := m_init z L inp) in *.
  assert (Ei : m_inp m0 = inp) by reflexivity. clearbody m0.
  destruct (Z_le_dec HEAD (i_mode (m_s m0))) as [H1 | H1];
    [destruct (Z_le_dec (i_mode (m_s m0)) BAD) as [H2 | H2] | ].
  - destruct (Zlib.proof.uncompr.URunFrame.run2_frame _ _ _ _ _ (conj H1 H2) Hrun) as (E & _).
    rewrite E. exact Ei.
  - (* a mode after BAD (MEM, SYNC, ...): the call returns at once *)
    assert (E : exists r, Zlib.proof.inflate.Model2.stepf2 flush lenfix_list distfix_list m0 = IRet r m0).
    { unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, m_mode. cbv zeta.
      set (md := i_mode (m_s m0)) in *. clearbody md.
      unfold HEAD, BAD in *.
      repeat match goal with |- context [if md =? ?X then _ else _] =>
        let E := fresh "E" in destruct (Z.eqb_spec md X) as [E | E];
        [ exfalso; rewrite E in H2; cbv in H2; apply H2; discriminate | ] end;
      destruct (md =? MEM); eexists; reflexivity. }
    destruct E as (r & E). destruct Hrun as (o & Hl & Hr).
    inversion Hl as [m r' m' Es | m m' Es | m m' o' Es]; subst; rewrite E in Es; try discriminate Es.
    injection Es as <- <-. subst res. reflexivity.
  - (* a mode before HEAD: the call returns at once *)
    assert (E : exists r, Zlib.proof.inflate.Model2.stepf2 flush lenfix_list distfix_list m0 = IRet r m0).
    { unfold Zlib.proof.inflate.Model2.stepf2, Zlib.proof.inflate.Model2.step2, m_mode. cbv zeta.
      set (md := i_mode (m_s m0)) in *. clearbody md.
      unfold HEAD in *.
      repeat match goal with |- context [if md =? ?X then _ else _] =>
        let E := fresh "E" in destruct (Z.eqb_spec md X) as [E | E];
        [ exfalso; rewrite E in H1; cbv in H1; apply H1; discriminate | ] end;
      destruct (md =? MEM); eexists; reflexivity. }
    destruct E as (r & E). destruct Hrun as (o & Hl & Hr).
    inversion Hl as [m r' m' Es | m m' Es | m m' o' Es]; subst; rewrite E in Es; try discriminate Es.
    injection Es as <- <-. subst res. reflexivity.
Qed.
