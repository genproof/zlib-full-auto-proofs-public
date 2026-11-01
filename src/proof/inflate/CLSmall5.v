(* case CODELENS: a code length here.val < 16: DROPBITS(here.bits); state->lens[state->have++] = here.val; (CLKit5.cl_small, cl_small_m) *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CLKit5.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Lemma cl_small_ok : cl_small_stmt.
Proof.
  intros Espec F m here HF W HM HL HE HB HV HH.
  destruct HE as (Eo & Eb & Ev).
  pose proof (mw_bits _ W) as WB. pose proof (mw_hold _ W) as WH. unfold lrange in WH.
  pose proof (sw_lens _ (mw_s _ W)) as [LL LF]. pose proof (sw_have _ (mw_s _ W)) as HV0.
  pose proof (mw_md _ W) as MD.
  destruct (md_codelens _ MD HM) as (_ & HN & HD & _).
  rewrite !loop_state_h_cl. unfold loop_state_clh, cl_sep, ent. abbreviate_semax.
  unfold loop_locals.
  freeze [5;6;7;8;9;10;11;12;13;14;16;17] FR.
  match goal with |- semax _ (PROPx ?P (LOCALx _ (SEPx ?S))) _ _ =>
    apply cl_semax_dowhile0 with (Q := PROPx P (LOCALx (loop_locals F (dropbits (e_bits here) m)) (SEPx S))) end.
  { forward. { entailer!. rep_lia. }
    forward. { entailer!. change (Int.unsigned Int64.iwordsize') with 64. lia. }
    forward. forward.
    unfold loop_locals, dropbits, m_have, m_left. mnorm_goal.
    entailer!. split.
    - rewrite cl_long_shru_eq by rep_lia. reflexivity.
    - rewrite cl_u32_repr. reflexivity. }
  assert (S1: m_s (dropbits (e_bits here) m) = m_s m) by reflexivity.
  unfold loop_locals. abbreviate_semax.
  forward. forward. forward. { entailer!. rep_lia. }
  forward.
  assert (MR: mem_rest_cl F (cl_small_m here m) = mem_rest_cl F m) by reflexivity.
  assert (SR: cl_strm F (cl_small_m here m) = cl_strm F m) by reflexivity.
  rewrite MR, SR. thaw FR.
  unfold cl_small_m, loop_locals, m_have, m_left. mnorm_goal.
  rewrite add_repr. rewrite zero_ext_inrange by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
  rewrite <- upd_Znth_map. entailer!.
Qed.
