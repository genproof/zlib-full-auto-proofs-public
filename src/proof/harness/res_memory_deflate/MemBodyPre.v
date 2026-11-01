(* Law res_memory_deflate: one iteration of main's loop up to set_buffer (MemKit.body_pre_stmt): take =
   upto(clip(data_len - read)), room = nondet_u32(), out = malloc(room) (return when NULL), set_buffer(&strm,
   data + read, take, out, room); continued at MemKit.C_at. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.za.deflate.Stmt.
Require Import Zlib.proof.deflate.AnyCalls.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.res_alloc_deflate.ACS.
Require Import Zlib.proof.harness.res_alloc_deflate.Specs.
Require Import Zlib.proof.harness.res_alloc_deflate.Gmain.
Require Import Zlib.proof.harness.res_alloc_deflate.InitFacts.
Require Import Zlib.proof.harness.res_alloc_deflate.StrmKit.
Require Import Zlib.proof.harness.res_alloc_deflate.MainKit.
Require Import Zlib.proof.harness.res_memory_deflate.Peak.
Require Import Zlib.proof.harness.res_memory_deflate.PeakExact.
Require Import Zlib.proof.harness.res_memory_deflate.MainStmt.
Require Import Zlib.proof.harness.res_memory_deflate.MemKit.
Require Zlib.contracts.res_memory_deflate.
Require Import Zlib.harness.res_memory_deflate.code.
Local Open Scope logic.
Local Ltac simplify_remove_localdef_temp ::= mem_simplify_rlt.


Lemma mem_body_pre : body_pre_stmt.
Proof.
  intros Espec K gv cp p dp bs mem W tr spp L AC TE Hk.
  unfold J_at, J_ok, setup_ok, J_loc, J_sep, lbody, Delta_m. Intros.
  abbreviate_semax.
  (* take = upto(clip(data_len - read)) *)
  rewrite <- !seq_assoc. forward_call (Zlength bs - ms_read L).
  forward_call (Z.min (Zlength bs - ms_read L) Int.max_unsigned).
  Intros take.
  forward.
  (* room = nondet_u32() *)
  rewrite <- !seq_assoc. abbreviate_semax. forward_call tt. Intros room. forward.
  rewrite Int.unsigned_repr by rep_lia.
  (* out = malloc(room) *)
  abbreviate_semax. rewrite <- !seq_assoc. forward_call (tarray tuchar room, gv).
  { simpl; rep_lia. }
  Intros out. forward.
  (* if (out == NULL) return 0 *)
  destruct (eq_dec out nullval) as [Eo | No].
  { subst out. forward_if.
    { sep_apply (strm_head_back K gv cp p spp (ms_s L) (ms_read L) (ms_tout L) (ms_msgv L) (ms_adler L) TE).
      sep_apply (count_at_back gv cp tr).
      forward. Exists (Int.repr 0). entailer!. }
    { contradiction. } }
  Intros.
  match goal with |- semax _ ?P _ _ => apply semax_seq with (Q := P) end.
  { forward_if; [ contradiction | ].
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION.
    eapply semax_post; [ | | | | apply semax_skip ]; intros; apply andp_left2;
      unfold overridePost, normal_ret_assert, Rbody, loop1_ret_assert; simpl;
      first [ apply derives_refl | normalize ]. }
  (* set_buffer(&strm, data + read, take, out, room), then the rest of the iteration (the continuation, whose
     postcondition is the whole Rbody: the sequence is split here, before abbreviate_semax narrows the
     postcondition of a statement without return to its normal part) *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION; subst MORE_COMMANDS POSTCONDITION.
  eapply semax_seq; [ | apply (Hk (mkCI take room out)) ].
  eapply semax_post with (R' := normal_ret_assert (C_at K gv cp p dp bs mem W tr spp L (mkCI take room out)));
    [ intros; apply andp_left2; unfold overridePost, normal_ret_assert, Rbody, loop1_ret_assert; simpl;
      first [ apply derives_refl | normalize ] .. | ].
  abbreviate_semax.
  unfold strm_head. Intros nin ain nout aout.
  sep_apply (@dstream_sp_open (kc (mc gv cp)) (ms_s L) p nullval spp gv).
  unfold api_fields. Intros.
  set (dt := vi (tr_data_type (d_tr (ms_s L)))).
  pose proof (@offer_pre (kc (mc gv cp)) p nin (vi ain) (vl (ms_read L)) nout (vi aout) (vl (ms_tout L))
                (ms_msgv L) spp dt (vl (ms_adler L))) as OP.
  unfold reset_fields in OP. sep_apply OP. clear OP.
  abbreviate_semax.
  forward_call (p, Ews, offset_val (ms_read L) dp, take, out, room, nin, vi ain, vl (ms_read L), nout, vi aout,
                vl (ms_tout L), ms_msgv L, spp, @za_alloc (kc (mc gv cp)), @za_free (kc (mc gv cp)),
                @za_opaque (kc (mc gv cp)), dt, vl (ms_adler L), Vundef).
  sep_apply (@offer_post (kc (mc gv cp))).
  sep_apply (wand_frame_elim (@strm_live (kc (mc gv cp)) p spp dt)
                             (@dstream_sp_za (kc (mc gv cp)) 2 (Some (ms_s L)) p nullval spp gv)).
  (* the members back to the live stream with the piece and the output space offered: C_at *)
  unfold C_at, C_ok, J_ok, setup_ok, C_loc, J_loc, C_sep, strm_offered, out_obj, api_fields.
  cbn [ci_take ci_room ci_out].
  entailer!; unfold u32_ok in *; rep_lia.
Qed.
