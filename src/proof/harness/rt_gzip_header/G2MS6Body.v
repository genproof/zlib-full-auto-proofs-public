(* Law rt_gzip_header on the round-2 harness, main's body, segment 6: the body of the inflate loop
   (G2MS6Kit.g6_body_stmt): avail_in = clip(compressed_len - (next_in - compressed)), code = inflate(&decompressor,
   Z_FINISH), `if (code == Z_MEM_ERROR) return 0`.  From the invariant g6_inv (the theory's P at position pos) to
   g6_cont (G2IFacts.gi_call: P at the new position while Z_BUF_ERROR leaves input, the header complete when the
   loop ends); on Z_MEM_ERROR main returns with its locals' memory. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2DFacts.
Require Import Zlib.proof.roundtrip.RTH9Spec.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Import Zlib.proof.harness.rt_gzip_header.G2MS6Kit.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_compressed against _compressed_len); each identifier comparison is decided by vm_compute. *)
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

Lemma g6_body_ok : g6_body_stmt.
Proof.
  intros Espec P gv vh vg vc vd vr g b cbp O X Y PF Pvd Pvr.
  unfold g6_body, POST_m, Delta_m. simplify_func_tycontext.
  abbreviate_semax.
  unfold g6_inv. Intros pos z0 L0.
  match goal with G : g6_glob _ _ _ _, HL : g6_live _ _ _ _ _ _ _ _ |- _ =>
    pose proof G as G0; destruct G as (Gok & DF & BO & Hb & Pc & Opos');
    destruct HL as (Zo & Lo & Sw & Hh & Eni0 & Eno0 & Eao0 & Ehp & Ehs & Exb & Enb & Ecb & Hpos) end.
  unfold g6_sep, g6_locals, gp_locals, gs_locals, lv_locals, g6_tup. cbn [app].
  rewrite Eni0.
  forward.
  forward_call (Zlength O - pos).
  { entailer!. apply g6_sameblock; auto. }
  { entailer!. try rewrite Eni0. unfold vl. rewrite g6_ptr_sub by (auto; unfold max_u64 in *; rep_lia). reflexivity. }
  { unfold max_u64 in *; rep_lia. }
  forward.
  rewrite <- Eni0.
  set (ai := Z.min (Zlength O - pos) Int.max_unsigned) in *.
  assert (Hai : 0 <= ai <= Int.max_unsigned) by (unfold ai; rep_lia).
  sep_apply (g6_fold gv vd z0 L0 ai Pvd Zo Lo Hai).
  rewrite Eni0, Eno0, Eao0.
  sep_apply (g6_bufs_pre L0 cbp b pos O vr).
  rewrite g6_r_split.
  set (inp := sublist pos (pos + clipz (Zlength O - pos)) O).
  assert (Hinp : Zlength inp = ai) by (unfold inp, ai, clipz, umax; rewrite Zlength_sublist; rep_lia).
  assert (INOK : in_ok (g6_ib cbp b pos O) inp) by (apply g6_in_ok; auto).
  (* code = inflate(&decompressor, Z_FINISH) *)
  forward_call (gv, Tsh, vd, GI.offer_z z0 (offset_val pos cbp) ai vr 1, Some L0, g6_ib cbp b pos O, inp,
                Some (g6_ob vr), 4, Ers, Ers, true, false).
  { rewrite g6_live_ptr by auto. simpl head_opt9. unfold ifz. cancel. }
  { split; [unfold out_tok_ok, g6_ob; intros; lia | ].
    split; [unfold g6_ib, in_ptr; cbn; rewrite Z.add_0_r; reflexivity | ].
    split; [split; [exact INOK | cbn; lia] | ].
    split; [split; [unfold g6_ob, out_ptr; cbn; rewrite isptr_offset_val_zero by auto; reflexivity
                   | exact (g6_out_ok vr Pvr)] | ].
    exact (conj Hh Sw). }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with Hr : S5.inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename Hr into REL end.
  match goal with Hd : hd9_ok _ |- _ => rename Hd into HD9 end.
  assert (NIB : g6_ib cbp b pos O <> InNull) by discriminate.
  destruct (g6_rel_keep _ _ _ _ _ _ _ _ _ _ _ Pvd NIB REL) as (L1 & -> & K1 & K2 & K3 & K4 & K5 & Rr).
  destruct HD9 as [Hh1 Sw1].
  rewrite g6_opt_ptr, !g6_live_ptr by auto. simpl head_opt9.
  rewrite g6_open. Intros.
  sep_apply (g6_bufs_post L0 cbp b pos O vr ow). Intros.
  forward_if.
  { (* Z_MEM_ERROR: return 0, main's locals back *)
    forward. Exists (Int.repr 0).
    apply andp_right; [apply prop_right; reflexivity | ].
    sep_apply (g6_head_ret L1 (S5.l_headp L1) eq_refl (eq_trans K2 Ehs)). rewrite K1.
    sep_apply (g6_strm_ret gv vd z' (S5.l_sp L1) L1).
    sep_apply (data_at_data_at_ Tsh t_g (hvals g) vh).
    cancel. }
  (* another code: the theory's step (G2IFacts.gi_call) *)
  assert (Hr : r <> Z_MEM_ERROR)
    by (intro E; subst r; match goal with Hn : _ <> _ |- _ => solve [apply Hn; reflexivity] end).
  assert (CP : GI.g2_call_pre O pos z0 L0 vd (g6_ib cbp b pos O) inp (g6_ob vr) 1).
  { unfold GI.g2_call_pre.
    refine (conj Lo (conj Sw (conj Zo (conj _ (conj NIB (conj INOK (conj (g6_out_ok vr Pvr) (conj _ (conj _ _))))))))).
    - destruct vd; try contradiction; discriminate.
    - unfold umax; lia.
    - rewrite Hinp; unfold ai, clipz, umax; rep_lia.
    - rewrite Hinp. unfold inp, ai, clipz, umax. f_equal; rep_lia. }
  assert (Ez1 : GI.offer_z z0 (offset_val pos cbp) ai vr 1 =
                GI.offer_z z0 (in_ptr (g6_ib cbp b pos O) 0) (Zlength inp) (out_ptr (g6_ob vr) 0) 1).
  { rewrite Hinp. unfold g6_ib, g6_ob, in_ptr, out_ptr. rewrite !Z.add_0_r, isptr_offset_val_zero by auto.
    reflexivity. }
  rewrite Ez1 in REL.
  match goal with HP : P _ _ _ _ _ _ _ |- _ =>
    destruct (GI.gi_call P PF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP CP REL Hr)
      as (L2 & E2 & Hai' & Hni' & Hao' & Hno' & How & Hcont & Hend) end.
  injection E2 as E2. subst L2.
  repeat match goal with Hc : S5.zf_ok z' /\ live_ok8 L1 |- _ => destruct Hc end.
  assert (LV1 : g6_live vg vr g cbp O (pos + (Zlength inp - AM.zf_ai z')) z' L1).
  { unfold g6_live.
    split; [assumption | ]. split; [assumption | ]. split; [exact Sw1 | ]. split; [exact Hh1 | ].
    split; [rewrite Hni'; unfold g6_ib, in_ptr; reflexivity | ].
    split; [rewrite Hno'; unfold g6_ob, out_ptr; cbn; apply isptr_offset_val_zero; auto | ].
    split; [exact Hao' | ].
    split; [congruence | ]. split; [congruence | ]. split; [congruence | ]. split; [congruence | ].
    split; [congruence | ].
    pose proof Hinp. unfold ai in *. rep_lia. }
  try forward.
  unfold g6_cont, g6_cont_at. Exists r (pos + (Zlength inp - AM.zf_ai z')) z' L1.
  unfold g6_sep, g6_locals, g6_tup, gp_locals, gs_locals, lv_locals. cbn [app].
  rewrite g6_r_split. unfold ifz.
  entailer!.
Qed.
