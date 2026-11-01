(* Law inflate_dict, main encoder half: a literal of a fixed block (statement in ITEncKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITEncKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

Lemma fixed_ll_lit b : 0 <= b < 256 -> Znth b fixed_ll <> 0.
Proof.
  intros Hb.
  assert (Hc: forallb (fun i => negb (Znth i fixed_ll =? 0)) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hc. specialize (Hc b).
  assert (Hin: In b (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat b). split; [lia | apply in_seq; lia]. }
  specialize (Hc Hin). apply negb_true_iff, Z.eqb_neq in Hc. auto.
Qed.

Lemma lit_data_sub (dcont: list val) (D: list Z) lit :
  Zlength D < Zlength dcont -> sublist 0 (Zlength D) dcont = bytes_rep D ->
  sublist 0 (Zlength (D ++ [lit])) (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))) = bytes_rep (D ++ [lit]).
Proof.
  intros Hl Hs. pose proof (Zlength_nonneg D).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite (sublist_split 0 (Zlength D) (Zlength D + 1)) by (rewrite ?Zlength_upd_Znth; lia).
  rewrite sublist_upd_Znth_l by lia. rewrite Hs.
  rewrite sublist_len_1 by (rewrite Zlength_upd_Znth; lia). rewrite upd_Znth_same by lia.
  unfold bytes_rep. rewrite map_app. reflexivity.
Qed.

Lemma sym_bits_lit E bs last syms lit :
  sym_bits E bs last (syms ++ [Lit lit]) = sym_bits E bs last syms ++ send_sym fixed_ll lit.
Proof.
  unfold sym_bits. rewrite <- flat_map_app. simpl. rewrite app_nil_r, <- app_assoc. reflexivity.
Qed.

(* THE part to prove: the literal with the normal postcondition (seg_lit has no break/continue/return) *)
Lemma seg_lit_ok_n {Espec: OracleKind} : forall E bs last syms dcont,
  semax Delta_m (sym_room E bs last syms dcont) seg_lit (normal_ret_assert (sym_inv E bs last)).
Proof.
  intros. unfold sym_room. cbv [seg_lit]. Intros.
  forward_call tt. Intros lit.
  set (D := edata E (bs ++ [Fixed syms])) in *.
  destruct H3 as (Hdc & HD & HDb & HDs).
  forward_call (Int.repr (if Zlength D <? 2^18 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 18)) with (Int.repr (2 ^ 18)). arg_cmp. }
  assumed. apply Z.ltb_lt in E0.
  remember (2^18) as N eqn:HN.
  forward.
  { entailer!. }
  forward.
  forward_call (Tsh, Ews, sym_bits E bs last syms, 2^19, e_srcp E, e_vw E, lit).
  { unfold bw_room. split; [lia | split; [ | rep_lia]].
    pose proof (Zlength_nonneg (sym_bits E bs last syms)).
    replace (Zlength (sym_bits E bs last syms) + 9 + 7) with (Zlength (sym_bits E bs last syms) + 2 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite <- sym_bits_lit.
  assert (Hz: Int.zero_ext 8 (Int.repr lit) = Int.repr lit)
    by (apply zero_ext_inrange; rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
  rewrite Hz, add_repr.
  unfold sym_inv. Exists (syms ++ [Lit lit]) (upd_Znth (Zlength D) dcont (Vint (Int.repr lit))).
  unfold sym_at. rewrite <- HN.
  assert (HD': edata E (bs ++ [Fixed (syms ++ [Lit lit])]) = D ++ [lit]) by apply data_fixed_lit.
  rewrite HD'.
  entailer!.
  split; [ | split].
  - apply syms_ok_snoc. split; auto. simpl. split; [unfold byte_ok; rep_lia | apply fixed_ll_lit; rep_lia].
  - unfold data_ok. rewrite Zlength_upd_Znth.
    split; [auto | split; [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | split]].
    + unfold is_bytes. apply Forall_app. split; [auto | repeat constructor; rep_lia].
    + apply lit_data_sub; auto. lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. auto.
Qed.

Lemma seg_lit_ok {Espec: OracleKind} : seg_lit_stmt.
Proof. intros E bs last syms dcont Post. apply sequential. destruct Post. apply seg_lit_ok_n. Qed.
