(* Law api_inflate_deterministic, main: the do-while body (AIDMainKit.seg_dbody) up to the asserts: the piece
   and the output space, the four objects and their NULL test, set_buffer() on both streams, inflate(&first)
   and inflate(&second) (AIDFacts.df_inflate), the test of Z_MEM_ERROR; the rest of the body is tail_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainDefs.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_inflate_deterministic.code.
(* inflate(&first), inflate(&second), the test of Z_MEM_ERROR, then tail_stmt *)
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBodyCall.
(* the test of the four objects when one is NULL, then when none is (set_buffer() and the rest) *)
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBodyNull.
Require Import Zlib.proof.harness.api_inflate_deterministic.AIDMainBodyOff.
Local Open Scope logic.

(* right-associate the statement, so that `x = malloc(...)` is a call followed by a set (forward_call on a
   call of a function returning a pointer immediately followed by `x = t'` is very slow) *)
Ltac split_call1 := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.

Lemma body_of : tail_stmt -> body_stmt.
Proof.
  intros TAIL. unfold body_stmt. intros Espec J gv va vb w inp src pos za La zb Lb GF.
  unfold seg_dbody, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  unfold dinv_at, dprop. Intros.
  match goal with H: swfW (l_s La) |- _ => rename H into SWa end.
  match goal with H: swfW (l_s Lb) |- _ => rename H into SWb end.
  match goal with H: raw_live (Some La) = _ |- _ => rename H into Rwa end.
  match goal with H: raw_live (Some Lb) = _ |- _ => rename H into Rwb end.
  match goal with H: J _ _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: 0 <= pos <= _ |- _ => rename H into Hpos end.
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  (* take = upto(clip(input_len - read)) *)
  forward_call (Zlength src - pos).
  forward_call (Z.min (Zlength src - pos) Int.max_unsigned). Intros take.
  forward.
  (* out_size = nondet_u32(); flush = (int) nondet_u32() *)
  rewrite <- !seq_assoc. forward_call tt. Intros room. forward.
  rewrite Int.unsigned_repr by rep_lia.
  forward_call tt. Intros u.
  assert (Ef: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  assert (Htk: 0 <= take /\ pos + take <= Zlength src /\ take <= Int.max_unsigned).
  { pose proof (Z.le_min_l (Zlength src - pos) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength src - pos) Int.max_unsigned). lia. }
  set (d := sublist pos (pos + take) src).
  assert (Hdl: Zlength d = take) by (unfold d; rewrite Zlength_sublist; lia).
  assert (Hdb: bytes_ok d) by (unfold d; apply Forall_sublist; auto).
  assert (CB: cbuf_ok false (offset_val pos inp) Ews inp pos (Zlength src) take (bytes_rep src) d).
  { unfold cbuf_ok. repeat split; auto; try lia. unfold d, bytes_rep. rewrite sublist_map. reflexivity. }
  rewrite <- bytes_adler_cs.
  (* the four objects: in_first, in_second (copy_of), out_first, out_second (malloc) *)
  split_call1. forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, d, gv).
  Intros ia. forward.
  split_call1. forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, d, gv).
  Intros ib. forward.
  split_call1. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros oa. forward.
  split_call1. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros ob. forward.
  fold (copy_obj ia take d) (copy_obj ib take d) (malloc_obj oa room) (malloc_obj ob room).
  (* if (in_first == NULL || in_second == NULL || out_first == NULL || out_second == NULL) return 0; *)
  assert (Hnull: (ia = nullval \/ ib = nullval \/ oa = nullval \/ ob = nullval) \/
                 (ia <> nullval /\ ib <> nullval /\ oa <> nullval /\ ob <> nullval)).
  { destruct (eq_dec ia nullval), (eq_dec ib nullval), (eq_dec oa nullval), (eq_dec ob nullval); tauto. }
  destruct Hnull as [Hnull | (N1 & N2 & N3 & N4)].
  { eapply semax_pre; [ | apply (body_null J gv va vb w inp src take room d ia ib oa ob _ Hnull)].
    match goal with |- context [istreamA ?g Tsh va ?z ?a (Some ?L)] => sep_apply (a_frame g va z a L) end.
    match goal with |- context [istreamA ?g Tsh vb ?z ?a (Some ?L)] => sep_apply (a_frame g vb z a L) end.
    entailer!. }
  eapply semax_pre; [ | apply (body_off J gv va vb w inp src pos take room flush ia ib oa ob za La zb Lb TAIL)].
  { unfold bt_pre. fold d. entailer!. }
  unfold bt_facts. refine (conj GF0 (conj HJ (conj SWa (conj SWb (conj Rwa (conj Rwb _)))))).
  repeat split; auto; lia.
Qed.
