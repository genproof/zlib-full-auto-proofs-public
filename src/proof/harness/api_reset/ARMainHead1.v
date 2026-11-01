(* Law api_reset, main: the do-while body in phase 1 (ARMainKit.seg_dbody), up to the test of Z_MEM_ERROR:
   the piece and the output space, the four objects, offer() on both streams, inflate(&used) then
   inflate(&fresh) (ARFacts.af_inflate1); the rest of the body is tail1_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
(* inflate(&used), inflate(&fresh), the test of Z_MEM_ERROR, then tail1_stmt *)
Require Import Zlib.proof.harness.api_reset.ARMainH1Call.
(* the test of the four objects when one is NULL, then when none is (the offers and the rest) *)
Require Import Zlib.proof.harness.api_reset.ARMainH1Null Zlib.proof.harness.api_reset.ARMainH1Off.
Local Open Scope logic.

(* right-associate the statement, so that `x = malloc(...)` is a call followed by a set (forward_call on a
   call of a function returning a pointer immediately followed by `x = t'` is very slow) *)
Ltac split_call1 := repeat match goal with |- semax _ _ (Ssequence (Ssequence _ _) _) _ => apply -> seq_assoc end.

Lemma body1_of : tail1_stmt -> body_stmt 1.
Proof.
  intros TAIL1. unfold body_stmt. intros Espec J0 J1 gv va vb w inp src pos za La zb Lb GF.
  unfold seg_dbody, dpost, Delta_m, Gmain, POST_m. simplify_func_tycontext. abbreviate_semax.
  unfold dinv_at, dprop, fresh_mem. simpl (1 =? 0). cbv iota. Intros.
  match goal with H: swfW (l_s La) |- _ => rename H into SWa end.
  match goal with H: swfW (l_s Lb) |- _ => rename H into SWb end.
  match goal with H: raw_live (Some La) = _ |- _ => rename H into Rwa end.
  match goal with H: raw_live (Some Lb) = _ |- _ => rename H into Rwb end.
  match goal with H: J1 _ _ _ _ _ _ _ |- _ => rename H into HJ end.
  match goal with H: 0 <= pos <= _ |- _ => rename H into Hpos end.
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  forward_call (Zlength src - pos).
  forward_call (Z.min (Zlength src - pos) Int.max_unsigned). Intros take.
  forward.
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
  split_call1. forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, d, gv).
  Intros iu. forward.
  split_call1. forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, d, gv).
  Intros ifr. forward.
  split_call1. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros ou. forward.
  split_call1. forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros ofr. forward.
  fold (copy_obj iu take d) (copy_obj ifr take d) (malloc_obj ou room) (malloc_obj ofr room).
  (* if (in_used == NULL || in_fresh == NULL || out_used == NULL || out_fresh == NULL) return 0; *)
  assert (Hnull: (iu = nullval \/ ifr = nullval \/ ou = nullval \/ ofr = nullval) \/
                 (iu <> nullval /\ ifr <> nullval /\ ou <> nullval /\ ofr <> nullval)).
  { destruct (eq_dec iu nullval), (eq_dec ifr nullval), (eq_dec ou nullval), (eq_dec ofr nullval); tauto. }
  destruct Hnull as [Hnull | (N1 & N2 & N3 & N4)].
  { eapply semax_pre; [ | apply (h1_null J0 J1 gv va vb w 1 inp src take room d iu ifr ou ofr _ Hnull)].
    match goal with |- context [istreamA ?g Tsh va ?z ?a (Some ?L)] => sep_apply (a_frame g va z a L) end.
    match goal with |- context [istreamA ?g Tsh vb ?z ?a (Some ?L)] => sep_apply (a_frame g vb z a L) end.
    entailer!. }
  eapply semax_pre; [ | apply (h1_off J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb Lb TAIL1)].
  { unfold h1t_pre. fold d. entailer!. }
  unfold h1t_facts. refine (conj GF0 (conj HJ (conj SWa (conj SWb (conj Rwa (conj Rwb _)))))).
  repeat split; auto; lia.
Qed.
