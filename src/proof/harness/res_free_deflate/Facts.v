(* Law res_free_deflate: the arithmetic of the counter count.now.

   - [cnt_now_mod]: count.now, computed in size_t, is the bytes held modulo 2^64, whatever the events;
   - [free_events_now]: deflateInit2_'s five allocations, then deflateEnd's five releases of the same sizes
     (deflate() in between keeps the sizes, DeflateKeep.v), leave nothing held;
   - [init_status]: the state a successful deflateInit2_ makes has a status deflateStateCheck accepts. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.za.deflate.ZSpec.
Require Import Zlib.proof.deflate.DeflateKit.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.deflate.LawFacts.
Require Zlib.proof.deflate.LTApiInit Zlib.proof.deflate.LTCInitKit.
#[local] Existing Instance DCS.CS.

Lemma cnt_now_mod : forall tr, fst (cnt tr) = za_now tr mod 2 ^ 64.
Proof.
  intros tr. rewrite <- (rev_involutive tr). induction (rev tr) as [| e l IH].
  - reflexivity.
  - simpl rev. unfold cnt in *. rewrite fold_left_app. simpl fold_left.
    destruct e as [n | n | ]; simpl cnt_step.
    + rewrite za_now_alloc, IH. rewrite Zplus_mod_idemp_l. reflexivity.
    + rewrite za_now_free, IH. rewrite Zminus_mod_idemp_l. reflexivity.
    + rewrite za_now_fail, IH. reflexivity.
Qed.

Lemma za_now_app_free : forall tr n, za_now (tr ++ [ZFree n]) = za_now tr - n.
Proof. exact za_now_free. Qed.

Lemma free_events_now : forall {ZA : zallocator} (s s' : dstate) (p : dptrs),
  dkeep s s' -> p_pbuf p <> nullval -> p_head p <> nullval -> p_prev p <> nullval -> p_window p <> nullval ->
  za_now ([] ++ dinit_events s ++ dend_events s' p) = 0.
Proof.
  intros ZA s s' p (_ & Ew & Eh & El & _) N1 N2 N3 N4.
  unfold dinit_events, dend_events, dend_free.
  destruct (eq_dec (p_pbuf p) nullval); [contradiction | ].
  destruct (eq_dec (p_head p) nullval); [contradiction | ].
  destruct (eq_dec (p_prev p) nullval); [contradiction | ].
  destruct (eq_dec (p_window p) nullval); [contradiction | ].
  rewrite Ew, Eh, El. unfold za_now, za_count. simpl. lia.
Qed.

Lemma init_status level method wbits mem strategy a1 a2 a3 a4 a5 z s z' r :
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (Some s, z', r) ->
  status_ok (d_status s) = true.
Proof.
  intros H. rewrite Zlib.proof.deflate.LTApiInit.init_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P; [ | discriminate].
  destruct a1; [ | discriminate].
  destruct (a2 && a3 && a4 && a5)%bool; [ | discriminate].
  rewrite (Zlib.proof.deflate.LTCInitKit.init_eq _ _ _ _ _ _ P) in H.
  inversion H; subst s. clear H.
  rewrite Zlib.proof.deflate.LTCInitKit.fin_eq.
  unfold Zlib.proof.deflate.LTCInitKit.sG. cbn [d_status].
  destruct (_ =? 2); reflexivity.
Qed.
