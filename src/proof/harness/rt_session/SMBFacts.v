(* Law rt_session (harness/rt_session.c): the session main's inflate side sees is one SIFacts.sc_ok accepts.

   After the deflate loop (SMKit.DE) the compressed bytes O are a finished stream of the data with the session's
   dictionary and header; the draws (SMKit.su_ok) give the rest of [sc_ok (scase_of u) (su_data u) O]: deflateInit2's
   parameters, a dictionary only with window_bits <= 15 (raw or zlib wrapper), a header only with window_bits > 15
   (gzip wrapper), the header's fields in the ranges of RTK7.rhdr_ok7 and got's buffers of the fields' sizes
   (G2IFacts.g2_bufs). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTK7.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMKit.
Import ListNotations.
Local Open Scope Z_scope.

(* a field given to deflateSetHeader as an object with its zero byte: a C string of RTK7.rcstr_ok7 *)
Lemma smb_cstr u m l :
  Zlength l <= 4294967294 -> nzbytes l -> rcstr_ok7 (selo u m (l ++ [0])).
Proof.
  intros Hl Hb l' E. unfold selo in E. destruct (has u m); inversion E; subst. eauto.
Qed.

(* head's fields are in the ranges deflateSetHeader's model accepts *)
Lemma smb_hdr_ok u : su_ok u -> rhdr_ok7 (gh_of u).
Proof.
  intros [(_ & _ & _ & _ & _ & _ & _ & _ & Hxl & Bx & Hnl & Bn & Hcl & Bc & _ & _ & _ & Htx & Htm & Hos & Hhc & _) _].
  pose proof (Zlength_nonneg (su_xf u)).
  assert (X : forall x, selo u 2 (su_xf u) = Some x ->
              Zlength x = Zlength (su_xf u) /\ Forall (fun b => 0 <= b < 256) x).
  { intros x E; unfold selo in E; destruct (has u 2); inversion E; subst; auto. }
  unfold rhdr_ok7, gh_of; cbn.
  split; [exact Htx | split; [exact Hhc | split; [exact Hos | split; [exact Htm | split; [lia | ]]]]].
  split; [exact X | split; apply smb_cstr; auto].
Qed.

(* got's buffers (h0) have the sizes of head's fields *)
Lemma smb_bufs u : su_ok u -> g2_bufs (gh_of u) (h0 u).
Proof.
  intros [(_ & _ & _ & _ & _ & _ & _ & _ & Hxl & _ & Hnl & _ & Hcl & _) _].
  pose proof (Zlength_nonneg (su_xf u)). pose proof (Zlength_nonneg (su_nm u)).
  pose proof (Zlength_nonneg (su_cm u)).
  unfold g2_bufs, h0, gh_of; cbn. rewrite !Zlength_Zrepeat by lia.
  repeat split; auto; try lia.
  - intros l E. unfold selo in E. destruct (has u 4); inversion E; subst.
    rewrite Zlength_app. reflexivity.
  - intros l E. unfold selo in E. destruct (has u 8); inversion E; subst.
    rewrite Zlength_app. reflexivity.
Qed.

(* the session: deflate's finished stream and the draws *)
Lemma smb_sc_ok u O :
  su_ok u -> dfinal (sdict u) (rwrap_of (su_wbits u)) (rwbe (su_wbits u)) (sgh u) (su_data u) O ->
  sc_ok (scase_of u) (su_data u) O.
Proof.
  intros Hu Hf. pose proof Hu as [(_ & _ & _ & _ & Hp & _ & Hdl & Bd & _ & _ & _ & _ & _ & _ & Hn & _) _].
  unfold sc_ok, scase_of, sc_wrap; cbn. split; [eauto | split; [exact Hf | split; [ | split; [ | split]]]].
  - unfold sdict, with_dict. intros E.
    destruct (su_wbits u <=? 15) eqn:W; cbn in E; [ | congruence].
    destruct (Z.odd (su_choice u)); cbn in E; [ | congruence].
    apply Z.leb_le in W. cbn. unfold rwrap_of.
    split; [ | split; [exact Bd | lia]].
    destruct (su_wbits u <? 0); [discriminate | ].
    destruct (su_wbits u >? 15) eqn:W2; [apply Z.gtb_lt in W2; lia | discriminate].
  - unfold sgh, with_head. intros E.
    destruct (15 <? su_wbits u) eqn:W; cbn in E; [ | congruence].
    apply Z.ltb_lt in W. unfold rwrap_of.
    destruct (su_wbits u <? 0) eqn:W1; [apply Z.ltb_lt in W1; lia | ].
    destruct (su_wbits u >? 15) eqn:W2; [reflexivity | rewrite Z.gtb_ltb in W2; apply Z.ltb_ge in W2; lia].
  - unfold sgh. intros gh E. destruct (with_head u); inversion E; subst.
    split; [apply smb_hdr_ok | apply smb_bufs]; exact Hu.
  - exact Hn.
Qed.
