(** * The z_stream fields after a successful deflateInit2_ (model), for the mains of the deflate laws on the v9
      specification (DSpec9.deflateInit2__spec_v9 returns total_in, total_out, adler as the model's values without
      their ranges). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.deflate.LTBInit Zlib.proof.deflate.LTCInitKit.
Import ListNotations.
Local Open Scope Z_scope.

Lemma init_ok_strm : forall level method wbits mem strategy a1 a2 a3 a4 a5 z os z',
  c_deflateInit2_ true true false level method wbits mem strategy a1 a2 a3 a4 a5 z = Some (os, z', Z_OK) ->
  z_total_in z' = 0 /\ z_total_out z' = 0 /\ (z_adler z' = 0 \/ z_adler z' = 1) /\
  z_avail_in z' = z_avail_in z /\ z_avail_out z' = z_avail_out z /\ z_msg z' = None.
Proof.
  intros level method wbits mem strategy a1 a2 a3 a4 a5 z os z' H.
  rewrite bi_shape in H.
  destruct (params_ok level method wbits mem strategy) eqn:P; [ | discriminate ].
  destruct a1; [ | discriminate ].
  destruct (a2 && a3 && a4 && a5)%bool; [ | discriminate ].
  rewrite (init_eq _ _ _ _ _ _ P) in H. injection H as _ <-.
  unfold rk_strm. cbn.
  repeat split; try reflexivity.
  destruct (_ =? 2); [left | right]; reflexivity.
Qed.
