(* Law rj_bad_level: the model fact.  deflateInit2_ checks the level before it allocates anything: with a level
   outside -1..9 (Z_DEFAULT_COMPRESSION is -1) it returns Z_STREAM_ERROR for every allocation outcome, so
   compress2_z's model result RTC2.c2_res exists and is Z_STREAM_ERROR with no output, for any data and any
   destLen. *)
From Coq Require Import ZArith List Lia Bool.
Require Import Zlib.proof.roundtrip.RTC2.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rjl_init_bad level a1 a2 a3 a4 a5 z0 : ~ (-1 <= level <= 9) ->
  c_deflateInit2_ true true false level 8 15 8 0 a1 a2 a3 a4 a5 z0 =
  Some (None, set_z_msg z0 None, Z_STREAM_ERROR).
Proof.
  intros Hl.
  assert (Hd : (level =? Z_DEFAULT_COMPRESSION) = false)
    by (apply Z.eqb_neq; unfold Z_DEFAULT_COMPRESSION; lia).
  assert (Hb : (level <? 0) = true \/ (level >? 9) = true).
  { destruct (Z.ltb_spec level 0); [left; reflexivity | right; apply Z.gtb_lt; lia]. }
  unfold c_deflateInit2_. change (negb true || negb true) with false. cbv beta iota zeta. rewrite Hd.
  change (15 <? 0) with false. change (15 >? 15) with false. cbv beta iota zeta.
  match goal with |- (if ?c then _ else _) = _ => replace c with true; [reflexivity | ] end.
  symmetry. rewrite !Bool.orb_true_iff. tauto.
Qed.

(* the model result of compress2_z with a rejected level: it exists, and every one is Z_STREAM_ERROR *)
Lemma rjl_c2_exists src cap level a1 a2 a3 a4 a5 z0 : ~ (-1 <= level <= 9) ->
  exists r out, c2_res src cap level a1 a2 a3 a4 a5 z0 r out.
Proof.
  intros Hl. exists Z_STREAM_ERROR, []. unfold c2_res.
  exists None, (set_z_msg z0 None), Z_STREAM_ERROR. split; [apply rjl_init_bad; exact Hl | ].
  left. split; [discriminate | split; reflexivity].
Qed.

Lemma rjl_c2_res src cap level a1 a2 a3 a4 a5 z0 r out : ~ (-1 <= level <= 9) ->
  c2_res src cap level a1 a2 a3 a4 a5 z0 r out -> r = Z_STREAM_ERROR.
Proof.
  intros Hl (os & z1 & code & Hi & H). rewrite rjl_init_bad in Hi by exact Hl.
  injection Hi as <- <- <-.
  destruct H as [(_ & -> & _) | (E & _)]; [reflexivity | discriminate].
Qed.
