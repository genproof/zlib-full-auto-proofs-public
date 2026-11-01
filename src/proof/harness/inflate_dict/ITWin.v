(* Law inflate_dict, theory part: inflateGetDictionary's bytes from the window invariant. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_dict.ITTheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma itw_get : forall G s out, it_ok G -> win_st G s out ->
  i_whave s = Z.min (Zlength out) (2 ^ g_wb G) /\
  dict_bytes s = sublist (Zlength out - i_whave s) (Zlength out) out.
Proof.
  intros G s out Hok (Hwb & Hws & _ & (Hh & Hn & Hlt & Hlen) & Hwin).
  assert (HW: 2 ^ g_wb G <> 0) by (destruct Hok as [Hb _]; apply Z.pow_nonzero; lia).
  destruct Hwin as [[H0 _] | (_ & Hwh & Hat)]; [congruence |].
  rewrite Hws in Hwh. split; [exact Hwh |].
  set (n := Zlength out) in *. set (h := i_whave s) in *. set (w := i_wnext s) in *.
  set (W := i_wsize s) in *.
  assert (Hhn: h <= n) by lia.
  unfold dict_bytes; fold h w.
  apply Znth_eq_ext.
  - rewrite Zlength_app, !Zlength_sublist by lia. lia.
  - intros i Hi. rewrite Zlength_app, !Zlength_sublist in Hi by lia.
    rewrite Znth_sublist by lia.
    specialize (Hat (h - i) ltac:(lia)). unfold win_at in Hat. fold w W in Hat.
    replace (i + (n - h)) with (n - (h - i)) by lia. rewrite <- Hat.
    destruct (Z.lt_ge_cases h W) as [HhW | HhW].
    + specialize (Hlt HhW). fold w h in Hlt.
      rewrite Znth_app2 by (rewrite Zlength_sublist by lia; lia).
      rewrite Zlength_sublist by lia. rewrite Znth_sublist by lia.
      destruct (Z.leb_spec (h - i) w); [| lia]. f_equal; lia.
    + assert (h = W) by lia.
      destruct (Z.lt_ge_cases i (h - w)).
      * rewrite Znth_app1 by (rewrite Zlength_sublist by lia; lia).
        rewrite Znth_sublist by lia.
        destruct (Z.leb_spec (h - i) w); [lia |]. f_equal; lia.
      * rewrite Znth_app2 by (rewrite Zlength_sublist by lia; lia).
        rewrite Zlength_sublist by lia. rewrite Znth_sublist by lia.
        destruct (Z.leb_spec (h - i) w); [| lia]. f_equal; lia.
Qed.
