(* Law inflate_dict: the body of the harness's static hist() (spec: ITMainKit.hist_spec). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITMainKit.
Require Import Zlib.harness.x_inflate_dict.code.

Lemma body_hist : semax_body [] [] f_hist hist_spec.
Proof.
start_function.
forward_if (temp _t'1 (Vint (Int.repr (Znth k (dict ++ pre))))).
- assert (Hb := is_bytes_Znth dict k H4 ltac:(lia)).
  forward.
  { entailer!. rewrite Znth_bytes_rep by lia. simpl. rewrite Int.unsigned_repr; rep_lia. }
  rewrite Znth_bytes_rep by lia.
  forward.
  entailer!.
  rewrite app_Znth1 by lia. reflexivity.
- assert (Hb := is_bytes_Znth pre (k - Zlength dict) H5 ltac:(lia)).
  assert (He : Znth (k - Zlength dict) acont = Vint (Int.repr (Znth (k - Zlength dict) pre))).
  { replace (Znth (k - Zlength dict) acont) with (Znth (k - Zlength dict) (sublist 0 (Zlength pre) acont))
      by (rewrite Znth_sublist by lia; f_equal; lia).
    rewrite H3, Znth_bytes_rep by lia. reflexivity. }
  forward.
  { entailer!. change (@Znth val Vundef) with (@Znth val Inhabitant_val). rewrite He. simpl. rewrite Int.unsigned_repr; rep_lia. }
  forward.
  entailer!.
  try (change (@Znth val Vundef) with (@Znth val Inhabitant_val)); rewrite He.
  rewrite app_Znth2 by lia. reflexivity.
- assert (Hb := is_bytes_Znth (dict ++ pre) k (is_bytes_app _ _ H4 H5) ltac:(rewrite Zlength_app; lia)).
  forward.
  entailer!.
  rewrite zero_ext_inrange; auto.
  rewrite Int.unsigned_repr by rep_lia. change (two_p 8 - 1) with 255. rep_lia.
Qed.
