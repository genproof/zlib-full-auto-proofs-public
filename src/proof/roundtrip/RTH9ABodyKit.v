(* The memory conversions of inflate()'s body against RTH9Spec.inflate_spec9 (RTH9ABody.body9_from): the header
   part of RTH9Spec.head_mem9 is the header RTH9HDefs.hd9 of the first machine of the call, and the final memory
   with the header hd9 of the final machine is inflate_spec9's postcondition (RTH8BCKit.mem_rep_istream8 for
   head_mem9). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.roundtrip.RTH9AKit.
Require Import Zlib.proof.inflate_api.Body5Conv.
Require Import Zlib.proof.roundtrip.RTH8BCBody.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the header part of head_mem9 (without the buffers' tokens) *)
Definition hdm9 (L: live) : mpred :=
  !! (hdr_mode (i_mode (l_s L)) = true) &&
     head_rep6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) ||
  !! (hdr_mode (i_mode (l_s L)) = false) &&
     head_rep8a (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_s L) (l_h L) ||
  !! (hdr_mode (i_mode (l_s L)) = false /\ h_done (l_h L) <> 1) &&
     hraw6 (l_hsh L) (l_headp L) (l_xb L) (l_nb L) (l_cb L) (l_h L).

Lemma head_mem9_split: forall L, head_mem9 L = hdm9 L * btoks8 L.
Proof. intros L. unfold head_mem9, hdm9, btoks8. rewrite !sepcon_assoc. reflexivity. Qed.

(* a stream that is not live is the same for inflate_spec9 and the prologue *)
Lemma istream8_opt_nolive: forall gv shs strmp z st, is_live strmp st = None ->
  istream8_opt gv shs strmp z st = istream_opt gv shs strmp z st.
Proof.
  intros gv shs strmp z st E. unfold is_live, istream8_opt, istream_opt in *.
  destruct (eq_dec strmp nullval); [reflexivity | ]. subst st. reflexivity.
Qed.

(* the loop state is monotone in its frame item *)
Lemma lstateH_X_derives: forall F X Y m, X |-- Y -> lstateH F X m |-- lstateH F Y m.
Proof.
  intros F X Y m H rho. unfold lstateH, PROPx, LOCALx, SEPx. simpl.
  apply andp_derives; [apply derives_refl | ]. apply andp_derives; [apply derives_refl | ].
  sep_apply H. cancel.
Qed.

(* the header of the first machine of a call (TYPE -> TYPEDO keeps the header mode and the flags) *)
Lemma head9_init: forall gv shs strmp L ib o gsh tsh z vh vl vb flush inp,
  hdm9 L |-- hd9 (mkF gv shs strmp L ib o gsh tsh z vh vl vb flush) (m_init z L inp).
Proof.
  intros. unfold hd9, hdm9. unfold m_mode. rewrite m_init_s, hdr_mode_typedo.
  destruct (hdr_mode (i_mode (l_s L))) eqn:EM.
  - assert (MS0: s_typedo (l_s L) = l_s L).
    { unfold s_typedo.
      destruct (Z.eqb_spec (i_mode (l_s L)) Zlib.proof.inflate.Model.TYPE) as [ET | ]; [ | reflexivity].
      rewrite ET in EM. discriminate. }
    apply orp_left; [apply orp_left | ].
    + apply derives_extract_prop; intros _. unfold hd6, mkF. cbn [f_hsh f_headp f_xb f_nb f_cb].
      rewrite m_init_s, MS0. apply derives_refl.
    + apply derives_extract_prop; intros H; discriminate.
    + apply derives_extract_prop; intros [H _]; discriminate.
  - unfold hd9a. apply orp_left; [apply orp_left | ].
    + apply derives_extract_prop; intros H; discriminate.
    + apply derives_extract_prop; intros _. apply orp_right1.
      unfold hd8a, head_rep8a, mkF. cbn [f_hsh f_headp f_xb f_nb f_cb]. rewrite m_init_s, fextra_typedo.
      apply derives_refl.
    + apply derives_extract_prop; intros [_ H]. apply orp_right2.
      apply andp_right; [apply prop_right; exact H | ]. unfold mkF. apply derives_refl.
Qed.

(* the final memory with the header hd9 of the final machine is inflate_spec9's (RTH8BCKit.mem_rep_istream8) *)
Lemma mem_rep_istream9: forall F m,
  live_ok8 (live_of F m) -> zf_ok (z_of F m) -> writable_share (f_shs F) -> f_strmp F <> nullval ->
  i_head (m_s m) = true ->
  mem_rep_hl F m * hdr_tok F m * malloc_token Ews t_state (f_sp F) * state_pad (f_sp F) * hd9 F m |--
  istream8_opt (f_gv F) (f_shs F) (f_strmp F) (z_of F m) (Some (live_of F m)) *
  head_opt9 (is_live (f_strmp F) (Some (live_of F m))) * in_rep (f_ib F) *
  out_opt (Some (f_ob F)) (m_ow m) * tables_rep (f_gsh F) (f_gv F) * crc_table_at (f_tsh F) (f_gv F).
Proof.
  intros F m HL HZ HW HN HI.
  assert (HD: hd9 F m |-- hdm9 (live_of F m)).
  { unfold hd9, hdm9, live_of. cbn [l_s l_h l_hsh l_headp l_xb l_nb l_cb]. unfold m_mode.
    destruct (hdr_mode (i_mode (m_s m))) eqn:EM.
    - apply orp_right1. apply orp_right1. apply andp_right; [apply prop_right; reflexivity | ].
      unfold hd6. apply derives_refl.
    - unfold hd9a. apply orp_left.
      + apply orp_right1. apply orp_right2. apply andp_right; [apply prop_right; reflexivity | ].
        unfold hd8a. apply derives_refl.
      + apply derives_extract_prop; intros H. apply orp_right2.
        apply andp_right; [apply prop_right; split; [reflexivity | exact H] | apply derives_refl]. }
  sep_apply HD.
  unfold head_opt9, is_live. destruct (eq_dec (f_strmp F) nullval) as [E | _]; [contradiction | ].
  rewrite head_mem9_split.
  unfold istream8_opt. destruct (eq_dec (f_strmp F) nullval) as [E | _]; [contradiction | ].
  unfold istream8, zstrm_at, state_mem, mem_rep_hl, head_part_hl, hdr_tok, out_opt, btoks8.
  unfold z_of, live_of; simpl. rewrite HI.
  entailer!.
Qed.
