(* The header cases FLAGS, TIME, OS keep what the header tokens (CaseHyps5.v hdr_tok, hd_ok) depend on: whether
   there is a header, which fields are present and the buffers' maxima (hkey). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseKitT5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Definition hkey (m: mst) : bool * bool * Z * bool * Z * bool * Z :=
  (i_head (m_s m), h_xp (m_h m), h_extra_max (m_h m), h_np (m_h m), h_name_max (m_h m),
   h_cp (m_h m), h_comm_max (m_h m)).

Lemma hkey_hdr_tok: forall F m m', hkey m' = hkey m -> hdr_tok F m' = hdr_tok F m.
Proof.
  intros F m m' E. unfold hkey in E. injection E as E1 E2 E3 E4 E5 E6 E7. unfold hdr_tok.
  rewrite E1, E3, E5, E7. reflexivity.
Qed.

Lemma hkey_hd_ok: forall F m m', hkey m' = hkey m -> hd_ok F m -> hd_ok F m'.
Proof.
  intros F m m' E H. unfold hkey in E. injection E as E1 E2 E3 E4 E5 E6 E7. unfold hd_ok in *.
  rewrite E1, E2, E4, E6. exact H.
Qed.

Lemma hkey_needbits_f: forall k n m, hkey (needbits_f k n m) = hkey m.
Proof.
  induction k; intros n m; simpl; auto.
  destruct (m_bits m <? n); auto. destruct (m_have m =? 0); auto. rewrite IHk. reflexivity.
Qed.

Lemma hkey_needbits: forall n m, hkey (needbits n m) = hkey m.
Proof. intros. apply hkey_needbits_f. Qed.

Lemma hkey_crc_if: forall m d, hkey (crc_if m d) = hkey m.
Proof. intros. unfold crc_if. destruct (andb _ _); reflexivity. Qed.

Lemma hkey_initbits: forall m, hkey (initbits m) = hkey m.
Proof. reflexivity. Qed.

Lemma hkey_set_mode: forall m md, hkey (set_mode m md) = hkey m.
Proof. reflexivity. Qed.
