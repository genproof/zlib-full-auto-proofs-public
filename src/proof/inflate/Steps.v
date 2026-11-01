(* One pass of the switch for each mode: stepf reduced to the case's function (Model.v). *)
From Coq Require Import ZArith.
Require Import Zlib.proof.inflate.Model.
Local Open Scope Z_scope.

Section Steps.
Variables (fl: Z) (fx dx: list entry).

Lemma stepf_HEAD (m: mst): m_mode m = HEAD -> stepf fl fx dx m = c_HEAD m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_FLAGS (m: mst): m_mode m = FLAGS -> stepf fl fx dx m = c_FLAGS m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_TIME (m: mst): m_mode m = TIME -> stepf fl fx dx m = c_TIME m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_OS (m: mst): m_mode m = OS -> stepf fl fx dx m = c_OS m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_EXLEN (m: mst): m_mode m = EXLEN -> stepf fl fx dx m = c_EXLEN m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_EXTRA (m: mst): m_mode m = EXTRA -> stepf fl fx dx m = c_EXTRA m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_NAME (m: mst): m_mode m = NAME -> stepf fl fx dx m = c_NAME m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_COMMENT (m: mst): m_mode m = COMMENT -> stepf fl fx dx m = c_COMMENT m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_HCRC (m: mst): m_mode m = HCRC -> stepf fl fx dx m = c_HCRC m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_DICTID (m: mst): m_mode m = DICTID -> stepf fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_DICT (m: mst): m_mode m = DICT -> stepf fl fx dx m = c_DICT fl m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_TYPE (m: mst): m_mode m = TYPE -> stepf fl fx dx m = c_TYPE fl m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_TYPEDO (m: mst): m_mode m = TYPEDO -> stepf fl fx dx m = c_TYPEDO fl m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_STORED (m: mst): m_mode m = STORED -> stepf fl fx dx m = c_STORED fl m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_COPY_ (m: mst): m_mode m = COPY_ -> stepf fl fx dx m = c_COPY_ m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_COPY (m: mst): m_mode m = COPY -> stepf fl fx dx m = c_COPY m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_TABLE (m: mst): m_mode m = TABLE -> stepf fl fx dx m = c_TABLE fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LENLENS (m: mst): m_mode m = LENLENS -> stepf fl fx dx m = c_LENLENS fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_CODELENS (m: mst): m_mode m = CODELENS -> stepf fl fx dx m = c_CODELENS fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LEN_ (m: mst): m_mode m = LEN_ -> stepf fl fx dx m = c_LEN_ fx dx (fast fx dx) m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LEN (m: mst): m_mode m = LEN -> stepf fl fx dx m = c_LEN fx dx (fast fx dx) m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LENEXT (m: mst): m_mode m = LENEXT -> stepf fl fx dx m = c_LENEXT fx dx m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_DIST (m: mst): m_mode m = DIST -> stepf fl fx dx m = c_DIST fx dx m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_DISTEXT (m: mst): m_mode m = DISTEXT -> stepf fl fx dx m = c_DISTEXT m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_MATCH (m: mst): m_mode m = MATCH -> stepf fl fx dx m = c_MATCH m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LIT (m: mst): m_mode m = LIT -> stepf fl fx dx m = c_LIT m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_CHECK (m: mst): m_mode m = CHECK -> stepf fl fx dx m = c_CHECK m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_LENGTH (m: mst): m_mode m = LENGTH -> stepf fl fx dx m = c_LENGTH m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_DONE (m: mst): m_mode m = DONE -> stepf fl fx dx m = c_DONE m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_BAD (m: mst): m_mode m = BAD -> stepf fl fx dx m = c_BAD m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_MEM (m: mst): m_mode m = MEM -> stepf fl fx dx m = IRet Z_MEM_ERROR m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
Lemma stepf_SYNC (m: mst): m_mode m = SYNC -> stepf fl fx dx m = IRet Z_STREAM_ERROR m.
Proof. intros H. unfold stepf, step. rewrite H. reflexivity. Qed.
End Steps.
