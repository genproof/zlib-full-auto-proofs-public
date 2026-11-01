(* One pass of the switch for each mode: stepf2 reduced to the case's function (Model2.v). *)
From Coq Require Import ZArith.
Require Import Zlib.proof.inflate.Model2.
Local Open Scope Z_scope.

Section Steps2.
Variables (fl: Z) (fx dx: list entry).

Lemma stepf2_HEAD (m: mst): m_mode m = HEAD -> stepf2 fl fx dx m = c_HEAD2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_FLAGS (m: mst): m_mode m = FLAGS -> stepf2 fl fx dx m = c_FLAGS2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_TIME (m: mst): m_mode m = TIME -> stepf2 fl fx dx m = c_TIME2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_OS (m: mst): m_mode m = OS -> stepf2 fl fx dx m = c_OS2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_EXLEN (m: mst): m_mode m = EXLEN -> stepf2 fl fx dx m = c_EXLEN2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_EXTRA (m: mst): m_mode m = EXTRA -> stepf2 fl fx dx m = c_EXTRA2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_NAME (m: mst): m_mode m = NAME -> stepf2 fl fx dx m = c_NAME2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_COMMENT (m: mst): m_mode m = COMMENT -> stepf2 fl fx dx m = c_COMMENT2 m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_HCRC (m: mst): m_mode m = HCRC -> stepf2 fl fx dx m = c_HCRC m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_DICTID (m: mst): m_mode m = DICTID -> stepf2 fl fx dx m = c_DICTID fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_DICT (m: mst): m_mode m = DICT -> stepf2 fl fx dx m = c_DICT fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_TYPE (m: mst): m_mode m = TYPE -> stepf2 fl fx dx m = c_TYPE fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_TYPEDO (m: mst): m_mode m = TYPEDO -> stepf2 fl fx dx m = c_TYPEDO fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_STORED (m: mst): m_mode m = STORED -> stepf2 fl fx dx m = c_STORED fl m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_COPY_ (m: mst): m_mode m = COPY_ -> stepf2 fl fx dx m = c_COPY_ m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_COPY (m: mst): m_mode m = COPY -> stepf2 fl fx dx m = c_COPY m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_TABLE (m: mst): m_mode m = TABLE -> stepf2 fl fx dx m = c_TABLE fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LENLENS (m: mst): m_mode m = LENLENS -> stepf2 fl fx dx m = c_LENLENS fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_CODELENS (m: mst): m_mode m = CODELENS -> stepf2 fl fx dx m = c_CODELENS fl fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LEN_ (m: mst): m_mode m = LEN_ -> stepf2 fl fx dx m = c_LEN_ fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LEN (m: mst): m_mode m = LEN -> stepf2 fl fx dx m = c_LEN fx dx (fast fx dx) m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LENEXT (m: mst): m_mode m = LENEXT -> stepf2 fl fx dx m = c_LENEXT fx dx m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_DIST (m: mst): m_mode m = DIST -> stepf2 fl fx dx m = c_DIST fx dx m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_DISTEXT (m: mst): m_mode m = DISTEXT -> stepf2 fl fx dx m = c_DISTEXT m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_MATCH (m: mst): m_mode m = MATCH -> stepf2 fl fx dx m = c_MATCH m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LIT (m: mst): m_mode m = LIT -> stepf2 fl fx dx m = c_LIT m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_CHECK (m: mst): m_mode m = CHECK -> stepf2 fl fx dx m = c_CHECK m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_LENGTH (m: mst): m_mode m = LENGTH -> stepf2 fl fx dx m = c_LENGTH m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_DONE (m: mst): m_mode m = DONE -> stepf2 fl fx dx m = c_DONE m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_BAD (m: mst): m_mode m = BAD -> stepf2 fl fx dx m = c_BAD m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_MEM (m: mst): m_mode m = MEM -> stepf2 fl fx dx m = IRet Z_MEM_ERROR m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
Lemma stepf2_SYNC (m: mst): m_mode m = SYNC -> stepf2 fl fx dx m = IRet Z_STREAM_ERROR m.
Proof. intros H. unfold stepf2, step2. rewrite H. reflexivity. Qed.
End Steps2.
