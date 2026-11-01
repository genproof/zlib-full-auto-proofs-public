(* Pure facts for the body proof of inflate_decode.c's dyn_header (DRefDyn.v). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.

Lemma ddf_code_okb_cl (cl: list Z) :
  Forall (fun c => 0 <= c <= 7) cl -> code_okb 0 cl = true -> cl_code_ok cl.
Proof.
  intros H1 H2. unfold code_okb in H2. simpl in H2. rewrite !orb_false_r in H2.
  apply Z.eqb_eq in H2. split; auto.
Qed.

Lemma ddf_code_okb_ll (l: list Z) :
  lens_ok l -> Znth 256 l <> 0 -> code_okb 1 l = true -> ll_code_ok l.
Proof.
  intros H1 H2 H3. unfold code_okb in H3. simpl in H3. rewrite orb_false_r in H3.
  split; [auto | split; [auto |]].
  apply orb_true_iff in H3; destruct H3 as [H3 | H3].
  - left. apply Z.eqb_eq in H3. exact H3.
  - right. apply andb_true_iff in H3; destruct H3 as [H3 H4].
    apply Z.eqb_eq in H3; apply Z.eqb_eq in H4. split; auto.
Qed.

Lemma ddf_code_okb_dl (l: list Z) :
  lens_ok l -> code_okb 2 l = true -> dl_code_ok l.
Proof.
  intros H1 H3. unfold code_okb in H3. simpl in H3.
  split; [auto |].
  apply orb_true_iff in H3; destruct H3 as [H3 | H3].
  2: { right; right. apply Z.eqb_eq in H3. exact H3. }
  apply orb_true_iff in H3; destruct H3 as [H3 | H3].
  - left. apply Z.eqb_eq in H3. exact H3.
  - right; left. apply andb_true_iff in H3; destruct H3 as [H3 H4].
    apply Z.eqb_eq in H3; apply Z.eqb_eq in H4. split; auto.
Qed.

Lemma ddf_cl_lens_order (cl: list Z) :
  Zlength cl = 19 -> cl_lens (map (fun k => Znth k cl) clorder) = cl.
Proof.
  intros H. rewrite Zlength_correct in H.
  do 19 (destruct cl as [|? cl]; [discriminate|]).
  destruct cl; [|simpl in H; lia].
  reflexivity.
Qed.

Lemma ddf_bits_msb_mod16 (x n: Z) :
  0 <= n <= 16 -> bits_msb (x mod 65536) n = bits_msb x n.
Proof.
  intros Hn. unfold bits_msb, bits_le. f_equal. apply map_ext_in. intros i Hi.
  apply in_seq in Hi.
  change 65536 with (2 ^ 16). apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma ddf_send_sym_canon (cl: list Z) (s: Z) :
  0 < Znth s cl <= 16 -> bits_msb (canon_val cl s) (Znth s cl) = send_sym cl s.
Proof.
  intros H. unfold canon_val, send_sym.
  destruct (Znth s cl =? 0) eqn:E; [apply Z.eqb_eq in E; lia |].
  apply ddf_bits_msb_mod16. lia.
Qed.

Lemma ddf_tok_expand_app1 (prev: list Z) (toks: list cltok) (t: cltok) :
  tok_expand prev (toks ++ [t]) = tok_expand prev toks ++ tok_vals (tok_expand prev toks) t.
Proof.
  revert prev; induction toks as [|a r IH]; intros prev; simpl; auto.
Qed.

Lemma ddf_toks_ok_app1 (cl prev: list Z) (toks: list cltok) (t: cltok) :
  toks_ok cl prev toks -> tok_ok cl (tok_expand prev toks) t -> toks_ok cl prev (toks ++ [t]).
Proof.
  revert prev; induction toks as [|a r IH]; intros prev H1 H2; simpl in *.
  - auto.
  - destruct H1. split; auto.
Qed.

Lemma ddf_Zlength_bits_le (v n: Z) : 0 <= n -> Zlength (bits_le v n) = n.
Proof.
  intros H. unfold bits_le. rewrite Zlength_correct, map_length, seq_length. lia.
Qed.

Lemma ddf_Znth_range (cl: list Z) (s: Z) :
  Forall (fun c => 0 <= c <= 7) cl -> 0 <= Znth s cl <= 7.
Proof.
  intros H. destruct (zlt s 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia |].
  destruct (zlt s (Zlength cl)).
  - eapply Forall_forall in H; [exact H |]. apply Znth_In. lia.
  - rewrite Znth_overflow by lia. unfold Inhabitant_Z; lia.
Qed.

Lemma ddf_send_sym_len (cl: list Z) (s: Z) :
  Forall (fun c => 0 <= c <= 7) cl -> 0 <= Zlength (send_sym cl s) <= 7.
Proof.
  intros H. pose proof (ddf_Znth_range cl s H). unfold send_sym, bits_msb.
  rewrite Zlength_rev, ddf_Zlength_bits_le by lia. lia.
Qed.

Lemma ddf_send_toks_len (cl: list Z) (toks: list cltok) :
  Forall (fun c => 0 <= c <= 7) cl -> Zlength (flat_map (send_tok cl) toks) <= 14 * Zlength toks.
Proof.
  intros H. induction toks as [|t r IH]; simpl.
  - rewrite !Zlength_nil. lia.
  - rewrite Zlength_app, Zlength_cons.
    assert (Zlength (send_tok cl t) <= 14).
    { destruct t; simpl.
      - pose proof (ddf_send_sym_len cl l H); lia.
      - pose proof (ddf_send_sym_len cl 16 H). rewrite Zlength_app, ddf_Zlength_bits_le by lia. lia.
      - destruct (r0 <=? 10).
        + pose proof (ddf_send_sym_len cl 17 H). rewrite Zlength_app, ddf_Zlength_bits_le by lia. lia.
        + pose proof (ddf_send_sym_len cl 18 H). rewrite Zlength_app, ddf_Zlength_bits_le by lia. lia. }
    lia.
Qed.

Lemma ddf_toks_count (cl prev: list Z) (toks: list cltok) :
  toks_ok cl prev toks -> Zlength prev + Zlength toks <= Zlength (tok_expand prev toks).
Proof.
  revert prev; induction toks as [|t r IH]; intros prev H; simpl in *.
  - rewrite Zlength_nil. lia.
  - destruct H as [H1 H2]. specialize (IH _ H2). rewrite Zlength_app in IH. rewrite Zlength_cons.
    assert (1 <= Zlength (tok_vals prev t)).
    { destruct t; simpl in *.
      - rewrite Zlength_cons, Zlength_nil. lia.
      - rewrite Zlength_correct, repeat_length. lia.
      - rewrite Zlength_correct, repeat_length. lia. }
    lia.
Qed.

(* all the facts in one statement; the lemmas below are its parts:
   - code_ok's results as Format's code conditions;
   - the code length code lengths sent in the order clorder give back cl;
   - bits_msb reads only the n low bits, so bw_code(canonical code, length) sends the symbol;
   - one more token: tok_expand / toks_ok;
   - sizes: a token's bits (code lengths <= 7), the number of tokens. *)
Lemma dref_dyn_facts :
  (forall cl: list Z, Forall (fun c => 0 <= c <= 7) cl -> code_okb 0 cl = true -> cl_code_ok cl) /\
  (forall l: list Z, lens_ok l -> Znth 256 l <> 0 -> code_okb 1 l = true -> ll_code_ok l) /\
  (forall l: list Z, lens_ok l -> code_okb 2 l = true -> dl_code_ok l) /\
  (forall cl: list Z, Zlength cl = 19 -> cl_lens (map (fun k => Znth k cl) clorder) = cl) /\
  (forall x n: Z, 0 <= n <= 16 -> bits_msb (x mod 65536) n = bits_msb x n) /\
  (forall (cl: list Z) (s: Z), 0 < Znth s cl <= 16 -> bits_msb (canon_val cl s) (Znth s cl) = send_sym cl s) /\
  (forall (prev: list Z) (toks: list cltok) (t: cltok),
     tok_expand prev (toks ++ [t]) = tok_expand prev toks ++ tok_vals (tok_expand prev toks) t) /\
  (forall (cl prev: list Z) (toks: list cltok) (t: cltok),
     toks_ok cl prev toks -> tok_ok cl (tok_expand prev toks) t -> toks_ok cl prev (toks ++ [t])) /\
  (forall (cl: list Z) (toks: list cltok),
     Forall (fun c => 0 <= c <= 7) cl -> Zlength (flat_map (send_tok cl) toks) <= 14 * Zlength toks) /\
  (forall (cl prev: list Z) (toks: list cltok),
     toks_ok cl prev toks -> Zlength prev + Zlength toks <= Zlength (tok_expand prev toks)).
Proof.
  split; [exact ddf_code_okb_cl |]. split; [exact ddf_code_okb_ll |]. split; [exact ddf_code_okb_dl |].
  split; [exact ddf_cl_lens_order |]. split; [exact ddf_bits_msb_mod16 |].
  split; [exact ddf_send_sym_canon |]. split; [exact ddf_tok_expand_app1 |].
  split; [exact ddf_toks_ok_app1 |]. split; [exact ddf_send_toks_len |].
  exact ddf_toks_count.
Qed.

Lemma code_okb_cl (cl: list Z) :
  Forall (fun c => 0 <= c <= 7) cl -> code_okb 0 cl = true -> cl_code_ok cl.
Proof. apply dref_dyn_facts. Qed.

Lemma code_okb_ll (l: list Z) :
  lens_ok l -> Znth 256 l <> 0 -> code_okb 1 l = true -> ll_code_ok l.
Proof. apply dref_dyn_facts. Qed.

Lemma code_okb_dl (l: list Z) :
  lens_ok l -> code_okb 2 l = true -> dl_code_ok l.
Proof. apply dref_dyn_facts. Qed.

Lemma cl_lens_order (cl: list Z) :
  Zlength cl = 19 -> cl_lens (map (fun k => Znth k cl) clorder) = cl.
Proof. apply dref_dyn_facts. Qed.

Lemma bits_msb_mod16 (x n: Z) :
  0 <= n <= 16 -> bits_msb (x mod 65536) n = bits_msb x n.
Proof. apply dref_dyn_facts. Qed.

Lemma send_sym_canon (cl: list Z) (s: Z) :
  0 < Znth s cl <= 16 -> bits_msb (canon_val cl s) (Znth s cl) = send_sym cl s.
Proof. apply dref_dyn_facts. Qed.

Lemma tok_expand_app1 (prev: list Z) (toks: list cltok) (t: cltok) :
  tok_expand prev (toks ++ [t]) = tok_expand prev toks ++ tok_vals (tok_expand prev toks) t.
Proof. apply dref_dyn_facts. Qed.

Lemma toks_ok_app1 (cl prev: list Z) (toks: list cltok) (t: cltok) :
  toks_ok cl prev toks -> tok_ok cl (tok_expand prev toks) t -> toks_ok cl prev (toks ++ [t]).
Proof. apply dref_dyn_facts. Qed.

Lemma send_toks_len (cl: list Z) (toks: list cltok) :
  Forall (fun c => 0 <= c <= 7) cl -> Zlength (flat_map (send_tok cl) toks) <= 14 * Zlength toks.
Proof. apply dref_dyn_facts. Qed.

Lemma toks_count (cl prev: list Z) (toks: list cltok) :
  toks_ok cl prev toks -> Zlength prev + Zlength toks <= Zlength (tok_expand prev toks).
Proof. apply dref_dyn_facts. Qed.
