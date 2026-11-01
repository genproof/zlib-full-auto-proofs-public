(* The kit of the abstract invariant (SIDefs.awf): the invariant with its two facts that no step writes
   (`awfx`: back bounded, the gzip header's flags not zero, also fields of awf: awfx_of_awf), what one step
   must give (`go_ok`), and the facts the cases share: the table walk `adecode` on a valid table, the fixed
   tables, the frame of a state update that keeps the tables. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Zlib.proof.inflate.FixedValid2 Zlib.proof.inflate.Step3Block.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant kept by the steps, and what a step gives                                        *)

Record awfx (src: list Z) (a: ast) : Prop := {
  ax_w : awf src a;
  ax_back : i_back (a_s a) <= 15;
  ax_gzf : TIME <= a_mode a <= HCRC -> i_flags (a_s a) <> 0 }.

Lemma awfx_of_awf: forall src a, awf src a -> awfx src a.
Proof. intros src a W. constructor; [exact W | apply (aw_back _ _ W) | apply (aw_gzf _ _ W)]. Qed.

(* one step keeps the invariant and has the shape of SIDefs.astep_shape *)
Definition go_ok (src: list Z) (a: ast) (o: aout) : Prop :=
  match o with
  | AGo n w a' => awfx src a' /\ a_q a <= n /\ a_q a' = n /\
      (a_O a' = a_O a \/ (w = true /\ exists b, a_O a' = a_O a ++ [b]))
  | AEnd _ => True
  end.

(* the step from a state of mode md *)
Definition case_ok (md: Z) : Prop :=
  forall src a, awfx src a -> a_mode a = md -> go_ok src a (astep lenfix_list distfix_list src a).

Ltac mdc := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Model.TYPE TYPEDO STORED COPY_ COPY
  TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in *.

(* a contradiction between facts about the mode (all other hypotheses are cleared first) *)
Ltac md_absurd :=
  exfalso;
  repeat match goal with
         | H: ?T |- _ =>
             lazymatch T with
             | context [i_mode _] => fail
             | context [a_mode _] => fail
             | _ => clear H
             end
         end;
  unfold decode_mode, hdr_mode, data_mode, win_mode, post_mode in *; mdc; lia.

(* ---------------------------------------------------------------------------------------------- *)
(* The input's bits                                                                               *)

Lemma sbits_range: forall src q n, 0 <= n -> 0 <= sbits src q n < 2 ^ n.
Proof. intros. unfold sbits. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma Znth_bytes: forall l i, bytes_ok l -> 0 <= Znth i l <= 255.
Proof.
  intros l i B. destruct (zlt i 0); [rewrite Znth_underflow by lia; compute; split; congruence|].
  destruct (zlt i (Zlength l)); [|rewrite Znth_overflow by lia; compute; split; congruence].
  pose proof (proj1 (Forall_Znth _ _) B i ltac:(lia)) as H. cbv beta in H. rep_lia.
Qed.

Lemma sbyte_range: forall src q, bytes_ok src -> 0 <= sbyte src q <= 255.
Proof. intros src q B. apply Znth_bytes; auto. Qed.

Lemma bytes_app1: forall l b, bytes_ok l -> 0 <= b <= 255 -> bytes_ok (l ++ [b]).
Proof. intros l b B H. apply Forall_app. split; [auto | constructor; [rep_lia | constructor]]. Qed.

Lemma align8_ge: forall q, q <= align8 q.
Proof. intros q. unfold align8. pose proof (Z.mod_pos_bound (q + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (q + 7) 8 ltac:(lia)). lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The tables                                                                                     *)

Lemma tab_entry_codes: forall fx dx s s' t, i_codes s = i_codes s' -> tab_entry fx dx s t = tab_entry fx dx s' t.
Proof. intros fx dx s s' t E. unfold tab_entry. rewrite E. reflexivity. Qed.

Lemma tvalid_codes: forall kind fx dx s s' t nb, i_codes s = i_codes s' ->
  tvalid kind fx dx s t nb -> tvalid kind fx dx s' t nb.
Proof. intros kind fx dx s s' t nb E. unfold tvalid, tvalid_b. rewrite (tab_entry_codes fx dx s s' t E). auto. Qed.

Lemma tvalid_len_codes: forall fx dx s s' t nb, i_codes s = i_codes s' ->
  tvalid_len fx dx s t nb -> tvalid_len fx dx s' t nb.
Proof. intros fx dx s s' t nb E. unfold tvalid_len, tvalid_b. rewrite (tab_entry_codes fx dx s s' t E). auto. Qed.

Lemma adecode_codes: forall fx dx src s s' t nb lk q, i_codes s = i_codes s' ->
  adecode fx dx src s t nb lk q = adecode fx dx src s' t nb lk q.
Proof. intros. unfold adecode. rewrite (tab_entry_codes fx dx s s' t H). reflexivity. Qed.

Lemma len_islink_eq: forall op, len_islink op = islink LENS op.
Proof. intros. reflexivity. Qed.

Lemma dist_islink_eq: forall op, dist_islink op = islink DISTS op.
Proof. intros. reflexivity. Qed.

(* the table walk on a valid table ends at a final entry, after at most 15 bits *)
Lemma adecode_final: forall kind fx dx src s t nb q,
  tvalid kind fx dx s t nb ->
  let r := adecode fx dx src s t nb (islink kind) q in
  entry_ok (fst r) /\ final_ok kind (fst r) /\ islink kind (e_op (fst r)) = false /\ 0 <= snd r <= 15.
Proof.
  intros kind fx dx src s t nb q (sz & _ & [RB SZ ROOT]). cbv zeta. unfold adecode.
  pose proof (sbits_range src q nb ltac:(lia)) as I.
  destruct (ROOT _ I) as [EO R]. cbv zeta in R.
  set (here := tab_entry fx dx s t (sbits src q nb)) in *.
  destruct (islink kind (e_op here)) eqn:L.
  - destruct R as (B & O1 & O2 & J).
    pose proof (sbits_range src (q + e_bits here) (e_op here) ltac:(lia)) as I2.
    destruct (J _ I2) as (_ & E2 & L2 & B2 & F2). cbn [fst snd].
    split; [auto|]. split; [auto|]. split; [auto|]. destruct E2 as (_ & [? ?] & _). lia.
  - cbn [fst snd]. destruct R as [B F]. split; [auto|]. split; [auto|]. split; [auto|].
    destruct EO as (_ & [? ?] & _). lia.
Qed.

(* every entry the walk may reach has the property P (all entries of the table's region) *)
Lemma adecode_prop: forall kind fx dx src s t nb sz q (P: entry -> Prop),
  tvalid_b kind fx dx s t nb sz -> (forall i, 0 <= i < sz -> P (tab_entry fx dx s t i)) ->
  P (fst (adecode fx dx src s t nb (islink kind) q)).
Proof.
  intros kind fx dx src s t nb sz q P [RB SZ ROOT] HP. unfold adecode.
  pose proof (sbits_range src q nb ltac:(lia)) as I.
  destruct (ROOT _ I) as [EO R]. cbv zeta in R.
  set (here := tab_entry fx dx s t (sbits src q nb)) in *.
  destruct (islink kind (e_op here)) eqn:L; cbn [fst].
  - destruct R as (B & O1 & O2 & J).
    pose proof (sbits_range src (q + e_bits here) (e_op here) ltac:(lia)) as I2.
    destruct (J _ I2) as (R2 & _). apply HP; auto.
  - apply HP. lia.
Qed.

(* the code length code's walk (no links): the root entry *)
Lemma adecode_nolink: forall fx dx src s t nb q,
  adecode fx dx src s t nb no_link q =
  (tab_entry fx dx s t (sbits src q nb), e_bits (tab_entry fx dx s t (sbits src q nb))).
Proof. intros. reflexivity. Qed.

Lemma tvalid_root_ok: forall kind fx dx s t nb i, tvalid kind fx dx s t nb -> 0 <= i < 2 ^ nb ->
  entry_ok (tab_entry fx dx s t i).
Proof. intros kind fx dx s t nb i (sz & _ & [RB SZ ROOT]) I. apply (ROOT i I). Qed.

Lemma tvalid_nb: forall kind fx dx s t nb, tvalid kind fx dx s t nb -> 1 <= nb <= 15.
Proof. intros kind fx dx s t nb (sz & _ & [RB _ _]). exact RB. Qed.

(* the fixed tables *)
Lemma tvalid_b_distfix: forall s, tvalid_b DISTS lenfix_list distfix_list s TDistfix 5 32.
Proof.
  intros s. unfold tvalid_b. simpl tab_entry. rewrite <- FixedValid2.distfix_len.
  apply FixedValid2.tab_nolinks_valid; [lia | rewrite FixedValid2.distfix_len; reflexivity |
                                        exact FixedValid2.distfix_ok].
Qed.

Lemma tvalid_fixed: forall s,
  tvalid LENS lenfix_list distfix_list s TLenfix 9 /\ tvalid DISTS lenfix_list distfix_list s TDistfix 5 /\
  tvalid_len lenfix_list distfix_list s TLenfix 9.
Proof.
  intros s. destruct (FixedValid2.tvalid_fixed2 s) as [A B]. split; [exact A|]. split; [exact B|].
  destruct (FixedValid2.lvalid_fixed s) as (sz & X & Y & Z).
  exists sz. split; [exact X|]. split; [exact Y|].
  intros i Hi. specialize (Z i Hi). unfold Inv2.len_ok. intros Hop. specialize (Z Hop). lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Building the invariant                                                                         *)

Lemma awfx_intro: forall src s n O,
  bytes_ok src -> swf s -> modewf s -> swf3 s -> tpre_ok s ->
  i_wbits s = 15 -> (i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) ->
  i_havedict s = 0 -> i_head s = false -> HEAD <= i_mode s <= BAD ->
  (i_mode s = MATCH -> i_offset s <= 32768) ->
  (i_mode s = DISTEXT -> i_offset s + 2 ^ i_extra s - 1 <= 32768) ->
  (decode_mode (i_mode s) -> forall src' q,
    dist_ok (fst (adecode lenfix_list distfix_list src' s (i_distcode s) (i_distbits s) dist_islink q))) ->
  0 <= n -> bytes_ok O -> (hdr_mode (i_mode s) -> O = []) ->
  (data_mode (i_mode s) -> i_wrap s <> 0 ->
     (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)) ->
  i_back s <= 15 -> (TIME <= i_mode s <= HCRC -> i_flags s <> 0) ->
  awfx src (AS s n O).
Proof. intros. constructor; [constructor | ..]; simpl; auto. Qed.

(* a state whose mode needs nothing of the tables nor of the code lengths *)
Lemma awfx_plain: forall src s n O,
  bytes_ok src -> swf s -> Step3Block.plain_md (i_mode s) -> i_mode s <> HEAD ->
  i_wbits s = 15 -> (i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) ->
  i_havedict s = 0 -> i_head s = false -> HEAD <= i_mode s <= BAD ->
  0 <= n -> bytes_ok O -> (hdr_mode (i_mode s) -> O = []) ->
  (data_mode (i_mode s) -> i_wrap s <> 0 ->
     (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)) ->
  i_back s <= 15 -> (TIME <= i_mode s <= HCRC -> i_flags s <> 0) ->
  awfx src (AS s n O).
Proof.
  intros src s n O B S P NH. intros.
  pose proof P as [P1 [P2 P3]].
  assert (ND: forall md, i_mode s = md -> decode_mode md -> False)
    by (intros md E D; apply P3; rewrite E; exact D).
  apply awfx_intro; auto.
  - apply Step3Block.modewf_plain; auto.
  - constructor; intros; try contradiction; exfalso; eapply ND; eauto; unfold decode_mode; tauto.
  - split; intros; try contradiction; exfalso; apply P3; auto.
  - intros E; exfalso; eapply ND; eauto; unfold decode_mode; tauto.
  - intros E; exfalso; eapply ND; eauto; unfold decode_mode; tauto.
  - intros D; exfalso; apply P3; auto.
Qed.

(* the step to BAD with the state s (the fields the step set before the test) *)
Lemma awfx_bad: forall src s n O,
  bytes_ok src -> swf s -> i_wbits s = 15 -> (i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) ->
  i_havedict s = 0 -> i_head s = false -> i_back s <= 15 -> 0 <= n -> bytes_ok O ->
  awfx src (AS (set_i_mode s BAD) n O).
Proof.
  intros. apply awfx_plain; simpl; auto.
  all: try (unfold hdr_mode, data_mode, decode_mode; mdc; lia).
  - destruct H0; constructor; simpl; auto; mdc; lia.
  - unfold Step3Block.plain_md, decode_mode; mdc; lia.
Qed.

(* the facts of awfx, by name *)
Lemma ax_src: forall src a, awfx src a -> bytes_ok src. Proof. intros src a [[] _ _]; auto. Qed.
Lemma ax_swf: forall src a, awfx src a -> swf (a_s a). Proof. intros src a [[] _ _]; auto. Qed.
Lemma ax_md: forall src a, awfx src a -> modewf (a_s a). Proof. intros src a [[] _ _]; auto. Qed.
Lemma ax_s3: forall src a, awfx src a -> swf3 (a_s a). Proof. intros src a [[] _ _]; auto. Qed.
Lemma ax_tp: forall src a, awfx src a -> tpre_ok (a_s a). Proof. intros src a [[] _ _]; auto. Qed.
Lemma ax_frame: forall src a, awfx src a ->
  i_wbits (a_s a) = 15 /\ (i_wrap (a_s a) = 0 \/ i_wrap (a_s a) = 5 \/ i_wrap (a_s a) = 6 \/ i_wrap (a_s a) = 7) /\
  i_havedict (a_s a) = 0 /\ i_head (a_s a) = false /\ i_back (a_s a) <= 15 /\ 0 <= a_q a /\ bytes_ok (a_O a).
Proof. intros src a [[] ? _]; repeat split; auto. Qed.

(* the step to BAD from a (abad) *)
Lemma go_abad: forall src a n, awfx src a -> a_q a <= n -> go_ok src a (abad a n).
Proof.
  intros src a n W Q. destruct (ax_frame _ _ W) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
  unfold abad, go_ok. simpl. split; [|split; [lia | split; [auto | left; auto]]].
  apply awfx_bad; auto; [eapply ax_src; eauto | eapply ax_swf; eauto | lia].
Qed.

(* a step that only changes the state (ago) *)
Lemma go_ago: forall src a n s, awfx src (AS s n (a_O a)) -> a_q a <= n -> go_ok src a (ago a n s).
Proof. intros. unfold ago, go_ok. simpl. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The decode modes: tables given                                                                 *)

Lemma awfx_decode: forall src s n O,
  bytes_ok src -> swf s -> decode_mode (i_mode s) ->
  tvalid LENS lenfix_list distfix_list s (i_lencode s) (i_lenbits s) ->
  tvalid DISTS lenfix_list distfix_list s (i_distcode s) (i_distbits s) ->
  tvalid_len lenfix_list distfix_list s (i_lencode s) (i_lenbits s) ->
  trep (tab_entry lenfix_list distfix_list s (i_lencode s)) (i_lenbits s) len_islink ->
  trep (tab_entry lenfix_list distfix_list s (i_distcode s)) (i_distbits s) dist_islink ->
  (forall src' q, dist_ok (fst (adecode lenfix_list distfix_list src' s (i_distcode s) (i_distbits s) dist_islink q))) ->
  (i_mode s = LENEXT -> i_extra s <= 5 /\ i_length s <= 258) ->
  (i_mode s = DISTEXT -> i_extra s <= 13) ->
  (i_mode s = MATCH -> 1 <= i_length s) ->
  (i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT -> 1 <= i_length s) ->
  (i_mode s = DISTEXT \/ i_mode s = MATCH -> 1 <= i_offset s) ->
  (i_mode s = MATCH -> i_offset s <= 32768) ->
  (i_mode s = DISTEXT -> i_offset s + 2 ^ i_extra s - 1 <= 32768) ->
  i_wbits s = 15 -> (i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) ->
  i_havedict s = 0 -> i_head s = false -> i_back s <= 15 ->
  (i_wrap s <> 0 -> (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)) ->
  0 <= n -> bytes_ok O ->
  awfx src (AS s n O).
Proof.
  intros src s n O B S D TL TD TLL RL RD DO LX DX MA LN OF MO DE W1 W2 W3 W4 BK CK N BO.
  assert (DM: HEAD <= i_mode s <= BAD) by (unfold decode_mode in D; mdc; lia).
  apply awfx_intro; auto.
  all: try (intros _; apply CK).
  all: try (intros H; md_absurd).
  - constructor; intros; auto; try md_absurd.
    + apply LX; auto.
    + repeat split; intros; lia.
  - constructor; intros; auto; try md_absurd.
    + apply LX; auto.
    + specialize (DE H). pose proof (Z.pow_pos_nonneg 2 (i_extra s) ltac:(lia) ltac:(destruct S; lia)). lia.
  - split; intros; auto. md_absurd.
Qed.

(* a decode state to another with the same tables and frame *)
Lemma awfx_decode_keep: forall src a s n O,
  awfx src a -> decode_mode (a_mode a) -> swf s -> decode_mode (i_mode s) ->
  i_codes s = i_codes (a_s a) -> i_lencode s = i_lencode (a_s a) -> i_distcode s = i_distcode (a_s a) ->
  i_lenbits s = i_lenbits (a_s a) -> i_distbits s = i_distbits (a_s a) ->
  i_wbits s = i_wbits (a_s a) -> i_wrap s = i_wrap (a_s a) -> i_havedict s = i_havedict (a_s a) ->
  i_head s = i_head (a_s a) -> i_back s = i_back (a_s a) -> i_flags s = i_flags (a_s a) ->
  i_check s = i_check (a_s a) ->
  (i_mode s = LENEXT -> i_extra s <= 5 /\ i_length s <= 258) ->
  (i_mode s = DISTEXT -> i_extra s <= 13) ->
  (i_mode s = MATCH -> 1 <= i_length s) ->
  (i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT -> 1 <= i_length s) ->
  (i_mode s = DISTEXT \/ i_mode s = MATCH -> 1 <= i_offset s) ->
  (i_mode s = MATCH -> i_offset s <= 32768) ->
  (i_mode s = DISTEXT -> i_offset s + 2 ^ i_extra s - 1 <= 32768) ->
  0 <= n -> bytes_ok O ->
  awfx src (AS s n O).
Proof.
  intros src a s n O W D S D' C1 C2 C3 C4 C5 F1 F2 F3 F4 F5 F6 F7. intros.
  destruct W as [W0 BK GZ]. unfold a_mode in *.
  destruct (md_tables _ (aw_md _ _ W0) D) as [TL TD].
  pose proof (s3_len _ (aw_s3 _ _ W0) D) as TLL. destruct (proj1 (aw_tp _ _ W0) D) as [RL RD].
  assert (X1: i_wbits s = 15) by (rewrite F1; apply (aw_wbits _ _ W0)).
  assert (X2: i_wrap s = 0 \/ i_wrap s = 5 \/ i_wrap s = 6 \/ i_wrap s = 7) by (rewrite F2; apply (aw_wrap _ _ W0)).
  assert (X3: i_havedict s = 0) by (rewrite F3; apply (aw_dict _ _ W0)).
  assert (X4: i_head s = false) by (rewrite F4; apply (aw_head _ _ W0)).
  assert (X5: i_back s <= 15) by (rewrite F5; exact BK).
  assert (X6: i_wrap s <> 0 -> (i_flags s = 0 /\ i_check s = 1) \/ (i_flags s <> 0 /\ i_check s = 0)).
  { intros NZ. rewrite F6, F7. apply (aw_chk _ _ W0); [unfold data_mode, a_mode; tauto | congruence]. }
  apply awfx_decode; auto.
  - apply (aw_src _ _ W0).
  - rewrite C2, C4. apply tvalid_codes with (a_s a); auto.
  - rewrite C3, C5. apply tvalid_codes with (a_s a); auto.
  - rewrite C2, C4. apply tvalid_len_codes with (a_s a); auto.
  - rewrite C2, C4, (tab_entry_codes _ _ s (a_s a) _ C1). auto.
  - rewrite C3, C5, (tab_entry_codes _ _ s (a_s a) _ C1). auto.
  - intros src' q. rewrite C3, C5, (adecode_codes _ _ _ s (a_s a) _ _ _ _ C1). apply (aw_dtab _ _ W0); auto.
Qed.

(* the equations of astep, one per mode *)
Section AstepEq.
Variables (src: list Z) (a: ast).
Local Ltac ae := intros E; unfold astep; rewrite E; reflexivity.
Lemma astep_HEAD: a_mode a = HEAD -> astep lenfix_list distfix_list src a = a_HEAD src a. Proof. ae. Qed.
Lemma astep_FLAGS: a_mode a = FLAGS -> astep lenfix_list distfix_list src a = a_FLAGS src a. Proof. ae. Qed.
Lemma astep_TIME: a_mode a = TIME -> astep lenfix_list distfix_list src a = a_TIME src a. Proof. ae. Qed.
Lemma astep_OS: a_mode a = OS -> astep lenfix_list distfix_list src a = a_OS src a. Proof. ae. Qed.
Lemma astep_EXLEN: a_mode a = EXLEN -> astep lenfix_list distfix_list src a = a_EXLEN src a. Proof. ae. Qed.
Lemma astep_EXTRA: a_mode a = EXTRA -> astep lenfix_list distfix_list src a = a_EXTRA src a. Proof. ae. Qed.
Lemma astep_NAME: a_mode a = NAME -> astep lenfix_list distfix_list src a = a_NAME src a. Proof. ae. Qed.
Lemma astep_COMMENT: a_mode a = COMMENT -> astep lenfix_list distfix_list src a = a_COMMENT src a. Proof. ae. Qed.
Lemma astep_HCRC: a_mode a = HCRC -> astep lenfix_list distfix_list src a = a_HCRC src a. Proof. ae. Qed.
Lemma astep_DICTID: a_mode a = DICTID -> astep lenfix_list distfix_list src a = a_DICTID src a. Proof. ae. Qed.
Lemma astep_DICT: a_mode a = DICT -> astep lenfix_list distfix_list src a = a_DICT a. Proof. ae. Qed.
Lemma astep_TYPE: a_mode a = Model.TYPE -> astep lenfix_list distfix_list src a = a_TYPE a. Proof. ae. Qed.
Lemma astep_TYPEDO: a_mode a = TYPEDO -> astep lenfix_list distfix_list src a = a_TYPEDO src a. Proof. ae. Qed.
Lemma astep_STORED: a_mode a = STORED -> astep lenfix_list distfix_list src a = a_STORED src a. Proof. ae. Qed.
Lemma astep_COPY_: a_mode a = COPY_ -> astep lenfix_list distfix_list src a = a_COPY_ a. Proof. ae. Qed.
Lemma astep_COPY: a_mode a = COPY -> astep lenfix_list distfix_list src a = a_COPY src a. Proof. ae. Qed.
Lemma astep_TABLE: a_mode a = TABLE -> astep lenfix_list distfix_list src a = a_TABLE src a. Proof. ae. Qed.
Lemma astep_LENLENS: a_mode a = LENLENS -> astep lenfix_list distfix_list src a = a_LENLENS src a. Proof. ae. Qed.
Lemma astep_CODELENS: a_mode a = CODELENS ->
  astep lenfix_list distfix_list src a = a_CODELENS lenfix_list distfix_list src a. Proof. ae. Qed.
Lemma astep_LEN_: a_mode a = LEN_ -> astep lenfix_list distfix_list src a = a_LEN_ a. Proof. ae. Qed.
Lemma astep_LEN: a_mode a = LEN -> astep lenfix_list distfix_list src a = a_LEN lenfix_list distfix_list src a.
Proof. ae. Qed.
Lemma astep_LENEXT: a_mode a = LENEXT -> astep lenfix_list distfix_list src a = a_LENEXT src a. Proof. ae. Qed.
Lemma astep_DIST: a_mode a = DIST -> astep lenfix_list distfix_list src a = a_DIST lenfix_list distfix_list src a.
Proof. ae. Qed.
Lemma astep_DISTEXT: a_mode a = DISTEXT -> astep lenfix_list distfix_list src a = a_DISTEXT src a. Proof. ae. Qed.
Lemma astep_MATCH: a_mode a = MATCH -> astep lenfix_list distfix_list src a = a_MATCH a. Proof. ae. Qed.
Lemma astep_LIT: a_mode a = LIT -> astep lenfix_list distfix_list src a = a_LIT a. Proof. ae. Qed.
Lemma astep_CHECK: a_mode a = CHECK -> astep lenfix_list distfix_list src a = a_CHECK src a. Proof. ae. Qed.
Lemma astep_LENGTH: a_mode a = LENGTH -> astep lenfix_list distfix_list src a = a_LENGTH src a. Proof. ae. Qed.
End AstepEq.
