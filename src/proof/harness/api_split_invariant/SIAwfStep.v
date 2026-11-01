(* The abstract invariant awfx (SIAwfKit.v) at the start (after inflateInit2 with the law's four windows)
   and after every step of the abstract decoder: the cases of SIAwfHdr/Blk/LL/CL/Dec.v, by mode. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfKit.
Require Import Zlib.proof.harness.api_split_invariant.SIAwfHdr Zlib.proof.harness.api_split_invariant.SIAwfBlk
  Zlib.proof.harness.api_split_invariant.SIAwfLL Zlib.proof.harness.api_split_invariant.SIAwfCL
  Zlib.proof.harness.api_split_invariant.SIAwfDec.
Require Zlib.proof.inflate.Step3Block.
Import ListNotations.
Local Open Scope Z_scope.

(* every step keeps awfx and has the shape of astep_shape *)
Lemma awfx_go: tabrep_stmt -> forall src a, awfx src a -> go_ok src a (astep lenfix_list distfix_list src a).
Proof.
  intros TR src a W.
  pose proof (aw_mode _ _ (ax_w _ _ W)) as MR.
  assert (C: a_mode a = HEAD \/ a_mode a = FLAGS \/ a_mode a = TIME \/ a_mode a = OS \/ a_mode a = EXLEN \/
    a_mode a = EXTRA \/ a_mode a = NAME \/ a_mode a = COMMENT \/ a_mode a = HCRC \/ a_mode a = DICTID \/
    a_mode a = DICT \/ a_mode a = Model.TYPE \/ a_mode a = TYPEDO \/ a_mode a = STORED \/ a_mode a = COPY_ \/
    a_mode a = COPY \/ a_mode a = TABLE \/ a_mode a = LENLENS \/ a_mode a = CODELENS \/ a_mode a = LEN_ \/
    a_mode a = LEN \/ a_mode a = LENEXT \/ a_mode a = DIST \/ a_mode a = DISTEXT \/ a_mode a = MATCH \/
    a_mode a = LIT \/ a_mode a = CHECK \/ a_mode a = LENGTH \/ a_mode a = DONE \/ a_mode a = BAD)
    by (clear -MR; mdc; lia).
  repeat destruct C as [C | C].
  - apply awf_HEAD; auto.
  - apply awf_FLAGS; auto.
  - apply awf_TIME; auto.
  - apply awf_OS; auto.
  - apply awf_EXLEN; auto.
  - apply awf_EXTRA; auto.
  - apply awf_NAME; auto.
  - apply awf_COMMENT; auto.
  - apply awf_HCRC; auto.
  - apply awf_DICTID; auto.
  - apply awf_DICT; auto.
  - apply awf_TYPE; auto.
  - apply awf_TYPEDO; auto.
  - apply awf_STORED; auto.
  - apply awf_COPY_; auto.
  - apply awf_COPY; auto.
  - apply awf_table; auto.
  - apply awf_lenlens; auto.
  - apply awf_codelens; auto.
  - apply awf_LEN_; auto.
  - apply awf_LEN; auto.
  - apply awf_LENEXT; auto.
  - apply awf_DIST; auto.
  - apply awf_DISTEXT; auto.
  - apply awf_MATCH; auto.
  - apply awf_LIT; auto.
  - apply awf_CHECK; auto.
  - apply awf_LENGTH; auto.
  - unfold astep. rewrite C. simpl. exact I.
  - unfold astep. rewrite C. simpl. exact I.
Qed.

(* the state after inflateInit2: zero_s through inflateReset2 *)
Lemma Forall_Zrepeat: forall {A} (P: A -> Prop) x n, P x -> Forall P (Zrepeat x n).
Proof.
  intros A P x n H. unfold Zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. subst; auto.
Qed.

Local Arguments Zrepeat : simpl never.

Lemma init_s_awfx: forall src wrap, bytes_ok src -> (wrap = 0 \/ wrap = 5 \/ wrap = 6 \/ wrap = 7) ->
  awfx src (AS (init_s wrap 15) 0 []).
Proof.
  intros src wrap B Hw.
  (* with windowBits 15 inflateReset2 keeps wrap (no bit 3) and the window, so init_s is a plain reset *)
  assert (E: init_s wrap 15 = reset_s (set_i_wbits (set_i_wrap zero_s wrap) 15)).
  { unfold init_s, reset2_s, reset_full_s, reset_hdr_s, reset2_wrap. cbn.
    destruct Hw as [-> | [-> | [-> | ->]]]; reflexivity. }
  rewrite E.
  assert (S: swf (reset_s (set_i_wbits (set_i_wrap zero_s wrap) 15))).
  { constructor; cbn; unfold srange, urange, lrange, tref_ok, ENOUGH_CODES; try rep_lia; auto.
    all: try (clear; mdc; lia).
    all: try (split; [apply Zlength_Zrepeat; lia | apply Forall_Zrepeat; lia]).
    all: try (split; [apply Zlength_Zrepeat; lia | apply Forall_Zrepeat; unfold entry_ok; simpl; lia]).
    all: try (split; [reflexivity | constructor]). }
  apply awfx_intro; cbn; auto; try (clear; mdc; lia).
  all: try (apply Step3Block.modewf_plain; cbn; unfold Step3Block.plain_md, decode_mode; clear; mdc; lia).
  all: try (constructor; cbn; intros; try lia; exfalso; clear -H; unfold decode_mode in H; mdc; lia).
  all: try (split; cbn; intros H; exfalso; clear -H; unfold decode_mode in H; mdc; lia).
  all: try (intros H; exfalso; clear -H; unfold data_mode, hdr_mode, decode_mode in H; mdc; lia).
  all: try constructor.
Qed.

Lemma a0_awfx: forall w src, si_window w -> bytes_ok src -> awfx src (a0 w).
Proof.
  intros w src Hw B. unfold a0, init_live.
  destruct Hw as [-> | [-> | [-> | ->]]]; cbn [reset2_wb]; simpl l_s.
  all: apply init_s_awfx; auto.
Qed.
