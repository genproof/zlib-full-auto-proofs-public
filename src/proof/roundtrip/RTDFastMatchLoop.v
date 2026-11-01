(** * RT-D part FAST, piece MATCH: the insertion loop of deflate_fast's match branch, functionally.
    The safety version is RTDLTCFastKit.insloop_stmt (proved: RTDLTCFastInsLoop.insloop_ok from ins_ok); the
    hypotheses here are those of insloop_stmt plus the functional ones: the chains are hash-consistent
    ([chain_hok]) and ins_h is primed for strstart + 1 at the start; the loop keeps both, INSERT_STRING at each
    p = strstart (after strstart++) by [ins_fspec2]. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFastKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(* wpos reads lookahead, strstart, window_size, block_start, insert, high_water, w_size: all kept by il_keep but
   strstart *)
Lemma fil_wpos a s x : il_keep a = il_keep s -> wpos (set_d_strstart s x) -> wpos (set_d_strstart a x).
Proof.
  intros Pk W.
  assert (E1 : d_lookahead a = d_lookahead s) by exact (f_equal d_lookahead Pk).
  assert (E2 : d_window_size a = d_window_size s) by exact (f_equal d_window_size Pk).
  assert (E3 : d_block_start a = d_block_start s) by exact (f_equal d_block_start Pk).
  assert (E4 : d_insert a = d_insert s) by exact (f_equal d_insert Pk).
  assert (E5 : d_high_water a = d_high_water s) by exact (f_equal d_high_water Pk).
  assert (E6 : d_w_size a = d_w_size s) by exact (f_equal d_w_size Pk).
  unfold wpos, MAX_DIST in *. autorewrite with fproj in *.
  rewrite E1, E2, E3, E4, E5, E6. exact W.
Qed.

(* chain_hok survives strstart++ (lim and the data end strstart + lookahead only grow) *)
Lemma fil_hok_ss a x : chain_hok a -> d_strstart a <= x -> chain_hok (set_d_strstart a x).
Proof.
  intros H Hx b Hb.
  destruct (H b Hb) as (Gb & H0 & H1). exists Gb. split; [exact H0|].
  intros q Gq q0 ql.
  assert (Hl : lim a <= lim (set_d_strstart a x)) by (apply mt_lim_mono; autorewrite with fproj; [reflexivity|lia]).
  destruct (H1 q Gq q0 ltac:(lia)) as (A & B & C).
  split; [autorewrite with fproj; lia|]. split; [exact B|exact C].
Qed.

Definition filP (s : dstate) (l : Z) (a : dstate) : Prop :=
  ilP s l a /\ chain_hok a /\ primed a (d_strstart a + 1).

Definition filQ (s : dstate) (l : Z) (r : dstate) : Prop :=
  ilQ s l r /\ chain_hok r /\ primed r (d_strstart r + 1).

Lemma fil_loop_fok : ins_fspec2 -> forall s l G a,
  prm s -> wstruct s -> chain_with s (d_strstart s + 1) l G ->
  1 <= d_match_length s -> 0 <= d_strstart s -> d_strstart s + d_match_length s < 65536 ->
  d_strstart s + d_match_length s + 2 < Zlength (mb_val (d_window s)) ->
  (forall i, 0 <= i <= d_strstart s + d_match_length s + 2 -> Znth i (mb_def (d_window s)) = true) ->
  d_strstart s + d_match_length s - d_w_size s < l ->
  l <= lim s -> 3 <= d_lookahead s ->
  (forall p, d_strstart s <= p <= d_strstart s + d_match_length s -> wpos (set_d_strstart s p)) ->
  chain_hok s -> primed s (d_strstart s + 1) ->
  loop FUEL df_insert_body s = Some a ->
  chain_hok a /\ primed a (d_strstart a + 1).
Proof.
  intros Hf s l G a0 Hp Hw Hc Hk H0 H64 Hlen Hdef Hl Hll H3 Hwp0 Hhok Hpr Ea.
  pose proof Zlib.proof.roundtrip.RTDLTCLmKit.ins_ok as Hins.
  assert (Hwin : forall a, il_keep a = il_keep s -> d_window a = d_window s)
    by (intros a E; exact (f_equal d_window E)).
  assert (Hws : forall a, il_keep a = il_keep s -> d_w_size a = d_w_size s)
    by (intros a E; exact (f_equal d_w_size E)).
  assert (Hla : forall a, il_keep a = il_keep s -> d_lookahead a = d_lookahead s)
    by (intros a E; exact (f_equal d_lookahead E)).
  assert (Hwp : 0 < d_w_size s).
  { destruct Hp as (Hb & Hp2 & _). rewrite Hp2. apply Z.pow_pos_nonneg; lia. }
  destruct (il_loop_measure df_insert_body (filP s l) (filQ s l) d_match_length) with (d := FUEL) (a := s)
    as [r [Er HQ]].
  - intros a ((Pp & Pw & Pk & P1 & P2 & P3 & Ga & Pc) & Phok & Ppr). split; [lia|].
    set (a1 := set_d_strstart a (d_strstart a + 1)).
    destruct (Hins a1 (d_strstart a + 1) (d_strstart a + 1) l Ga) as (s2 & h & E2 & K2 & W2 & _ & C2 & _).
    + apply il_prm_ss; exact Pp.
    + apply il_wstruct_ss; exact Pw.
    + apply il_chain_ss; exact Pc.
    + lia.
    + unfold a1. change (d_window (set_d_strstart a (d_strstart a + 1))) with (d_window a).
      rewrite (Hwin a Pk). lia.
    + unfold a1. change (d_window (set_d_strstart a (d_strstart a + 1))) with (d_window a).
      rewrite (Hwin a Pk). apply Hdef. lia.
    + unfold a1. change (d_w_size (set_d_strstart a (d_strstart a + 1))) with (d_w_size a).
      rewrite (Hws a Pk). lia.
    + unfold a1. change (d_w_size (set_d_strstart a (d_strstart a + 1))) with (d_w_size a).
      rewrite (Hws a Pk). lia.
    + assert (Ess : d_strstart s2 = d_strstart a + 1) by (exact (f_equal d_strstart K2)).
      assert (Eml : d_match_length s2 = d_match_length a) by (exact (f_equal d_match_length K2)).
      (* the functional facts of this INSERT_STRING *)
      assert (Hlim1 : lim s <= lim a1).
      { apply mt_lim_mono; unfold a1; autorewrite with fproj; [exact (Hws a Pk)|lia]. }
      destruct (Hf a1 (d_strstart a + 1) s2 h) as (_ & _ & Hhok2 & Hpr2).
      * apply il_prm_ss; exact Pp.
      * apply il_wstruct_ss; exact Pw.
      * unfold a1. apply (fil_wpos a s _ Pk). apply Hwp0. lia.
      * exists Ga. apply (mt_chain_mono a1 (d_strstart a + 1) _ l _ Ga); [exact Pc|unfold a1; autorewrite with fproj; lia|lia].
      * unfold a1. apply fil_hok_ss; [exact Phok|lia].
      * exact Ppr.
      * unfold a1; autorewrite with fproj; lia.
      * unfold a1; autorewrite with fproj. rewrite (Hws a Pk). lia.
      * unfold a1; autorewrite with fproj. rewrite (Hla a Pk). lia.
      * unfold a1 in *; autorewrite with fproj in *. rewrite (Hws a Pk). lia.
      * exact E2.
      * assert (Ebody : df_insert_body a =
                  if d_match_length a - 1 =? 0 then Some (inr (set_d_match_length s2 (d_match_length a - 1)))
                  else Some (inl (set_d_match_length s2 (d_match_length a - 1)))).
        { unfold df_insert_body. rewrite (il_u32_id (d_strstart a + 1)) by lia.
          fold a1. change (d_strstart a1) with (d_strstart a + 1). rewrite E2. cbn [bind].
          rewrite Eml, (il_u32_id (d_match_length a - 1)) by lia. reflexivity. }
        rewrite Z.max_r in C2 by lia.
        assert (Kk : il_keep (set_d_match_length s2 (d_match_length a - 1)) = il_keep s).
        { rewrite <- Pk. change (il_keep' (hc_keep s2) = il_keep' (hc_keep a1)). rewrite K2. reflexivity. }
        assert (Pp2 : prm s2) by (apply (il_prm_hc s2 a1 K2); apply il_prm_ss; exact Pp).
        assert (Hhok3 : chain_hok (set_d_match_length s2 (d_match_length a - 1))) by exact Hhok2.
        assert (Hpr3 : primed (set_d_match_length s2 (d_match_length a - 1))
                         (d_strstart (set_d_match_length s2 (d_match_length a - 1)) + 1)).
        { autorewrite with fproj. rewrite Ess. exact Hpr2. }
        rewrite Ebody. destruct (Z.eqb_spec (d_match_length a - 1) 0) as [Z0|Z0].
        -- left. eexists; split; [reflexivity|]. split; [|split; [exact Hhok3|exact Hpr3]]. unfold ilQ.
           split; [exact Kk|]. split; [apply il_wstruct_ml; exact W2|].
           change (d_strstart (set_d_match_length s2 (d_match_length a - 1))) with (d_strstart s2).
           change (d_match_length (set_d_match_length s2 (d_match_length a - 1))) with (d_match_length a - 1).
           split; [lia|]. split; [lia|].
           eexists. apply il_chain_ml. rewrite Ess. exact C2.
        -- right. eexists; split; [reflexivity|].
           change (d_match_length (set_d_match_length s2 (d_match_length a - 1))) with (d_match_length a - 1).
           split; [|lia]. split; [|split; [exact Hhok3|exact Hpr3]]. unfold ilP.
           change (d_strstart (set_d_match_length s2 (d_match_length a - 1))) with (d_strstart s2).
           change (d_match_length (set_d_match_length s2 (d_match_length a - 1))) with (d_match_length a - 1).
           split; [apply il_prm_ml; exact Pp2|]. split; [apply il_wstruct_ml; exact W2|].
           split; [exact Kk|]. split; [lia|]. split; [lia|]. split; [lia|].
           eexists. apply il_chain_ml. rewrite Ess. exact C2.
  - split; [|split; [exact Hhok|exact Hpr]].
    split; [exact Hp|]. split; [exact Hw|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
    split; [lia|]. exists G. exact Hc.
  - unfold FUEL. change (2 ^ Z.of_nat 40) with 1099511627776. lia.
  - rewrite Ea in Er. injection Er as Er. subst r. destruct HQ as (_ & Q1 & Q2). split; [exact Q1|exact Q2].
Qed.
