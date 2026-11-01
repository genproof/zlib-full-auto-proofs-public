(* Part of the decode theory: the passes from TABLE, LENLENS, CODELENS.  Definitions: DecodeDefs.v / Decode.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.rfc1951.DecTabKit Zlib.proof.rfc1951.DecTabTab Zlib.proof.rfc1951.DecTabLL
  Zlib.proof.rfc1951.DecTabIter Zlib.proof.rfc1951.DecTabCL.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dt_mwf3_unleave m : mwf3 (set_leave m) -> m_leave m = 0 -> mwf3 m.
Proof. intros [W S] L. split; [|exact S]. destruct W; constructor; auto; lia. Qed.

Lemma dt_kd_leave G pos inp ob m : Kd G pos inp ob m -> m_mode m <> DONE -> Kd G pos inp ob (set_leave m).
Proof.
  intros [] N. constructor; auto.
  unfold set_leave, m_mode in *. cbn [m_s m_ret m_leave set_m_leave] in *.
  replace (i_mode (m_s m) =? DONE) with false in * by (symmetry; apply Z.eqb_neq; exact N). exact kd_ret.
Qed.

Lemma dt_tin G pos inp ob m : Kd G pos inp ob m -> mwf3 m -> m_leave m = 0 -> tin G pos inp ob m.
Proof.
  intros K W L. destruct W as [W _].
  split; [exact K|]. split; [exact L|]. split.
  - pose proof (mw_nx _ W). rewrite (kd_inp _ _ _ _ _ K) in H. exact H.
  - pose proof (mw_s _ W) as S. split; [apply (sw_lens _ S)|]. apply (sw_codes _ S).
Qed.

Lemma dt_final (SM: stepf2_mwf3_stmt) (DEC: group_ok md_dec) G pos inp ob flush m P :
  dctx_ok G -> 0 <= pos -> pos + Zlength inp <= Zlength (dc_src G) ->
  inp = sublist pos (pos + Zlength inp) (dc_src G) ->
  mwf3 m -> m_leave m = 0 ->
  (forall fl, stepf2 fl lenfix_list distfix_list m = ttab_run fl P) ->
  tt_ok G pos inp ob (m_ow m) P ->
  dstep_post G pos inp ob flush m (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros OK P0 PL E W L SE O.
  rewrite SE. destruct P as [o|mX].
  - destruct o as [m'|r m']; [|destruct O].
    destruct O as (K & Ow & L1 & N & S). cbn [ttab_run dstep_post].
    split; [exact K|]. split; [exists []; rewrite app_nil_r; exact Ow|].
    intros _. right. left. split; assumption.
  - destruct O as (KX & Ow & LX & MX).
    pose proof (SM Z_TREES m W L) as WT. rewrite SE in WT. cbn [ttab_run] in WT.
    rewrite Z.eqb_refl in WT.
    pose proof (dt_mwf3_unleave mX WT LX) as WX.
    cbn [ttab_run]. destruct (Z.eqb_spec flush Z_TREES) as [EF|EF].
    + cbn [dstep_post]. split; [apply dt_kd_leave; [exact KX | rewrite MX; unfold LEN_, DONE; lia]|].
      split; [exists []; rewrite app_nil_r; exact Ow|].
      intros _. right. right. right. right. exact EF.
    + assert (EE: stepf2 flush lenfix_list distfix_list mX =
                  c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list) mX)
        by (unfold stepf2, step2; rewrite MX; reflexivity).
      assert (D: dstep_post G pos inp ob flush mX (stepf2 flush lenfix_list distfix_list mX))
        by (apply DEC; auto; rewrite MX; left; reflexivity).
      rewrite <- EE. destruct (stepf2 flush lenfix_list distfix_list mX) as [m'|r m']; [|destruct D].
      destruct D as (K' & (d & Ow') & LW). split; [exact K'|]. split; [|exact LW].
      exists d. rewrite Ow', Ow. reflexivity.
Qed.

(* the assembly, given the parts and the bound of the deflate stream *)
Lemma group_tab_of_parts :
  (forall G, dctx_ok G -> slen_ok G) -> part_tab_stmt -> part_ll_stmt -> part_iter_stmt -> part_cl_stmt ->
  dkit_stmt -> tabdec_stmt -> stepf2_mwf3_stmt -> group_ok md_dec -> group_ok md_tab.
Proof.
  intros SO PT PL PI PC DK TD SM DEC G pos inp ob flush m OK P0 PL0 E K W L Md.
  assert (C: ictx G pos inp) by (split; [exact OK|]; split; [exact P0|]; split; assumption).
  pose proof (SO G OK) as S.
  pose proof (dt_tin G pos inp ob m K W L) as T.
  assert (HCL: forall m', tin G pos inp ob m' -> m_mode m' = CODELENS -> m_ow m' = m_ow m ->
                 tt_ok G pos inp ob (m_ow m) (ttab_cl m')).
  { intros m' T' M' O'. rewrite <- O'. apply PC; auto. }
  assert (HLL: forall m', tin G pos inp ob m' -> m_mode m' = LENLENS -> m_ow m' = m_ow m ->
                 tt_ok G pos inp ob (m_ow m) (ttab_ll m')).
  { intros m' T' M' O'. rewrite <- O'. apply PL; auto. intros m'' T'' M'' O''. rewrite O'. apply HCL; auto. congruence. }
  unfold md_tab in Md. destruct Md as [H|[H|H]].
  - apply (dt_final SM DEC G pos inp ob flush m (ttab_tab m) OK P0 PL0 E W L).
    + intros fl. rewrite <- (ttab_tab_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply PT; auto.
  - apply (dt_final SM DEC G pos inp ob flush m (ttab_ll m) OK P0 PL0 E W L).
    + intros fl. rewrite <- (ttab_ll_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply HLL; auto.
  - apply (dt_final SM DEC G pos inp ob flush m (ttab_cl m) OK P0 PL0 E W L).
    + intros fl. rewrite <- (ttab_cl_eq fl m). unfold stepf2, step2. rewrite H. reflexivity.
    + apply HCL; auto.
Qed.

Lemma dt_slen_ok (DK: dkit_stmt) G : dctx_ok G -> slen_ok G.
Proof.
  intros OK. unfold slen_ok. pose proof (dk_slen DK G OK) as E.
  assert (0 <= trl_len (dc_w G)) by (unfold trl_len; destruct (dc_w G); lia). lia.
Qed.

Lemma group_tab : dkit_stmt -> tabdec_stmt -> stepf2_mwf3_stmt -> group_ok md_dec -> group_ok md_tab.
Proof.
  intros DK TD SM DEC.
  exact (group_tab_of_parts (dt_slen_ok DK) part_tab part_ll part_iter part_cl DK TD SM DEC).
Qed.
