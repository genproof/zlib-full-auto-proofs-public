(* Law inflate_codes, theory part: the gzip header cases FLAGS .. HCRC *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* what the cases keep from the loop head on: Kc, plus the facts the fallthroughs need *)
Record thd_H (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (m: mst) : Prop := {
  thd_kc : Kc wrap src pos inp aout m;
  thd_lv : m_leave m = 0;
  thd_nx : 0 <= m_nx m <= Zlength (m_inp m);
  thd_len : 0 <= i_length (m_s m);
  thd_ret : m_ret m = Z_OK;
  thd_bits : 0 <= m_bits m <= 31;
  thd_md : md_hdr (m_mode m) }.

Definition thd_P (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kc wrap src pos inp aout m' /\ (m_leave m' = 0 -> m_mode m' <> DICT)
  | IRet _ _ => False
  end.

Lemma thd_md_ne x : md_hdr x \/ x = Zlib.proof.inflate.Model.TYPE \/ x = BAD ->
  x <> SYNC /\ x <> DONE /\ x <> HEAD /\ x <> DICTID /\ x <> DICT /\ x <> MEM.
Proof.
  unfold md_hdr. intros H.
  repeat match type of H with _ \/ _ => destruct H as [H|H] end; subst x;
  unfold FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, BAD,
    SYNC, DONE, HEAD, DICTID, DICT, MEM; repeat split; lia.
Qed.

Lemma thd_Kc wrap src pos inp aout m m' :
  thd_H wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) -> m_out m' = m_out m -> m_ret m' = m_ret m -> m_nx m <= m_nx m' ->
  md_hdr (m_mode m') \/ m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = BAD ->
  (m_leave m' = 1 -> m_mode m' <> BAD) ->
  (m_mode m' = BAD -> m_msg m' <> None) ->
  (m_mode m' <> BAD -> 0 <= m_bits m' <= 31) ->
  thd_P wrap src pos inp aout (IBrk m').
Proof.
  intros Hh Hi Ha Hw Hhd Ho Hr Hn Hmd Hlv Hmsg Hb.
  destruct Hh as [K Hl Hnx Hlen Hret Hbits Hmd0].
  destruct (thd_md_ne _ Hmd) as (N1 & N2 & N3 & N4 & N5 & N6).
  cbn [thd_P]. split; [|intros _; exact N5].
  constructor.
  - rewrite Hi; apply (kc_inp _ _ _ _ _ _ K).
  - rewrite Ha; apply (kc_aout _ _ _ _ _ _ K).
  - rewrite Hw; apply (kc_wrap _ _ _ _ _ _ K).
  - rewrite Hhd; apply (kc_head _ _ _ _ _ _ K).
  - exact N1.
  - intros _ _. rewrite Hr. exact Hret.
  - intros L. split; [intros; contradiction|]. intros B. exfalso. apply (Hlv L B).
  - exact Hmsg.
  - intros B _. auto.
  - intros O. rewrite Ho, Ha in O. pose proof (kc_out _ _ _ _ _ _ K O). lia.
  - intros _ E; contradiction.
  - intros E; contradiction.
  - intros E; contradiction.
Qed.

Lemma thd_H_of wrap src pos inp aout m m' :
  thd_H wrap src pos inp aout m ->
  m_inp m' = m_inp m -> m_aout m' = m_aout m -> i_wrap (m_s m') = i_wrap (m_s m) ->
  i_head (m_s m') = i_head (m_s m) -> m_out m' = m_out m -> m_ret m' = m_ret m -> m_nx m <= m_nx m' ->
  md_hdr (m_mode m') -> m_leave m' = 0 -> m_nx m' <= Zlength (m_inp m') -> 0 <= i_length (m_s m') ->
  0 <= m_bits m' <= 31 ->
  thd_H wrap src pos inp aout m'.
Proof.
  intros Hh Hi Ha Hw Hhd Ho Hr Hn Hmd Hlv Hnx Hlen Hb.
  assert (P : thd_P wrap src pos inp aout (IBrk m')).
  { apply (thd_Kc wrap src pos inp aout m _ Hh); auto.
    - intros _. destruct (thd_md_ne (m_mode m')) as (_ & _ & _ & _ & _ & _); auto.
      unfold md_hdr in Hmd. intro E; rewrite E in Hmd.
      unfold FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, BAD in Hmd; lia.
    - intro E. rewrite E in Hmd. unfold md_hdr, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, BAD in Hmd; lia. }
  destruct P as [K _].
  pose proof (thd_nx _ _ _ _ _ _ Hh). pose proof (thd_ret _ _ _ _ _ _ Hh).
  constructor; auto; lia.
Qed.

(* NEEDBITS(n) from bits <= 39 *)
Lemma thd_nbf n k m :
  0 < n <= 32 -> 0 <= m_bits m <= 39 -> 0 <= m_nx m <= Zlength (m_inp m) ->
  exists nx' h' b' lv',
    needbits_f k n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv' /\
    m_nx m <= nx' <= Zlength (m_inp m) /\
    ((lv' = 1 /\ 0 <= b' < n) \/ (lv' = m_leave m /\ 0 <= b' <= 39)).
Proof.
  intros Hn. revert m. induction k as [|k IH]; intros m Hb Hx.
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
    split; [lia|]. right. split; [reflexivity|lia].
  - cbn [needbits_f]. destruct (Z.ltb_spec (m_bits m) n) as [L|L].
    + destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
      * exists (m_nx m), (m_hold m), (m_bits m), 1. split; [destruct m; reflexivity|].
        split; [lia|]. left. split; [reflexivity|lia].
      * unfold m_have in H0.
        assert (Hb' : 0 <= m_bits (pull m) <= 39).
        { cbn [pull m_bits set_m_bits]. unfold u32. rewrite Z.mod_small; lia. }
        assert (Hx' : 0 <= m_nx (pull m) <= Zlength (m_inp (pull m))) by (cbn; lia).
        destruct (IH (pull m) Hb' Hx') as (nx' & h' & b' & lv' & E & R & C).
        rewrite E. exists nx', h', b', lv'. split; [destruct m; reflexivity|].
        cbn [pull m_nx m_inp m_leave set_m_nx set_m_hold set_m_bits] in R, C. split; [lia|]. exact C.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). split; [destruct m; reflexivity|].
      split; [lia|]. right. split; [reflexivity|lia].
Qed.

Lemma thd_nb n m :
  0 < n <= 32 -> 0 <= m_bits m <= 31 -> 0 <= m_nx m <= Zlength (m_inp m) ->
  exists nx' h' b' lv',
    needbits n m = set_m_leave (set_m_bits (set_m_hold (set_m_nx m nx') h') b') lv' /\
    m_nx m <= nx' <= Zlength (m_inp m) /\
    ((lv' = 1 /\ 0 <= b' < n) \/ (lv' = m_leave m /\ 0 <= b' <= 39)).
Proof. intros. apply thd_nbf; auto; lia. Qed.

Lemma thd_crc m d : exists c, crc_if m d = upd_s m (fun s => set_i_check s c).
Proof.
  unfold crc_if. destruct (andb _ _).
  - eexists; reflexivity.
  - exists (i_check (m_s m)). destruct m as [s]; destruct s; reflexivity.
Qed.

Lemma thd_zstr k bytes have : forall length max wr buf copy cp b ln buf',
  zstr_f k bytes have length max wr buf copy = (cp, b, ln, buf') -> 0 <= copy < have ->
  copy <= cp <= have /\ length <= ln.
Proof.
  induction k as [|k IH]; intros length max wr buf copy cp b ln buf' E C.
  - cbn in E. inversion E; subst. lia.
  - cbn [zstr_f] in E.
    match type of E with context [if ?c then _ else _] =>
      destruct c eqn:G; [|]
    end.
    + match type of E with context [if ?c then _ else _] => destruct c eqn:G2 end.
      * apply andb_true_iff in G2. destruct G2 as [_ G2]. apply Z.ltb_lt in G2.
        apply IH in E; [|lia]. lia.
      * inversion E; subst. lia.
    + match type of E with context [if ?c then _ else _] => destruct c eqn:G2 end.
      * apply andb_true_iff in G2. destruct G2 as [_ G2]. apply Z.ltb_lt in G2.
        apply IH in E; [|lia]. lia.
      * inversion E; subst. lia.
Qed.

Ltac thd_red :=
  unfold m_mode, m_have in *;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
       upd_s upd_h set_mode set_leave set_bad initbits andb negb
       i_mode i_wrap i_head i_length i_flags i_check set_i_mode set_i_check set_i_length set_i_flags] in *.

Lemma thd_01 : (0 =? 1) = false.
Proof. reflexivity. Qed.

Ltac thd_side :=
  thd_red;
  repeat match goal with H: thd_H _ _ _ _ _ ?x |- _ =>
    let a := fresh in let b := fresh in let c := fresh in let d := fresh in
    let e := fresh in let f := fresh in let g := fresh in
    destruct H as [a b c d e f g] end;
  unfold md_hdr, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE, BAD in *;
  intros; first [reflexivity | lia | congruence | discriminate | tauto | idtac].

Lemma thd_hcrc wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_HCRC m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_HCRC. cbv beta zeta.
  destruct (negb _).
  - destruct (thd_nb 16 m ltac:(lia) Hbits Hnx) as (nx' & h' & b' & lv' & E & R & C). rewrite E.
    thd_red. rewrite Hhd.
    destruct C as [[-> C]|[-> C]].
    + rewrite Z.eqb_refl. apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
    + rewrite Hl, thd_01.
      destruct (andb _ _).
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
  - rewrite Hhd. apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_comment wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_COMMENT2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_COMMENT2. cbv beta zeta.
  destruct (negb _).
  - destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
    + unfold m_have in H0.
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[cp b] ln] buf] eqn:Ez.
      apply thd_zstr in Ez; [|unfold m_have; lia].
      destruct (thd_crc m (inbytes m cp)) as [c ->].
      destruct (negb _).
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
      * apply thd_hcrc. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
  - rewrite Hhd. apply thd_hcrc. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_name wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_NAME2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_NAME2. cbv beta zeta.
  destruct (negb _).
  - destruct (Z.eqb_spec (m_have m) 0) as [H0|H0].
    + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
    + unfold m_have in H0.
      destruct (zstr_f _ _ _ _ _ _ _ _) as [[[cp b] ln] buf] eqn:Ez.
      apply thd_zstr in Ez; [|unfold m_have; lia].
      destruct (thd_crc m (inbytes m cp)) as [c ->].
      destruct (negb _).
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
      * apply thd_comment. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
  - rewrite Hhd. apply thd_comment. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Ltac thd_if :=
  match goal with |- thd_P _ _ _ _ _ (if ?c then _ else _) => destruct c end.

Ltac thd_crcs :=
  repeat match goal with |- context [crc_if ?x ?d] => destruct (thd_crc x d) as [? ->] end; thd_red.

Ltac thd_nbcase n m Hbits Hnx Hhd Hl :=
  let nx' := fresh "nx'" in let h' := fresh "h'" in let b' := fresh "b'" in let lv' := fresh "lv'" in
  let E := fresh "E" in let R := fresh "R" in let C := fresh "C" in
  destruct (thd_nb n m ltac:(lia) Hbits Hnx) as (nx' & h' & b' & lv' & E & R & C); rewrite E;
  thd_red; rewrite ?Hhd;
  destruct C as [[-> C]|[-> C]]; [rewrite Z.eqb_refl | rewrite Hl, thd_01].

Lemma thd_extra wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_EXTRA2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_EXTRA2. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)).
  - destruct (negb (Z.min (i_length (m_s m)) (m_have m) =? 0)).
    + rewrite Hhd. thd_red. thd_crcs. thd_if.
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
      * apply thd_name. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
    + thd_if.
      * apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
      * apply thd_name. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
  - apply thd_name. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_exlen wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_EXLEN2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_EXLEN2. cbv beta zeta.
  destruct (negb (Z.land (i_flags (m_s m)) 1024 =? 0)).
  - thd_nbcase 16 m Hbits Hnx Hhd Hl.
    + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
    + thd_crcs. apply thd_extra. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
      unfold u32. apply Z.mod_pos_bound. lia.
  - rewrite Hhd. apply thd_extra. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_os wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_OS2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_OS2. cbv beta zeta.
  thd_nbcase 16 m Hbits Hnx Hhd Hl.
  + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
  + thd_crcs. apply thd_exlen. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_time wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_TIME2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_TIME2. cbv beta zeta.
  thd_nbcase 32 m Hbits Hnx Hhd Hl.
  + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
  + thd_crcs. apply thd_os. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_flags wrap src pos inp aout m :
  thd_H wrap src pos inp aout m -> thd_P wrap src pos inp aout (c_FLAGS2 m).
Proof.
  intros Hh. pose proof Hh as [K Hl Hnx Hlen Hret Hbits Hmd].
  pose proof (kc_head _ _ _ _ _ _ K) as Hhd.
  unfold c_FLAGS2. cbv beta zeta.
  thd_nbcase 16 m Hbits Hnx Hhd Hl.
  + apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side.
  + thd_if; [apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side|].
    thd_if; [apply (thd_Kc wrap src pos inp aout m _ Hh); thd_side|].
    thd_crcs. apply thd_time. apply (thd_H_of wrap src pos inp aout m _ Hh); thd_side.
Qed.

Lemma thd_post wrap src pos inp aout m o :
  thd_P wrap src pos inp aout o -> step_post wrap src pos inp aout m o.
Proof. destruct o; cbn; tauto. Qed.

Lemma th_hdr : hdr_stmt.
Proof.
  intros wrap src pos inp aout flush m Hc K Hw Hl Hmd.
  assert (Hh : thd_H wrap src pos inp aout m).
  { pose proof (proj1 Hw) as W.
    assert (N : m_mode m <> BAD /\ m_mode m <> DONE /\ m_mode m <> MEM).
    { unfold md_hdr in Hmd.
      repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end; rewrite Hmd;
      unfold FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, BAD, DONE, MEM; repeat split; lia. }
    destruct N as (N1 & N2 & N3).
    constructor; auto.
    - apply (Inv.mw_nx _ W).
    - apply (Inv.sw_length _ (Inv.mw_s _ W)).
    - apply (kc_ret _ _ _ _ _ _ K); auto.
    - apply (kc_bits _ _ _ _ _ _ K); auto. }
  apply thd_post.
  unfold md_hdr in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 _ _ _ m) with (c_FLAGS2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_flags; auto.
  - replace (stepf2 _ _ _ m) with (c_TIME2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_time; auto.
  - replace (stepf2 _ _ _ m) with (c_OS2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_os; auto.
  - replace (stepf2 _ _ _ m) with (c_EXLEN2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_exlen; auto.
  - replace (stepf2 _ _ _ m) with (c_EXTRA2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_extra; auto.
  - replace (stepf2 _ _ _ m) with (c_NAME2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_name; auto.
  - replace (stepf2 _ _ _ m) with (c_COMMENT2 m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_comment; auto.
  - replace (stepf2 _ _ _ m) with (c_HCRC m) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    apply thd_hcrc; auto.
Qed.
