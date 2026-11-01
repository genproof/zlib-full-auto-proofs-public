(* RT-D part FLUSH: the dynamic block of _tr_flush_block (interface: RTDFlushDefs.v, RTDFlushDefs2.v). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFlushDefs2.
Require Import Zlib.proof.roundtrip.RTDFlushDyn2Facts.
Require Zlib.proof.huffman.FlushStream.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Helpers *)

Lemma dyn2_tok_expand_app : forall t1 t2 prev,
  F.tok_expand prev (t1 ++ t2) = F.tok_expand (F.tok_expand prev t1) t2.
Proof. induction t1 as [|a t1 IH]; intros t2 prev; [reflexivity|]. cbn [app F.tok_expand]. apply IH. Qed.

Lemma dyn2_toks_ok_app : forall cl t1 t2 prev,
  F.toks_ok cl prev t1 -> F.toks_ok cl (F.tok_expand prev t1) t2 -> F.toks_ok cl prev (t1 ++ t2).
Proof.
  intros cl t1. induction t1 as [|a t1 IH]; intros t2 prev H1 H2; [exact H2|].
  cbn [app F.toks_ok F.tok_expand] in *. destruct H1 as [A B]. split; [exact A|]. apply IH; assumption.
Qed.

Lemma dyn2_forall_sublist : forall (P : Z -> Prop) (l : list Z) n,
  0 <= n <= Zlength l -> (forall i, 0 <= i < n -> P (Znth i l)) -> Forall P (sublist 0 n l).
Proof.
  intros P l n Hn H. apply Forall_forall. intros y Hy. apply In_Znth in Hy. destruct Hy as [i [Hi E]].
  rewrite Zlength_sublist in Hi by lia. rewrite Znth_sublist in E by lia. subst y. apply H. lia.
Qed.

Lemma dyn2_cimpl : forall codes lens n c,
  0 <= c < n -> n <= Zlength lens -> code_ok codes lens c ->
  (Znth c lens <> 0 -> F.bits_le (Znth c codes) (Znth c lens) = F.send_sym (sublist 0 n lens) c) ->
  cimpl codes lens (sublist 0 n lens) c.
Proof.
  intros codes lens n c Hc Hn [H1 H2] Hb. unfold cimpl.
  rewrite Znth_sublist by lia. rewrite Z.add_0_r. repeat split; try lia. apply Hb. lia.
Qed.

Lemma dyn2_clsent_len : forall bl n, 0 <= n -> Zlength (clsent_of bl n) = n.
Proof.
  intros bl n Hn. unfold clsent_of. rewrite Zlength_map, Zlength_correct, seq_length. lia.
Qed.

Lemma dyn2_clsent_range : forall bl n, 0 <= n <= 19 -> (forall i, 0 <= i < 19 -> 0 <= Znth i (dl bl) <= 7) ->
  Forall (fun c => 0 <= c <= 7) (clsent_of bl n).
Proof.
  intros bl n Hn H. unfold clsent_of. apply Forall_map, Forall_forall. intros i Hi. apply in_seq in Hi.
  apply H. apply Zlib.proof.huffman.FlushStream.bl_order_range. lia.
Qed.

Lemma dyn2_pending_le : forall o, bits_ok o -> 8 * o_pending o <= bitpos o.
Proof. intros o [A _]. unfold bitpos. lia. Qed.

Theorem rtd_dyn2_ok : wsend_stmt -> tabs2_stmt -> comp_stmt -> symsok_stmt -> canon_stmt -> hdr_stmt -> toks_stmt -> dyn_stmt.
Proof.
  intros Hws Htab Hcomp Hsok Hcanon Hhdr Htoks t syms sl s' olb slb mbi wmax out o1 Hpre Hlev Hprep Hrok Hok1 Hp1 Hlen1 Hov.
  destruct (dyn2_facts t syms sl s' olb slb mbi Hpre Hlev Hprep)
    as [[Hlm Hdm] [[HLl [HDl [HBl HBf]]] [[HLg HDg] [HLr [HDr [HLs [HDs [HEnd [HLk [HDk [HBr [HBk [HQ [Hmbi Hmz]]]]]]]]]]]]]].
  destruct (Hcanon t syms sl s' olb slb mbi Hpre Hlev Hprep) as [Cl [Cd Cb]].
  destruct Htab as [_ [_ [Tl Td]]].
  pose proof (fp_syms _ _ Hpre) as [_ [HnL [Hval _]]].
  set (lt := tr_ltree s') in *. set (dt := tr_dtree s') in *. set (bl := tr_bltree s') in *.
  set (lmax := tr_lmax s') in *. set (dmax := tr_dmax s') in *. set (L := tr_lit_bufsize t) in *.
  clearbody lt dt bl lmax dmax L.
  set (o2 := send_all_trees o1 lt dt bl (lmax + 1) (dmax + 1) (mbi + 1)) in *.
  unfold overlay_ok in Hov. destruct Hov as [Hok2 [Hlen2 [_ [Hsc [_ Hbits]]]]].
  assert (Hb0 := Hbits O ltac:(lia)). cbn [firstn compress_sep] in Hb0. change (Z.of_nat 0) with 0 in Hb0.
  assert (Hbn := Hbits (length syms) ltac:(lia)). rewrite firstn_all in Hbn.
  rewrite <- Zlength_correct in Hbn.
  pose proof (dyn2_pending_le _ Hok2) as Hpe2.
  assert (Hok3 : bits_ok (compress_sep o2 (fc lt) (dl lt) (fc dt) (dl dt) syms)).
  { destruct (compress_sep_spec syms o2 (fc lt) (dl lt) (fc dt) (dl dt) Hok2
                ltac:(intros x Hx; split; auto)) as [[_ [H _]] _]. exact H. }
  pose proof (dyn2_pending_le _ Hok3) as Hpe3.
  pose proof (Zlength_nonneg syms) as Hn0.
  unfold HEAP_SIZE, D_CODES in *.
  destruct (Htoks (dl lt) lmax ltac:(lia) ltac:(lia) HLg HLr) as [TE1 TO1].
  destruct (Htoks (dl dt) dmax ltac:(lia) ltac:(lia) HDg HDr) as [TE2 TO2].
  set (t1 := tree_toks (dl lt) lmax) in *. set (t2 := tree_toks (dl dt) dmax) in *.
  set (llsub := sublist 0 (lmax + 1) (dl lt)) in *. set (dlsub := sublist 0 (dmax + 1) (dl dt)) in *.
  assert (Zl1 : Zlength llsub = lmax + 1) by (unfold llsub; rewrite Zlength_sublist; lia).
  assert (Zl2 : Zlength dlsub = dmax + 1) by (unfold dlsub; rewrite Zlength_sublist; lia).
  assert (Hexp : F.dyn_lens (t1 ++ t2) = llsub ++ dlsub).
  { unfold F.dyn_lens. rewrite dyn2_tok_expand_app, TE1, TE2. reflexivity. }
  assert (Hdll : F.dyn_ll (lmax + 1) (t1 ++ t2) = llsub).
  { unfold F.dyn_ll. rewrite Hexp, sublist_app1 by lia. apply sublist_same; lia. }
  assert (Hddl : F.dyn_dl (lmax + 1) (dmax + 1) (t1 ++ t2) = dlsub).
  { unfold F.dyn_dl. rewrite Hexp, sublist_app2 by lia. rewrite Zl1. apply sublist_same; lia. }
  assert (Zsl : forall (l : list Z) n i, 0 <= i < n -> n <= Zlength l -> Znth i (sublist 0 n l) = Znth i l).
  { intros l n i Hi Hn. rewrite Znth_sublist by lia. f_equal; lia. }
  (* the header *)
  assert (HQc : forall q, In q (Header.tree_syms (dl lt) (lmax + 1 - 1) ++ Header.tree_syms (dl dt) (dmax + 1 - 1)) ->
     cimpl (fc bl) (dl bl) (sublist 0 19 (dl bl)) (fst q)).
  { intros q Hq. rewrite !Z.add_simpl_r in Hq. destruct (HQ q Hq) as [Hq1 Hq2].
    apply dyn2_cimpl; [lia|lia|exact Hq2|]. intros Hnz. apply Cb; auto. }
  destruct (Hhdr o1 lt dt bl (lmax + 1) (dmax + 1) (mbi + 1) Hok1 Hp1 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(lia) ltac:(lia) HBl HBf ltac:(intros i Hi; apply HLr; lia) ltac:(intros i Hi; apply HDr; lia)
              HBr ltac:(intros r Hr; apply Hmz; lia) HQc ltac:(fold o2; lia)) as [Hcl [_ Hob2]].
  fold o2 in Hob2. rewrite !Z.add_simpl_r in Hob2. fold t1 t2 in Hob2.
  (* the symbols *)
  assert (Hzs : zsyms_ok syms).
  { intros x Hx. destruct (Hval x Hx) as [A B]. destruct (Z.eqb_spec (fst x) 0); lia. }
  assert (Hsc' : syms_cimpl (fc lt) (dl lt) (fc dt) (dl dt) llsub dlsub syms).
  { intros x Hx. destruct (HLs x Hx) as [Hl1 Hl2]. destruct (Hval x Hx) as [V1 V2].
    unfold lcode_of, LITERALS in Hl1, Hl2.
    destruct (Z.eqb_spec (fst x) 0) as [E|E].
    - apply dyn2_cimpl; [lia|lia|auto|]; intros Hnz; apply Cl; auto; lia.
    - destruct (HDs x Hx E) as [Hd1 Hd2]. destruct (Tl (snd x) ltac:(lia)) as [T1 [T2 _]].
      destruct (Td (fst x) ltac:(lia)) as [D1 [D2 _]].
      rewrite <- T1, <- D1. split.
      + replace (257 + Znth (snd x) length_code_tab) with (Znth (snd x) length_code_tab + 256 + 1) by lia.
        apply dyn2_cimpl; [lia|lia|auto|]; intros Hnz; apply Cl; auto; lia.
      + apply dyn2_cimpl; [lia|lia|auto|]; intros Hnz; apply Cd; auto; lia. }
  assert (HEc : cimpl (fc lt) (dl lt) llsub END_BLOCK).
  { unfold END_BLOCK in *. apply dyn2_cimpl; [lia|lia|auto|]; intros Hnz; apply Cl; auto; lia. }
  destruct (Hcomp o2 (fc lt) (dl lt) (fc dt) (dl dt) llsub dlsub syms Hok2 Hzs Hsc' HEc ltac:(destruct Hok2 as [_ [_ ?]]; lia) ltac:(lia))
    as [Hok3' Hob3].
  assert (Hso : F.syms_ok wmax llsub dlsub out (map fsym syms)).
  { apply Hsok; auto. intros x Hx. destruct (HLs x Hx) as [Hl1 [Hl2 _]]. destruct (Hval x Hx) as [V1 V2].
    unfold lcode_of, LITERALS in Hl1, Hl2.
    destruct (Z.eqb_spec (fst x) 0) as [E|E].
    - unfold llsub. rewrite Zsl by lia. lia.
    - destruct (HDs x Hx E) as [Hd1 [Hd2 _]]. destruct (Tl (snd x) ltac:(lia)) as [T1 [T2 _]].
      destruct (Td (fst x) ltac:(lia)) as [D1 [D2 _]].
      rewrite <- T1, <- D1. unfold llsub, dlsub.
      replace (257 + Znth (snd x) length_code_tab) with (Znth (snd x) length_code_tab + 256 + 1) by lia.
      rewrite !Zlength_sublist, !Zsl by lia. lia. }
  exists (lmax + 1), (dmax + 1), (clsent_of bl (mbi + 1)), (t1 ++ t2). split.
  - unfold F.block_ok. rewrite Hdll, Hddl, Hcl, dyn2_clsent_len by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [apply dyn2_clsent_range; auto; lia|].
    split; [split; [apply dyn2_forall_sublist; [lia|]; intros i Hi; apply HBr; lia|exact HBk]|].
    split.
    { apply dyn2_toks_ok_app; [apply TO1|rewrite TE1; apply TO2]; intros q Hq.
      - destruct (HQ q ltac:(apply in_or_app; left; exact Hq)) as [A [B _]]. rewrite Zsl by lia. lia.
      - destruct (HQ q ltac:(apply in_or_app; right; exact Hq)) as [A [B _]]. rewrite Zsl by lia. lia. }
    split; [rewrite Hexp, Zlength_app; lia|].
    split.
    { split; [apply dyn2_forall_sublist; [lia|]; intros i Hi; unfold F.MAXLEN; apply HLr; lia|].
      split; [unfold llsub; rewrite Zsl by lia; destruct HEnd; unfold END_BLOCK in *; lia|].
      left. exact HLk. }
    split.
    { split; [apply dyn2_forall_sublist; [lia|]; intros i Hi; unfold F.MAXLEN; apply HDr; lia|].
      left. exact HDk. }
    exact Hso.
  - cbv zeta. split; [exact Hok3'|]. rewrite Hob3, Hob2. unfold dyn_body. rewrite Hdll, Hddl.
    rewrite app_assoc. reflexivity.
Qed.
