(** * deflate_rle: the literal case ([R_lit]); the worked pattern: Body_huff.v. Kit: RleKit.v. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.CompressKit.
Require Import Zlib.proof.deflate.RleKit.
Require Import Zlib.deflate.code.
#[export] Existing Instance DCS.CS.
Open Scope cmodel_scope.

Lemma rle_lit_ok : rle_lit_stmt.
Proof.
  intros Espec p pin pout ish R msgv gv flush s s' z bf H.
  unfold R_lit, RL, Delta_rle. cbv [rsub f_deflate_rle fn_body]. unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold rle_lit_m in H.
  apply bind_inv in H. destruct H as [c [Hc H]].
  assert (Hwok : mb_ok (d_window s)) by (open_dranges H3; assumption).
  destruct (mb_rd_vals _ _ _ Hwok Hc) as (Hi & Hz & Hcr).
  pose proof (Zlength_mb_vals _ Hwok) as Hwl.
  assert (0 <= d_strstart s <= Int.max_unsigned) by drange.
  unfold match_at, win_at. Intros.
  forward. forward. forward.
  { go_lower. apply prop_right.
    match goal with |- context [Znth ?i ?l] => replace (Znth i l) with (vi c) by (symmetry; exact Hz) end.
    exact (tc_val_tuchar_repr c ltac:(lia)). }
  match goal with |- context [temp _ (Znth ?i ?l)] => replace (Znth i l) with (vi c) by (symmetry; exact Hz) end.
  forward.
  (* _tr_tally_lit *)
  apply bind_inv in H. destruct H as [[s3 bf0] [Hd H]]. inversion H; subst s' bf0; clear H.
  unfold c_dtally_lit in Hd. apply bind_inv in Hd. destruct Hd as [[t3 bf'] [Ht Hd]].
  inversion Hd; subst s3 bf'; clear Hd.
  unfold d_trm in Ht. cbn [fst snd d_tr d_pbm] in Ht.
  unfold c_tr_tally_lit in Ht.
  remember (d_tr s) as t0 eqn:Et0. remember (d_pbm s) as m0 eqn:Em0.
  destruct (tr_out t0) as [buf pend bb bv bu] eqn:Eo.
  apply bind_inv in Ht. destruct Ht as [c1 [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi1 ->].
  apply bind_inv in Ht. destruct Ht as [c2 [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi2 ->].
  apply bind_inv in Ht. destruct Ht as [[t3' m3] [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi3 E3].
  apply bind_inv in Ht. destruct Ht as [t4 [Hp Ht]]. apply c_incr_lfreq_inv in Hp. destruct Hp as [Hi4 ->].
  inversion Ht; subst t3; clear Ht.
  cbn [fst snd put_sym_c tr_out set_sym_next set_out tr_sym_next tr_lit_bufsize o_buf o_pending o_bi_buf
       o_bi_valid o_bi_used] in Hi1, Hi2, Hi3, E3.
  rewrite Eo in Hi1, Hi2, Hi3, E3. cbn [o_buf] in Hi1, Hi2, Hi3, E3.
  rewrite !Zlength_upd_Znth in Hi2, Hi3.
  rewrite trees_at_open.
  unfold d_trm. cbn [fst snd]. rewrite <- Et0, <- Em0. rewrite Eo.
  unfold out_at, sym_at. Intros. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  sep_apply (pb_split Ews (Zlength buf) (tr_lit_bufsize t0) (pb_vals buf m0) (p_pbuf p)).
  { lia. } { apply Zlength_pb_vals. match goal with Hok : out_ok _ _ |- _ => destruct Hok as [[Hml _] _]; exact Hml end. }
  Intros.
  assert (Hml : Zlength m0 = Zlength buf).
  { match goal with Hok : out_ok _ _ |- _ => destruct Hok as [[Hml _] _]; exact Hml end. }
  assert (Hbl : Zlength buf <= Int.max_unsigned).
  { match goal with Hok : out_ok _ _ |- _ => destruct Hok as [_ [[_ Hbl] _]]; exact Hbl end. }
  rewrite Zlength_upd_Znth in Hi3.
  forward. forward. forward. forward.
  sym_store_fold.
  forward. forward. forward. forward.
  sym_store_fold.
  forward. forward. forward. forward.
  sym_store_fold.
  (* dyn_ltree[cc].Freq++ *)
  pose proof (u8_range c) as Hu8.
  unfold ltree_at. Intros.
  match goal with Ht : tree_ok (tr_ltree t0) _ |- _ => pose proof Ht as (Hfl & Hdl & Hfr) end.
  unfold HEAP_SIZE, L_CODES, LITERALS in Hfl, Hdl, Hfr.
  assert (Hlt : 0 <= u8 c < Zlength (fc (tr_ltree t0))) by lia.
  destruct (Hfr (u8 c) ltac:(lia)) as [Hf Hd].
  forward.
  { go_lower. apply prop_right. rewrite Znth_ct_canon by lia. cbv iota beta. apply tc_val_tushort_repr; lia. }
  rewrite Znth_ct_canon by lia. cbv iota beta.
  forward.
  rewrite ct_canon_incr by lia.
  (* bflush *)
  forward. forward. forward.
  (* lookahead--, strstart++ *)
  forward. forward. forward. forward.
  dsimpl in E3. inversion E3; subst t3' m3; clear E3.
  match goal with E : _ = bf |- _ => dsimpl in E; rename E into Ebf end.
  assert (Eb : Z.b2z (zeq (tr_sym_next t0 + 1 + 1 + 1) (tr_sym_end t0)) = Z.b2z bf).
  { rewrite <- Ebf. destruct (zeq _ _) as [E|E];
      [rewrite (proj2 (Z.eqb_eq _ _) E)|rewrite (proj2 (Z.eqb_neq _ _) E)]; reflexivity. }
  rewrite Eb.
  match goal with |- context [dstate_ranges ?S] => assert (Hr4 : dstate_ranges S) by dranges_tac H3 end.
  rewrite trees_at_open.
  unfold ltree_at, out_at, sym_at, dtype_at, match_at, win_at, hash_at, cfg_at, stat_at; dsimpl; dsimpl in Hr4.
  match goal with |- context [trees_rest ?t _ _ _] =>
    lazymatch t with t0 => fail | _ => rewrite (trees_rest_ext t t0) by reflexivity end end.
  rewrite ?Zlength_upd_Znth.
  sep_apply (pb_join Ews (Zlength buf) (tr_lit_bufsize t0));
    [ lia | rewrite Zlength_pb_vals; rewrite ?Zlength_upd_Znth; lia | ].
  rewrite ?sub_repr32, ?add_repr32; unfold vi, vl; rewrite ?repr_u32.
  entailer!.
  split; [apply tree_ok_incr; auto|].
  repeat (apply out_ok_upd; [|rewrite ?Zlength_upd_Znth; lia]); assumption.
Qed.
