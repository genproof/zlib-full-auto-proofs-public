(** * deflate_rle: the match case ([R_dist]). Kit: RleKit.v. *)
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

Lemma rd_mod_mod a n m : 0 < n -> 0 < m -> (n | m) -> (a mod m) mod n = a mod n.
Proof. intros. symmetry. apply Zmod_div_mod; auto. Qed.

Lemma rd_len a : Int.zero_ext 8 (Int.zero_ext 8 (Int.sub (Int.repr a) (Int.repr 3))) =
  Int.repr (u8 (u32 (a - MIN_MATCH))).
Proof.
  rewrite Int.zero_ext_idem by lia. rewrite sub_repr32, zext8_repr. unfold u8, u32, MIN_MATCH.
  rewrite rd_mod_mod by (try lia; exists 16777216; reflexivity). reflexivity.
Qed.

Lemma rd_dist a b : Int.zero_ext 16 (Int.zero_ext 16 (Int.sub (Int.repr a) (Int.repr b))) =
  Int.repr (u16 (u32 (a - b))).
Proof.
  rewrite Int.zero_ext_idem by lia. rewrite sub_repr32, zext16_repr. unfold u16, u32.
  rewrite rd_mod_mod by (try lia; exists 65536; reflexivity). reflexivity.
Qed.

Lemma rd_shr d : 0 <= d < 65536 ->
  Int.zero_ext 8 (Int.shr (Int.repr d) (Int.repr 8)) = Int.repr (u8 (Z.shiftr d 8)).
Proof.
  intros. rewrite shr_repr by rep_lia. rewrite byte_zext8. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma rd_shru d : 0 <= d < 65536 ->
  Int.zero_ext 8 (Int.shru (Int.repr d) (Int.repr 8)) = Int.repr (u8 (Z.shiftr d 8)).
Proof.
  intros. rewrite shru_repr by rep_lia. rewrite byte_zext8. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma rd_rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma rd_rd_forall (P : Z -> Prop) l i x : Forall P l -> rd l i = Some x -> P x.
Proof.
  intros HF H. apply rd_rd_inv in H. destruct H as [Hi ->].
  rewrite Forall_forall in HF. apply HF. apply Znth_In. exact Hi.
Qed.

Lemma rd_forallb_range lo hi l :
  forallb (fun x => andb (lo <=? x) (x <=? hi)) l = true -> Forall (fun x => lo <= x <= hi) l.
Proof.
  intros H. rewrite forallb_forall in H. rewrite Forall_forall. intros x Hx.
  specialize (H x Hx). apply andb_prop in H. destruct H. lia.
Qed.

Lemma rd_length_code_range i x : rd length_code_tab i = Some x -> 0 <= x <= 28.
Proof. apply (rd_rd_forall (fun x => _ <= x <= _)). apply rd_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_dist_code_range i x : rd dist_code_tab i = Some x -> 0 <= x <= 29.
Proof. apply (rd_rd_forall (fun x => _ <= x <= _)). apply rd_forallb_range. vm_compute. reflexivity. Qed.
Lemma rd_d_code_range d x : c_d_code d = Some x -> 0 <= x <= 29.
Proof. unfold c_d_code. destruct (d <? 256); apply rd_dist_code_range. Qed.
Lemma rd_Zlength_length_code_tab : Zlength length_code_tab = 256. Proof. reflexivity. Qed.
Lemma rd_Zlength_dist_code_tab : Zlength dist_code_tab = 512. Proof. reflexivity. Qed.

(** deflate_globals with the two code tables apart (the rest mentions trees.c's globals, unknown to deflate.c's
    type context). *)
Definition rd_grest (gv : globals) : mpred :=
  (static_trees gv *
   @data_at DCS.CS Ers (tarray tint 29) (map vi base_length_tab) (gv Zlib.trees.code._base_length) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi base_dist_tab) (gv Zlib.trees.code._base_dist) *
   @data_at DCS.CS Ers (tarray tint 29) (map vi extra_lbits) (gv Zlib.trees.code._extra_lbits) *
   @data_at DCS.CS Ers (tarray tint 30) (map vi extra_dbits) (gv Zlib.trees.code._extra_dbits) *
   @data_at DCS.CS Ers (tarray tint 19) (map vi extra_blbits) (gv Zlib.trees.code._extra_blbits) *
   @data_at DCS.CS Ers (tarray tuchar 19) (map vi bl_order) (gv Zlib.trees.code._bl_order) *
   @data_at DCS.CS Ers t_sd (gv Zlib.trees.code._static_ltree, (gv Zlib.trees.code._extra_lbits, (vi 257, (vi 286, vi 15)))) (gv Zlib.trees.code._static_l_desc) *
   @data_at DCS.CS Ers t_sd (gv Zlib.trees.code._static_dtree, (gv Zlib.trees.code._extra_dbits, (vi 0, (vi 30, vi 15)))) (gv Zlib.trees.code._static_d_desc) *
   @data_at DCS.CS Ers t_sd (nullval, (gv Zlib.trees.code._extra_blbits, (vi 0, (vi 19, vi 7)))) (gv Zlib.trees.code._static_bl_desc) *
   dglobals_rest gv)%logic.

Lemma rd_globals_open gv : deflate_globals gv =
  (@data_at DCS.CS Ers (tarray tuchar 512) (map vi dist_code_tab) (gv Zlib.deflate.code.__dist_code) *
   @data_at DCS.CS Ers (tarray tuchar 256) (map vi length_code_tab) (gv Zlib.deflate.code.__length_code) *
   rd_grest gv)%logic.
Proof.
  rewrite deflate_globals_open. unfold trees_globals, trees_tables, rd_grest. apply pred_ext; cancel.
Qed.

(** The tally part of [R_dist]: [_tr_tally_dist(s, 1, s->match_length - MIN_MATCH, bflush)]. *)
Definition rd_T := RL [0;0;1;1;1;1;0;1;1;0]%nat.
Definition rd_U := RL [0;0;1;1;1;1;0;1;1;1]%nat.
Lemma rd_dist_eq : R_dist = Ssequence rd_T rd_U.
Proof. reflexivity. Qed.

Lemma rd_tally_ok {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s s' : dstate) (z : strm) (bf : bool) :
  c_dtally_dist s 1 (u32 (d_match_length s - MIN_MATCH)) = Some (s', bf) ->
  @semax DCS.CS Espec Delta_rle
    (PROP () LOCAL (gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    rd_T
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush (vi (Z.b2z bf)); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s' z p pin pout ish R msgv gv; deflate_globals gv))).
Proof.
  intros H.
  unfold rd_T, RL, Delta_rle. cbv [rsub f_deflate_rle fn_body]. unfold dfull, dstate_at. Intros. abbreviate_semax.
  unfold c_dtally_dist in H. apply bind_inv in H. destruct H as [[t3 bf'] [Ht H]].
  inversion H; subst s' bf'; clear H.
  unfold d_trm in Ht. cbn [fst snd] in Ht.
  unfold c_tr_tally_dist in Ht.
  remember (d_tr s) as t0 eqn:Et0. remember (d_pbm s) as m0 eqn:Em0.
  destruct (tr_out t0) as [buf pend bb bv bu] eqn:Eo.
  apply bind_inv in Ht. destruct Ht as [c1 [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi1 ->].
  apply bind_inv in Ht. destruct Ht as [c2 [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi2 ->].
  apply bind_inv in Ht. destruct Ht as [[t3' m3] [Hp Ht]]. apply c_put_sym_inv in Hp. destruct Hp as [Hi3 E3].
  apply bind_inv in Ht. destruct Ht as [code [Hcode Ht]].
  apply bind_inv in Ht. destruct Ht as [t4 [Hp Ht]]. apply c_incr_lfreq_inv in Hp. destruct Hp as [Hi4 ->].
  apply bind_inv in Ht. destruct Ht as [dc [Hdc Ht]].
  apply bind_inv in Ht. destruct Ht as [t5 [Hp Ht]]. apply c_incr_dfreq_inv in Hp. destruct Hp as [Hi5 ->].
  inversion Ht; subst t3; clear Ht.
  set (dd := u16 1) in *.
  set (ll := u8 (u32 (d_match_length s - MIN_MATCH))) in *.
  cbn [fst snd put_sym_c tr_out set_sym_next set_out tr_sym_next tr_lit_bufsize o_buf o_pending o_bi_buf
       o_bi_valid o_bi_used] in Hi1, Hi2, Hi3, E3.
  rewrite Eo in Hi1, Hi2, Hi3, E3. cbn [o_buf] in Hi1, Hi2, Hi3, E3.
  rewrite !Zlength_upd_Znth in Hi2, Hi3.
  unfold match_at. Intros.
  forward. forward. rewrite rd_len. fold ll.
  forward.
  replace (Int.zero_ext 16 (Int.zero_ext 16 (Int.repr 1))) with (Int.repr dd) by reflexivity.
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
  assert (Hdd : 0 <= dd < 65536) by (unfold dd, u16; apply Z.mod_pos_bound; lia).
  assert (Hll : 0 <= ll < 256) by (unfold ll, u8; apply Z.mod_pos_bound; lia).
  assert (Ell : u8 ll = ll) by (unfold ll; apply u8_u8).
  forward. forward. forward. forward.
  sym_store_fold.
  forward. forward. forward. forward.
  rewrite ?Int.zero_ext_idem by lia. rewrite ?rd_shr, ?rd_shru by lia.
  sym_store_fold.
  forward. forward. forward. forward.
  sym_store_fold.
  dsimpl in E3. inversion E3; subst t3' m3; clear E3.
  dsimpl in Hi4. dsimpl in Hi5. dsimpl in H5.
  (* dist-- *)
  forward.
  replace (Int.zero_ext 16 (Int.sub (Int.repr dd) (Int.repr 1))) with (Int.repr (u16 (dd - 1)))
    by (rewrite sub_repr32, zext16_repr; reflexivity).
  (* dyn_ltree[_length_code[len] + LITERALS + 1].Freq++ *)
  pose proof (rd_length_code_range _ _ Hcode) as Hcr.
  apply rd_rd_inv in Hcode. destruct Hcode as [Hlli Ecode].
  rewrite rd_globals_open. Intros.
  forward.
  { go_lower. apply prop_right. rewrite <- Ecode. apply tc_val_tuchar_repr; lia. }
  forward.
  rewrite <- Ecode.
  unfold ltree_at. Intros.
  match goal with Ht : tree_ok (tr_ltree t0) _ |- _ => pose proof Ht as (Hfl & Hdl & Hfr) end.
  unfold HEAP_SIZE, L_CODES, LITERALS in Hfl, Hdl, Hfr, Hi4.
  destruct (Hfr (code + (256 + 1)) ltac:(lia)) as [Hf Hd].
  destruct (Hfr (code + 257) ltac:(lia)) as [Hf' Hd'].
  forward.
  { go_lower. apply prop_right. rewrite Znth_ct_canon by lia. cbv iota beta. apply tc_val_tushort_repr; lia. }
  rewrite Znth_ct_canon by lia. cbv iota beta.
  forward.
  rewrite ct_canon_incr by lia.
  (* d_code(dist) *)
  pose proof (rd_d_code_range _ _ Hdc) as Hdcr.
  set (dm := u16 (dd - 1)) in *.
  assert (Hdm : 0 <= dm < 65536) by (unfold dm, u16; apply Z.mod_pos_bound; lia).
  unfold c_d_code in Hdc.
  match goal with |- semax _ (PROPx ?P (LOCALx ?L (SEPx ?S))) _ _ =>
    forward_if (PROPx P (LOCALx (temp _t'27 (vi dc) :: L) (SEPx S))) end.
  - rewrite (proj2 (Z.ltb_lt dm 256) ltac:(lia)) in Hdc.
    apply rd_rd_inv in Hdc. destruct Hdc as [Hdmi Edc].
    forward.
    forward. rewrite <- Edc. entailer!.
  - assert (Edm : dm = 0) by reflexivity. exfalso. lia.
  - unfold dtree_at. Intros.
    match goal with Ht : tree_ok (tr_dtree t0) _ |- _ => pose proof Ht as (Hfl2 & Hdl2 & Hfr2) end.
    unfold D_CODES in Hfl2, Hdl2, Hfr2.
    destruct (Hfr2 dc ltac:(lia)) as [Hf2 Hd2].
    forward.
    { go_lower. apply prop_right. rewrite Znth_ct_canon by lia. cbv iota beta. apply tc_val_tushort_repr; lia. }
    rewrite Znth_ct_canon by lia. cbv iota beta.
    forward.
    rewrite ct_canon_incr by lia.
    forward. forward. forward.
    assert (Ebf : Z.b2z (zeq (tr_sym_next t0 + 1 + 1 + 1) (tr_sym_end t0)) = Z.b2z bf).
    { rewrite <- H5. destruct (zeq _ _) as [E|E];
        [rewrite (proj2 (Z.eqb_eq _ _) E)|rewrite (proj2 (Z.eqb_neq _ _) E)]; reflexivity. }
    rewrite Ebf.
    replace (code + (256 + 1)) with (code + LITERALS + 1) by (unfold LITERALS; lia).
    (rewrite trees_at_open, rd_globals_open;
      unfold ltree_at, dtree_at, out_at, sym_at, dtype_at, match_at, win_at, hash_at, cfg_at, stat_at; dsimpl;
      match goal with |- context [trees_rest ?t _ _ _] =>
        lazymatch t with t0 => fail | _ => rewrite (trees_rest_ext t t0) by reflexivity end end;
      rewrite ?Zlength_upd_Znth;
      sep_apply (pb_join Ews (Zlength buf) (tr_lit_bufsize t0));
        [ lia | rewrite Zlength_pb_vals; rewrite ?Zlength_upd_Znth; lia | ];
      rewrite ?sub_repr32, ?add_repr32; unfold vi, vl; rewrite ?repr_u32;
      entailer!;
      split; [apply tree_ok_incr; auto|split; [|apply tree_ok_incr; auto]];
      repeat (apply out_ok_upd; [|rewrite ?Zlength_upd_Znth; lia]); assumption).

Qed.

Lemma rd_upd_ok {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (R : list val) (msgv : val)
    (gv : globals) (flush : Z) (s : dstate) (z : strm) (vb : val) :
  @semax DCS.CS Espec Delta_rle
    (PROP () LOCAL (temp _bflush vb; gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish R msgv gv; deflate_globals gv))
    rd_U
    (normal_ret_assert
      (PROP () LOCAL (temp _bflush vb; gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull (set_d_match_length (set_d_strstart (set_d_lookahead s (u32 (d_lookahead s - d_match_length s)))
                     (u32 (d_strstart s + d_match_length s))) 0) z p pin pout ish R msgv gv;
            deflate_globals gv))).
Proof.
  unfold rd_U, RL, Delta_rle. cbv [rsub f_deflate_rle fn_body]. unfold dfull, dstate_at, match_at. Intros.
  abbreviate_semax.
  forward. forward. forward. forward. forward. forward. forward.
  assert (Hr : dstate_ranges (set_d_match_length (set_d_strstart (set_d_lookahead s
                 (u32 (d_lookahead s - d_match_length s))) (u32 (d_strstart s + d_match_length s))) 0)).
  { match goal with H : dstate_ranges s |- _ => dranges_tac H end. }
  entailer!.
  unfold dstate_at, match_at, win_at, hash_at, cfg_at, stat_at, d_trm. dsimpl.
  rewrite ?sub_repr32, ?add_repr32; unfold vi, vl; rewrite ?repr_u32.
  entailer!.
Qed.

Lemma rle_dist_ok : rle_dist_stmt.
Proof.
  intros Espec p pin pout ish R msgv gv flush s s' z bf H.
  unfold rle_dist_m in H. apply bind_inv in H. destruct H as [[s1 bf'] [Ht H]].
  inversion H; subst s' bf'; clear H.
  rewrite rd_dist_eq.
  eapply (rl_seq Delta_rle); [apply tycontext_sub_refl | | apply (rd_tally_ok p pin pout ish R msgv gv flush s s1 z bf Ht) | ].
  { apply andp_left2, derives_refl. }
  apply rd_upd_ok.
Qed.
