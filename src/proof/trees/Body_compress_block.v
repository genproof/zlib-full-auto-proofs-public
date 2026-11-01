(** * The body of trees.c's compress_block against its shared specification (TSpec.compress_block_spec).

    The inlined send_bits / send_code macro blocks: [SendKit.sb_block] (see SendKit.v's header). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.SendKit2.
Require Import Zlib.proof.trees.CBKit.
Require Import Zlib.proof.trees.CBLit Zlib.proof.trees.CBLsend Zlib.proof.trees.CBLextra.
Require Import Zlib.proof.trees.CBDsend Zlib.proof.trees.CBDextra Zlib.proof.trees.CBEnd.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.


(** ** Model facts *)

Lemma cb_rd_pb_inv o m i d : out_ok o m -> c_rd_pb (o, m) i = Some d ->
  0 <= i < Zlength (o_buf o) /\ Znth i m = true /\ d = Znth i (o_buf o) /\ 0 <= d < 256.
Proof.
  intros Hok H. unfold c_rd_pb, in_range in H.
  destruct (andb (andb (0 <=? i) (i <? Zlength (o_buf o))) (Znth i m)) eqn:E; [|discriminate].
  injection H as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct Hok as ((Hl & Hb) & _). cbn [mb_val mb_def] in *.
  repeat split; auto; apply Hb; auto.
Qed.

Lemma cb_iter k lb sn LC LL DC DL om sx x :
  c_compress_loop (S k) lb sn LC LL DC DL om sx = Some x ->
  exists d0 d1 lc om',
    c_rd_pb om (lb + sx) = Some d0 /\ c_rd_pb om (lb + sx + 1) = Some d1 /\ c_rd_pb om (lb + sx + 2) = Some lc /\
    c_send_symbol om LC LL DC DL (Z.land d0 255 + Z.shiftl (Z.land d1 255) 8) lc = Some om' /\
    (if sx + 3 <? sn then c_compress_loop k lb sn LC LL DC DL om' (sx + 3) else Some om') = Some x.
Proof.
  intros H. cbn [c_compress_loop] in H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  exists x0, x1, x2, x3. auto.
Qed.

Lemma cb_symbol_match om LC LL DC DL dist lc r : dist <> 0 ->
  c_send_symbol om LC LL DC DL dist lc = Some r ->
  exists code om1 extra om2 dcode om3 extra2,
    rd length_code_tab lc = Some code /\ c_send_code om (code + LITERALS + 1) LC LL = Some om1 /\
    rd extra_lbits code = Some extra /\
    (if negb (extra =? 0) then let* bl := rd base_length_tab code in c_send_bits om1 (lc - bl) extra
     else Some om1) = Some om2 /\
    c_d_code (dist - 1) = Some dcode /\ c_send_code om2 dcode DC DL = Some om3 /\
    rd extra_dbits dcode = Some extra2 /\
    (if negb (extra2 =? 0) then let* bd := rd base_dist_tab dcode in c_send_bits om3 (dist - 1 - bd) extra2
     else Some om3) = Some r.
Proof.
  intros Hd H. unfold c_send_symbol in H. rewrite (proj2 (Z.eqb_neq _ _) Hd) in H.
  inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H. inv_bind H.
  exists x, x0, x1, x2, x3, x4, x5. auto 10.
Qed.

(** ** The symbol buffer: split the pending_buf array at [sym_buf] for a load [sym_buf[sx]] *)

Lemma cb_split_at sh n lb (v : list val) p :
  0 <= lb <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  @data_at DCS.CS sh (tarray tuchar n) v p =
  (@data_at DCS.CS sh (tarray tuchar lb) (sublist 0 lb v) p *
   @data_at DCS.CS sh (tarray tuchar (n - lb)) (sublist lb n v) (offset_val lb p))%logic.
Proof.
  intros Hb Hl Hc. unfold tarray.
  rewrite (split2_data_at_Tarray_tuchar sh n lb v p) by (try lia; rewrite Hl; lia).
  rewrite field_address0_offset.
  - simpl. replace (0 + 1 * lb) with lb by lia. reflexivity.
  - auto with field_compatible.
Qed.

Lemma cb_merge_at sh n lb (v : list val) p :
  0 <= lb <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  (@data_at DCS.CS sh (tarray tuchar lb) (sublist 0 lb v) p *
   @data_at DCS.CS sh (tarray tuchar (n - lb)) (sublist lb n v) (offset_val lb p))%logic
  |-- @data_at DCS.CS sh (tarray tuchar n) v p.
Proof. intros. rewrite (cb_split_at sh n lb v p) by auto. apply derives_refl. Qed.

Lemma cb_Znth_indep {A} (d1 d2 : Inhabitant A) i (l : list A) :
  0 <= i < Zlength l -> @Znth A d1 i l = @Znth A d2 i l.
Proof.
  intros H. unfold Znth. destruct (Z_lt_dec i 0); [lia|]. apply nth_indep.
  rewrite Zlength_correct in H. lia.
Qed.

Lemma cb_land255 d : 0 <= d < 256 -> Z.land d 255 = d.
Proof.
  intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma cb_and255 d : 0 <= d < 256 -> Int.and (Int.repr d) (Int.repr 255) = Int.repr d.
Proof.
  intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. rewrite cb_land255 by lia. reflexivity.
Qed.

Lemma cb_shl8 d : 0 <= d < 256 -> Int.shl (Int.repr d) (Int.repr 8) = Int.repr (d * 256).
Proof.
  intros. unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma cb_dist_eq d0 d1 : 0 <= d0 < 256 -> 0 <= d1 < 256 ->
  Z.land d0 255 + Z.shiftl (Z.land d1 255) 8 = d0 + d1 * 256.
Proof.
  intros. rewrite !cb_land255 by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(** Floyd's [Delta] after start_function is [Delta_cb] with an opaque specs map: [Delta_cb] is a sub-context. *)
Lemma cb_tsub DS : tycontext_sub Delta_cb
  (mk_tycontext (temp_types Delta_cb) (var_types Delta_cb) (ret_type Delta_cb) (glob_types Delta_cb) DS
     (Maps.PTree.Empty)).
Proof.
  unfold tycontext_sub. cbn [temp_types var_types ret_type glob_types glob_specs annotations].
  split; [intros id; destruct (Maps.PTree.get id (temp_types Delta_cb)); auto|].
  split; [auto|]. split; [auto|].
  split; [intros id; destruct (Maps.PTree.get id (glob_types Delta_cb)); simpl; auto|].
  split.
  - intros id. replace (glob_specs Delta_cb) with (Maps.PTree.empty funspec) by reflexivity.
    rewrite Maps.PTree.gempty. exact I.
  - intros id. replace (annotations Delta_cb) with (Maps.PTree.empty Annotation) by reflexivity.
    rewrite Maps.PTree.gempty. simpl. auto.
Qed.

Ltac cb_delta :=
  lazymatch goal with DS : Maps.PTree.t funspec |- _ =>
    eapply semax_Delta_subsumption; [exact (cb_tsub DS) |] end.

(** Expose the statement and postcondition abbreviated by Floyd (to apply a part lemma). *)
Ltac cb_unabbrev :=
  repeat match goal with
  | X := @abbreviate statement _ |- _ => unfold abbreviate in X; subst X
  | X := @abbreviate ret_assert _ |- _ => unfold abbreviate in X; subst X
  end.

(** The entailment into a part's precondition. *)
Ltac cb_ent :=
  unfold cb_assert, cb_sep, cb_base, out_at, sym_at, trees_tables, vi; cbn [fst snd]; entailer!.

(** A part lemma (in [Delta_cb]) as the first statement of a sequence. *)
Lemma cb_seq {Espec : OracleKind} Delta P P' Q c1 c2 R :
  tycontext_sub Delta_cb Delta -> ENTAIL Delta, P |-- P' ->
  semax Delta_cb P' c1 (normal_ret_assert Q) -> semax Delta Q c2 R -> semax Delta P (Ssequence c1 c2) R.
Proof.
  intros HT HP H1 H2. eapply semax_seq; [|exact H2].
  apply (cb_apply Delta P P' c1 Q R HP). eapply semax_Delta_subsumption; eauto.
Qed.

Lemma cb_shru7 v : 0 <= v <= Int.max_unsigned -> Int.shru (Int.repr v) (Int.repr 7) = Int.repr (Z.shiftr v 7).
Proof. intros. unfold Int.shru. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma cb_tab_eq tab i x : rd tab i = Some x -> Znth i tab = x.
Proof. intros H. apply cb_rd_inv in H. destruct H as [_ ->]. reflexivity. Qed.

(** A load of a table entry (Floyd leaves [vi (Znth i tab)]). *)
Ltac cb_tload E :=
  let Hi := fresh "Hi" in pose proof (proj1 (cb_rd_inv _ _ _ E)) as Hi;
  forward; rewrite ?(cb_tab_eq _ _ _ E);
  try (lazymatch goal with |- _ |-- local _ => unfold vi; tc_side end).

(** A table entry loaded from [trees_tables]. *)
Lemma cb_tab_val tab i x (d : Inhabitant val) : rd tab i = Some x -> @Znth val d i (map vi tab) = Vint (Int.repr x).
Proof.
  intros H. apply cb_rd_inv in H. destruct H as [Hi ->].
  rewrite (cb_Znth_indep d Inhabitant_val) by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia. reflexivity.
Qed.

Lemma body_compress_block : semax_body Vprog Gprog_compress_block f_compress_block compress_block_spec.
Proof.
  start_function.
  unfold c_compress_block in H. inv_bind H. rename Ha into Hloop, H into Hend.
  rewrite !sk_tree_arr_codes. Intros.
  assert (Hok : cb_ok lsh ln lt dsh dn dt) by (split; [|split; [|split]]; assumption).
  forward.
  unfold sym_at. Intros.
  forward.
  forward_if (PROP () LOCAL (temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv)
    SEP (out_at (fst x) (snd x) sp pbp; sym_at ts sp pbp; tree_codes lsh ln lt ltp; tree_codes dsh dn dt dtp;
         trees_tables gv)).
  { (* the do-while loop *)
    rewrite (proj2 (Z.eqb_neq _ _) H5) in Hloop.
    cbn [negb] in Hloop.
    forward_loop (EX k : nat, EX sx : Z, EX om : cout,
      PROP (c_compress_loop k (tr_lit_bufsize ts) (tr_sym_next ts) (fc lt) (dl lt) (fc dt) (dl dt) om sx = Some x;
            0 <= sx)
      LOCAL (temp _sx (vi sx); temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv)
      SEP (out_at (fst om) (snd om) sp pbp; sym_at ts sp pbp; tree_codes lsh ln lt ltp;
           tree_codes dsh dn dt dtp; trees_tables gv))
    break: (PROP () LOCAL (temp _s sp; temp _ltree ltp; temp _dtree dtp; gvars gv)
      SEP (out_at (fst x) (snd x) sp pbp; sym_at ts sp pbp; tree_codes lsh ln lt ltp; tree_codes dsh dn dt dtp;
           trees_tables gv)).
    { Exists (Z.to_nat (tr_sym_next ts)) 0 (o, m). cbn [fst snd]. unfold sym_at. entailer!. }
    clear Hloop. Intros k sx om.
    lazymatch goal with Hx : c_compress_loop _ _ _ _ _ _ _ _ _ = Some x |- _ => rename Hx into Hk end.
    destruct k as [|k]; [discriminate|].
    apply cb_iter in Hk. destruct Hk as (d0 & d1 & lc & om' & Hd0 & Hd1 & Hlc & Hsym & Hnext).
    destruct om as [o1 m1]. cbn [fst snd] in *.
    unfold out_at at 1. Intros.
    lazymatch goal with Hx : out_ok o1 m1 |- _ => rename Hx into Hok1 end.
    pose proof (cb_rd_pb_inv _ _ _ _ Hok1 Hd0) as (Hi0 & Hm0 & Hv0 & Hr0).
    pose proof (cb_rd_pb_inv _ _ _ _ Hok1 Hd1) as (Hi1 & Hm1 & Hv1 & Hr1).
    pose proof (cb_rd_pb_inv _ _ _ _ Hok1 Hlc) as (Hi2 & Hm2 & Hv2 & Hr2).
    pose proof Hok1 as ((Hml & Hmb) & Hok1'). cbn [mb_val mb_def] in Hml, Hmb.
    assert (Hlen : Zlength (pb_vals (o_buf o1) m1) = Zlength (o_buf o1)) by (apply Zlength_pb_vals; lia).
    unfold sym_at. Intros.
    assert_PROP (field_compatible (tarray tuchar (Zlength (o_buf o1))) [] pbp) as Hfc by entailer!.
    rewrite (cb_split_at Ews (Zlength (o_buf o1)) (tr_lit_bufsize ts) (pb_vals (o_buf o1) m1) pbp)
      by (auto; lia). Intros.
    assert (E0 : forall d : Inhabitant val, @Znth val d sx (sublist (tr_lit_bufsize ts) (Zlength (o_buf o1)) (pb_vals (o_buf o1) m1)) =
                 Vint (Int.repr d0)).
    { intros d. rewrite (cb_Znth_indep d Inhabitant_val) by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia. rewrite Znth_pb_vals by lia.
      replace (sx + tr_lit_bufsize ts) with (tr_lit_bufsize ts + sx) by lia. rewrite Hm0, <- Hv0. reflexivity. }
    assert (E1 : forall d : Inhabitant val, @Znth val d (sx + 1) (sublist (tr_lit_bufsize ts) (Zlength (o_buf o1)) (pb_vals (o_buf o1) m1)) =
                 Vint (Int.repr d1)).
    { intros d. rewrite (cb_Znth_indep d Inhabitant_val) by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia. rewrite Znth_pb_vals by lia.
      replace (sx + 1 + tr_lit_bufsize ts) with (tr_lit_bufsize ts + sx + 1) by lia. rewrite Hm1, <- Hv1.
      reflexivity. }
    assert (E2 : forall d : Inhabitant val, @Znth val d (sx + 1 + 1) (sublist (tr_lit_bufsize ts) (Zlength (o_buf o1)) (pb_vals (o_buf o1) m1)) =
                 Vint (Int.repr lc)).
    { intros d. rewrite (cb_Znth_indep d Inhabitant_val) by (rewrite Zlength_sublist; lia).
      rewrite Znth_sublist by lia. rewrite Znth_pb_vals by lia.
      replace (sx + 1 + 1 + tr_lit_bufsize ts) with (tr_lit_bufsize ts + sx + 2) by lia. rewrite Hm2, <- Hv2.
      reflexivity. }
    forward. forward. forward.
    forward; [rewrite E0; tc_side | rewrite E0].
    forward. rewrite cb_and255 by lia.
    forward. forward. rewrite add_repr. forward.
    forward; [rewrite E1; tc_side | rewrite E1].
    forward. rewrite cb_and255, cb_shl8, add_repr by lia.
    forward. forward. rewrite add_repr. forward.
    forward; [rewrite E2; tc_side | rewrite E2].
    sep_apply (cb_merge_at Ews (Zlength (o_buf o1)) (tr_lit_bufsize ts) (pb_vals (o_buf o1) m1) pbp
                 ltac:(lia) Hlen Hfc).
    rewrite add_repr. replace (sx + 1 + 1 + 1) with (sx + 3) by lia.
    rewrite (cb_dist_eq d0 d1 Hr0 Hr1) in Hsym.
    assert (HD : 0 <= d0 + d1 * 256 < 65536) by lia.
    forward_if (PROPx [] (LOCALx (cb_base (sx + 3) sp ltp dtp gv)
      (SEPx (cb_sep om' sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)))).
    { (* a literal *)
      assert (HD0 : d0 + d1 * 256 = 0) by (first [lia | apply repr_inj_unsigned; auto; rep_lia]).
      rewrite HD0 in Hsym. unfold c_send_symbol in Hsym. cbn [Z.eqb] in Hsym.
      cb_unabbrev.
      cb_delta.
      eapply semax_pre; [| apply (cb_lit_ok Espec (sx + 3) lc sp pbp ltp dtp gv ts lsh ln lt dsh dn dt (o1, m1) om' Hok
                                   ltac:(lia) Hsym)].
      cb_ent. }
    { (* a match *)
      assert (HDn : d0 + d1 * 256 <> 0) by (first [lia | intro E; rewrite E in *; congruence]).
      apply cb_symbol_match in Hsym; [|exact HDn].
      destruct Hsym as (code & om1 & extra & om2 & dcode & om3 & extra2 &
                        Hcode & Hs1 & Hex & Hs2 & Hdc & Hs3 & Hex2 & Hs4).
      pose proof (rd_length_code_range _ _ Hcode) as Hcr.
      pose proof (rd_extra_lbits_range _ _ Hex) as Hexr.
      pose proof (rd_extra_dbits_range _ _ Hex2) as Hex2r.
      assert (Hdcr : 0 <= dcode <= 29).
      { unfold c_d_code in Hdc. destruct (_ <? 256); eapply rd_dist_code_range; exact Hdc. }
      unfold trees_tables. Intros.
      cb_tload Hcode.
      cb_unabbrev.
      eapply cb_seq; [exact (cb_tsub Delta_specs) |
        | apply (cb_lsend_ok Espec (sx + 3) lc (d0 + d1 * 256) code sp pbp ltp dtp gv ts lsh ln lt dsh dn dt
                   (o1, m1) om1 Hok Hcr Hs1) | ]; [cb_ent | ].
      unfold cb_assert, cb_sep, cb_base, trees_tables. abbreviate_semax. Intros.
      cb_tload Hex.
      cb_unabbrev.
      eapply cb_seq; [exact (cb_tsub Delta_specs) |
        | apply (cb_lextra_ok Espec (sx + 3) lc (d0 + d1 * 256) code extra sp pbp ltp dtp gv ts lsh ln lt
                   dsh dn dt om1 om2 Hok Hr2 Hcr Hex Hs2) | ]; [cb_ent | ].
      unfold cb_assert, cb_sep, cb_base. abbreviate_semax.
      forward. rewrite sub_repr.
      assert (Hsh : Int.add (Int.repr 256) (Int.shru (Int.repr (d0 + d1 * 256 - 1)) (Int.repr 7)) =
                    Int.repr (256 + Z.shiftr (d0 + d1 * 256 - 1) 7)).
      { rewrite cb_shru7 by rep_lia. apply add_repr. }
      forward_if (PROPx [] (LOCALx (temp _t'10 (vi dcode) :: temp _dist (vi (d0 + d1 * 256 - 1)) ::
                                    cb_base (sx + 3) sp ltp dtp gv)
                   (SEPx (cb_sep om2 sp pbp ts lsh ln lt ltp dsh dn dt dtp gv)))).
      { unfold c_d_code in Hdc. rewrite (proj2 (Z.ltb_lt (d0 + d1 * 256 - 1) 256) ltac:(lia)) in Hdc.
        unfold trees_tables. Intros.
        cb_tload Hdc. forward.
        unfold cb_sep, cb_base, trees_tables, vi. entailer!. }
      { unfold c_d_code in Hdc. rewrite (proj2 (Z.ltb_ge (d0 + d1 * 256 - 1) 256) ltac:(lia)) in Hdc.
        unfold trees_tables. Intros.
        pose proof (proj1 (cb_rd_inv _ _ _ Hdc)) as Hdci.
        assert (Hu : Int.unsigned (Int.add (Int.repr 256) (Int.shru (Int.repr (d0 + d1 * 256 - 1)) (Int.repr 7)))
                     = 256 + Z.shiftr (d0 + d1 * 256 - 1) 7).
        { rewrite Hsh. apply Int.unsigned_repr. rewrite Zlength_dist_code_tab in Hdci. rep_lia. }
        assert (Hrng : 0 <= Int.unsigned (Int.add (Int.repr 256) (Int.shru (Int.repr (d0 + d1 * 256 - 1))
                         (Int.repr 7))) < Zlength dist_code_tab) by (rewrite Hu; lia).
        forward; rewrite ?Hu, ?(cb_tab_eq _ _ _ Hdc);
          try (lazymatch goal with |- _ |-- local _ => unfold vi; tc_side end).
        forward.
        unfold cb_sep, cb_base, trees_tables, vi. entailer!. }
      unfold cb_base, cb_sep. forward.
      cb_unabbrev.
      eapply cb_seq; [exact (cb_tsub Delta_specs) |
        | apply (cb_dsend_ok Espec (sx + 3) (d0 + d1 * 256 - 1) dcode sp pbp ltp dtp gv ts lsh ln lt dsh dn dt
                   om2 om3 Hok Hdcr Hs3) | ]; [cb_ent | ].
      unfold cb_assert, cb_sep, cb_base, trees_tables. abbreviate_semax. Intros.
      cb_tload Hex2.
      cb_unabbrev. cb_delta.
      eapply semax_pre; [| apply (cb_dextra_ok Espec (sx + 3) (d0 + d1 * 256 - 1) dcode extra2 sp pbp ltp dtp gv ts
                                   lsh ln lt dsh dn dt om3 om' Hok ltac:(lia) Hdcr Hex2 Hs4)].
      cb_ent. }
    (* the loop test *)
    unfold cb_base, cb_sep, sym_at. Intros. forward.
    assert (Hsx3 : sx + 3 <= Int.max_unsigned) by lia.
    forward_if.
    - forward. Exists k (sx + 3) om'.
      rewrite (proj2 (Z.ltb_lt (sx + 3) (tr_sym_next ts)) ltac:(lia)) in Hnext.
      unfold sym_at, vi. entailer!.
    - forward.
      rewrite (proj2 (Z.ltb_ge (sx + 3) (tr_sym_next ts)) ltac:(lia)) in Hnext. injection Hnext as <-.
      unfold sym_at. entailer!. }
  { (* no symbols *)
    forward.
    rewrite (proj2 (Z.eqb_eq _ _) H5) in Hloop. cbn [negb] in Hloop. injection Hloop as <-.
    cbn [fst snd]. unfold sym_at. entailer!. }
  (* send_code(s, END_BLOCK, ltree) *)
  cb_unabbrev.
  eapply semax_post'; [| cb_delta;
    eapply semax_pre; [| apply (cb_end_ok Espec sp pbp ltp dtp gv ts lsh ln lt dsh dn dt x r Hok Hend)]].
  - unfold cb_assert, cb_sep, cb_base. rewrite !sk_tree_arr_codes. unfold tree_codes. entailer!.
  - cb_ent.
Qed.
