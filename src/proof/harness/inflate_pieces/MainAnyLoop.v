(* Law rj_any_input, main: one iteration of the do-while (its body), from the loop invariant pk_inv4 to the
   invariant again (or a `return 0` when an allocation or inflate() / inflateSetDictionary runs out of memory):
   the piece and the output space, set_buffer(), position_of() (the offered position in `at`), inflate() and the
   check of its return code (code_doc), for an empty piece and no output space the check that the code is not
   Z_OK (Progress.pieces_progress) and that unmoved() holds (the members after the call are the offered ones,
   MainSession.unmoved_after), `read`, the two free()s, the optional inflateSetDictionary of any bytes. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5 Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.inflate_pieces.LawCS.
Require Import Zlib.proof.harness.inflate_pieces.Globals.
Require Import Zlib.proof.harness.inflate_pieces.Facts.
Require Import Zlib.proof.harness.inflate_pieces.MainKit.
Require Import Zlib.proof.harness.inflate_pieces.Progress.
Require Import Zlib.proof.harness.inflate_pieces.MainSession.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.rj_any_input.code.

#[local] Existing Instance Any.CS.
#[local] Existing Instances Any.CC_inflate Any.CC_adler32 Any.CC_crc32 Any.CC_zutil Any.CC_inffast
  Any.CC_inftrees Any.CC_compress.
Import AnyK AnyS.

Definition Gk_any := @Gk_of Any.CS Gk_extra_any.
Definition Delta_any : tycontext := func_tycontext f_main (QPvarspecs Any.p) Gk_any nil.
Definition POST_any : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the body of the do-while *)
Definition seg_body_any : statement := ltac:(get_loop_body f_main).

Ltac ret0a := forward; Exists (Int.repr 0); sep_apply a_frame; entailer!.

(* the code of a call that is not Z_OK is not 0 as an int *)
Lemma code_ne0 r : code_doc r -> r <> Z_OK -> Int.repr r <> Int.repr 0.
Proof.
  intros C N E. apply N. unfold code_doc in C.
  apply repr_inj_signed in E; [exact E | | rep_lia].
  destruct C as [->|[->|[->|[->| ->]]]]; cbv; split; discriminate.
Qed.

(* An empty piece and no output space: the two objects, lent to unmoved (their malloc tokens keep the two
   pointers valid). *)
Lemma io_gather_unmoved z z' piece take cin outp room cout :
  isptr piece -> isptr outp -> take = 0 -> room = 0 -> pz_of z' = pz_offer z piece take outp room ->
  (data_at Ews (tarray tuchar take) cin piece * malloc_token Ews (tarray tuchar take) piece *
   data_at Ews (tarray tuchar room) cout outp * malloc_token Ews (tarray tuchar room) outp)%logic
  |-- io_objs piece take cin outp room cout && LS.unmoved_cmp (pz_of z') (pz_offer z piece take outp room).
Proof.
  intros Pp Po -> -> ->. eapply derives_trans; [ | apply io_lend_unmoved; auto]. unfold io_objs. cancel.
Qed.

Lemma body_any_loop {Espec: OracleKind} P gv vs va inp src Fr z L :
  pieces_facts P -> pieces_progress P -> P z L -> zf_ok z -> 0 <= zf_tin z <= Zlength src ->
  Zlength src <= 9223372036854775807 -> is_bytes src -> isptr inp -> isptr vs ->
  semax Delta_any
    (PROP ()
     LOCAL (temp _input_len (Vlong (Int64.repr (Zlength src))); temp _input inp;
            temp _read (Vlong (Int64.repr (zf_tin z))); lvar _strm t_zsl vs; lvar _at t_posl va; gvars gv)
     SEP (istreamA gv Tsh vs z Vundef (Some L); mem_mgr gv; zfuncs gv; tables_rep Ers gv; crc_table_at Ers gv;
          malloc_token Ews (tarray tuchar (Zlength src)) inp;
          data_at Ews (tarray tuchar (Zlength src)) (bytes_rep src) inp; data_at_ Tsh t_posl va; Fr))
    seg_body_any
    (loop1_ret_assert (pk_inv4 P gv vs va inp src Fr) (overridePost (pk_inv4 P gv vs va inp src Fr) POST_any)).
Proof.
  intros PF PG HP Zo Ht Hlen Hsb Pinp Pvs.
  unfold seg_body_any, Delta_any, Gk_any, Gk_extra_any, Gk_of, POST_any. simplify_func_tycontext. abbreviate_semax.
  set (tin := zf_tin z) in *.
  forward_call (Zlength src - tin).
  forward_call (Z.min (Zlength src - tin) Int.max_unsigned). Intros take.
  forward.
  split_call. forward_call tt. Intros room. forward. rewrite Int.unsigned_repr by rep_lia.
  assert (Htk: 0 <= take <= Zlength src - tin /\ take <= Int.max_unsigned).
  { pose proof (Z.le_min_l (Zlength src - tin) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength src - tin) Int.max_unsigned). lia. }
  set (data := sublist tin (tin + take) src).
  assert (Hdl: Zlength data = take) by (unfold data; rewrite Zlength_sublist; lia).
  assert (Hdb: is_bytes data) by (unfold data; apply Forall_sublist; auto).
  split_call.
  rewrite <- bytes_a.
  forward_call (offset_val tin inp, Ews, inp, tin, Zlength src, bytes_rep src, take, data, gv).
  { unfold cbuf_ok. repeat split; auto; try lia.
    unfold data, bytes_rep. rewrite sublist_map. reflexivity. }
  Intros piece.
  forward.
  split_call.
  forward_call (room, gv). Intros vret. destruct vret as [outp bs]. simpl fst in *; simpl snd in *.
  rewrite !bytes_a, !tok_a.
  forward.
  destruct (eq_dec piece nullval) as [NP|NP].
  { subst piece. ifpostv _t'12 (Vint (Int.repr 1)); [forward; entailer! | infeas | ].
    forward_if; [ret0a | infeas]. }
  Intros. aptr piece Ppiece.
  destruct (eq_dec outp nullval) as [NO|NO].
  { subst outp. ifpostv _t'12 (Vint (Int.repr 1)); [infeas | forward; entailer! | ].
    forward_if; [ret0a | infeas]. }
  Intros. aptr outp Poutp.
  ifpostv _t'12 (Vint (Int.repr 0)); [infeas | forward; entailer!; destruct outp; try contradiction; reflexivity | ].
  forward_if; [infeas | ].
  (* offer(&strm, piece, take, out, room) *)
  sep_apply (istreamA_zs gv vs z Vundef L). Intros.
  assert (HL: live_ok L) by assumption.
  forward_call (vs, Tsh, piece, take, outp, room, zf_ni z, Vint (Int.repr (zf_ai z)), Vlong (Int64.repr tin),
                zf_no z, Vint (Int.repr (zf_ao z)), Vlong (Int64.repr (zf_tout z)), msg_val gv (zf_msg z), l_sp L,
                gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval, Vint (Int.repr (zf_dt z)),
                adler_v (raw_live (Some L)) z Vundef, zf_res z).
  (* position_of(&strm, &at) *)
  rewrite set_ses, pos_ses_.
  change (LS.mk_posz piece take tin outp room (zf_tout z)) with (pz_offer z piece take outp room).
  forward_call (vs, Tsh, pz_offer z piece take outp room,
                (msg_val gv (zf_msg z), l_sp L, gv Zlib.inflate.code._zcalloc, gv Zlib.inflate.code._zcfree, nullval,
                 Vint (Int.repr (zf_dt z)), adler_v (raw_live (Some L)) z Vundef, zf_res z), va, Tsh).
  { split; [auto|]. split; [auto|]. apply pz_offer_ok; auto; rep_lia. }
  unfold pz_offer at 1. rewrite <- set_ses.
  pose proof (pf_head P PF z L HP) as Hhd.
  sep_apply (offer_fold gv vs z Vundef L piece take data outp room bs); auto; try lia.
  sep_apply (bufs_pre_l vs L piece take data outp room bs); auto.
  (* code = inflate(&strm, any flush) *)
  forward_call tt. Intros u.
  assert (Eu: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Eu. clear Eu. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  assert (INOK: in_ok (ib_of piece take data) data) by (apply in_ok_of; auto; rep_lia).
  assert (OUTOK: out_ok (ob_of outp room bs) room) by (apply out_ok_of; auto; rep_lia).
  forward_call (gv, Tsh, vs, offer_z z (in_ptr (ib_of piece take data) 0) take (out_ptr (ob_of outp room bs) 0) room,
                Vundef, Some L, ib_of piece take data, data, Some (ob_of outp room bs), flush, Ers, Ers, true, true).
  { pose proof INOK as I'. pose proof OUTOK as O'. pose proof (pf_swf P PF z L HP) as [SW1 SW2]. unfold in_ok, ib_of in I'. unfold out_ok, ob_of in O'.
    decompose [and] I'. decompose [and] O'. repeat split; auto; try discriminate; simpl; try lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. simpl fst in *; simpl snd in *.
  match goal with H: inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into REL end.
  forward.
  forward_if.
  { forward. Exists (Int.repr 0). sep_apply pos_back. sep_apply a_frame_opt. entailer!. }
  assert (Hr: r <> Z_MEM_ERROR) by (intro E; subst r; contradiction).
  assert (REL': inflate_rel flush vs (offer_z z (in_ptr (ib_of piece take data) 0) (Zlength data)
                                        (out_ptr (ob_of outp room bs) 0) room)
                  (Some L) (ib_of piece take data) data (Some (ob_of outp room bs)) r z' st' ow)
    by (rewrite Hdl; exact REL).
  destruct (pf_inflate P PF z L vs flush (ib_of piece take data) data (ob_of outp room bs) room r z' st' ow
              HP HL Zo ltac:(intro E; subst vs; contradiction) Hfl ltac:(discriminate) INOK OUTOK
              ltac:(rep_lia) ltac:(rep_lia) REL' Hr)
    as (L' & Est & HP' & Hwrap & Hcode & Hai & Hao & Hni & Hno & Htin & Htout & How).
  subst st'.
  rewrite istreamA_opt_ptr by auto. rewrite head_none by (auto; eapply pf_head; eauto).
  sep_apply (bufs_post_l vs L piece take data outp room bs ow); auto; try lia. Intros.
  assert (AC: after_call z z' piece take outp room)
    by (apply (after_call_of z z' piece take data outp room bs); auto).
  (* the check: a documented return code *)
  match goal with |- semax _ ?Pre _ _ => apply semax_seq with Pre end.
  { destruct Hcode as [E|[E|[E|[E|E]]]]; subst r.
    - ifk _t'15 1. ifk _t'16 1. ifk _t'17 1. ifk _t'18 1. forward_call (Int.repr 1). entailer!.
    - ifk _t'15 1. ifk _t'16 1. ifk _t'17 1. ifk _t'18 1. forward_call (Int.repr 1). entailer!.
    - ifk _t'15 0. ifk _t'16 1. ifk _t'17 1. ifk _t'18 1. forward_call (Int.repr 1). entailer!.
    - ifk _t'15 0. ifk _t'16 0. ifk _t'17 1. ifk _t'18 1. forward_call (Int.repr 1). entailer!.
    - ifk _t'15 0. ifk _t'16 0. ifk _t'17 0. ifk _t'18 1. forward_call (Int.repr 1). entailer!. }
  (* if (take == 0 && room == 0) gp_assert(code != Z_OK && unmoved(&strm, &at)) *)
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  match goal with |- semax _ ?Pre _ _ => apply semax_seq with Pre end.
  { destruct (Z.eq_dec take 0) as [T0|T0]; [destruct (Z.eq_dec room 0) as [R0|R0] | ].
    - assert (Hnok: r <> Z_OK).
      { intros E. destruct (PG z L vs flush (ib_of piece take data) data (ob_of outp room bs) room r z' (Some L') ow
           HP HL Zo ltac:(intro E'; subst vs; contradiction) Hfl ltac:(discriminate) INOK OUTOK
           ltac:(rep_lia) ltac:(rep_lia) REL' E); lia. }
      assert (Eo: pz_of z' = pz_offer z piece take outp room).
      { rewrite T0, R0 in *. apply unmoved_after; auto. }
      ifpostv _t'21 (Vint (Int.repr 1));
        [forward; entailer!; rewrite R0; reflexivity
        | exfalso; match goal with H: Int64.repr take <> _ |- _ => apply H; rewrite T0; reflexivity end | ].
      forward_if; [ | infeas].
      ifpostv _t'19 (Vint (Int.repr 1)).
      { rewrite (istreamA_unfold gv Tsh vs z' Vundef L'). Intros. rewrite pk_ses.
        sep_apply (io_gather_unmoved z z' piece take (bytes_rep data) outp room
                     (bytes_rep (ow ++ sublist (Zlength ow) room bs))); auto.
        forward_call (vs, Tsh, pz_of z', rest_of gv z' (adler_v (raw_live (Some L')) z' Vundef) (l_sp L'), va, Tsh,
                      pz_offer z piece take outp room,
                      io_objs piece take (bytes_rep data) outp room (bytes_rep (ow ++ sublist (Zlength ow) room bs))).
        { split; [apply (pz_of_ok z z' piece take outp room); auto | apply pz_offer_ok; auto; rep_lia]. }
        replace (LS.unmoved_b (pz_of z') (pz_offer z piece take outp room)) with true
          by (rewrite Eo; symmetry; apply Zlib.proof.harness.laws_session.Facts.unmoved_b_iff; reflexivity).
        forward.
        unfold io_objs. rewrite <- pk_ses. sep_apply (istreamA_fold gv Tsh vs z' Vundef L'); auto.
        entailer!. }
      { exfalso. apply (code_ne0 r Hcode Hnok). assumption. }
      forward_call (Int.repr 1). entailer!.
    - ifpostv _t'21 (Vint (Int.repr 0));
        [forward; entailer!; rewrite Int64.eq_false; auto; intro E; apply R0;
         apply (f_equal Int64.unsigned) in E; rewrite !Int64.unsigned_repr in E by rep_lia; lia
        | exfalso; match goal with H: Int64.repr take <> _ |- _ => apply H; rewrite T0; reflexivity end | ].
      forward_if; [infeas | forward; entailer!].
    - ifpostv _t'21 (Vint (Int.repr 0));
        [exfalso; apply T0; match goal with H: Int64.repr take = _ |- _ =>
           apply (f_equal Int64.unsigned) in H; rewrite Int64.unsigned_repr in H by rep_lia; exact H end
        | forward; entailer! | ].
      forward_if; [infeas | forward; entailer!]. }
  sep_apply (pos_back Tsh (LS.pos_of (pz_offer z piece take outp room)) va).
  (* read += take - strm.avail_in *)
  unfold MORE_COMMANDS, abbreviate. abbreviate_semax.
  rewrite (istreamA_unfold gv Tsh vs z' Vundef L'). Intros. unfold pk_tup.
  forward.
  forward.
  rewrite (read_step tin take (zf_ai z')) by rep_lia.
  rewrite Hdl in Htin. fold tin in Htin. rewrite <- Htin.
  sep_apply (istreamA_fold gv Tsh vs z' Vundef L'); auto.
  (* free(piece); free(out) *)
  sep_apply (free_pre take (bytes_rep data) piece NP).
  forward_call (tarray tuchar take, piece, gv).
  sep_apply (free_pre room (bytes_rep (ow ++ sublist (Zlength ow) room bs)) outp NO).
  forward_call (tarray tuchar room, outp, gv).
  assert (Hz': zf_ok z') by assumption.
  assert (Ht': 0 <= zf_tin z' <= Zlength src) by (rewrite Htin, Z.mod_small by rep_lia; rep_lia).
  (* between calls: inflateSetDictionary of any bytes, or not *)
  forward_call tt. Intros c.
  forward_if.
  2: { forward. unfold pk_inv4. Exists z' L'. entailer!. }
  split_call. forward_call tt. Intros dl. forward. rewrite Int.unsigned_repr by rep_lia.
  split_call.
  forward_call (dl, gv).
  Intros vret. destruct vret as [dp d]. simpl fst in *; simpl snd in *.
  rewrite !bytes_a, !tok_a.
  forward.
  destruct (eq_dec dp nullval) as [ND|ND].
  { subst dp. if_seq. forward_if; [ | infeas].
    forward. forward_if; [ | infeas]. ret0a. }
  Intros. aptr dp Pdp.
  if_seq. forward_if; [infeas | ].
  rewrite (dict_i dl (bytes_rep d) dp), (dtok_i dl dp).
  rewrite <- (istreamA_opt_ptr gv Tsh vs z' Vundef (Some L')) by auto.
  forward_call (gv, Tsh, vs, z', Vundef, Some L', Ews, dp, 0, dl, bytes_rep d, d, true).
  { entailer!. destruct dp; try contradiction. simpl. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia.
    reflexivity. }
  { assert (Zlength (bytes_rep d) = dl) by (unfold bytes_rep; rewrite Zlength_map; auto).
    split; auto. rewrite sublist_same by lia. reflexivity. }
  Intros vret. destruct vret as [aok winp]. simpl fst in *; simpl snd in *.
  rewrite !on_live_fst, !on_live_snd, !on_live_thd by auto.
  set (sd := setdict_f d aok winp z' L') in *.
  forward.
  if_seq. forward_if.
  { forward. Exists (Int.repr 0). sep_apply a_frame_opt. entailer!. }
  match goal with H: Int.repr (fst3 sd) <> _ |- _ => rename H into Hnm end.
  assert (Hsd: fst3 sd <> Z_MEM_ERROR) by (intro E; apply Hnm; rewrite E; reflexivity).
  destruct (pf_setdict P PF z' L' d aok winp HP' ltac:(assumption) Hz' ltac:(assumption) ltac:(rep_lia) Hsd) as (Ez & HP'' & Hw'').
  fold sd in Ez, HP''. rewrite Ez.
  try rewrite <- (dict_i dl (bytes_rep d) dp). try rewrite <- (dtok_i dl dp).
  sep_apply (free_pre dl (bytes_rep d) dp ND).
  forward_call (tarray tuchar dl, dp, gv).
  rewrite istreamA_opt_ptr by auto.
  unfold pk_inv4. Exists z' (thd3 sd). entailer!.
Qed.
