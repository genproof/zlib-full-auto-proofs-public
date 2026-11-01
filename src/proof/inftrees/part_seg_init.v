(* Part: the segment seg_init of the body of inflate_table (verif_it_defs.v). *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inftrees.
Require Import Zlib.inftrees.code.
Require Import Zlib.proof.inftrees.verif_it_defs.

#[local] Existing Instance Inftrees.CS.
#[local] Arguments counts : simpl never.

Lemma seg_init_maxlen_le : forall l, Forall (fun x => 0 <= x <= MAXBITS) l -> 0 <= maxlen l <= 15.
Proof.
  induction 1; unfold maxlen in *; simpl; unfold MAXBITS in *; lia.
Qed.

Lemma seg_init_minlen_le : forall l, Forall (fun x => 0 <= x <= MAXBITS) l -> 0 <= minlen l <= 16.
Proof.
  induction 1; unfold minlen in *; simpl; [lia|].
  destruct (x =? 0); lia.
Qed.

Lemma seg_init_model_enough : forall type lens req old,
  1 <= maxlen lens -> acc_test type lens -> over type (Z.shiftl 1 (root_of req lens)) = true ->
  inflate_table_model type lens req old = REnough old.
Proof.
  intros type lens req old H1 [lft [E F]] O.
  unfold inflate_table_model. destruct (maxlen lens =? 0) eqn:M; [lia|].
  rewrite E, F, O. reflexivity.
Qed.

Lemma seg_init_ltb : forall a b, bool2val (zlt a b) = Vint (Int.repr (Z.b2z (a <? b))).
Proof.
  intros. destruct (zlt a b) as [Hl|Hl].
  - rewrite (proj2 (Z.ltb_lt _ _) Hl). reflexivity.
  - rewrite (proj2 (Z.ltb_ge a b) ltac:(lia)). reflexivity.
Qed.

Lemma seg_init_ok : loop_facts -> seg_init_stmt.
Proof.
  intros LF Espec X WF.
  destruct X as [type lens req old gv shg shl sh pl pw ptab pt pb here count offs].
  unfold it_wf in WF; cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs] in WF.
  destruct WF as (Hshg & Hshl & Hsh & Hin & Hold & Hcap).
  unfold A_sorted, A_loop, it_sep, params_locs, POST_it, it_model, base_v, extra_v, it_mx, it_root,
    count_at, work_sorted, init_state;
  cbn [c_type c_lens c_req c_old c_gv c_shg c_shl c_sh c_pl c_pw c_ptab c_pt c_pb c_here c_count c_offs
       s_huff s_sym s_len s_curr s_drop s_low s_used s_next s_cnt s_tab].
  unfold Delta_it. simplify_func_tycontext. unfold seg_init. abbreviate_semax.
  assert (Ht: type = 0 \/ type = 1 \/ type = 2) by (destruct Hin; lia).
  match goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: _ :: _ :: _ :: _ :: ?Q) (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _min (Vint (Int.repr (minlen lens))) ::
     temp _max (Vint (Int.repr (maxlen lens))) ::
     temp _root (Vint (Int.repr (root_of req lens))) ::
     temp _base (if type =? LENS then gv _lbase else if type =? DISTS then gv _dbase else nullval) ::
     temp _extra (if type =? LENS then gv _lext else if type =? DISTS then gv _dext else nullval) ::
     temp _match (Vint (Int.repr (match_of type))) :: Q) (SEPx R)))
  end.
  { forward. forward. entailer!. }
  { forward. forward. forward. forward. entailer!. }
  { forward. forward. forward. entailer!. }
  { exfalso; destruct Ht as [ -> | [ -> | -> ] ]; auto. }
  destruct Hin as (Htype & Hcodes & Hlens & Hreq).
  pose proof (seg_init_maxlen_le _ Hlens) as Hmx.
  pose proof (seg_init_minlen_le _ Hlens) as Hmn.
  assert (Hroot: 0 <= root_of req lens <= 16) by (unfold root_of; lia).
  forward. forward. forward. forward. forward. forward. forward.
  forward. { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  forward.
  set (u := Z.shiftl 1 (root_of req lens)).
  assert (Hu: 1 <= u <= 65536).
  { unfold u. rewrite Z.shiftl_1_l. split. apply (Z.pow_le_mono_r 2 0); lia.
    apply (Z.pow_le_mono_r 2 _ 16); lia. }
  assert (Hsh1: Int.shl (Int.repr 1) (Int.repr (root_of req lens)) = Int.repr u).
  { unfold Int.shl. rewrite !Int.unsigned_repr by rep_lia. reflexivity. }
  rewrite Hsh1, sub_repr.
  assert (Hudef: u = Z.shiftl 1 (root_of req lens)) by reflexivity.
  clearbody u.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'3 (Vint (Int.repr (Z.b2z ((type =? 1) && (852 <? u))%bool))) :: Q) (SEPx R)))
  end.
  { forward. entailer!. rewrite seg_init_ltb. reflexivity. }
  { forward. entailer!. rewrite (proj2 (Z.eqb_neq _ _) H1). reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx P (LOCALx (temp _t'4 (Vint (Int.repr (Z.b2z (over type u)))) :: Q) (SEPx R)))
  end.
  { forward. entailer!. unfold over, LENS, ENOUGH_LENS. rewrite H1. reflexivity. }
  { forward_if.
    { forward. forward. entailer!. rewrite seg_init_ltb. reflexivity. }
    { forward. entailer!. destruct Ht as [ -> | [ -> | -> ] ]; try congruence; unfold over, LENS, DISTS, ENOUGH_LENS in *; simpl in H1 |- *; rewrite ?H1; reflexivity. } }
  forward_if.
  { forward.
    rewrite (seg_init_model_enough type lens req old) by (auto; rewrite <- Hudef; auto).
    cbn [it_ret it_tab it_adv it_bits]. rewrite Z.mul_0_r.
    assert_PROP (isptr pt) by entailer!. rewrite isptr_offset_val_zero by auto.
    entailer!. }
  { forward. subst u.
    assert_PROP (isptr pt) by entailer!. rewrite Z.mul_0_r, isptr_offset_val_zero by auto.
    replace (Int.neg (Int.repr 1)) with (Int.repr (Z.ones 32))
      by (rewrite Int.neg_repr; apply Int.eqm_samerepr; exists 1; reflexivity).
    entailer!. }
Qed.
