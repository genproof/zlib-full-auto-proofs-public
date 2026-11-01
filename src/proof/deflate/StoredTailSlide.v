(** * deflate_stored, second phase, part 1 (StoredTailKit.S_p2_slide): [have = (unsigned)(s->window_size -
    s->strstart);] and the slide of the window when more input is waiting and block_start >= w_size
    (zmemcpy(s->window, s->window + s->w_size, s->strstart)), against StoredTailKit.ds_slide. *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.deflate.StoredTailKit.
Require Import Zlib.proof.deflate.StoredSlideKit.
Require Import Zlib.proof.zutil.Libc.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

Lemma slide_state_bs s win1 :
  clamp_insert (incr_matches (set_d_window (set_d_strstart (set_d_block_start s (d_block_start s - d_w_size s))
    (u32 (d_strstart s - d_w_size s))) win1)) =
  upd_win s (if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s) win1
    (u32 (d_strstart s - d_w_size s))
    (if d_insert s >? u32 (d_strstart s - d_w_size s) then u32 (d_strstart s - d_w_size s) else d_insert s)
    (d_block_start s - d_w_size s).
Proof.
  destruct s as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? [] ?].
  unfold clamp_insert, incr_matches, upd_win, d_matches. cbn.
  destruct (_ <? 2); destruct (_ >? _); reflexivity.
Qed.

Lemma ds_slide_true s z s1 h :
  ds_slide s z = Some (s1, h) ->
  andb (z_avail_in z >? u32 (u64 (d_window_size s - d_strstart s))) (d_block_start s >=? d_w_size s) = true ->
  exists win1, mb_move (d_window s) 0 (d_w_size s) (u32 (d_strstart s - d_w_size s)) = Some win1 /\
  s1 = upd_win s (if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s) win1
    (u32 (d_strstart s - d_w_size s))
    (if d_insert s >? u32 (d_strstart s - d_w_size s) then u32 (d_strstart s - d_w_size s) else d_insert s)
    (d_block_start s - d_w_size s) /\
  h = u32 (u32 (u64 (d_window_size s - d_strstart s)) + d_w_size s).
Proof.
  unfold ds_slide. intros H E. rewrite E in H.
  cbn [d_window d_w_size d_strstart set_d_strstart set_d_block_start] in H.
  destruct (mb_move _ _ _ _) as [win1|] eqn:Em; cbn in H; [|discriminate].
  exists win1. split; [reflexivity|]. inversion H; subst; clear H.
  split; [rewrite <- slide_state_bs; reflexivity|].
  unfold incr_matches. destruct (_ <? 2); reflexivity.
Qed.

Lemma ds_slide_false s z s1 h :
  ds_slide s z = Some (s1, h) ->
  andb (z_avail_in z >? u32 (u64 (d_window_size s - d_strstart s))) (d_block_start s >=? d_w_size s) = false ->
  s1 = s /\ h = u32 (u64 (d_window_size s - d_strstart s)).
Proof. unfold ds_slide. intros H E. rewrite E in H. inversion H; auto. Qed.

Lemma st_slide_frag {Espec : OracleKind} (p : dptrs) (pin pout : val) (ish : share) (rest : list val)
    (msgv : val) (gv : globals) (s : dstate) (z : strm) (flush : Z) (s1 : dstate) (h : Z) :
  ds_slide s z = Some (s1, h) ->
  semax Delta_ds
    (PROP () LOCAL (temp _last (vi 0); gvars gv; temp _s (p_s p); temp _flush (vi flush))
     SEP (dfull s z p pin pout ish rest msgv gv; deflate_globals gv))
    S_p2_slide
    (normal_ret_assert
      (PROP () LOCAL (temp _have (vi h); temp _last (vi 0); gvars gv; temp _s (p_s p); temp _flush (vi flush))
       SEP (dfull s1 z p pin pout ish rest msgv gv; deflate_globals gv))).
Proof.
  intros Hm.
  cbv [S_p2_slide S_phase2 sub f_deflate_stored fn_body].
  sep_apply (dfull_open s z p pin pout ish rest msgv gv). Intros. rename H into Hwp.
  pose proof (win_pure_ranges _ _ _ _ Hwp) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & Rz & Ri).
  assert (Ra : 0 <= z_avail_in z <= Int.max_unsigned)
    by (destruct Rz as (_ & _ & _ & _ & Hu & _); unfold u32_ok in Hu; lia).
  unfold wfields, wframe. Intros.
  forward. forward. forward.
  forward. forward.
  set (h0 := u32 (u64 (d_window_size s - d_strstart s))).
  match goal with |- context [temp _have ?v] =>
    replace v with (vi h0) by (unfold h0; rewrite vi_u32'; unfold vi;
                                rewrite (Int.unsigned_repr (d_strstart s)) by lia; rewrite u64_sub_unsigned'; reflexivity)
  end.
  assert (Rh0 : 0 <= h0 <= Int.max_unsigned) by apply u32_range'.
  forward_if (temp _t'11 (Val.of_bool ((z_avail_in z >? h0) && (d_block_start s >=? d_w_size s)))).
  - forward. forward. forward.
    try rewrite Int.unsigned_repr in H by lia.
    entailer!.
    rewrite (proj2 (Z.gtb_lt _ _) H). cbn [andb]. unfold Int64.cmp, Int64.lt.
    rewrite ?Int.unsigned_repr by lia. rewrite !Int64.signed_repr by rep_lia.
    destruct (zlt _ _); destruct (Z.geb_spec (d_block_start s) (d_w_size s)); try lia; reflexivity.
  - forward. try rewrite Int.unsigned_repr in H by lia.
    entailer!.
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge h0 (z_avail_in z)) ltac:(lia)). reflexivity.
  - destruct (andb (z_avail_in z >? h0) (d_block_start s >=? d_w_size s)) eqn:Ec.
    + destruct (ds_slide_true s z s1 h Hm Ec) as (win1 & Hm1 & -> & ->).
      apply andb_prop in Ec as [Ec1 Ec2]. apply Z.geb_le in Ec2. apply Z.gtb_lt in Ec1.
      forward_if.
      * forward. forward. forward.
        forward. forward. forward.
        replace (Vlong (Int64.sub (Int64.repr (d_block_start s)) (Int64.repr (Int.unsigned (Int.repr (d_w_size s))))))
          with (vl (d_block_start s - d_w_size s))
          by (unfold vl; rewrite Int.unsigned_repr by lia; rewrite sub64_repr; reflexivity).
        set (st1 := u32 (d_strstart s - d_w_size s)) in *.
        replace (Vint (Int.sub (Int.repr (d_strstart s)) (Int.repr (d_w_size s)))) with (vi st1)
          by (unfold st1; rewrite vi_u32'; unfold vi; rewrite sub_repr; reflexivity).
        assert (Rst1 : 0 <= st1 <= Int.max_unsigned) by apply u32_range'.
        assert (Hle : st1 <= d_w_size s) by (eapply mb_move_le; [lia | lia | exact Hm1]).
        assert_PROP (field_compatible (tarray tuchar (Zlength (mb_val (d_window s)))) [] (p_window p)) as FCw
          by entailer!.
        destruct (win_join_move Ews (d_window s) (p_window p) (d_w_size s) st1 win1 R2 Hm1 Hle FCw)
          as (bytes1 & Hr1 & Fb1 & Lb1 & Hok1 & Lw1 & J).
        forward. forward. forward. forward.
        rewrite <- Lb1 in Hr1, J.
        sep_apply (win_split_move Ews (d_window s) (p_window p) (d_w_size s) (Zlength bytes1) bytes1 R2 Hr1
                     ltac:(lia)).
        Intros.
        change (map vi bytes1) with (byte_vals bytes1).
        forward_call (Ews, p_window p, Ews, offset_val (d_w_size s) (p_window p), bytes1).
        { assert (isptr (p_window p)) by auto.
          entailer!. destruct (p_window p); try contradiction.
          simpl. unfold vi. rewrite ptr_add_uint by lia. rewrite Int.unsigned_repr by lia.
          rewrite Lb1. reflexivity. }
        all: try match goal with |- bytes_ok _ => apply bytes_ok_256; auto | |- _ |-- _ => cancel end.
        rewrite !byte_vals_vi. sep_apply J. clear J.
        forward.
        forward_if (PROP () LOCAL (temp _have (vi h0); temp _last (vi 0); gvars gv; temp _s (p_s p);
                                   temp _flush (vi flush))
          SEP (wframe s z p pout rest msgv gv;
               wfields s z p pin ish (if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s) win1 st1
                 (d_insert s) (d_block_start s - d_w_size s);
               deflate_globals gv)).
        -- forward. forward.
           unfold wfields, wframe. rewrite (proj2 (Z.ltb_lt _ _) H0), vi_u32', add_repr.
           change (Vint (Int.repr (d_matches s + 1))) with (vi (d_matches s + 1)).
           entailer!.
        -- forward.
           rewrite (proj2 (Z.ltb_ge (d_matches s) 2) ltac:(lia)).
           unfold wfields, wframe. entailer!.
        -- unfold wfields. Intros.
           forward. forward.
           replace (Vint (Int.add (Int.repr h0) (Int.repr (d_w_size s)))) with (vi (u32 (h0 + d_w_size s)))
             by (rewrite vi_u32'; unfold vi; rewrite add_repr; reflexivity).
           forward. forward.
           assert (Hma : 0 <= (if d_matches s <? 2 then u32 (d_matches s + 1) else d_matches s) <= Int.max_unsigned)
             by (destruct (_ <? 2); [apply u32_range' | lia]).
           assert (Rbs : Int64.min_signed <= d_block_start s - d_w_size s <= Int64.max_signed) by rep_lia.
           forward_if.
           ++ forward. forward.
              rewrite (proj2 (Z.gtb_lt (d_insert s) st1) H0).
              change (Vint (Int.repr st1)) with (vi st1).
              pose proof (dfull_fold s z p pin pout ish rest msgv gv _ win1 st1 st1 (d_block_start s - d_w_size s)
                            Hwp Hma Hok1 ltac:(lia) Rst1 Rst1 Rbs) as F.
              unfold wfields in F. sep_apply F. clear F. entailer!.
           ++ forward.
              rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge st1 (d_insert s)) ltac:(lia)).
              pose proof (dfull_fold s z p pin pout ish rest msgv gv _ win1 st1 (d_insert s)
                            (d_block_start s - d_w_size s) Hwp Hma Hok1 ltac:(lia) Rst1 R7 Rbs) as F.
              unfold wfields in F. sep_apply F. clear F. entailer!.
      * inv H.
    + destruct (ds_slide_false s z s1 h Hm Ec) as [-> ->].
      forward_if.
      * contradiction.
      * forward.
        pose proof (dfull_fold s z p pin pout ish rest msgv gv (d_matches s) (d_window s) (d_strstart s)
                      (d_insert s) (d_block_start s) Hwp R8 R2 R3 R6 R7 R5) as F.
        unfold wfields, wframe in F. rewrite upd_win_id in F. sep_apply F. clear F. entailer!.
Qed.
