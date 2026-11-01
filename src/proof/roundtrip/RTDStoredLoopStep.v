(* RT-D part STORED LOOP: one iteration of the first-phase loop of deflate_stored, with the bits it
   produces (the safety part is RTDLTCStoredLoop.ds_step, whose proof this extends). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDStoredLoopLib.
Require Export Zlib.proof.roundtrip.RTDLTCStoredLoop.
Require Import Zlib.proof.roundtrip.RTDLTCStoredSblk.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Local Strategy opaque [loop loop2].

(** The functional loop invariant, relative to the state [s0, z0] at the start and the bit position [p]. *)
Definition finv (s0 : dstate) (z0 : strm) (p : Z) (a : dstate * strm) : Prop :=
  let '(s, z) := a in
  exists k x bl,
    zstep (d_wrap s0) z0 z k x /\
    Forall (fun d => Zlength d <= 65535) bl /\
    concat bl = sublist (d_block_start s0) (d_block_start s) (mb_val (d_window s0)) ++
                sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0) /\
    F.bytes_bits (x ++ pend s) ++ bibits s = bibits s0 ++ enc_out p (map F.Stored bl) false /\
    (p + Zlength (enc_out p (map F.Stored bl) false) - d_bi_valid s) mod 8 = 0.

Definition ffin (s0 : dstate) (z0 : strm) (p : Z) (b : dstate * strm * Z) : Prop :=
  let '(s1, z1, last) := b in
  exists k x bl,
    zstep (d_wrap s0) z0 z1 k x /\
    Forall (fun d => Zlength d <= 65535) bl /\
    concat bl = sublist (d_block_start s0) (d_block_start s1) (mb_val (d_window s0)) ++
                sublist (z_next_in z0) (z_next_in z0 + k) (z_in z0) /\
    F.bytes_bits (x ++ pend s1) ++ bibits s1 = bibits s0 ++ enc_out p (map F.Stored bl) (last =? 1) /\
    (last = 1 -> bl <> []) /\
    (p + Zlength (enc_out p (map F.Stored bl) (last =? 1)) - d_bi_valid s1) mod 8 = 0.

Lemma ffin_top s0 z0 p s z : finv s0 z0 p (s, z) -> ffin s0 z0 p (s, z, 0).
Proof.
  intros (k & x & bl & H1 & H2 & H3 & H4 & H5). exists k, x, bl.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros E; discriminate|exact H5].
Qed.

Section FStep.
Variables (sbf : stored_block_fspec) (fpf : fpend_fspec2) (s0 : dstate) (z0 : strm) (flush p : Z).
Hypotheses (HW : W s0) (Hlev : d_level s0 = 0) (Hz0 : zall z0) (Ha0 : adler_ok (d_wrap s0) (z_adler z0))
  (Hf : 0 <= flush <= 5) (Hao0 : z_avail_out z0 <= 1073741824) (Hp : 0 <= p).

Lemma fds_step : forall a, linv s0 z0 flush a -> finv s0 z0 p a ->
  exists r, ds_body flush (ds_min_block s0) a = Some r /\
    match r with
    | inl a' => linv s0 z0 flush a' /\ finv s0 z0 p a'
    | inr b => ffin s0 z0 p b
    end.
Proof.
  intros [s z] Hinv Hfi. pose proof Hinv as
    (evs & k & x & Hob & Hbs & Hok & Hq & Hgr & Hzs & Hbx & Hao & Hk & Hk0 & Hch & Hev & Hl0).
  pose proof Hfi as Hfi0. destruct Hfi as (k' & x' & bl & Fz & Fbl & Fcat & Fbits & Falign).
  assert (Ekx : k' = k /\ x' = x).
  { destruct Fz as (_ & _ & N1 & _ & _ & _ & O1 & _), Hzs as (_ & _ & N2 & _ & _ & _ & O2 & _).
    split; [lia|]. apply (app_inv_head (z_out z0)). rewrite <- O1, <- O2. reflexivity. }
  destruct Ekx as [-> ->]. clear Fz.
  pose proof (s0_facts s0 HW) as (Hps & Hps1 & Hws1 & Hmb).
  pose proof HW as (_ & (Hwl & Hwmb & Hwsz & _) & (Hp1 & Hp2 & Hp3 & Hp4 & Hp5 & _) & Hwin & _ & _ & Hlz & _).
  destruct (Hlz Hlev) as [Hla0 Hbs0].
  assert (Ess : d_strstart s = d_strstart s0) by exact (f_equal d_strstart Hob).
  assert (Ewin : d_window s = d_window s0) by exact (f_equal d_window Hob).
  assert (Epbs : d_pending_buf_size s = d_pending_buf_size s0) by exact (f_equal d_pending_buf_size Hob).
  assert (Ewr : d_wrap s = d_wrap s0) by exact (f_equal d_wrap Hob).
  assert (Ela : d_lookahead s = d_lookahead s0) by exact (f_equal d_lookahead Hob).
  assert (Hz : zall z) by (eapply zall_zstep; eauto).
  assert (Ha : adler_ok (d_wrap s) (z_adler z)) by (rewrite Ewr; eapply zall_adler; [exact Hz0|exact Ha0|exact Hzs]).
  assert (HA0 : z_avail_out z <= z_avail_out z0)
    by (destruct Hzs as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); rewrite E; pose proof (Zlength_nonneg x); lia).
  destruct Hq as (Hq1 & Hq2 & Hq3).
  assert (Pend0 : pend s = []) by (unfold pend; rewrite Hq1, Hq2, Z.add_0_r; apply sublist_nil).
  rewrite Pend0, app_nil_r in Fbits.
  assert (Ob0 : obits (tr_out (d_tr s)) = bibits s).
  { unfold obits, bibits. change (o_pending (tr_out (d_tr s))) with (d_pending s). rewrite Hq1, sublist_nil.
    reflexivity. }
  pose proof Hok as (Hok1 & Hok2 & Hok3 & Hok4 & Hok5 & Hok6).
  assert (Hbv : 0 <= d_bi_valid s <= 7) by (destruct Hok2 as (? & _); unfold d_bi_valid in *; lia).
  pose proof (stored_hdr_eq s Hbv) as Ehdr.
  set (hdr := (d_bi_valid s + 42) / 8) in Ehdr.
  assert (Hhdr : 5 <= hdr <= 6) by (unfold hdr; Z.div_mod_to_equations; lia).
  assert (Ehdr' : hide (hdr = (d_bi_valid s + 42) / 8)) by (apply hide_i; reflexivity). clearbody hdr.
  pose proof Hz as ((Hzb & Hzn & Hzai & Hzl & Hzt) & (Hzo & Hzto & Hzs1)).
  assert (Hlb : Zlength (o_buf (tr_out (d_tr s))) = d_pending_buf_size s0) by (destruct Hgr as (G & _); lia).
  apply hide_i in Hmb.
  unfold ds_body. rewrite Ehdr.
  set (left := d_strstart s - d_block_start s).
  assert (Hleft : 0 <= left <= 16777216) by (unfold left; lia).
  set (ai := z_avail_in z) in *. set (A := z_avail_out z) in *.
  destruct (Z.ltb_spec A hdr) as [Lt|Ge].
  { exists (inr (s, z, 0)). split; [reflexivity|]. apply ffin_top; exact Hfi0. }
  rewrite (u32_id (A - hdr)) by lia.
  replace (in_long left) with true by (unfold in_long; zb). cbn [bind guard].
  rewrite (u32_id left) by lia. rewrite (u64_id (left + ai)) by lia. rewrite !(u32_id (left + ai)) by lia.
  unfold MAX_STORED. rewrite min3_eq.
  set (len := Z.min (Z.min 65535 (left + ai)) (A - hdr)).
  assert (Elen : len = Z.min (Z.min 65535 (left + ai)) (A - hdr)) by reflexivity. clearbody len.
  assert (Hlen : 0 <= len <= 65535 /\ len <= left + ai /\ len <= A - hdr) by lia.
  apply hide_i in Elen.
  rewrite (unhide _ Hmb). set (mb := Z.min (d_pending_buf_size s0 - 5) (d_w_size s0)).
  assert (Emb : mb = Z.min (d_pending_buf_size s0 - 5) (d_w_size s0)) by reflexivity. clearbody mb.
  assert (Hmb1 : mb <= 32768 /\ Z.min (d_pending_buf_size s0 - 6) (d_w_size s0) <= mb) by lia.
  apply hide_i in Emb. apply hide_i in Hmb1.
  assert (Eleft : left = d_strstart s - d_block_start s) by reflexivity. clearbody left.
  destruct ((len <? mb) && (((len =? 0) && negb (flush =? Z_FINISH)) || (flush =? Z_NO_FLUSH) ||
             negb (len =? left + ai))) eqn:Ebrk.
  { exists (inr (s, z, 0)). split; [reflexivity|]. apply ffin_top; exact Hfi0. }
  assert (Hcont : len < mb -> flush <> Z_NO_FLUSH /\ len = left + ai /\ (len = 0 -> flush = Z_FINISH))
    by (revert Ebrk; bsolve).
  apply hide_i in Hcont. clear Ebrk.
  set (last := if (flush =? Z_FINISH) && (len =? left + ai) then 1 else 0).
  assert (Hlast : (last = 1 /\ flush = Z_FINISH /\ len = left + ai) \/
                  (last = 0 /\ (flush <> Z_FINISH \/ len <> left + ai))) by (unfold last; bsolve).
  assert (Hl01 : 0 <= last <= 1) by (unfold last; bsolve).
  clearbody last. apply hide_i in Hlast.
  (* the empty stored block *)
  destruct (sblk_ok (tr_out (d_tr s)) (d_pbm s) [] 0 last) as (o1 & m1 & E1 & P1 & V1 & B1 & G1 & Gr1 & D1).
  { exact Hok2. } { lia. } { cbn; lia. } { unfold MAX_STORED; lia. } { constructor. }
  { destruct Hok1 as [H _]. exact H. }
  { rewrite Hlb. unfold d_pending, d_bi_valid in *. rewrite Hq1. rewrite <- (unhide _ Ehdr'). lia. }
  clear G1.
  (* F: the bits of the empty stored block *)
  assert (Fo1 : obits o1 = bibits s ++
            F.enc_block (p + Zlength (enc_out p (map F.Stored bl) false)) (last =? 1) (F.Stored [])).
  { rewrite <- Ob0.
    refine (proj2 (proj2 (sbf (tr_out (d_tr s)) (d_pbm s) [] 0 last o1 m1
                              (p + Zlength (enc_out p (map F.Stored bl) false)) Hok2 Hl01 _ _ _ _ _ E1))).
    - lia.
    - left; reflexivity.
    - constructor.
    - pose proof (Zlength_nonneg (enc_out p (map F.Stored bl) false)). lia.
    - exact Falign. }
  change (d_out s) with (tr_out (d_tr s), d_pbm s). rewrite E1. cbn [bind].
  assert (Pd1' : o_pending o1 = hdr).
  { change (o_pending (tr_out (d_tr s))) with (d_pending s) in P1.
    change (o_bi_valid (tr_out (d_tr s))) with (d_bi_valid s) in P1.
    rewrite Hq1, <- (unhide _ Ehdr') in P1. rewrite P1. ring. }
  clear P1.
  assert (L1' : Zlength (o_buf o1) = d_pending_buf_size s0) by (destruct Gr1 as (G & _); lia).
  assert (Fh : F.bytes_bits (sublist 0 (hdr - 4) (o_buf o1)) =
               bibits s ++ [last =? 1; false; false] ++
               F.zeros (F.pad8 (p + Zlength (enc_out p (map F.Stored bl) false) + 3))).
  { unfold obits in Fo1. rewrite Pd1', V1, bits_le_0, app_nil_r, enc_stored_eq in Fo1.
    rewrite (sublist_split 0 (hdr - 4) hdr) in Fo1 by lia. rewrite bytes_bits_app in Fo1.
    apply (app_inv_len _ (F.bytes_bits (sublist (hdr - 4) hdr (o_buf o1))) _ (F.bits_le 0 16 ++ F.bits_le 65535 16)).
    - rewrite Zlength_bytes_bits, Zlength_sublist, Zlength_app, !Zlength_bits_le by lia. lia.
    - rewrite Fo1. rewrite <- !app_assoc. reflexivity. }
  assert (Pd1 : d_pending (set_d_out s (o1, m1)) = hdr) by exact Pd1'.
  assert (L1 : Zlength (o_buf (tr_out (d_tr (set_d_out s (o1, m1))))) = d_pending_buf_size s0) by exact L1'.
  assert (Ok1 : outok (set_d_out s (o1, m1))).
  { apply outok_set_out.
    - apply (proj2 (proj2 (proj2 Gr1))). exact Hok1.
    - exact B1.
    - exact Hok3.
    - rewrite Pd1', Hq2, Epbs. lia.
    - rewrite Pd1', Hq2.
      unfold mb_defined; cbn [mb_val mb_def]. split; [lia|]. split; [lia|].
      intros i Hi. apply D1. change (o_pending (tr_out (d_tr s))) with (d_pending s). lia.
    - intros _. exact Hq2. }
  (* the length bytes *)
  destruct (pb_wr_ok (set_d_out s (o1, m1)) (u64 (d_pending (set_d_out s (o1, m1)) - 4)) (u8 len) Ok1
              ltac:(rewrite Pd1, u64_id by lia; lia) (u8_range _)) as (s2 & E2 & K2 & P2 & V2 & O2 & Ok2 & Gr2).
  rewrite E2. cbn [bind].
  assert (L2 : Zlength (o_buf (tr_out (d_tr s2))) = d_pending_buf_size s0) by (destruct Gr2 as (G & _); lia).
  destruct (pb_wr_ok s2 (u64 (d_pending s2 - 3)) (u8 (Z.shiftr len 8)) Ok2
              ltac:(rewrite P2, Pd1, u64_id by lia; lia) (u8_range _)) as (s3 & E3 & K3 & P3 & V3 & O3 & Ok3 & Gr3).
  rewrite E3. cbn [bind].
  assert (L3 : Zlength (o_buf (tr_out (d_tr s3))) = d_pending_buf_size s0) by (destruct Gr3 as (G & _); lia).
  destruct (pb_wr_ok s3 (u64 (d_pending s3 - 2)) (u8 (u32 (Z.lnot len))) Ok3
              ltac:(rewrite P3, P2, Pd1, u64_id by lia; lia) (u8_range _)) as (s4 & E4 & K4 & P4 & V4 & O4 & Ok4 & Gr4).
  rewrite E4. cbn [bind].
  assert (L4 : Zlength (o_buf (tr_out (d_tr s4))) = d_pending_buf_size s0) by (destruct Gr4 as (G & _); lia).
  destruct (pb_wr_ok s4 (u64 (d_pending s4 - 1)) (u8 (Z.shiftr (u32 (Z.lnot len)) 8)) Ok4
              ltac:(rewrite P4, P3, P2, Pd1, u64_id by lia; lia) (u8_range _)) as (s5 & E5 & K5 & P5 & V5 & O5 & Ok5 & Gr5).
  rewrite E5. cbn [bind].
  assert (L5 : Zlength (o_buf (tr_out (d_tr s5))) = d_pending_buf_size s0) by (destruct Gr5 as (G & _); lia).
  assert (Kp5 : fp_keep s5 = fp_keep s) by (rewrite K5, K4, K3, K2; apply fp_keep_set_d_out).
  assert (Pb5 : d_pending_buf_size s5 = d_pending_buf_size s0) by (rewrite <- Epbs; exact (f_equal d_pending_buf_size Kp5)).
  assert (Pd5 : d_pending s5 = hdr) by (rewrite P5, P4, P3, P2, Pd1; reflexivity).
  assert (Bv5 : d_bi_valid s5 = 0) by (rewrite V5, V4, V3, V2; exact V1).
  (* F: the patched length bytes *)
  assert (Buf5 : sublist 0 hdr (o_buf (tr_out (d_tr s5))) =
                 sublist 0 (hdr - 4) (o_buf o1) ++
                 [u8 len; u8 (Z.shiftr len 8); u8 (u32 (Z.lnot len)); u8 (Z.shiftr (u32 (Z.lnot len)) 8)]).
  { rewrite (proj1 (pb_wr_eq _ _ _ _ E5)), (proj1 (pb_wr_eq _ _ _ _ E4)), (proj1 (pb_wr_eq _ _ _ _ E3)),
      (proj1 (pb_wr_eq _ _ _ _ E2)).
    rewrite P4, P3, P2, Pd1, pj_out_tr. rewrite !u64_id by lia. apply sublist_upd4. lia. }
  assert (Fp5 : F.bytes_bits (pend s5) =
                bibits s ++ [last =? 1; false; false] ++
                F.zeros (F.pad8 (p + Zlength (enc_out p (map F.Stored bl) false) + 3)) ++
                F.bits_le len 16 ++ F.bits_le (65535 - len) 16).
  { unfold pend. rewrite O5, O4, O3, O2, pj_out_po, Hq2, Pd5, Z.add_0_l, Buf5, bytes_bits_app, Fh,
      len_bytes_bits by lia.
    rewrite <- !app_assoc. reflexivity. }
  (* flush_pending *)
  assert (Hr5 : fp_room s5) by (left; lia).
  destruct (fpend_ok s5 z ltac:(lia) ltac:(lia) Ok5 (proj2 Hz) Hr5)
    as (s6 & z6 & x1 & Ef & Zo & Bx1 & Lx & Pe & Bv6 & Ok6 & Gb6 & K6 & Gr6).
  assert (Hb5 : d_bi_valid s5 < 8 \/ d_po s5 = 0) by (left; lia).
  destruct (fpf s5 z s6 z6 Ok5 (proj2 Hz) Hb5 Ef) as (x1' & Zo' & Fp). clear Hb5.
  assert (x1' = x1).
  { destruct Zo as (_ & _ & _ & _ & _ & _ & Oa & _), Zo' as (_ & _ & _ & _ & _ & _ & Ob & _).
    apply (app_inv_head (z_out z)). rewrite <- Oa, <- Ob. reflexivity. }
  subst x1'. clear Zo'.
  assert (B5 : bibits s5 = []) by (unfold bibits; rewrite Bv5; reflexivity).
  rewrite B5, app_nil_r, Fp5 in Fp. clear Fp5 B5 Buf5 Fh Fo1.
  rewrite Ef. cbn [bind].
  assert (EA : A = z_avail_out z) by reflexivity. assert (Eai : ai = z_avail_in z) by reflexivity.
  clearbody A ai.
  assert (Gr6' : pb_grow (tr_out (d_tr s0)) (d_pbm s0) (tr_out (d_tr s6)) (d_pbm s6)).
  { eapply pb_grow_trans; [exact Hgr|]. eapply pb_grow_trans; [exact Gr1|].
    eapply pb_grow_trans; [exact Gr2|]. eapply pb_grow_trans; [exact Gr3|].
    eapply pb_grow_trans; [exact Gr4|]. eapply pb_grow_trans; [exact Gr5|]. exact Gr6. }
  assert (Kp6 : fp_keep s6 = fp_keep s) by (rewrite K6; exact Kp5).
  clear E1 E2 E3 E4 E5 K2 K3 K4 K5 K6 P2 P3 P4 P5 V2 V3 V4 V5 O2 O3 O4 O5 Ok1 Ok2 Ok3 Ok4 Ok5
    L1 L1' L2 L3 L4 L5 D1 Pd1 Pd1' Hr5 Ef Kp5 Pb5 Gr1 Gr2 Gr3 Gr4 Gr5 Gr6 Hgr Hok1 Hok5 Hinv.
  assert (Bs6 : d_block_start s6 = d_block_start s) by exact (f_equal d_block_start Kp6).
  assert (Ew6 : d_window s6 = d_window s0) by (rewrite <- Ewin; exact (f_equal d_window Kp6)).
  rewrite Pd5, Bv5 in Lx, Pe. rewrite Bv5 in Bv6. change (0 / 8) with 0 in Lx, Pe. change (0 mod 8) with 0 in Bv6.
  rewrite Z.add_0_r in Lx, Pe. rewrite Z.min_l in Lx by lia.
  assert (Fx1 : F.bytes_bits x1 =
                bibits s ++ [last =? 1; false; false] ++
                F.zeros (F.pad8 (p + Zlength (enc_out p (map F.Stored bl) false) + 3)) ++
                F.bits_le len 16 ++ F.bits_le (65535 - len) 16).
  { assert (E6 : pend s6 = []) by (unfold pend; replace (d_pending s6) with 0 by lia; rewrite Z.add_0_r; apply sublist_nil).
    assert (B6 : bibits s6 = []) by (unfold bibits; rewrite Bv6; reflexivity).
    rewrite E6, B6, !app_nil_r in Fp. exact Fp. }
  clear Fp.
  assert (Zs6 : zstep (d_wrap s) z z6 0 x1).
  { apply zout_only_zstep; [exact Hz|exact Ha|exact Zo|].
    destruct Zo as (_ & _ & _ & _ & _ & _ & _ & Za & _). lia. }
  clear Zo.
  pose proof Zs6 as (_ & _ & _ & Z64 & _ & _ & _ & _ & Z68 & Z69 & _).
  assert (Hz6 : zall z6) by (eapply zall_zstep; [exact Hz|exact Zs6|]; lia).
  assert (Ha6 : adler_ok (d_wrap s) (z_adler z6)) by (eapply zall_adler; [exact Hz|exact Ha|exact Zs6]).
  apply hide_i in Hzs. apply hide_i in Zs6. apply hide_i in Hz.
  (* the copy from the window *)
  assert (Hkw : 0 <= Z.min left len <= left /\ Z.min left len <= len /\
                (Z.min left len = left \/ Z.min left len = len)) by (clear - Hleft Hlen; lia).
  destruct (win_copy_ok2 (d_wrap s) s6 z6 len left) as (s7 & z7 & wb & E7 & Zs7 & Lwb & Bwb & Bs7 & Ob7 & Tr7 & Pbm7 & Po7 & Wb).
  { lia. } { lia. } { rewrite Bs6; lia. } { rewrite Bs6; lia. } { lia. } { lia. } { exact Hz6. } { exact Ha6. }
  { rewrite Ew6; exact Hwmb. }
  { rewrite Ew6, Bs6. unfold mb_defined. split; [lia|]. split; [lia|].
    intros i Hi. apply Hwin. lia. }
  cbv zeta in E7. rewrite E7. cbn [bind]. clear E7.
  set (kw := Z.min left len) in *. clearbody kw.
  rewrite Bs6, Ew6 in Wb.
  pose proof Zs7 as (_ & _ & _ & Z74 & _ & _ & _ & _ & Z78 & Z79 & _).
  assert (Hz7 : zall z7) by (eapply zall_zstep; [exact Hz6|exact Zs7|]; lia).
  assert (Ha7 : adler_ok (d_wrap s) (z_adler z7)) by (eapply zall_adler; [exact Hz6|exact Ha6|exact Zs7]).
  apply hide_i in Zs7. apply hide_i in Hz6.
  assert (Ob7' : ob_keep s7 = ob_keep s0) by (rewrite Ob7, <- Hob; unfold ob_keep; rewrite Kp6; reflexivity).
  assert (Wr7 : d_wrap s7 = d_wrap s0) by exact (f_equal d_wrap Ob7').
  pose proof Hz7 as ((_ & Hz7n & Hz7ai & Hz7l & _) & (Hz7o & _)).
  (* the copy from next_in *)
  destruct (in_copy_ok s7 z7 (len - kw)) as (z8 & E8 & Zs8).
  { lia. } { lia. } { lia. } { exact Hz7. } { rewrite Wr7, <- Ewr. exact Ha7. }
  cbv zeta in E8. rewrite E8. cbn [bind]. clear E8.
  set (data := sublist (z_next_in z7) (z_next_in z7 + (len - kw)) (z_in z7)) in *.
  assert (Ldata : Zlength data = len - kw) by (unfold data; rewrite Zlength_sublist by lia; lia).
  assert (Bdata : bytes data) by (unfold data; destruct Hz7 as ((Hb7 & _) & _); apply bytes_sublist; exact Hb7).
  assert (Edata : data = sublist (z_next_in z7) (z_next_in z7 + (len - kw)) (z_in z7)) by reflexivity.
  clearbody data.
  pose proof Zs8 as (_ & _ & _ & Z84 & _ & _ & _ & _ & Z88 & Z89 & _).
  apply hide_i in Zs8. apply hide_i in Hz7.
  (* the new state *)
  assert (T3 : zstep (d_wrap s0) z0 z8 (k + (len - kw)) (x ++ x1 ++ wb ++ data)).
  { apply unhide in Zs6, Zs7, Zs8, Hzs.
    rewrite Ewr in Zs6, Zs7. rewrite Wr7 in Zs8.
    pose proof (zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 Hzs Zs6) as T1.
    pose proof (zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 T1 Zs7) as T2.
    pose proof (zstep_trans _ _ _ _ _ _ _ _ (proj1 Hz0) Ha0 T2 Zs8) as T3.
    rewrite <- !app_assoc, !Z.add_0_r in T3. exact T3. }
  apply hide_i in T3.
  assert (Ao8 : z_avail_out z8 = A - hdr - len) by lia.
  rewrite (u64_id (z_total_out z + Zlength x1)) in Z69 by lia.
  rewrite (u64_id (z_total_out z6 + Zlength wb)) in Z79 by lia.
  rewrite (u64_id (z_total_out z7 + Zlength data)) in Z89 by lia.
  assert (To8 : z_total_out z8 = z_total_out z + hdr + len) by lia.
  assert (Ai8 : z_avail_in z8 = ai - (len - kw)) by lia.
  assert (Ss7 : d_strstart s7 = d_strstart s0) by exact (f_equal d_strstart Ob7').
  assert (La7 : d_lookahead s7 = 0) by (rewrite <- Hla0; exact (f_equal d_lookahead Ob7')).
  assert (Bs7' : d_block_start s7 = d_block_start s + kw) by (rewrite Bs7, Bs6; reflexivity).
  assert (Pbs7 : d_pending_buf_size s7 = d_pending_buf_size s6) by exact (f_equal d_pending_buf_size Ob7).
  assert (Ok7 : outok s7) by exact (outok_same s6 s7 Tr7 Pbm7 Po7 Pbs7 Ok6).
  assert (Pd7 : d_pending s7 = 0).
  { unfold d_pending; rewrite Tr7; fold (d_pending s6). rewrite Pe, Lx. ring. }
  assert (Bv7 : d_bi_valid s7 = 0) by (unfold d_bi_valid; rewrite Tr7; exact Bv6).
  assert (Q7 : quiet s7).
  { split; [exact Pd7|]. split; [|rewrite Bv7; lia]. destruct Ok7 as (_ & _ & _ & _ & _ & P0). exact (P0 Pd7). }
  assert (Gr7 : pb_grow (tr_out (d_tr s0)) (d_pbm s0) (tr_out (d_tr s7)) (d_pbm s7)) by (rewrite Tr7, Pbm7; exact Gr6').
  set (e := DStored (Gb s (z_total_out z)) len last).
  assert (Ch8 : ev_chain (Gb s0 (z_total_out z0)) (evs ++ [e]) (Gb s7 (z_total_out z8))).
  { apply (ev_chain_app _ _ _ _ _ Hch); [reflexivity|].
    unfold e, ev_after, Gb. rewrite Pd7, Bv7, Hq1, To8, !Z.add_0_r.
    rewrite gb_after by exact Hbv. rewrite <- (unhide _ Ehdr'). ring. }
  assert (Ev8 : Forall (ev_ok s0 flush) (evs ++ [e])).
  { apply Forall_app. split; [exact Hev|]. constructor; [|constructor].
    exact (ev_ok_blk s0 flush _ len last mb left ai Hlev ltac:(lia) Hl01 (unhide _ Hmb1) (unhide _ Hcont)
             (unhide _ Hlast)). }
  assert (Hub : k + (len - kw) + ub s0 = sum_len (evs ++ [e]) + ub s7).
  { rewrite sum_len_app. unfold ub in *. cbn [ev_len e]. rewrite Ss7, La7, Bs7'. rewrite Ess, Ela, Hla0 in Hk. lia. }
  rewrite Ess in Eleft.
  assert (Hk8 : 0 < k + (len - kw) -> d_block_start s7 = d_strstart s0).
  { intros Hpk. rewrite Bs7'. destruct (Z_lt_le_dec 0 k) as [Kp|Kp].
    - pose proof (Hk0 Kp) as B. clear - B Eleft Hkw. lia.
    - clear - Hpk Kp Eleft Hkw. lia. }
  assert (Hbs7 : d_block_start s0 <= d_block_start s7 <= d_strstart s0) by (rewrite Bs7'; clear - Hbs Eleft Hkw; lia).
  assert (Hx8 : bytes (x ++ x1 ++ wb ++ data)) by (apply Forall_app; split; [exact Hbx|];
    apply Forall_app; split; [exact Bx1|]; apply Forall_app; split; [exact Bwb|exact Bdata]).
  (* F: the new block *)
  assert (Eni7 : z_next_in z7 = z_next_in z0 + k /\ z_in z7 = z_in z0).
  { apply unhide in Zs6. apply unhide in Zs7. apply unhide in Hzs.
    destruct Hzs as (I0 & _ & N0 & _), Zs6 as (I6 & _ & N6 & _), Zs7 as (I7 & _ & N7 & _).
    split; [lia|congruence]. }
  assert (Hk0' : 0 <= k) by (apply unhide in Hzs; destruct Hzs as (_ & K & _); lia).
  assert (Hni0 : 0 <= z_next_in z0) by (destruct Hz0 as ((_ & N & _) & _); exact N).
  assert (Fcat' : concat (bl ++ [wb ++ data]) =
                  sublist (d_block_start s0) (d_block_start s7) (mb_val (d_window s0)) ++
                  sublist (z_next_in z0) (z_next_in z0 + (k + (len - kw))) (z_in z0)).
  { rewrite concat_app, Fcat. cbn [concat]. rewrite app_nil_r, Wb, Edata, (proj1 Eni7), (proj2 Eni7), Bs7'.
    assert (Hin0 : z_next_in z0 + k + (len - kw) <= Zlength (z_in z0))
      by (destruct Eni7 as [N I]; rewrite <- N, <- I; lia).
    replace (z_next_in z0 + k + (len - kw)) with (z_next_in z0 + (k + (len - kw))) by lia.
    destruct (Z_lt_le_dec 0 k) as [Kp|Kp].
    - assert (Hw0 : kw = 0) by (pose proof (Hk0 Kp); lia). rewrite Hw0.
      rewrite !Z.add_0_r, !Z.sub_0_r, sublist_nil, app_nil_l. rewrite <- app_assoc. f_equal.
      rewrite Hw0 in Hin0. apply sublist_rejoin; lia.
    - assert (k = 0) by lia. subst k.
      rewrite !Z.add_0_r, Z.add_0_l, sublist_nil, app_nil_r, app_assoc.
      rewrite Z.add_0_r in Hin0. rewrite sublist_rejoin by lia. reflexivity. }
  assert (Fbl' : Forall (fun d => Zlength d <= 65535) (bl ++ [wb ++ data]))
    by (apply Forall_app; split; [exact Fbl|]; constructor; [rewrite Zlength_app; lia|constructor]).
  assert (Fbits' : F.bytes_bits ((x ++ x1 ++ wb ++ data) ++ pend s7) ++ bibits s7 =
                   bibits s0 ++ enc_from p (map F.Stored bl) false ++
                   F.enc_block (p + Zlength (enc_from p (map F.Stored bl) false)) (last =? 1) (F.Stored (wb ++ data))).
  { assert (E7 : pend s7 = []) by (unfold pend; rewrite Pd7, Z.add_0_r; apply sublist_nil).
    assert (B7 : bibits s7 = []) by (unfold bibits; rewrite Bv7; reflexivity).
    rewrite E7, B7, !app_nil_r, enc_stored_eq, Zlength_app, Lwb, Ldata, !bytes_bits_app, Fx1.
    replace (kw + (len - kw)) with len by lia.
    rewrite <- !app_assoc. rewrite (app_assoc (F.bytes_bits x) (bibits s)), Fbits.
    rewrite <- !app_assoc. reflexivity. }
  apply unhide in Hlast.
  destruct Hlast as [(HL1 & HF & HL) | (HL0 & _)].
  - subst last. exists (inr (s7, z8, 1)). split; [reflexivity|].
    exists (k + (len - kw)), (x ++ x1 ++ wb ++ data), (bl ++ [wb ++ data]).
    split; [exact (unhide _ T3)|]. split; [exact Fbl'|]. split; [exact Fcat'|].
    change (1 =? 1) with true. rewrite map_app. cbn [map]. rewrite enc_out_stored_last.
    split; [exact Fbits'|].
    split; [intros _ E; symmetry in E; exact (app_cons_not_nil _ _ _ E)|].
    rewrite Bv7, Z.sub_0_r, <- enc_from_snoc. apply enc_from_stored_snoc_align.
  - subst last. exists (inl (s7, z8)). split; [reflexivity|]. split.
    2:{ exists (k + (len - kw)), (x ++ x1 ++ wb ++ data), (bl ++ [wb ++ data]).
        split; [exact (unhide _ T3)|]. split; [exact Fbl'|]. split; [exact Fcat'|].
        rewrite map_app. cbn [map]. rewrite enc_out_false, enc_from_snoc.
        split; [exact Fbits'|].
        rewrite Bv7, Z.sub_0_r, <- enc_from_snoc. apply enc_from_stored_snoc_align. }
    exists (evs ++ [e]), (k + (len - kw)), (x ++ x1 ++ wb ++ data).
    split; [exact Ob7'|]. split; [exact Hbs7|]. split; [exact Ok7|]. split; [exact Q7|]. split; [exact Gr7|].
    split; [exact (unhide _ T3)|]. split; [exact Hx8|]. split; [lia|]. split; [exact Hub|]. split; [exact Hk8|].
    split; [exact Ch8|]. split; [exact Ev8|].
    apply Forall_app. split; [exact Hl0|]. constructor; [reflexivity|constructor].
Qed.

End FStep.
