(** * The output of deflate at level 0: [l0_trail_stmt] (see Level0Stmts.v) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.Level0Stmts.
Import ListNotations.
Local Open Scope Z_scope.

(** put_byte appends at pending_buf[pending] while there is room in the buffer: pending grows by one, the bytes
    [0, pending) stay defined and the new one is defined; pending_out, bi_valid and wrap are kept. Only the
    lengths of pending_buf and of its mask are needed (the values of the trailer bytes do not matter). *)
Lemma l0t_dput_byte : forall s c,
  Zlength (d_pbm s) = Zlength (o_buf (tr_out (d_tr s))) -> 0 <= d_pending s ->
  d_pending s + 1 <= Zlength (o_buf (tr_out (d_tr s))) -> mb_defined (d_pb s) 0 (d_pending s) ->
  exists s1, c_dput_byte s c = Some s1 /\
    Zlength (d_pbm s1) = Zlength (o_buf (tr_out (d_tr s1))) /\
    Zlength (o_buf (tr_out (d_tr s1))) = Zlength (o_buf (tr_out (d_tr s))) /\
    d_pending s1 = d_pending s + 1 /\ mb_defined (d_pb s1) 0 (d_pending s1) /\
    d_po s1 = d_po s /\ d_bi_valid s1 = d_bi_valid s /\ d_wrap s1 = d_wrap s.
Proof.
  intros s c Hm Hp Hr (_ & _ & Hd).
  unfold d_pending, d_bi_valid, d_pb in *. cbn [mb_val mb_def] in Hd.
  unfold c_dput_byte, c_put_byte, d_out.
  destruct (tr_out (d_tr s)) as [b pn bb bv bu] eqn:Eo. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  unfold wr.
  replace (in_range pn (Zlength b)) with true
    by (symmetry; unfold in_range; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  cbn [bind]. eexists; split; [reflexivity|].
  cbn [set_d_out fst snd tr_out d_tr d_pbm d_po d_wrap set_d_pbm set_d_tr set_out o_buf o_pending o_bi_valid].
  rewrite !upd_Znth_Zlength by lia.
  split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|repeat split].
  unfold mb_defined. cbn [mb_val mb_def]. rewrite upd_Znth_Zlength by lia.
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.eq_dec i pn) as [->|Ne].
  - rewrite upd_Znth_same by lia. reflexivity.
  - rewrite upd_Znth_diff by lia. apply Hd. lia.
Qed.

(** The same for a list of bytes. *)
Lemma l0t_dput_bytes : forall l s,
  Zlength (d_pbm s) = Zlength (o_buf (tr_out (d_tr s))) -> 0 <= d_pending s ->
  d_pending s + Zlength l <= Zlength (o_buf (tr_out (d_tr s))) -> mb_defined (d_pb s) 0 (d_pending s) ->
  exists s1, c_dput_bytes s l = Some s1 /\
    d_pending s1 = d_pending s + Zlength l /\ mb_defined (d_pb s1) 0 (d_pending s1) /\
    d_po s1 = d_po s /\ d_bi_valid s1 = d_bi_valid s /\ d_wrap s1 = d_wrap s.
Proof.
  induction l as [|c l IH]; intros s Hm Hp Hr Hd.
  - exists s. rewrite Zlength_nil, Z.add_0_r. split; [reflexivity|]. split; [lia|]. split; [exact Hd|]. auto.
  - rewrite Zlength_cons in Hr. pose proof (Zlength_nonneg l).
    destruct (l0t_dput_byte s c) as (s1 & E1 & Hm1 & Hl1 & Hp1 & Hd1 & Ho1 & Hb1 & Hw1); auto; [lia|].
    destruct (IH s1) as (s2 & E2 & Hp2 & Hd2 & Ho2 & Hb2 & Hw2); auto; [lia..|].
    exists s2. cbn [c_dput_bytes]. rewrite E1. cbn [bind].
    rewrite Zlength_cons. split; [exact E2|]. split; [lia|]. split; [exact Hd2|]. split; [|split]; congruence.
Qed.

(** flush_pending with whole bytes only (bi_valid = 0), pending_out = 0 and room for all [n] pending bytes at
    next_out: the [n] bytes are appended to the output and nothing stays pending. *)
Lemma l0t_flush_all : forall s z,
  d_bi_valid s = 0 -> d_po s = 0 -> 0 <= d_pending s <= z_avail_out z ->
  mb_defined (d_pb s) 0 (d_pending s) -> 0 <= z_total_out z -> z_total_out z + z_avail_out z <= 4294967295 ->
  exists s' z' T, c_flush_pending s z = Some (s', z') /\
    z_out z' = z_out z ++ T /\ Zlength T = d_pending s /\ z_total_out z' = z_total_out z + d_pending s /\
    d_pending s' = 0 /\ d_wrap s' = d_wrap s.
Proof.
  intros s z Hbv Hpo Hp Hd Ht0 Ht.
  unfold c_flush_pending, c_tr_flush_bits, c_bi_flush, d_out.
  unfold d_bi_valid, d_pending, d_pb in *.
  destruct (tr_out (d_tr s)) as [b pn bb bv bu] eqn:Eo. cbn [o_buf o_pending o_bi_buf o_bi_valid o_bi_used] in *.
  subst bv. cbn [Z.eqb Z.geb Z.compare negb]. cbn [bind].
  cbn [set_d_out fst snd tr_out d_tr d_pbm d_po d_wrap set_d_pbm set_d_tr set_out o_buf o_pending].
  rewrite Hpo.
  replace (if pn >? z_avail_out z then z_avail_out z else u32 pn) with pn.
  2: { destruct (Z.gtb_spec pn (z_avail_out z)); [lia|]. unfold u32. rewrite Z.mod_small by lia. reflexivity. }
  destruct (Z.eqb_spec pn 0) as [P0|P0].
  - exists (set_d_out s (mkOut b pn bb 0 bu, d_pbm s)), z, []. rewrite app_nil_r, Zlength_nil, P0, Z.add_0_r.
    repeat split; reflexivity.
  - unfold mb_read.
    replace ((0 <=? pn) && mb_definedb (mkMB b (d_pbm s)) 0 (0 + pn)) with true.
    2: { symmetry. apply andb_true_iff. split; [apply Z.leb_le; lia|]. rewrite Z.add_0_l.
         destruct Hd as (D0 & D1 & D2). unfold mb_definedb. cbn [mb_val mb_def] in *.
         apply andb_true_iff. split; [apply andb_true_iff; split; [apply Z.leb_le|apply Z.leb_le]; lia|].
         apply forallb_forall. intros i Hi. apply in_map_iff in Hi. destruct Hi as (k & <- & Hk).
         apply in_seq in Hk. apply D2. lia. }
    cbn [bind mb_val]. unfold out_put. rewrite Zlength_sublist by (destruct Hd as (_ & D1 & _); cbn in D1; lia).
    replace (0 + pn - 0 <=? z_avail_out z) with true by (symmetry; apply Z.leb_le; lia).
    cbn [bind set_d_out set_d_po fst snd tr_out d_tr d_pbm d_po d_wrap set_d_pbm set_d_tr set_out o_buf
         o_pending o_bi_buf o_bi_valid o_bi_used d_pending].
    rewrite Z.sub_diag. cbn [Z.eqb].
    do 3 eexists. split; [reflexivity|].
    cbn [z_out z_total_out set_z_out set_z_total_out set_z_avail_out d_pending d_wrap set_d_po set_d_out
         set_d_pbm set_d_tr set_out tr_out d_tr fst snd o_pending].
    unfold u64. rewrite Z.mod_small by lia.
    split; [reflexivity|].
    rewrite Zlength_sublist by (destruct Hd as (_ & D1 & _); cbn in D1; lia).
    repeat split; lia.
Qed.

Theorem l0_trail : l0_trail_stmt.
Proof.
  intros s z Hok Hpd Hpo Hbv Hbuf Hw Hroom Ht0 Ht.
  unfold c_deflate_trailer. cbn [Z.eqb negb].
  destruct (Z.leb_spec (d_wrap s) 0) as [W0|W0].
  { exists s, z, []. rewrite app_nil_r. replace (d_wrap s) with 0 by lia. cbn. rewrite Z.add_0_r. auto. }
  destruct Hok as ((Hm & _) & _ & _ & _ & _ & _). unfold d_pb in Hm. cbn [mb_val mb_def] in Hm.
  assert (Hd0 : mb_defined (d_pb s) 0 (d_pending s)).
  { rewrite Hpd. unfold mb_defined, d_pb. cbn [mb_val]. pose proof (Zlength_nonneg (o_buf (tr_out (d_tr s)))).
    split; [lia|]. split; [lia|]. intros; lia. }
  set (a := z_adler z). set (t := z_total_in z).
  assert (Hput : exists s1,
    (if d_wrap s =? 2 then
       c_dput_bytes s [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255;
                       Z.land (Z.shiftr a 24) 255; Z.land t 255; Z.land (Z.shiftr t 8) 255;
                       Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
     else
       let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in
       c_putShortMSB s (u32 (Z.land a 65535))) = Some s1 /\
    d_pending s1 = tlr_len (d_wrap s) /\ mb_defined (d_pb s1) 0 (d_pending s1) /\
    d_po s1 = 0 /\ d_bi_valid s1 = 0 /\ d_wrap s1 = d_wrap s).
  { destruct (Z.eqb_spec (d_wrap s) 2) as [E2|E2].
    - match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
        destruct (l0t_dput_bytes l s) as (s1 & E & P & D & O & B & Wr); auto; try (rewrite Hpd; cbn; lia) end.
      exists s1. split; [exact E|].
      split; [rewrite P, Hpd, E2; reflexivity|]. split; [exact D|]. rewrite O, B, Wr, Hpo, Hbv. auto.
    -
      (* the two putShortMSB are four put_byte *)
      replace (let* s := c_putShortMSB s (u32 (Z.shiftr a 16)) in c_putShortMSB s (u32 (Z.land a 65535)))
        with (c_dput_bytes s [Z.shiftr (u32 (Z.shiftr a 16)) 8; Z.land (u32 (Z.shiftr a 16)) 255;
                              Z.shiftr (u32 (Z.land a 65535)) 8; Z.land (u32 (Z.land a 65535)) 255]).
      2: { unfold c_putShortMSB. cbn [c_dput_bytes].
           destruct (c_dput_byte s _) as [s2|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s2 _) as [s3|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s3 _) as [s4|]; cbn [bind]; [|reflexivity].
           destruct (c_dput_byte s4 _); reflexivity. }
      match goal with |- exists s1, c_dput_bytes _ ?l = _ /\ _ =>
        destruct (l0t_dput_bytes l s) as (s1 & E & P & D & O & B & Wr); auto; try (rewrite Hpd; cbn; lia) end.
      exists s1. split; [exact E|].
      split; [rewrite P, Hpd; replace (d_wrap s) with 1 by lia; reflexivity|]. split; [exact D|].
      rewrite O, B, Wr, Hpo, Hbv. auto. }
  destruct Hput as (s1 & E1 & P1 & D1 & O1 & B1 & Wr1).
  rewrite E1. cbn [bind].
  assert (Htl : 0 <= tlr_len (d_wrap s)) by (unfold tlr_len; destruct (d_wrap s =? 0), (d_wrap s =? 1); lia).
  destruct (l0t_flush_all s1 z) as (s' & z' & T & Ef & Ho & HT & Hto & Pd & Wr'); auto; [lia..|].
  replace (negb (Z_FINISH =? Z_FINISH)) with false by reflexivity.
  rewrite Ef. cbn [bind].
  rewrite Wr', Wr1. replace (d_wrap s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  exists (set_d_wrap s' (- d_wrap s)), z', T.
  change (d_pending (set_d_wrap s' (- d_wrap s))) with (d_pending s'). rewrite Pd. cbn [Z.eqb negb].
  split; [reflexivity|]. split; [exact Ho|]. split; [congruence|]. rewrite Hto. congruence.
Qed.
