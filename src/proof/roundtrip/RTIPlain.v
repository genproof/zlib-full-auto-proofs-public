(* RT-I, part rti_plain_rz: RTIIface.if_plain for the raw and zlib wrappers (the gzip wrapper: RTITheory.v), from the decode theory (Decode.decode_of_parts: decode_init_stmt, decode_call_stmt). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.rfc1951.Decode.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Helpers (copied from harness/inflate_dict/ITCtx.v, ITPost.v)                                    *)

Lemma rtip_bval_range l : 0 <= bval l < 2 ^ Zlength l.
Proof.
  induction l as [|b r IH]; simpl.
  - rewrite ?Zlength_nil. simpl. lia.
  - rewrite Zlength_cons, Z.pow_succ_r by (pose proof (Zlength_nonneg r); lia).
    destruct b; simpl; lia.
Qed.

Lemma rtip_pack_ok bs : bytes_ok (pack bs).
Proof.
  unfold bytes_ok, pack. apply Forall_map, Forall_forall. intros k _.
  set (l := sublist (8 * Z.of_nat k) (8 * Z.of_nat k + 8) bs). pose proof (rtip_bval_range l).
  assert (Zlength l <= 8).
  { unfold l, sublist. rewrite Zlength_correct, length_skipn, length_firstn. lia. }
  assert (2 ^ Zlength l <= 2 ^ 8) by (apply Z.pow_le_mono_r; [lia | pose proof (Zlength_nonneg l); lia]).
  unfold Basics.compose; cbv beta; fold l. change (2 ^ 8) with 256 in *.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma rtip_le_ok v n : bytes_ok (le_bytes v n).
Proof.
  unfold bytes_ok, le_bytes. apply Forall_map, Forall_forall. intros i _.
  pose proof (Z.mod_pos_bound (Z.shiftr v (8 * Z.of_nat i)) 256 ltac:(lia)). unfold Basics.compose; cbv beta.
  change compcert.lib.Integers.Byte.max_unsigned with 255. lia.
Qed.

Lemma rtip_be_ok v n : bytes_ok (be_bytes v n).
Proof. unfold be_bytes, bytes_ok. apply Forall_rev, rtip_le_ok. Qed.

Lemma rtip_fold_ext {A: Type} (f: list Z -> A -> list Z) :
  (forall out a, exists d, f out a = out ++ d) ->
  forall l out, exists d, fold_left f l out = out ++ d.
Proof.
  intros F l; induction l as [|a l IH]; intros out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (F out a) as [d1 E1]; rewrite E1. destruct (IH (out ++ d1)) as [d2 E2].
    exists (d1 ++ d2); rewrite E2, app_assoc; auto.
Qed.

Lemma rtip_lz_ext : forall n dist out, exists d, lz_copy n dist out = out ++ d.
Proof.
  induction n as [|n IH]; intros dist out; simpl.
  - exists []; rewrite app_nil_r; auto.
  - destruct (IH dist (out ++ [Znth (Zlength out - dist) out])) as [d E]; rewrite E.
    exists ([Znth (Zlength out - dist) out] ++ d); rewrite app_assoc; auto.
Qed.

Lemma rtip_block_ext : forall out b, exists d, block_data out b = out ++ d.
Proof.
  assert (S: forall out syms, exists d, syms_data out syms = out ++ d).
  { intros out syms; unfold syms_data; apply rtip_fold_ext.
    intros o [b|len dist]; simpl; [exists [b]; auto | apply rtip_lz_ext]. }
  intros out [bytes|syms|nlen ndist cl toks syms]; simpl; [exists bytes; auto|apply S|apply S].
Qed.

Lemma rtip_expand_data : forall hist bs, expand hist bs = hist ++ data hist bs.
Proof.
  intros hist bs. unfold data. destruct (rtip_fold_ext block_data rtip_block_ext bs hist) as [d E].
  unfold expand; rewrite E. f_equal. rewrite Zlength_app. rewrite sublist_app2 by (pose proof (Zlength_nonneg hist); lia).
  rewrite Z.sub_diag. replace (Zlength hist + Zlength d - Zlength hist) with (Zlength d) by lia.
  rewrite sublist_same by lia; auto.
Qed.

(* the zlib header deflate writes without a dictionary is Format's: FCHECK = 31 never happens (finite check) *)
Definition rtip_hchk (wb flg : Z) : bool :=
  negb ((RF.zcmf wb * 256 + flg) mod 31 =? 0) || Z.testbit flg 5 ||
  (match zlib_hdr wb (flg / 64) false with [a; b] => (a =? RF.zcmf wb) && (b =? flg) | _ => false end).

Lemma rtip_hchk_all :
  forallb (fun wb => forallb (fun flg => rtip_hchk wb flg) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 9 7))
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rtip_zhdr wb flg : 9 <= wb <= 15 -> RF.zflg_ok wb false flg -> [RF.zcmf wb; flg] = zlib_hdr wb (flg / 64) false.
Proof.
  intros Hwb (Hf & Hm & Ht).
  pose proof rtip_hchk_all as A. rewrite forallb_forall in A.
  assert (Iw: In wb (map Z.of_nat (seq 9 7))).
  { apply in_map_iff. exists (Z.to_nat wb). split; [lia|]. apply in_seq. lia. }
  specialize (A wb Iw). rewrite forallb_forall in A.
  assert (If: In flg (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat flg). split; [lia|]. apply in_seq. lia. }
  specialize (A flg If). unfold rtip_hchk in A.
  rewrite Hm, Ht in A. cbn [Z.eqb negb orb] in A.
  destruct (zlib_hdr wb (flg / 64) false) as [|a [|b [|]]]; try discriminate.
  apply andb_prop in A as [A1 A2]. apply Z.eqb_eq in A1, A2. subst. reflexivity.
Qed.

Lemma rti_plain_rz : decode_parts ->
  forall wrap wb D O sp z res, (wrap = 0 \/ wrap = 1) ->
    RF.dfinal [] wrap wb None D O -> Zlength D <= 1048576 -> Zlength O <= 4194304 ->
    live_ok (init_live sp (iw_of wrap wb)) -> zcall_ok z O D ->
    run2 4 lenfix_list distfix_list (m_init z (init_live sp (iw_of wrap wb)) O) res ->
    rdone O D res.
Proof.
  intros DP wrap wb D O sp z res Hw Hfin HD HO HL Hz Hrun.
  destruct (decode_of_parts DP) as [DI DC].
  destruct Hfin as (Hwb & bs & Hwf & Hdat & Hsh).
  (* the decode context *)
  assert (exists G, dc_wb G = wb /\ dc_hist G = [] /\ dc_bs G = bs /\ dc_src G = O /\ dc_iw G = iw_of wrap wb /\
            (forall wb' fl did, dc_w G = WZlib wb' fl did -> did = None) /\
            (forall h, dc_w G <> WGzip h) /\
            stream_bytes (dc_w G) [] bs = O /\ stream_ok (dc_w G) wb [] bs /\ accepts G) as (G & Gwb & Gh & Gb & Gs & Gi & Gz & Gg & Gsb & Gok & Gacc).
  { destruct Hw as [-> | ->].
    - exists (DCtx WRaw wb [] bs (- wb) O). cbn [dc_hist dc_bs dc_src dc_iw dc_w dc_wb].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros ? ? ? E; discriminate|]. split; [intros h E; discriminate|].
      split; [symmetry; exact Hsh|].
      split; [unfold stream_ok, wrapper_ok; split; [lia|]; split; [exact I|]; split; [exact I|]; exact Hwf|].
      unfold accepts; reflexivity.
    - destruct Hsh as (_ & flg & Hflg & HO').
      exists (DCtx (WZlib wb (flg / 64) None) wb [] bs 0 O). cbn [dc_hist dc_bs dc_src dc_iw dc_w dc_wb].
      split; [reflexivity|].
      pose proof Hflg as (Hf1 & Hf2 & Hf3).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros ? ? ? E; inversion E; auto|]. split; [intros h E; discriminate|].
      split; [cbn [stream_bytes]; rewrite HO', <- (rtip_zhdr wb flg) by auto; rewrite Hdat; reflexivity|].
      split; [|unfold accepts; cbn [dc_w dc_iw dc_wb]; right; left; reflexivity].
      unfold stream_ok, wrapper_ok. split; [lia|]. split; [|split; [reflexivity|exact Hwf]].
      split; [lia|]. split; [|reflexivity]. split; [apply Z.div_pos; lia|].
      apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
  assert (Hbo: bytes_ok O).
  { rewrite <- Gsb. destruct (dc_w G) as [|wb' fl did|h]; cbn [stream_bytes]; unfold deflate_bytes.
    - apply rtip_pack_ok.
    - destruct did; [specialize (Gz wb' fl (Some z0) eq_refl); discriminate|].
      unfold bytes_ok; rewrite !Forall_app. destruct Gok as (_ & (Hwb2 & Hfl & _) & _).
      repeat split; [|constructor|apply rtip_pack_ok|apply rtip_be_ok].
      unfold zlib_hdr. set (c := (31 - _ mod 31) mod 31).
      assert (0 <= c < 31) by (apply Z.mod_pos_bound; lia).
      change compcert.lib.Integers.Byte.max_unsigned with 255. repeat (apply Forall_cons; [lia|]); apply Forall_nil.
    - exfalso; exact (Gg h eq_refl). }
  assert (Hsl: slen G = Zlength O) by (unfold slen; rewrite Gh, Gb, Gsb; reflexivity).
  assert (Hok: dctx_ok G).
  { unfold dctx_ok. rewrite Gwb, Gh, Gb, Gs, Hsl, sublist_same by lia.
    split; [auto|]. split; [auto|]. split; [intros h E; exfalso; exact (Gg h E)|].
    split; [intros ? ? ? E; left; eapply Gz; eauto|].
    split; [lia|]. split; [lia|]. split; auto. }
  assert (Hfull: full G = D).
  { unfold full. rewrite Gh, Gb, rtip_expand_data, Hdat. reflexivity. }
  specialize (DI G sp Hok Gh Gz). rewrite Gi in DI.
  destruct Hz as (Hzf & Hai & Hao & Hto).
  replace (dinv G 0 [] (l_s (init_live sp (iw_of wrap wb))) 0) with (dinv G 0 [] (l_s (init_live sp (iw_of wrap wb))) (zf_tout z)) in DI by (rewrite Hto; reflexivity).
  specialize (DC G 0 [] (init_live sp (iw_of wrap wb)) z O 4 res Hok DI HL Hzf ltac:(lia) ltac:(lia)
    ltac:(rewrite Gs; lia) ltac:(rewrite Gs, Z.add_0_l, sublist_same by lia; reflexivity) Hrun).
  cbv zeta in DC.
  destruct DC as [Hm | (Hr & Hsnx & Hsow & Haout & _ & _ & _ & Hend & Hnend & _)]; [left; exact Hm|].
  right.
  destruct (Z.eq_dec (r_ret res) Z_STREAM_END) as [He|He].
  - destruct (Hend He) as [Ho Hp]. rewrite Hfull in Ho. cbn [app] in Ho.
    split; [exact He|]. split; [lia|]. split; [exact Ho|]. split; [rewrite Hsow, Ho; reflexivity|]. lia.
  - exfalso. rewrite Hfull, Hsl in Hnend. cbn [app] in Hnend.
    destruct (Hnend He) as [[_ C]|[[C1 C2]|C]]; [lia|lia|].
    unfold Z_BLOCK, Z_TREES in C; lia.
Qed.
