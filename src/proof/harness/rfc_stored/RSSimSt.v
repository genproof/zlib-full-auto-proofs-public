(* Law rfc_stored, the padding simulation: the stored-block passes (STORED, falling through COPY_ into COPY, and
   COPY) read LEN, NLEN and the block's bytes, never the first byte of a block, so they do the same on the real
   input as on the canonical one. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.rfc_stored.RSSimKit.
Require Import Zlib.proof.rfc1951.DecKit Zlib.proof.rfc1951.DecType.
Import ListNotations.
Local Open Scope Z_scope.

(* NEEDBITS keeps the input *)
Lemma rs_nb_inp k : forall n m, m_inp (needbits_f k n m) = m_inp m.
Proof.
  induction k as [|k IH]; intros n m; [reflexivity|]. cbn [needbits_f].
  destruct (m_bits m <? n); [|reflexivity]. destruct (m_have m =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* COPY reads the bytes [nx, nx + length) at most *)
Lemma rs_copy_inp m x :
  Zlength x = Zlength (m_inp m) -> 0 <= m_nx m <= Zlength (m_inp m) -> Zlength (m_ow m) <= m_aout m ->
  0 <= i_length (m_s m) ->
  (forall i, m_nx m <= i < m_nx m + i_length (m_s m) -> Znth i x = Znth i (m_inp m)) ->
  c_COPY (set_m_inp m x) = rs_iom x (c_COPY m).
Proof.
  intros Hl Hx Hw Hr Ha. unfold c_COPY.
  change (m_s (set_m_inp m x)) with (m_s m). rewrite (rs_have_inp m x Hl).
  change (m_left (set_m_inp m x)) with (m_left m).
  destruct (negb (i_length (m_s m) =? 0)).
  - set (cp := Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)).
    assert (Cp : 0 <= cp <= i_length (m_s m)) by (unfold cp, m_have, m_left; lia).
    destruct (cp =? 0); cbn [rs_iom]; [f_equal; apply rs_leave_inp|].
    rewrite (rs_inbytes_inp m x cp Hl) by (try lia; intros i Hi; apply Ha; lia).
    change (m_nx (set_m_inp m x)) with (m_nx m). change (m_ow (set_m_inp m x)) with (m_ow m).
    generalize (m_ow m ++ inbytes m cp) (m_nx m + cp). intros o n.
    destruct m; reflexivity.
  - destruct m; reflexivity.
Qed.

(* STORED: NEEDBITS(32) after BYTEBITS reads LEN and NLEN; COPY then the bytes [nx, nx + LEN) at most *)
Lemma rs_stored_inp flush m x :
  Zlength x = Zlength (m_inp m) -> 0 <= m_bits m ->
  (forall i, m_nx m <= i -> 8 * i < 8 * m_nx m - m_bits (bytebits m) + 32 -> Znth i x = Znth i (m_inp m)) ->
  let m1 := needbits 32 (bytebits m) in
  (m_leave m1 <> 1 ->
   0 <= m_nx m1 <= Zlength (m_inp m) /\ Zlength (m_ow m1) <= m_aout m1 /\
   forall i, m_nx m1 <= i < m_nx m1 + m_hold m1 mod 65536 -> Znth i x = Znth i (m_inp m)) ->
  c_STORED flush (set_m_inp m x) = rs_iom x (c_STORED flush m).
Proof.
  intros Hl Hb Ha m1 H1. unfold c_STORED.
  replace (bytebits (set_m_inp m x)) with (set_m_inp (bytebits m) x) by (destruct m; reflexivity).
  rewrite rs_needbits_inp4; [|exact Hl|cbn; pose proof (Z.mod_le (m_bits m) 8); lia|lia|intros i H2 H3; apply Ha; auto].
  fold m1. assert (I1 : m_inp m1 = m_inp m) by (unfold m1, needbits; rewrite rs_nb_inp; reflexivity).
  change (m_leave (set_m_inp m1 x)) with (m_leave m1). change (m_hold (set_m_inp m1 x)) with (m_hold m1).
  destruct (Z.eqb_spec (m_leave m1) 1) as [L1|L1]; [reflexivity|].
  destruct (H1 L1) as (Hx & Hw & Hc).
  destruct (negb (Z.land (m_hold m1) 65535 =? Z.lxor (Z.shiftr (m_hold m1) 16) 65535));
    [destruct m1; reflexivity|].
  set (m3 := set_mode (initbits (upd_s m1 (fun s => set_i_length s (m_hold m1 mod 65536)))) COPY_).
  replace (set_mode (initbits (upd_s (set_m_inp m1 x) (fun s => set_i_length s (m_hold m1 mod 65536)))) COPY_)
    with (set_m_inp m3 x) by (subst m3; destruct m1; reflexivity).
  destruct (flush =? Z_TREES); [cbn [rs_iom]; f_equal; apply rs_leave_inp|].
  unfold c_COPY_. replace (set_mode (set_m_inp m3 x) COPY) with (set_m_inp (set_mode m3 COPY) x)
    by (destruct m3; reflexivity).
  apply rs_copy_inp; subst m3; cbn [m_inp m_nx m_ow m_aout m_s upd_s set_mode initbits set_m_s set_m_bits
    set_m_hold set_i_mode set_i_length i_length]; rewrite ?I1; auto.
  - pose proof (Z.mod_pos_bound (m_hold m1) 65536). lia.
Qed.

(* a byte strictly inside a stored block is not the first byte of a block *)
Lemma rs_not_pad (LAY: rs_lay_stmt) G k bytes a :
  dctx_ok7a G -> rs_stored_only G -> 0 <= k < nblk G -> blk G k = Stored bytes ->
  bpos G k < 8 * a < bpos G (k + 1) -> ~ rs_padat G a.
Proof.
  intros Gok So Hk Eb Ha (j & Hj & Ej).
  destruct (Z.lt_trichotomy j k) as [Lt|[Eq|Gt]].
  - pose proof (rl_mono LAY G j k So ltac:(lia) ltac:(lia)). lia.
  - subst j. lia.
  - destruct (Z.eq_dec j (k + 1)) as [E|E]; [subst j; lia|].
    pose proof (rl_mono LAY G (k + 1) j So ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma rs_pass_st : rs_lay_stmt -> rs_pass_ok (fun md => md = STORED \/ md = COPY_ \/ md = COPY).
Proof.
  intros LAY G pos x inp' ob flush m' Gok So Hp Hl Hinp Hx K W L0 P.
  destruct Hx as (Hxl & Hxb & Hxe).
  pose proof (kd_inp _ _ _ _ _ K) as Ki. pose proof (kd_at _ _ _ _ _ K) as A.
  pose proof (mwW_nx _ (proj1 W)) as Hnx. pose proof (mwW_ow _ (proj1 W)) as [Hw _].
  rewrite Ki in Hnx.
  assert (Bs : bytes_ok (dc_src G)) by (destruct Gok as (_ & _ & _ & _ & _ & _ & B & _); exact B).
  (* the bytes strictly inside a stored block are the same in both inputs *)
  assert (EQ : forall k bytes i, 0 <= k < nblk G -> blk G k = Stored bytes -> 0 <= i ->
                 bpos G k < 8 * (pos + i) < bpos G (k + 1) -> Znth i x = Znth i inp').
  { intros k bytes i Hk Eb Hi Hb.
    destruct (Z_lt_le_dec i (Zlength x)) as [Lt|Ge].
    - destruct (Hxe i ltac:(lia)) as [E|(Pd & _)]; [exact E|].
      exfalso. exact (rs_not_pad LAY G k bytes (pos + i) Gok So Hk Eb Hb Pd).
    - rewrite !Znth_overflow by lia. reflexivity. }
  assert (Lx : Zlength x = Zlength (m_inp m')) by (rewrite Ki; exact Hxl).
  destruct P as [E|[E|E]].
  - (* STORED *)
    replace (stepf2 flush lenfix_list distfix_list m') with (c_STORED flush m')
      by (unfold stepf2, step2; rewrite E; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list (set_m_inp m' x)) with (c_STORED flush (set_m_inp m' x))
      by (unfold stepf2, step2; change (m_mode (set_m_inp m' x)) with (m_mode m'); rewrite E; reflexivity).
    destruct (dt_at_stored _ _ _ _ _ _ A E) as [Hh (k & bytes & (Hk & _) & Ebk & _ & Hpos)].
    cbv zeta in Hpos.
    destruct (rl_blk LAY G k bytes Gok So Hk Ebk) as (Eb1 & Nl & _ & Sb).
    pose proof (rl_align LAY G k So ltac:(lia)) as Al.
    set (n := Zlength bytes) in *. assert (N0 : 0 <= n) by apply Zlength_nonneg.
    assert (P5 : pad8 (bpos G k + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia).
    set (mb := bytebits m').
    assert (Hmb : hold_ok G (pos + m_nx mb) (m_hold mb) (m_bits mb) /\
                  8 * (pos + m_nx mb) - m_bits mb = bpos G k + 8 /\ m_bits mb mod 8 = 0 /\ 0 <= m_bits mb < 32).
    { subst mb. unfold bytebits. cbn [m_nx m_hold m_bits set_m_bits set_m_hold].
      destruct Hh as (Hh1 & Hh2 & Hh3).
      split; [apply (dt_drop dkit _ _ _ (m_bits m')); [split; [|split]; auto|
                pose proof (Z.mod_pos_bound (m_bits m') 8); pose proof (Z.mod_le (m_bits m') 8); lia|lia]|].
      rewrite P5 in Hpos.
      destruct Hpos as [(Q & B8)|(Q & B0 & B32)].
      - rewrite (Z.mod_small (m_bits m')) by lia. rewrite Z.sub_diag, Z.mod_0_l by lia.
        assert (m_bits m' = 5) by (Z.to_euclidean_division_equations; lia). lia.
      - rewrite B0, Z.sub_0_r. lia. }
    destruct Hmb as (Hmb & Qb & Mb8 & Bb32).
    assert (Imb : m_inp mb = m_inp m') by reflexivity. assert (Xmb : m_nx mb = m_nx m') by reflexivity.
    apply rs_stored_inp; [exact Lx|apply Hh|..].
    { intros i H1 H2. rewrite Ki. apply (EQ k bytes); auto; [lia|].
      fold mb in H2. rewrite Xmb in Qb. lia. }
    intros Lv. fold mb. unfold needbits.
    destruct (dt_nbf dkit G pos inp' 32 4 mb Bs ltac:(rewrite Imb, Ki; exact Hinp) Hp Hl
                ltac:(rewrite Imb, Xmb, Ki; lia) Hmb ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia))
      as (nx' & h' & b' & lv' & E1 & R1 & R2 & R3 & C).
    unfold needbits in Lv. fold mb in Lv. rewrite E1 in Lv |- *. cbn [m_leave set_m_leave] in Lv.
    destruct C as [(-> & _ & _)|(Cl & Cb1 & Cb2 & Cb3)]; [lia|].
    cbn [m_nx m_ow m_aout m_hold set_m_leave set_m_bits set_m_hold set_m_nx].
    rewrite Xmb in Qb, R3, R2. rewrite Imb in R2. change (m_ow mb) with (m_ow m'). change (m_aout mb) with (m_aout m').
    assert (B32 : b' = 32) by (clear -Mb8 Bb32 Cb1 Cb2 R3; Z.to_euclidean_division_equations; lia). subst b'.
    pose proof (dk_hold_lt dkit _ _ _ _ R1 Bs) as HL.
    pose proof (dk_bitsn dkit _ _ _ _ 32 R1 ltac:(lia)) as HB.
    pose proof (dt_stored_lenbits (bpos G k - D0 G) (lastflag G k =? 1) bytes) as SL.
    replace (bpos G k - D0 G + 3) with (bpos G k + 3 - D0 G) in SL by lia.
    rewrite dt_pad8_shift, P5 in SL by (apply (dk_D0 dkit)).
    rewrite Z.mod_small in HB by lia.
    replace (8 * (pos + nx') - 32) with (bpos G k + (3 + 5)) in HB by lia.
    replace (bpos G k + (3 + 5) + 32) with (bpos G k + (3 + 5 + 32)) in HB by lia.
    assert (Bp0 : 0 <= bpos G k).
    { pose proof (rl_D0 LAY G k ltac:(lia)). unfold D0 in *. pose proof (Zlength_nonneg (hdr_bytes (dc_w G))). lia. }
    rewrite (dt_sub_in _ _ _ _ _ _ Sb) in HB by lia.
    replace (bpos G k + (3 + 5) - bpos G k) with (3 + 5) in HB by lia.
    replace (bpos G k + (3 + 5 + 32) - bpos G k) with (3 + 5 + 32) in HB by lia.
    rewrite SL, dt_bval_app, !dt_bval_le, dt_bits_le_len in HB by (try change (2 ^ 16) with 65536; lia).
    change (2 ^ 16) with 65536 in HB.
    assert (HM : h' mod 65536 = n) by (rewrite HB; Z.to_euclidean_division_equations; lia).
    rewrite HM. split; [rewrite Ki; lia|]. split; [exact Hw|].
    intros i Hi. rewrite Ki. apply (EQ k bytes); auto; lia.
  - (* COPY_ *)
    replace (stepf2 flush lenfix_list distfix_list m') with (c_COPY (set_mode m' COPY))
      by (unfold stepf2, step2; rewrite E; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list (set_m_inp m' x)) with (c_COPY (set_m_inp (set_mode m' COPY) x))
      by (unfold stepf2, step2; change (m_mode (set_m_inp m' x)) with (m_mode m'); rewrite E;
          cbv iota beta delta [c_COPY_ Z.eqb]; cbn; f_equal; destruct m'; reflexivity).
    destruct (dt_at_copy _ _ _ _ _ _ A (or_introl E)) as [Hh (k & bytes & (Hk & _) & Ebk & Hr & Hb0 & Hq & _)].
    destruct (rl_blk LAY G k bytes Gok So Hk Ebk) as (Eb1 & Nl & _ & Sb).
    pose proof (rl_align LAY G k So ltac:(lia)) as Al.
    assert (P5 : pad8 (bpos G k + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia).
    cbv zeta in Hq. rewrite P5 in Hq. pose proof (Zlength_nonneg bytes).
    apply rs_copy_inp; cbn [m_inp m_nx m_ow m_aout m_s upd_s set_mode set_m_s set_i_mode i_length]; auto; [lia|lia|].
    intros i Hi. rewrite Ki. apply (EQ k bytes); auto; lia.
  - (* COPY *)
    replace (stepf2 flush lenfix_list distfix_list m') with (c_COPY m')
      by (unfold stepf2, step2; rewrite E; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list (set_m_inp m' x)) with (c_COPY (set_m_inp m' x))
      by (unfold stepf2, step2; change (m_mode (set_m_inp m' x)) with (m_mode m'); rewrite E; reflexivity).
    destruct (dt_at_copy _ _ _ _ _ _ A (or_intror E)) as [Hh (k & bytes & (Hk & _) & Ebk & Hr & Hb0 & Hq & _)].
    destruct (rl_blk LAY G k bytes Gok So Hk Ebk) as (Eb1 & Nl & _ & Sb).
    pose proof (rl_align LAY G k So ltac:(lia)) as Al.
    assert (P5 : pad8 (bpos G k + 3) = 5) by (unfold pad8; Z.to_euclidean_division_equations; lia).
    cbv zeta in Hq. rewrite P5 in Hq. pose proof (Zlength_nonneg bytes).
    apply rs_copy_inp; auto; [rewrite Ki; lia|lia|].
    intros i Hi. rewrite Ki. apply (EQ k bytes); auto; lia.
Qed.
