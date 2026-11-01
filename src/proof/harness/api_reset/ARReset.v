(* Law api_reset, the theory: inflateReset with fix F8 makes a stream that relates to a fresh one.

   After any phase-0 use, stream used still has the wrapper inflateInit2_ stored (inflate() never writes wrap)
   and the window size W0 it stored, unless W0 = 0 and a header stored its own (IRDefs.wcl).  With fix F8,
   W0 = 0 comes with bit 3 of wrap (ApiModel.reset2_wrap), and inflateReset (ApiModel.reset_full_s) then sets
   wbits = 0 again and frees the window; otherwise wbits is W0.  Both the reset state and the fresh one are
   reset_keep_s of states with the same wrap and an empty window (wsize = whave = wnext = 0, no window bytes),
   so they are related by srel (which leaves free what inflate() writes before reading it, and the window
   allocation), and have the same wbits W0. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_reset.ARTheoryDefs.
Require Zlib.proof.inflate_api.Body5_reset.
Import ListNotations.
Local Open Scope Z_scope.

Ltac ar_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC]
  in *; lia.

(* the state inflateInit2_ makes: mode HEAD, no gz_header, an empty bit buffer *)
Lemma ar_init_s (sp: val) (w: Z) : wbits_ok w = true ->
  i_mode (l_s (init_live sp w)) = HEAD /\ i_head (l_s (init_live sp w)) = false /\
  i_hold (l_s (init_live sp w)) = 0 /\ i_bits (l_s (init_live sp w)) = 0.
Proof.
  unfold wbits_ok, init_live. destruct (reset2_wb w) as [[wr wb]|]; [|discriminate].
  intros _. unfold init_s. cbn. repeat split.
Qed.

Lemma ar_hd0 (src: list Z) : ir_hd src 0 0 0.
Proof. unfold ir_hd. rewrite sublist_nil. cbn. lia. Qed.

(* bit 3 of the wrapper inflateInit2_ stores is set exactly when the window size is to come from the header *)
Lemma ar_wrap8 (wr wb: Z) : (wr = 0 /\ 8 <= wb <= 15) \/ (5 <= wr <= 7 /\ (wb = 0 \/ 8 <= wb <= 15)) ->
  (Z.land (reset2_wrap wr wb) 8 =? 0) = negb (wb =? 0).
Proof.
  unfold reset2_wrap. intros C.
  destruct (Z.eqb_spec wb 0) as [E|E].
  - subst wb. destruct C as [(_ & B) | (A & _)]; [lia|].
    assert (R: wr = 5 \/ wr = 6 \/ wr = 7) by lia. destruct R as [-> | [-> | ->]]; reflexivity.
  - destruct C as [(-> & _) | (A & _)]; [reflexivity|].
    assert (R: wr = 5 \/ wr = 6 \/ wr = 7) by lia. destruct R as [-> | [-> | ->]]; reflexivity.
Qed.

(* inflateReset (fix F8) on wbits and wrap *)
Lemma ar_full_wbits (s: istate) :
  i_wbits (reset_full_s s) = if Z.land (i_wrap s) 8 =? 0 then i_wbits s else 0.
Proof. unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); reflexivity. Qed.

Lemma ar_full_wrap (s: istate) : i_wrap (reset_full_s s) = i_wrap s.
Proof. unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); reflexivity. Qed.

Lemma ar_full_mode (s: istate) : i_mode (reset_full_s s) = HEAD.
Proof. unfold reset_full_s, reset_hdr_s. destruct (Z.land (i_wrap s) 8 =? 0); reflexivity. Qed.

(* the state inflateInit2_ makes is inflateReset's of the zeroed state with the wrapper and window size set
   (the zeroed state has no window, so inflateReset2's free does not apply) *)
Lemma ar_init_full (wr wb: Z) :
  init_s wr wb = reset_full_s (set_i_wbits (set_i_wrap zero_s (reset2_wrap wr wb)) wb).
Proof. reflexivity. Qed.

(* two states reset by inflateResetKeep after their windows were emptied are related when their wrappers are
   equal (as x_inflate_reset's IRRun.irr_srel_rk) *)
Lemma ar_srel_rk (ta tb: istate) :
  i_wrap ta = i_wrap tb -> i_wsize ta = i_wsize tb -> i_whave ta = i_whave tb -> i_wnext ta = i_wnext tb ->
  i_wdata ta = i_wdata tb -> srel True (reset_keep_s ta) (reset_keep_s tb).
Proof.
  intros A B C D E. constructor; unfold lenlive, reset_keep_s; simpl; auto;
    try (right; left; reflexivity); try (right; right; split; [left; reflexivity | exact I]);
    try (intros X; exfalso; unfold decode_mode in X; ar_md).
Qed.

Lemma ar_srel_full (sa sb: istate) : i_wrap sa = i_wrap sb -> srel True (reset_full_s sa) (reset_full_s sb).
Proof.
  intros A. unfold reset_full_s, reset_s. apply ar_srel_rk; try reflexivity.
  unfold reset_hdr_s. destruct (Z.land (i_wrap sa) 8 =? 0), (Z.land (i_wrap sb) 8 =? 0); exact A.
Qed.

Lemma ar_land1 (x: Z) : 0 <= Z.land x 1 <= 1.
Proof.
  change (Z.land x 1) with (Z.land x (Z.ones 1)). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(reflexivity)). simpl in *. lia.
Qed.

Lemma ar_reset : ar_reset_stmt.
Proof.
  intros w src pos za La (W & IV) LV ZF.
  destruct (reset2_wb w) as [[wr wb]|] eqn:E; [|unfold wbits_ok in W; rewrite E in W; discriminate].
  pose proof (reset2_wb_cases w wr wb E) as C.
  pose proof (ar_wrap8 wr wb C) as W8.
  assert (Ls: forall sp, l_s (init_live sp w) = init_s wr wb) by (intros sp; unfold init_live; rewrite E; reflexivity).
  assert (WR: ar_wrap w = reset2_wrap wr wb) by (unfold ar_wrap; rewrite Ls; rewrite ar_init_full, ar_full_wrap; reflexivity).
  assert (WB: ar_wb0 w = wb).
  { unfold ar_wb0. rewrite Ls, ar_init_full, ar_full_wbits. cbn [i_wrap i_wbits set_i_wbits set_i_wrap].
    rewrite W8. destruct (Z.eqb_spec wb 0); cbn; [subst; reflexivity | reflexivity]. }
  destruct IV as [IVr IVw IVh IVwa IVwb IVhd IVs IVtin IVtout IVmsg IVdt IVad].
  rewrite WR in IVw.
  (* the reset stream's wbits: W0 *)
  assert (RB: i_wbits (reset_full_s (l_s La)) = wb).
  { rewrite ar_full_wbits, IVw, W8. destruct (Z.eqb_spec wb 0) as [Z0|Z0]; cbn; [lia|].
    rewrite WB in IVwb. destruct IVwb as [Q|(Q & _)]; [exact Q | congruence]. }
  unfold reset_f, fst3, snd3, thd3. cbv zeta. cbn [fst snd].
  split; [reflexivity|].
  split; [exact (Zlib.proof.inflate_api.Body5_reset.live_reset za La LV)|].
  split.
  { unfold swfW. cbn [l_s set_l_s]. rewrite ar_full_mode. split; intros X; exfalso; ar_md. }
  intros src' zb sp SPb LVb ZFb T0 O0 M0 D0 AN AP BS'.
  split; [exact W|].
  constructor; cbn [l_s set_l_s].
  - rewrite Ls, ar_init_full. apply ar_srel_full. rewrite IVw. reflexivity.
  - unfold ar_wrap. rewrite !Ls. reflexivity.
  - destruct (ar_init_s sp w W) as (_ & H & _ & _). exact H.
  - left. rewrite RB, WB. reflexivity.
  - left. unfold ar_wb0. rewrite !Ls. reflexivity.
  - intros _ _. destruct (ar_init_s sp w W) as (_ & _ & Ho & Bi). rewrite Ho, Bi. apply ar_hd0.
  - destruct (ar_init_s sp w W) as (M & _ & _ & _). rewrite M. ar_md.
  - rewrite T0. reflexivity.
  - rewrite O0. reflexivity.
  - rewrite M0. reflexivity.
  - rewrite D0. reflexivity.
  - destruct (Z_lt_le_dec w 0) as [N|N]; [rewrite (AN N); reflexivity|].
    rewrite (AP N). unfold reset_keep_z. cbn [zf_adler]. rewrite ar_full_wrap, IVw, Ls, ar_init_full, ar_full_wrap.
    cbn [i_wrap set_i_wbits set_i_wrap].
    assert (NZ: reset2_wrap wr wb <> 0).
    { unfold reset2_wb in E. destruct (Z.ltb_spec w 0); [lia|].
      destruct C as [(-> & _) | (A & _)]; [| unfold reset2_wrap; destruct (wb =? 0); [rewrite Z.lor_comm; destruct wr; try lia; discriminate | lia]].
      exfalso. destruct (Z.ltb_spec w 48).
      - destruct (_ || _)%bool; [|discriminate]. injection E as E1 _.
        assert (0 <= Z.shiftr w 4) by (apply Z.shiftr_nonneg; lia). lia.
      - destruct (_ || _)%bool; [|discriminate]. injection E as E1 _.
        assert (0 <= Z.shiftr w 4) by (apply Z.shiftr_nonneg; lia). lia. }
    destruct (Z.eqb_spec (reset2_wrap wr wb) 0); [contradiction | reflexivity].
Qed.
