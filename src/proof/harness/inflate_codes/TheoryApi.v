(* Law inflate_codes, theory: the invariant after inflateInit2_ and across inflateSetDictionary. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_codes.TheoryDefs.
Require Import Zlib.proof.harness.inflate_codes.TheoryRun.
Require Import Zlib.proof.inflate_api.ResetFacts.
Import ListNotations.
Local Open Scope Z_scope.

Ltac ap_md := cbv [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT Zlib.proof.inflate.Model.TYPE TYPEDO
  STORED COPY_ COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC
  Z_OK Z_STREAM_END Z_NEED_DICT Z_STREAM_ERROR Z_DATA_ERROR Z_MEM_ERROR Z_BUF_ERROR Z_FINISH] in *; lia.

Lemma ap_wrap_neg (w: Z) : wbits_ok w = true -> w < 0 -> wrap_of w = 0.
Proof.
  intros W N. apply (proj2 (wrap_of_low w)). revert W N.
  unfold wbits_ok, wrap_low, reset2_wb. intros W N.
  destruct (Z.ltb_spec w 0); [|lia]. destruct (w <? -15); [discriminate|].
  destruct (andb _ _); [reflexivity | discriminate].
Qed.

Lemma ap_wrap_pos (w: Z) : wbits_ok w = true -> 0 <= w -> wrap_of w <> 0.
Proof.
  intros W N. rewrite (proj2 (wrap_of_low w)). revert W N.
  unfold wbits_ok, wrap_low, reset2_wb. intros W N.
  destruct (Z.ltb_spec w 0); [lia|].
  destruct (orb _ _); [|discriminate].
  pose proof (Z.shiftr_nonneg w 4). assert (0 <= Z.shiftr w 4) by (apply Z.shiftr_nonneg; lia). lia.
Qed.

(* after inflateInit2_: the state of ResetFacts.init_s_eq, whose wrap is wrap_of w (bit 3 for windowBits 0, 16, 32) *)
Lemma ap_init (w: Z) (src: list Z) (z: zfields) (sp: val) :
  wbits_ok w = true -> zf_msg z = None -> inv w src 0 Z_OK 0 z (init_live sp w).
Proof.
  intros W M. unfold inv, init_live. cbn [l_s].
  destruct (reset2_wb w) as [[wr wb]|] eqn:E; [|unfold wbits_ok in W; rewrite E in W; discriminate].
  assert (R: 0 <= wr <= 7) by (destruct (reset2_wb_cases w wr wb E); lia).
  assert (WO: wrap_of w = reset2_wrap wr wb) by (unfold wrap_of; rewrite E; reflexivity).
  rewrite WO, (init_s_eq wr wb R). unfold reset_s, reset_keep_s, zero_s. cbn.
  split; [exact W|]. split; [reflexivity|]. split; [reflexivity|]. split; [ap_md|].
  split; [left; split; [reflexivity | ap_md]|]. split; [intros; ap_md|]. split; [intros; lia|].
  split; [intros _ _; unfold hd_head; rewrite sublist_nil; cbn; lia|].
  split; [intros; ap_md|]. split; [intros; ap_md|]. right; split; [reflexivity | ap_md].
Qed.

Lemma ap_setdict (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) (dict: list Z) (alloc_ok: bool)
    (winp: val) :
  inv w src pos final indict z L ->
  setdict_post inv w src pos final indict dict z (setdict_f dict alloc_ok winp z L).
Proof.
  intros IV. pose proof IV as IV0.
  destruct IV as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  set (s := l_s L) in *.
  assert (UPD: forall L', l_s L' = setdict_s s dict ->
            inv w src pos final indict z L').
  { intros L' E. unfold inv. rewrite E. unfold setdict_s.
    destruct (rn_uw s dict) as (U1 & U2 & U3 & U4 & U5 & U6). cbn.
    rewrite U1, U2, U3, U4, U5, U6. fold s.
    exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 A11)))))))))). }
  assert (MEMI: inv w src pos Z_MEM_ERROR 0 z (set_l_s L (set_i_mode s MEM))).
  { unfold inv. cbn. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [ap_md|].
    split; [right; right; right; split; reflexivity|]. split; [intros; ap_md|]. split; [intros _ N; contradiction|].
    split; [intros _ E; ap_md|]. split; [intros E; ap_md|]. split; [intros E; ap_md|]. right; split; [reflexivity|ap_md]. }
  assert (DCH: i_mode s = DICT -> wrap_of w <> 0).
  { intros E. destruct (A10 E) as (D1 & _). intros Z0. rewrite Z0 in D1. apply D1. reflexivity. }
  unfold setdict_f, setdict_check. fold s.
  destruct (Z.eqb_spec (i_mode s) DICT) as [MD|MD].
  - (* DICT: a wrapped stream, inflate asked for a dictionary *)
    assert (WP: 0 <= w) by (destruct (Z_lt_le_dec w 0) as [N|N]; auto; exfalso; apply (DCH MD); apply ap_wrap_neg; auto).
    destruct (A10 MD) as (D1 & D2 & D3 & D4 & D5).
    assert (I1: indict = 1) by (destruct A11 as [(I & _)|(_ & N)]; [auto | contradiction]).
    rewrite andb_false_r. cbn [negb andb].
    assert (REF: Zlib.proof.adler32.Model.ref_adler32 1 dict = adler32_z_val 1 dict).
    { symmetry. apply Zlib.proof.adler32.Model.adler32_z_val_ref.
      unfold Zlib.proof.adler32.Model.adler_valid, Zlib.proof.adler32.Model.adler_lo, Zlib.proof.adler32.Model.adler_hi,
        Zlib.proof.adler32.Model.ADLER_BASE. cbn. lia. }
    destruct (Z.eqb_spec (adler32_z_val 1 dict) (i_check s)) as [EQ|NE]; cbn [negb].
    + destruct (i_win s) eqn:WN; [|destruct alloc_ok]; cbn.
      * split; [lia|]. split; [lia|]. split; [intros _ _; split; [split; [intros; ap_md | intros N; exfalso; apply N; rewrite REF, EQ, D4, D5; reflexivity] | left; reflexivity]|].
        apply UPD. reflexivity.
      * split; [lia|]. split; [lia|]. split; [intros _ _; split; [split; [intros; ap_md | intros N; exfalso; apply N; rewrite REF, EQ, D4, D5; reflexivity] | left; reflexivity]|].
        apply UPD. reflexivity.
      * split; [lia|]. split; [lia|]. split; [intros _ _; split; [split; [intros; ap_md | intros N; exfalso; apply N; rewrite REF, EQ, D4, D5; reflexivity] | right; right; reflexivity]|].
        exact MEMI.
    + cbn. split; [lia|]. split; [lia|].
      split; [intros _ _; split; [split; [intros _; rewrite REF, D5, <- D4; exact NE | intros; reflexivity] | right; left; reflexivity]|].
      exact IV0.
  - destruct (Z_lt_le_dec w 0) as [WN|WP].
    + (* raw *)
      assert (W0: i_wrap s = 0) by (rewrite A2; apply ap_wrap_neg; auto).
      rewrite W0. cbn [Z.eqb negb andb].
      destruct (i_win s) eqn:WI; [|destruct alloc_ok]; cbn.
      * split; [intros; left; reflexivity|]. split; [lia|]. split; [lia|]. apply UPD. reflexivity.
      * split; [intros; left; reflexivity|]. split; [lia|]. split; [lia|]. apply UPD. reflexivity.
      * split; [intros; right; reflexivity|]. split; [lia|]. split; [lia|]. exact MEMI.
    + (* wrapped, not in DICT: Z_STREAM_ERROR *)
      assert (W0: i_wrap s <> 0) by (rewrite A2; apply ap_wrap_pos; auto).
      assert (I0: indict = 0) by (destruct A11 as [(_ & E)|(I & _)]; [contradiction | auto]).
      rewrite (proj2 (Z.eqb_neq _ _) W0). cbn.
      split; [lia|]. split; [intros; reflexivity|]. split; [intros _ N; contradiction|]. exact IV0.
Qed.
