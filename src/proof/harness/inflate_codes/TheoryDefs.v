(* Law inflate_codes, the theory: THE definitions shared by Theory*.v.

   - `inv`: the invariant I of the harness's loop (call boundaries) that `codes_theory` chooses;
   - `Kc`: the facts kept at every loop head of one inflate() call (Model2.loop2 from Spec5.m_init) and at
     its exit, relative to the call's context: wrap (fixed by windowBits), src (the harness's n input bytes),
     pos (the bytes consumed before the call), inp (the bytes offered: src[pos .. pos + |inp|)), aout;
   - `step_post`: what one pass of the switch (stepf2) gives from a loop head satisfying Kc and mwf3;
   - `group_ok P`: step_post for every loop head whose mode satisfies P; the parts prove it per group of
     modes (TheoryHead.v, TheoryHdr.v, TheoryDict.v, TheoryBlock.v, TheoryDec.v, TheoryFast.v, TheoryTab.v).

   Why bits <= 31 (kc_bits): CHECK's `out = left` hides the call's output from inf_leave's Z_BUF_ERROR test;
   "Z_BUF_ERROR only without progress" holds because CHECK's NEEDBITS(32) must pull a byte when bits <= 31
   (kc_out: out <> avail_out on entry -> a byte was consumed).  bits > 31 only right after NEEDBITS(32), which
   is always followed by INITBITS or BAD; table lookups pull only while bits < e_bits <= 15 (Tables.tvalid);
   inflate_fast leaves bits < 8. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_codes.Facts.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Values of byte strings                                                                         *)

(* little-endian value of bytes (the bit buffer `hold` after pulling them from bits = 0) *)
Fixpoint le_val (l: list Z) : Z :=
  match l with [] => 0 | b :: l' => b + 256 * le_val l' end.

(* the zlib header's FDICT flag (byte 1, bit 5) *)
Definition fdict (src: list Z) : Prop := Z.land (Znth 1 src) 32 <> 0.

(* the bit buffer in HEAD (wrapped stream): p <= 1 bytes of the header read *)
Definition hd_head (src: list Z) (p hold bits: Z) : Prop :=
  0 <= p <= 1 /\ bits = 8 * p /\ hold = le_val (sublist 0 p src).

(* the bit buffer in DICTID: the zlib header (2 bytes, FDICT) read, then p - 2 bytes of the dictionary id *)
Definition hd_dictid (src: list Z) (p hold bits: Z) : Prop :=
  fdict src /\ 2 <= p <= 5 /\ bits = 8 * (p - 2) /\ hold = le_val (sublist 2 p src).

(* the dictionary id: the big-endian bytes 2..5 *)
Definition dict_id (src: list Z) : Z := be32 (sublist 2 6 src).

(* the wrap value inflateInit2_ sets for an accepted windowBits w: the wrapper of reset2_wb, with bit 3 set when
   the window size comes from the header (windowBits 0, 16 or 32; patch F8) *)
Definition wrap_of (w: Z) : Z := match reset2_wb w with Some (wrap, wb) => reset2_wrap wrap wb | None => 0 end.

(* its low three bits: the wrapper alone (0 raw, 5 zlib, 6 gzip, 7 zlib or gzip) *)
Definition wrap_low (w: Z) : Z := match reset2_wb w with Some (wrap, _) => wrap | None => 0 end.

Lemma wrap_of_low (w: Z) : Z.land (wrap_of w) 7 = wrap_low w /\ (wrap_of w = 0 <-> wrap_low w = 0).
Proof.
  unfold wrap_of, wrap_low. destruct (reset2_wb w) as [[wrap wb]|] eqn:E; [|split; [reflexivity | tauto]].
  destruct (reset2_wrap_ok w wrap wb E) as (_ & _ & A & B). auto.
Qed.

(* the bits the header modes test (1: zlib, 2: gzip, 4: check the header) are those of wrap_low *)
Lemma wrap_of_land (w k: Z) : 0 <= k <= 7 -> Z.land (wrap_of w) k = Z.land (wrap_low w) k.
Proof.
  intros K. rewrite <- (proj1 (wrap_of_low w)), <- Z.land_assoc.
  assert (C: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The call's context and the intra-call invariant                                               *)

(* the bytes offered are src[pos .. pos + |inp|) *)
Definition ctx_ok (src: list Z) (pos: Z) (inp: list Z) : Prop :=
  0 <= pos /\ pos + Zlength inp <= Zlength src /\ bytes_ok src /\
  (forall k, 0 <= k < Zlength inp -> Znth k inp = Znth (pos + k) src).

Record Kc (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (m: mst) : Prop := {
  kc_inp : m_inp m = inp;
  kc_aout : m_aout m = aout;
  kc_wrap : i_wrap (m_s m) = wrap;
  kc_head : i_head (m_s m) = false;
  kc_sync : m_mode m <> SYNC;
  (* ret is Z_OK until DONE / BAD set it *)
  kc_ret : m_mode m <> BAD -> m_mode m <> DONE -> m_ret m = Z_OK;
  kc_retx : m_leave m = 1 ->
    (m_mode m = DONE -> m_ret m = Z_STREAM_END) /\ (m_mode m = BAD -> m_ret m = Z_DATA_ERROR);
  kc_msg : m_mode m = BAD -> m_msg m <> None;
  kc_bits : m_mode m <> BAD -> m_mode m <> MEM -> 0 <= m_bits m <= 31;
  (* `out` differs from avail_out on entry only after CHECK, which consumed a byte *)
  kc_out : m_out m <> m_aout m -> 0 < m_nx m;
  (* the header bytes in the bit buffer *)
  kc_hd : wrap <> 0 -> m_mode m = HEAD -> hd_head src (pos + m_nx m) (m_hold m) (m_bits m);
  kc_did : m_mode m = DICTID -> Z.land wrap 1 <> 0 /\ hd_dictid src (pos + m_nx m) (m_hold m) (m_bits m);
  kc_dict : m_mode m = DICT ->
    Z.land wrap 1 <> 0 /\ fdict src /\ pos + m_nx m = 6 /\
    i_check (m_s m) = dict_id src /\ m_adler m = dict_id src }.

(* what one pass of the switch gives from a loop head *)
Definition step_post (wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (m: mst) (o: iout) : Prop :=
  match o with
  | IBrk m' => Kc wrap src pos inp aout m' /\ (m_leave m' = 0 -> m_mode m' <> DICT)
  | IRet r m' =>
      (r = Z_MEM_ERROR /\ m' = m /\ m_mode m = MEM) \/
      (r = Z_NEED_DICT /\ (m_mode m = DICTID \/ m_mode m = DICT) /\ m_mode m' = DICT /\
       m_snx m' = m_nx m' /\ m_sow m' = Zlength (m_ow m') /\ m_ow m' = m_ow m /\ m_leave m' = 0 /\
       Kc wrap src pos inp aout m')
  end.

(* step_post for every loop head whose mode satisfies P *)
Definition group_ok (P: Z -> Prop) : Prop :=
  forall wrap src pos inp aout flush m,
    ctx_ok src pos inp -> Kc wrap src pos inp aout m -> mwf3 m -> m_leave m = 0 -> P (m_mode m) ->
    step_post wrap src pos inp aout m (stepf2 flush lenfix_list distfix_list m).

(* the groups of modes (each part proves its group_ok) *)
Definition md_head (md: Z) : Prop := md = HEAD.
Definition md_hdr (md: Z) : Prop :=
  md = FLAGS \/ md = TIME \/ md = OS \/ md = EXLEN \/ md = EXTRA \/ md = NAME \/ md = COMMENT \/ md = HCRC.
Definition md_dict (md: Z) : Prop :=
  md = DICTID \/ md = DICT \/ md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO.
Definition md_block (md: Z) : Prop :=
  md = STORED \/ md = COPY_ \/ md = COPY \/ md = CHECK \/ md = LENGTH \/ md = DONE \/ md = BAD \/ md = MEM.
Definition md_tab (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS.
(* md_dec: Inv.decode_mode (LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT) *)

(* LEN's fast path: inflate_fast and `if (state->mode == TYPE) state->back = -1;` keep Kc *)
Definition fast_kc_stmt : Prop :=
  forall wrap src pos inp aout m,
    Kc wrap src pos inp aout m -> m_leave m = 0 -> m_mode m = LEN -> m_out m = m_aout m ->
    let m' := fast lenfix_list distfix_list (restore m) in
    let m' := if m_mode m' =? Zlib.proof.inflate.Model.TYPE then upd_s m' (fun s => set_i_back s (-1)) else m' in
    Kc wrap src pos inp aout m' /\ m_leave m' = 0 /\
    (m_mode m' = LEN \/ m_mode m' = Zlib.proof.inflate.Model.TYPE \/ m_mode m' = BAD).

(* the parts *)
Definition head_stmt : Prop := group_ok md_head.
Definition hdr_stmt : Prop := group_ok md_hdr.
Definition dict_stmt : Prop := group_ok md_dict.
Definition block_stmt : Prop := group_ok md_block.
Definition dec_stmt : Prop := fast_kc_stmt -> group_ok decode_mode.
(* TABLE -> LENLENS -> CODELENS fall into LEN_ (dec): the tables built in the pass are valid (the pass with
   flush = Z_TREES stops at LEN_, and stepf2_mwf3_stmt gives mwf3 there) *)
Definition tab_stmt : Prop := stepf2_mwf3_stmt -> group_ok decode_mode -> group_ok md_tab.

(* ---------------------------------------------------------------------------------------------- *)
(* The invariant of the harness's loop (call boundaries)                                          *)

Definition final_mode (final md: Z) : Prop :=
  (final = Z_OK /\ md <> DONE /\ md <> BAD) \/ (final = Z_STREAM_END /\ md = DONE) \/
  (final = Z_DATA_ERROR /\ md = BAD) \/ (final = Z_MEM_ERROR /\ md = MEM).

Definition inv (w: Z) (src: list Z) (pos final indict: Z) (z: zfields) (L: live) : Prop :=
  let s := l_s L in
  wbits_ok w = true /\ i_wrap s = wrap_of w /\ i_head s = false /\ i_mode s <> SYNC /\
  final_mode final (i_mode s) /\
  (i_mode s = BAD -> zf_msg z <> None) /\
  (i_mode s <> BAD -> i_mode s <> MEM -> 0 <= i_bits s <= 31) /\
  (wrap_of w <> 0 -> i_mode s = HEAD -> hd_head src pos (i_hold s) (i_bits s)) /\
  (i_mode s = DICTID -> Z.land (wrap_of w) 1 <> 0 /\ hd_dictid src pos (i_hold s) (i_bits s)) /\
  (i_mode s = DICT -> Z.land (wrap_of w) 1 <> 0 /\ fdict src /\ pos = 6 /\
                      i_check s = dict_id src /\ zf_adler z = dict_id src) /\
  ((indict = 1 /\ i_mode s = DICT) \/ (indict = 0 /\ i_mode s <> DICT)).
