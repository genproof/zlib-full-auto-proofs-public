(* Law inflate_reset, the theory: THE definitions shared by IRSim*.v, IRTabDet.v, IRRun.v.

   The claim: after inflateReset / inflateReset2, stream a behaves like stream b, freshly made by inflateInit2_.
   Their model states (istate) are NOT equal: the resets write only some fields (ApiModel.reset_s), the others
   keep what phase 1 left there (check, length, offset, extra, lenbits, distbits, ncode, nlen, ndist, have,
   lens, codes, was, the window allocation; wbits after inflateReset).  They are related by `srel`: equal
   wherever inflate() may READ them before writing them (per mode), free elsewhere.  wbits: HEAD stores the
   window size from the header when wbits is 0; a reset stream keeps the one phase 1 stored, a fresh one
   stores it again from the same header bytes: `wcl` ties both to the header src[0..2) (hdr_wb), and srel lets
   them differ only in HEAD (and BAD).  The machines of one inflate() call are related by `mrel` (every local
   and stream field equal, the gz_header m_h free: i_head is false), the loop heads by `Kr`.

   The parts: one pass of the switch (stepf2) from related loop heads gives related results (`sim_post`), per
   group of modes (`sgroup_ok`), as Facts of inflate_codes' theory (TheoryDefs.v group_ok) do for one stream:
   IRSimHead.v (HEAD: the only part that unfolds c_HEAD), IRSimHdr.v, IRSimDict.v, IRSimBlock.v, IRSimDec.v
   (+ IRSimFast.v: inflate_fast), IRSimTab.v (+ IRTabDet.v: inflate_table's reachable entries do not depend on
   the old contents of the table space).  IRRun.v: loop2 / run2 / inf_leave, the invariants I1 I2, the facts
   of IRFacts.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.harness.inflate_reset.IRFacts.
Require Export Zlib.proof.inflate.Model2 Zlib.proof.inflate.Inv3 Zlib.proof.inflate.Tables.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The input                                                                                      *)

(* little-endian value of bytes (the bit buffer `hold` after pulling them from bits = 0) *)
Fixpoint ir_le (l: list Z) : Z :=
  match l with [] => 0 | b :: l' => b + 256 * ir_le l' end.

(* the bit buffer in HEAD (wrapped stream): p <= 1 bytes of the header read *)
Definition ir_hd (src: list Z) (p hold bits: Z) : Prop :=
  0 <= p <= 1 /\ bits = 8 * p /\ hold = ir_le (sublist 0 p src).

(* the bytes offered to the call are src[pos .. pos + |inp|) *)
Definition ir_ctx (src: list Z) (pos: Z) (inp: list Z) : Prop :=
  0 <= pos /\ pos + Zlength inp <= Zlength src /\ bytes_ok src /\
  (forall k, 0 <= k < Zlength inp -> Znth k inp = Znth (pos + k) src).

(* the window size HEAD stores from wbits 0 for the header src[0..2), when it accepts the header
   (gzip: 15; zlib: CINFO + 8 <= 15, with a valid check and method); None: the header is not accepted *)
Definition hdr_wb (wrap: Z) (src: list Z) : option Z :=
  if Zlength src <? 2 then None else
  let b0 := Znth 0 src in let b1 := Znth 1 src in
  if (negb (Z.land wrap 2 =? 0) && (b0 =? 31) && (b1 =? 139))%bool then Some 15
  else if (negb (Z.land wrap 1 =? 0) && ((b0 * 256 + b1) mod 31 =? 0) && (Z.land b0 15 =? 8) &&
           (Z.shiftr b0 4 + 8 <=? 15))%bool
  then Some (Z.shiftr b0 4 + 8)
  else None.

(* wbits of a stream started (init or reset) with wbits W0 on the input src: W0, or what HEAD stored from 0
   (only a wrapped stream starts with wbits 0: ApiModel.reset2_wb) *)
Definition wcl (W0 wrap: Z) (src: list Z) (wb: Z) : Prop :=
  wb = W0 \/ (W0 = 0 /\ wrap <> 0 /\ forall v, hdr_wb wrap src = Some v -> wb = v).

(* ---------------------------------------------------------------------------------------------- *)
(* The relation                                                                                   *)

(* the entries of the table t (root bits rb) that a lookup can read (Tables.v tvalid: the root entries and the
   sub-tables of the links), equal in both states *)
Definition treach_eq (kind: Z) (sa sb: istate) (t: tref) (rb: Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb ->
    let e := tab_entry lenfix_list distfix_list sa t i in
    e = tab_entry lenfix_list distfix_list sb t i /\
    (islink kind (e_op e) = true -> forall j, 0 <= j < 2 ^ e_op e ->
       tab_entry lenfix_list distfix_list sa t (e_val e + j) = tab_entry lenfix_list distfix_list sb t (e_val e + j)).

(* state->length is read before being written *)
Definition lenlive (s: istate) : Prop :=
  i_mode s = COPY_ \/ i_mode s = COPY \/ i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT \/
  i_mode s = MATCH \/ i_mode s = LIT \/ (i_mode s = EXTRA /\ Z.land (i_flags s) 1024 <> 0).

(* sa (the reset stream) and sb (the fresh one); the conditions are on sb's mode (= sa's).
   noout: no output in the current call (HEAD and a BAD header leave the check value unwritten) *)
Record srel (noout: Prop) (sa sb: istate) : Prop := {
  sr_mode : i_mode sa = i_mode sb;
  sr_last : i_last sa = i_last sb;
  sr_wrap : i_wrap sa = i_wrap sb;
  sr_havedict : i_havedict sa = i_havedict sb;
  sr_flags : i_flags sa = i_flags sb;
  sr_dmax : i_dmax sa = i_dmax sb;
  sr_total : i_total sa = i_total sb;
  sr_head : i_head sa = i_head sb;
  sr_wsize : i_wsize sa = i_wsize sb;
  sr_whave : i_whave sa = i_whave sb;
  sr_wnext : i_wnext sa = i_wnext sb;
  sr_wdata : i_wdata sa = i_wdata sb;
  sr_hold : i_hold sa = i_hold sb;
  sr_bits : i_bits sa = i_bits sb;
  sr_lencode : i_lencode sa = i_lencode sb;
  sr_distcode : i_distcode sa = i_distcode sb;
  sr_next : i_next sa = i_next sb;
  sr_sane : i_sane sa = i_sane sb;
  sr_back : i_back sa = i_back sb;
  sr_wbits : i_wbits sa = i_wbits sb \/ i_mode sb = HEAD \/ i_mode sb = BAD;
  sr_check : i_check sa = i_check sb \/ i_wrap sb = 0 \/ ((i_mode sb = HEAD \/ i_mode sb = BAD) /\ noout);
  sr_length : lenlive sb -> i_length sa = i_length sb;
  sr_offset : i_mode sb = DISTEXT \/ i_mode sb = MATCH -> i_offset sa = i_offset sb;
  sr_extra : i_mode sb = LENEXT \/ i_mode sb = DISTEXT -> i_extra sa = i_extra sb;
  sr_lenbits : i_mode sb = CODELENS \/ decode_mode (i_mode sb) -> i_lenbits sa = i_lenbits sb;
  sr_distbits : decode_mode (i_mode sb) -> i_distbits sa = i_distbits sb;
  sr_ncode : i_mode sb = LENLENS -> i_ncode sa = i_ncode sb;
  sr_nlen : i_mode sb = LENLENS \/ i_mode sb = CODELENS ->
    i_nlen sa = i_nlen sb /\ i_ndist sa = i_ndist sb /\ i_have sa = i_have sb;
  sr_lenlens : i_mode sb = LENLENS -> forall k, 0 <= k < i_have sb ->
    Znth (Znth k order) (i_lens sa) = Znth (Znth k order) (i_lens sb);
  sr_codelens : i_mode sb = CODELENS -> forall k, 0 <= k < i_have sb -> Znth k (i_lens sa) = Znth k (i_lens sb);
  sr_cltab : i_mode sb = CODELENS -> treach_eq CODES sa sb (i_lencode sb) (i_lenbits sb);
  sr_dectab : decode_mode (i_mode sb) ->
    treach_eq LENS sa sb (i_lencode sb) (i_lenbits sb) /\ treach_eq DISTS sa sb (i_distcode sb) (i_distbits sb)
}.

(* the machines of one call: everything equal but the states (srel) and the gz_header (unused) *)
Record mrel (ma mb: mst) : Prop := {
  mr_s : srel (m_ow mb = []) (m_s ma) (m_s mb);
  mr_inp : m_inp ma = m_inp mb;
  mr_aout : m_aout ma = m_aout mb;
  mr_nx : m_nx ma = m_nx mb;
  mr_ow : m_ow ma = m_ow mb;
  mr_hold : m_hold ma = m_hold mb;
  mr_bits : m_bits ma = m_bits mb;
  mr_in : m_in ma = m_in mb;
  mr_out : m_out ma = m_out mb;
  mr_ret : m_ret ma = m_ret mb;
  mr_leave : m_leave ma = m_leave mb;
  mr_adler : m_adler ma = m_adler mb;
  mr_msg : m_msg ma = m_msg mb;
  mr_tin : m_tin ma = m_tin mb;
  mr_tout : m_tout ma = m_tout mb;
  mr_snx : m_snx ma = m_snx mb;
  mr_sow : m_sow ma = m_sow mb }.

(* the loop heads of the two calls (and their exits), in the call's context: W0 the wbits both streams
   started with, wrap, src (the harness's input), pos (bytes consumed before the call), inp, aout.
   (With ma = mb this is a one-stream invariant: phase 1 uses it for stream a.) *)
Record Kr (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (ma mb: mst) : Prop := {
  kr_rel : mrel ma mb;
  kr_inp : m_inp mb = inp;
  kr_aout : m_aout mb = aout;
  kr_wrap : i_wrap (m_s mb) = wrap;
  kr_head : i_head (m_s mb) = false;
  kr_wa : wcl W0 wrap src (i_wbits (m_s ma));
  kr_wb : wcl W0 wrap src (i_wbits (m_s mb));
  kr_hd : wrap <> 0 -> m_mode mb = HEAD -> ir_hd src (pos + m_nx mb) (m_hold mb) (m_bits mb) /\ m_ow mb = [] }.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass of the switch                                                                         *)

(* both passes break (with related machines) or both return the same code (with related machines) *)
Definition sim_post (W0 wrap: Z) (src: list Z) (pos: Z) (inp: list Z) (aout: Z) (oa ob: iout) : Prop :=
  match oa, ob with
  | IBrk ma', IBrk mb' => Kr W0 wrap src pos inp aout ma' mb'
  | IRet ra ma', IRet rb mb' => ra = rb /\ Kr W0 wrap src pos inp aout ma' mb'
  | _, _ => False
  end.

(* sim_post for every pair of related loop heads whose mode satisfies P *)
Definition sgroup_ok (P: Z -> Prop) : Prop :=
  forall W0 wrap src pos inp aout flush ma mb,
    ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3 ma -> mwf3 mb -> m_leave mb = 0 ->
    P (m_mode mb) ->
    sim_post W0 wrap src pos inp aout (stepf2 flush lenfix_list distfix_list ma)
      (stepf2 flush lenfix_list distfix_list mb).

(* the groups of modes *)
Definition md_head (md: Z) : Prop := md = HEAD.
Definition md_hdr (md: Z) : Prop :=
  md = FLAGS \/ md = TIME \/ md = OS \/ md = EXLEN \/ md = EXTRA \/ md = NAME \/ md = COMMENT \/ md = HCRC.
Definition md_dict (md: Z) : Prop :=
  md = DICTID \/ md = DICT \/ md = Zlib.proof.inflate.Model.TYPE \/ md = TYPEDO.
Definition md_block (md: Z) : Prop :=
  md = STORED \/ md = COPY_ \/ md = COPY \/ md = CHECK \/ md = LENGTH \/ md = DONE \/ md = BAD \/ md = MEM \/
  md = SYNC.
Definition md_tab (md: Z) : Prop := md = TABLE \/ md = LENLENS \/ md = CODELENS.
(* decode modes: Inv.decode_mode (LEN_, LEN, LENEXT, DIST, DISTEXT, MATCH, LIT) *)

(* inflate_fast (LEN's fast path) from related machines *)
Definition fast_sim_stmt : Prop :=
  forall W0 wrap src pos inp aout ma mb,
    ir_ctx src pos inp -> Kr W0 wrap src pos inp aout ma mb -> mwf3 ma -> mwf3 mb -> m_leave mb = 0 ->
    m_mode mb = LEN -> m_out mb = m_aout mb -> 6 <= m_have mb -> 258 <= m_left mb -> m_bits mb < 8 ->
    Kr W0 wrap src pos inp aout (fast lenfix_list distfix_list (restore ma))
      (fast lenfix_list distfix_list (restore mb)).

(* inflate_table's table, as far as a lookup reads it (the root entries and the links' sub-tables), does not
   depend on the old contents of the space it is built in; neither do its return value, size and root bits *)
Definition treach_l (kind: Z) (t1 t2: list entry) (rb: Z) : Prop :=
  forall i, 0 <= i < 2 ^ rb ->
    Znth i t1 = Znth i t2 /\
    (islink kind (e_op (Znth i t1)) = true -> forall j, 0 <= j < 2 ^ e_op (Znth i t1) ->
       Znth (e_val (Znth i t1) + j) t1 = Znth (e_val (Znth i t1) + j) t2).

Definition tabdet_stmt : Prop :=
  forall type lens req old1 old2,
    inputs_ok type lens req -> (type = CODES -> Zlength lens <= 19) ->
    cap_ok type lens req (Zlength old1) -> Forall entry_ok old1 ->
    Zlength old2 = Zlength old1 -> Forall entry_ok old2 ->
    it_ret (inflate_table_model type lens req old1) = it_ret (inflate_table_model type lens req old2) /\
    it_adv (inflate_table_model type lens req old1) = it_adv (inflate_table_model type lens req old2) /\
    it_bits req (inflate_table_model type lens req old1) = it_bits req (inflate_table_model type lens req old2) /\
    (forall root used t1, inflate_table_model type lens req old1 = ROk root used t1 ->
       exists t2, inflate_table_model type lens req old2 = ROk root used t2 /\ treach_l type t1 t2 root).

(* the parts *)
Definition head_sim_stmt : Prop := sgroup_ok md_head.
Definition hdr_sim_stmt : Prop := sgroup_ok md_hdr.
Definition dict_sim_stmt : Prop := sgroup_ok md_dict.
Definition block_sim_stmt : Prop := sgroup_ok md_block.
Definition dec_sim_stmt : Prop := fast_sim_stmt -> sgroup_ok decode_mode.
(* TABLE -> LENLENS -> CODELENS fall into LEN_ (dec) *)
Definition tab_sim_stmt : Prop :=
  stepf2_mwf3_stmt -> Zlib.proof.inflate.Cover3.cover3_stmt -> tabdet_stmt -> sgroup_ok decode_mode ->
  sgroup_ok md_tab.
