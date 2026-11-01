(* The invariant of the inflate machine (Model.v): the ranges of the values (as the C types hold
   them) and the structural facts the memory safety of the cases needs.  A record with named fields,
   so that proofs use projections and the record can grow. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Model.
Require Export Zlib.proof.zutil.Libc.
Require Export Zlib.proof.inflate.Fixed.
Require Export Zlib.proof.inflate.Tables.
Import ListNotations.
Local Open Scope Z_scope.

Definition urange (x: Z) : Prop := 0 <= x <= Int.max_unsigned.
Definition srange (x: Z) : Prop := Int.min_signed <= x <= Int.max_signed.
Definition lrange (x: Z) : Prop := 0 <= x <= Int64.max_unsigned.

Definition tref_ok (t: tref) : Prop :=
  match t with TCodes k => 0 <= k <= ENOUGH_CODES | _ => True end.

(* the struct inflate_state *)
Record swf (s: istate) : Prop := {
  sw_mode : HEAD <= i_mode s <= SYNC;
  sw_last : 0 <= i_last s <= 1;
  (* bits 0-2: zlib, gzip, check; bit 3 (patch F8: the window size comes from each header) only with bit 0 or
     bit 1 (inflateReset2 sets it for windowBits 0, 16 and 32; inflateValidate toggles bit 2) *)
  sw_wrap : 0 <= i_wrap s <= 7 \/ 9 <= i_wrap s <= 11 \/ 13 <= i_wrap s <= 15;
  sw_havedict : 0 <= i_havedict s <= 1;
  sw_flags : srange (i_flags s);
  sw_dmax : urange (i_dmax s);
  sw_check : lrange (i_check s);
  sw_total : lrange (i_total s);
  sw_wbits : 0 <= i_wbits s <= 23;
  sw_wsize : i_wsize s = 0 \/ (i_win s = true /\ i_wsize s = 2 ^ i_wbits s);
  sw_whave : 0 <= i_whave s <= i_wsize s;
  sw_wnext : 0 <= i_wnext s <= i_wsize s /\ (0 < i_wsize s -> i_wnext s < i_wsize s);
  sw_wvalid : i_whave s < i_wsize s -> i_wnext s = i_whave s;
  sw_wdata : Zlength (i_wdata s) = i_whave s /\ bytes_ok (i_wdata s);
  sw_hold : lrange (i_hold s);
  sw_bits : 0 <= i_bits s <= 39;
  sw_length : urange (i_length s);
  sw_offset : urange (i_offset s);
  sw_extra : 0 <= i_extra s <= 15;
  sw_lencode : tref_ok (i_lencode s);
  sw_distcode : tref_ok (i_distcode s);
  sw_lenbits : 0 <= i_lenbits s <= 15;
  sw_distbits : 0 <= i_distbits s <= 15;
  sw_ncode : 0 <= i_ncode s <= 19;
  sw_nlen : 0 <= i_nlen s <= 288;
  sw_ndist : 0 <= i_ndist s <= 32;
  sw_have : 0 <= i_have s <= 320;
  sw_next : 0 <= i_next s <= ENOUGH_CODES;
  sw_lens : Zlength (i_lens s) = 320 /\ Forall (fun x => 0 <= x <= 65535) (i_lens s);
  sw_codes : Zlength (i_codes s) = ENOUGH_CODES /\ Forall entry_ok (i_codes s);
  sw_sane : i_sane s = 1;
  sw_back : -1 <= i_back s <= 1000;
  sw_was : urange (i_was s) }.

(* The values of state->wrap that sw_wrap allows, and what the code does with them: the bit tests and the updates
   of inflateValidate (bit 2), inflateSync (bit 2 cleared, bit 3 hidden from its inflateReset call) and
   inflateReset (bit 3). *)
Lemma wrap_cases (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 ->
  w = 0 \/ w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/
  w = 9 \/ w = 10 \/ w = 11 \/ w = 13 \/ w = 14 \/ w = 15.
Proof. lia. Qed.

Ltac wrap_cases H := destruct (wrap_cases _ H) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
  [-> | [-> | [-> | ->]]]]]]]]]]]]].

Lemma wrap_range (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 -> 0 <= w <= 15.
Proof. lia. Qed.

(* bit 3 only with bit 0 or bit 1 *)
Lemma wrap_land8 (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 ->
  Z.land w 8 <> 0 -> Z.land w 3 <> 0.
Proof. intros H. wrap_cases H; cbv; congruence. Qed.

(* bit 3 cleared: 0..7, zero exactly when wrap is *)
Lemma wrap_clear8 (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 ->
  0 <= Z.land w (Z.lnot 8) <= 7 /\ (Z.land w (Z.lnot 8) = 0 <-> w = 0) /\
  Z.land (Z.land w (Z.lnot 8)) 1 = Z.land w 1.
Proof. intros H. wrap_cases H; cbv; intuition congruence. Qed.

(* inflateValidate and inflateSync: bit 2 set (on a nonzero wrap) or cleared *)
Lemma wrap_set4 (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 -> w <> 0 ->
  0 <= Z.lor w 4 <= 7 \/ 9 <= Z.lor w 4 <= 11 \/ 13 <= Z.lor w 4 <= 15.
Proof. intros H N. wrap_cases H; cbv; first [congruence | intuition congruence]. Qed.

Lemma wrap_clear4 (w: Z) : 0 <= w <= 7 \/ 9 <= w <= 11 \/ 13 <= w <= 15 ->
  0 <= Z.land w (Z.lnot 4) <= 7 \/ 9 <= Z.land w (Z.lnot 4) <= 11 \/ 13 <= Z.land w (Z.lnot 4) <= 15.
Proof. intros H. wrap_cases H; cbv; intuition congruence. Qed.

Lemma sw_wrap_range (s: istate) : swf s -> 0 <= i_wrap s <= 15.
Proof. intros H. exact (wrap_range _ (sw_wrap _ H)). Qed.

(* the gz_header *)
Record hwf (h: hstate) : Prop := {
  hw_text : srange (h_text h);
  hw_time : lrange (h_time h);
  hw_xflags : srange (h_xflags h);
  hw_os : srange (h_os h);
  hw_extra_len : urange (h_extra_len h);
  hw_extra_max : 0 <= h_extra_max h <= 65536;
  hw_name_max : 0 <= h_name_max h <= 65536;
  hw_comm_max : 0 <= h_comm_max h <= 65536;
  hw_xbuf : Zlength (h_xbuf h) = h_extra_max h /\ bytes_ok (h_xbuf h);
  hw_nbuf : Zlength (h_nbuf h) = h_name_max h /\ bytes_ok (h_nbuf h);
  hw_cbuf : Zlength (h_cbuf h) = h_comm_max h /\ bytes_ok (h_cbuf h);
  hw_hcrc : srange (h_hcrc h);
  hw_done : srange (h_done h) }.

(* the modes that decode with the tables *)
Definition decode_mode (md: Z) : Prop :=
  md = LEN_ \/ md = LEN \/ md = LENEXT \/ md = DIST \/ md = DISTEXT \/ md = MATCH \/ md = LIT.

(* what each mode needs of the state *)
Record modewf (s: istate) : Prop := {
  md_lenlens : i_mode s = LENLENS ->
    4 <= i_ncode s <= 19 /\ 0 <= i_have s <= i_ncode s /\ 257 <= i_nlen s <= 286 /\ 1 <= i_ndist s <= 30 /\
    (forall k, 0 <= k < i_have s -> Znth (Znth k order) (i_lens s) <= 7);
  md_codelens : i_mode s = CODELENS ->
    0 <= i_have s <= i_nlen s + i_ndist s /\ 257 <= i_nlen s <= 286 /\ 1 <= i_ndist s <= 30 /\
    i_lencode s = TCodes 0 /\ tvalid CODES lenfix_list distfix_list s (i_lencode s) (i_lenbits s) /\
    (forall k, 0 <= k < i_have s -> Znth k (i_lens s) <= 15);
  md_tables : decode_mode (i_mode s) ->
    tvalid LENS lenfix_list distfix_list s (i_lencode s) (i_lenbits s) /\
    tvalid DISTS lenfix_list distfix_list s (i_distcode s) (i_distbits s);
  md_lenext : i_mode s = LENEXT -> i_extra s <= 5;
  md_distext : i_mode s = DISTEXT -> i_extra s <= 13;
  md_match : i_mode s = MATCH -> 1 <= i_length s;
  (* a match's length (from a LENS entry, 3..258) and distance (from a DISTS entry, >= 1) *)
  md_length : i_mode s = LENEXT \/ i_mode s = DIST \/ i_mode s = DISTEXT -> 1 <= i_length s;
  md_offset : i_mode s = DISTEXT \/ i_mode s = MATCH -> 1 <= i_offset s;
  (* state->back counts the bits of a symbol from 0 (LEN): no int overflow on the way *)
  md_back : (i_mode s = LENEXT -> i_back s <= 15) /\ (i_mode s = DIST -> i_back s <= 20) /\
            (i_mode s = DISTEXT -> i_back s <= 35) }.

(* the machine *)
Record mwf (m: mst) : Prop := {
  mw_md : modewf (m_s m);
  mw_s : swf (m_s m);
  mw_h : hwf (m_h m);
  mw_inp : Zlength (m_inp m) <= Int.max_signed /\ bytes_ok (m_inp m);
  mw_aout : 0 <= m_aout m <= Int.max_signed;
  mw_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mw_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mw_hold : lrange (m_hold m);
  mw_bits : 0 <= m_bits m <= 39;
  mw_in : m_in m = Zlength (m_inp m);
  mw_out : urange (m_out m);
  mw_ret : -5 <= m_ret m <= 2;
  mw_leave : 0 <= m_leave m <= 1;
  mw_adler : lrange (m_adler m);
  mw_tin : lrange (m_tin m);
  mw_tout : lrange (m_tout m);
  mw_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mw_sow : 0 <= m_sow m <= Zlength (m_ow m);
  (* `out` (the output space at the start of the call) is avail_out's start value, except after CHECK's
     `out = left` (modes LENGTH, DONE, BAD then) *)
  mw_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

Lemma mwf_left: forall m, mwf m -> 0 <= m_left m <= Int.max_signed.
Proof. intros m H. destruct H. unfold m_left. pose proof (Zlength_nonneg (m_ow m)). lia. Qed.

Lemma mwf_have: forall m, mwf m -> 0 <= m_have m <= Int.max_signed.
Proof. intros m H. destruct H. unfold m_have. lia. Qed.

Lemma mwf_out_eq: forall m, mwf m -> m_mode m <> LENGTH -> m_mode m <> DONE -> m_mode m <> BAD ->
  m_out m = m_aout m.
Proof. intros m H A B C. destruct (mw_outeq _ H) as [E | [E | [E | E]]]; congruence. Qed.
