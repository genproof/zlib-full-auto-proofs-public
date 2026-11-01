(* The model of inflate.c's API functions other than inflate() (whose model is
   src/proof/inflate/Model.v `run`): pure functions over the stream fields the application sees
   (zfields) and the struct inflate_state (istate).  Each follows the C code of inflate.c. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Export Zlib.proof.inflate.Model.
Import ListNotations.
Local Open Scope Z_scope.

Definition Z_VERSION_ERROR := -6.

(* the fields of struct z_stream the application sees (state, zalloc, zfree, opaque aside) *)
Record zfields := ZF {
  zf_ni : val; zf_ai : Z; zf_tin : Z; zf_no : val; zf_ao : Z; zf_tout : Z;
  zf_msg : option msgid; zf_dt : Z; zf_adler : Z; zf_res : val }.

Definition set_zf_counters (z: zfields) (tin tout: Z) : zfields :=
  ZF (zf_ni z) (zf_ai z) tin (zf_no z) (zf_ao z) tout (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).
Definition set_zf_in (z: zfields) (ni: val) (ai tin: Z) : zfields :=
  ZF ni ai tin (zf_no z) (zf_ao z) (zf_tout z) (zf_msg z) (zf_dt z) (zf_adler z) (zf_res z).
Definition set_zf_msg (z: zfields) (msg: option msgid) : zfields :=
  ZF (zf_ni z) (zf_ai z) (zf_tin z) (zf_no z) (zf_ao z) (zf_tout z) msg (zf_dt z) (zf_adler z) (zf_res z).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateResetKeep / inflateReset / inflateReset2                                               *)

Definition reset_keep_s (s: istate) : istate :=
  let s := set_i_total s 0 in
  let s := set_i_mode s HEAD in
  let s := set_i_last s 0 in
  let s := set_i_havedict s 0 in
  let s := set_i_flags s (-1) in
  let s := set_i_dmax s 32768 in
  let s := set_i_head s false in
  let s := set_i_hold s 0 in
  let s := set_i_bits s 0 in
  let s := set_i_lencode s (TCodes 0) in
  let s := set_i_distcode s (TCodes 0) in
  let s := set_i_next s 0 in
  let s := set_i_sane s 1 in
  set_i_back s (-1).

Definition reset_keep_z (z: zfields) (s: istate) : zfields :=
  ZF (zf_ni z) (zf_ai z) 0 (zf_no z) (zf_ao z) 0 None 0
     (if i_wrap s =? 0 then zf_adler z else Z.land (i_wrap s) 1) (zf_res z).

(* inflateReset when bit 3 of wrap is clear: the window is emptied (but kept), then inflateResetKeep
   (inflateSync calls inflateReset with bit 3 hidden: this is its reset) *)
Definition reset_s (s: istate) : istate :=
  reset_keep_s (set_i_wdata (set_i_wnext (set_i_whave (set_i_wsize s 0) 0) 0) []).

(* patch F8: bit 3 of wrap says that the window size comes from each header (inflateReset2 with windowBits 0,
   16 or 32); inflateReset then frees the window (the next header may ask for a larger one) and sets wbits = 0
   again, as for a new stream *)
Definition reset_hdr_s (s: istate) : istate :=
  if Z.land (i_wrap s) 8 =? 0 then s else set_i_wbits (set_i_win s false) 0.

(* inflateReset *)
Definition reset_full_s (s: istate) : istate := reset_s (reset_hdr_s s).

(* inflateReset2's windowBits: Some (wrap, wbits) when accepted *)
Definition reset2_wb (w: Z) : option (Z * Z) :=
  if w <? 0 then
    if w <? -15 then None else
    let wb := - w in
    if (8 <=? wb) && (wb <=? 15) then Some (0, wb) else None
  else
    let wrap := Z.shiftr w 4 + 5 in
    let wb := if w <? 48 then Z.land w 15 else w in
    if (wb =? 0) || ((8 <=? wb) && (wb <=? 15)) then Some (wrap, wb) else None.

(* inflateReset2 on an accepted windowBits (wrap, wb of reset2_wb): the window is freed when its size changes;
   with wb = 0 (the window size of the header) bit 3 of wrap is set (patch F8); then inflateReset *)
Definition reset2_wrap (wrap wb: Z) : Z := if wb =? 0 then Z.lor wrap 8 else wrap.

Definition reset2_s (wrap wb: Z) (s: istate) : istate :=
  let s := if i_win s && negb (i_wbits s =? wb) then set_i_win s false else s in
  reset_full_s (set_i_wbits (set_i_wrap s (reset2_wrap wrap wb)) wb).

(* the accepted windowBits: raw with 8..15, or zlib / gzip / either (wrap 5..7) with 0 or 8..15 *)
Lemma reset2_wb_cases (w wrap wb: Z) : reset2_wb w = Some (wrap, wb) ->
  (wrap = 0 /\ 8 <= wb <= 15) \/ (5 <= wrap <= 7 /\ (wb = 0 \/ 8 <= wb <= 15)).
Proof.
  intros H. unfold reset2_wb in H.
  destruct (Z.ltb_spec w 0).
  - destruct (Z.ltb_spec w (-15)); [discriminate | ].
    destruct (andb (8 <=? - w) (- w <=? 15)) eqn:E; [ | discriminate].
    injection H as <- <-. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
  - destruct (Z.ltb_spec w 48).
    + destruct (orb (Z.land w 15 =? 0) (andb (8 <=? Z.land w 15) (Z.land w 15 <=? 15))) eqn:E; [ | discriminate].
      injection H as <- <-. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
      assert (0 <= w / 16) by (apply Z.div_pos; lia).
      assert (w / 16 < 3) by (apply Z.div_lt_upper_bound; lia).
      right. split; [lia | ].
      apply orb_prop in E. destruct E as [E | E]; [left; apply Z.eqb_eq in E; lia | right].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
    + destruct (orb (w =? 0) (andb (8 <=? w) (w <=? 15))) eqn:E; [ | discriminate].
      exfalso. apply orb_prop in E. destruct E as [E | E]; [apply Z.eqb_eq in E; lia | ].
      apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2. lia.
Qed.

(* the wrap that inflateReset2 stores: the range of Inv.sw_wrap, bit 3 exactly when wb = 0, bits 0-2 those of
   reset2_wb *)
Lemma reset2_wrap_ok (w wrap wb: Z) : reset2_wb w = Some (wrap, wb) ->
  (0 <= reset2_wrap wrap wb <= 7 \/ 9 <= reset2_wrap wrap wb <= 11 \/ 13 <= reset2_wrap wrap wb <= 15) /\
  (Z.land (reset2_wrap wrap wb) 8 =? 0) = negb (wb =? 0) /\
  Z.land (reset2_wrap wrap wb) 7 = wrap /\ (reset2_wrap wrap wb = 0 <-> wrap = 0).
Proof.
  intros H. unfold reset2_wrap.
  destruct (reset2_wb_cases w wrap wb H) as [[-> B] | [A B]].
  - destruct (Z.eqb_spec wb 0) as [E | E]; [lia | ]. cbv. intuition congruence.
  - assert (wrap = 5 \/ wrap = 6 \/ wrap = 7) as [-> | [-> | ->]] by lia;
      destruct (Z.eqb_spec wb 0); cbv; intuition congruence.
Qed.

(* zmemzero of the state, window = NULL, mode = HEAD (inflateInit2_ before inflateReset2) *)
Definition zero_s : istate :=
  IS HEAD 0 0 0 0 0 0 0 false 0 0 0 0 false [] 0 0 0 0 0 (TCodes 0) (TCodes 0) 0 0 0 0 0 0 0
     (Zrepeat 0 320) (Zrepeat (mkE 0 0 0) ENOUGH_CODES) 0 0 0.

(* the state after a successful inflateInit2_(strm, w) *)
Definition init_s (wrap wb: Z) : istate := reset2_s wrap wb zero_s.

(* inflateInit2_'s windowBits test (zlib.h; the harness's inflate_wbits_ok) *)
Definition wbits_ok (w: Z) : bool := match reset2_wb w with Some _ => true | None => false end.

(* ---------------------------------------------------------------------------------------------- *)
(* inflatePrime(strm, bits, value): None = Z_STREAM_ERROR                                         *)

Definition prime_s (bits value: Z) (s: istate) : option istate :=
  if bits =? 0 then Some s
  else if bits <? 0 then Some (set_i_bits (set_i_hold s 0) 0)
  else if (16 <? bits) || (32 <? i_bits s + bits) then None
  else
    let v := Z.land value (2 ^ bits - 1) in
    Some (set_i_bits (set_i_hold s (u64 (i_hold s + v * 2 ^ i_bits s))) (i_bits s + bits)).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetDictionary: the window's bytes in stream order                                      *)

Definition dict_bytes (s: istate) : list Z :=
  sublist (i_wnext s) (i_whave s) (i_wdata s) ++ sublist 0 (i_wnext s) (i_wdata s).

(* ---------------------------------------------------------------------------------------------- *)
(* inflateValidate, inflateMark, inflateCodesUsed, inflateSyncPoint                               *)

Definition validate_s (check: Z) (s: istate) : istate :=
  if negb (check =? 0) && negb (i_wrap s =? 0) then set_i_wrap s (Z.lor (i_wrap s) 4)
  else set_i_wrap s (Z.land (i_wrap s) (Z.lnot 4)).

(* the value of inflateMark (a long), for a live stream *)
Definition mark_val (s: istate) : Z :=
  let x := Z.shiftl (i_back s mod 2 ^ 64) 16 mod 2 ^ 64 in
  let hi := if x <? 2 ^ 63 then x else x - 2 ^ 64 in
  hi + (if i_mode s =? COPY then i_length s
        else if i_mode s =? MATCH then u32 (i_was s - i_length s) else 0).

Definition syncpoint_val (s: istate) : Z :=
  if (i_mode s =? STORED) && (i_bits s =? 0) then 1 else 0.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSync                                                                                    *)

(* syncsearch: the pattern 0 0 ff ff; (got', bytes looked at) *)
Fixpoint ssearch (got: Z) (buf: list Z) : Z * Z :=
  match buf with
  | [] => (got, 0)
  | b :: r =>
      if got <? 4 then
        let got' := if b =? (if got <? 2 then 0 else 255) then got + 1
                    else if negb (b =? 0) then 0 else 4 - got in
        let '(g, n) := ssearch got' r in (g, n + 1)
      else (got, 0)
  end.

(* the whole bytes of the bit buffer (after dropping to a byte boundary) *)
Fixpoint hold_bytes (k: nat) (hold: Z) : list Z :=
  match k with O => [] | S k' => hold mod 256 :: hold_bytes k' (Z.shiftr hold 8) end.

(* the first part of inflateSync when the mode is not SYNC yet *)
Definition sync_start (s: istate) : istate :=
  let hold := Z.shiftr (i_hold s) (Z.land (i_bits s) 7) in
  let bits := i_bits s - Z.land (i_bits s) 7 in
  let buf := hold_bytes (Z.to_nat (bits / 8)) hold in
  let s := set_i_mode s SYNC in
  let s := set_i_hold s (Z.shiftr hold (8 * (bits / 8))) in
  let s := set_i_bits s (bits mod 8) in
  set_i_have s (fst (ssearch 0 buf)).

Inductive sync_out := SyncBuf | SyncData (s: istate) (len: Z) | SyncOk (s: istate) (len: Z).

(* inflateSync(strm) on a live stream offered the bytes inp (avail_in = |inp|) *)
Definition sync_s (s: istate) (inp: list Z) : sync_out :=
  if (Zlength inp =? 0) && (i_bits s <? 8) then SyncBuf else
  let s := if i_mode s =? SYNC then s else sync_start s in
  let '(got, len) := ssearch (i_have s) inp in
  let s := set_i_have s got in
  if negb (got =? 4) then SyncData s len else
  (* patch F6 (patch/PATCH.md): no header read yet -> raw, and a window size of 2^15 if none was set *)
  let s := if i_flags s =? -1 then
             (let s := set_i_wrap s 0 in if i_wbits s =? 0 then set_i_wbits s 15 else s)
           else set_i_wrap s (Z.land (i_wrap s) (Z.lnot 4)) in
  let fl := i_flags s in
  let s := reset_s s in
  SyncOk (set_i_mode (set_i_flags s fl) TYPE) len.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateSetDictionary: before the window update                                                *)

Inductive setdict_out := SDStream | SDData | SDUpdate.

Definition setdict_check (s: istate) (dict: list Z) : setdict_out :=
  if negb (i_wrap s =? 0) && negb (i_mode s =? DICT) then SDStream
  else if (i_mode s =? DICT) && negb (adler32_z_val 1 dict =? i_check s) then SDData
  else SDUpdate.

(* the state after a successful window update *)
Definition setdict_s (s: istate) (dict: list Z) : istate :=
  set_i_havedict (set_i_win (updatewindow s dict) true) 1.
