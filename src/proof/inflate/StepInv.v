(* The strengthened invariant in the form the case proofs use (mwf2 = mwf + xwf): the same facts as
   Inv2.v's mwf2, Inv.v's mwf plus:
   - the window: wbits = 0 only without a window (HEAD sets wbits when it is 0);
   - LENEXT: length <= 258, DISTEXT: offset <= 32768 (no u32 wrap of length / offset);
   - the decode modes: the length table's length entries give at most 258 (base + extra bits):
     inflate_fast copies a whole match into the >= 258 bytes of output space it checked. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.MwfLemmas.
Require Export Zlib.proof.inflate.Cover2Def.
Import ListNotations.
Local Open Scope Z_scope.

(* a length entry (op 16..21: base val, op - 16 extra bits) gives at most 258 *)
Definition len_ok (e: entry) : Prop := 16 <= e_op e <= 21 -> e_val e + 2 ^ (e_op e - 16) <= 259.

(* a valid length table (Tables.v tvalid LENS) whose entries are len_ok *)
Definition lvalid (fx dx: list entry) (s: istate) (t: tref) (rb: Z) : Prop :=
  exists sz, sz <= tab_size t /\ tvalid_b LENS fx dx s t rb sz /\
             forall i, 0 <= i < sz -> len_ok (tab_entry fx dx s t i).

Lemma lvalid_tvalid: forall fx dx s t rb, lvalid fx dx s t rb -> tvalid LENS fx dx s t rb.
Proof. intros fx dx s t rb (sz & A & B & _). exists sz; auto. Qed.

Record xwf (m: mst) : Prop := {
  xw_wbits : i_wbits (m_s m) = 0 -> i_wsize (m_s m) = 0;
  xw_lenext : m_mode m = LENEXT -> i_length (m_s m) <= 258;
  xw_distext : m_mode m = DISTEXT -> i_offset (m_s m) <= 32768;
  xw_lens : decode_mode (m_mode m) ->
            lvalid lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)) }.

Record mwf2 (m: mst) : Prop := { m2_w : mwf m; m2_x : xwf m }.

(* the covering fact for len_ok: the length tables inflate_table builds give at most 258 *)
Definition cover3_stmt : Prop :=
  forall lens req old root used t,
    inputs_ok LENS lens req -> cap_ok LENS lens req (Zlength old) -> Forall entry_ok old ->
    inflate_table_model LENS lens req old = ROk root used t ->
    forall i, 0 <= i < used -> len_ok (Znth i t).

(* the machine after one pass satisfies P *)
Definition iout_ok (P: mst -> Prop) (o: iout) : Prop :=
  match o with IBrk m => P m | IRet _ m => P m end.
