(* The invariant of the inflate machine for inputs and output spaces of up to 2^32-1 bytes.

   Inv.v's mwf bounds the input of a call (|m_inp|) and its output space (m_aout) by 2^31-1, and so does
   Spec5's inflate_spec (avail_in, avail_out <= Int.max_signed).  zlib's avail_in and avail_out are uInt,
   and the clients of the short laws offer up to UINT_MAX bytes per call; inflate.c and inffast.c hold
   these sizes in unsigned variables.  mwfW is mwf with these two bounds raised to Int.max_unsigned
   (every other field as in mwf); mwf3W adds Inv3.v's swf3 as mwf3 does, and hdrW.

   hdrW is what the wider input needs in the gzip header's extra field (case EXTRA): the copy into the
   application's extra buffer tests `len + copy > extra_max` in 32 bits, with copy <= the remaining extra
   length; with an input of up to 2^32-1 bytes the sum would wrap if that length could be near 2^32.  EXLEN
   reads it from 16 bits of the bit buffer, so it stays small, provided the bit buffer holds only its bits
   (hold < 2^bits) when EXLEN starts: hdrW records both facts (swfW: the same for the saved state).  The
   length matters only when the header has an extra field (flag 0x0400): without it EXLEN leaves the length
   as it was (any value: the state comes from the caller's allocator) and falls through EXTRA, which then
   does not read it. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.inflate.Inv3.
Require Import Zlib.proof.inflate.CaseHyps5.
Import ListNotations.
Local Open Scope Z_scope.

Record mwfW (m: mst) : Prop := {
  mwW_md : modewf (m_s m);
  mwW_s : swf (m_s m);
  mwW_h : hwf (m_h m);
  mwW_inp : Zlength (m_inp m) <= Int.max_unsigned /\ bytes_ok (m_inp m);
  mwW_aout : 0 <= m_aout m <= Int.max_unsigned;
  mwW_nx : 0 <= m_nx m <= Zlength (m_inp m);
  mwW_ow : Zlength (m_ow m) <= m_aout m /\ bytes_ok (m_ow m);
  mwW_hold : lrange (m_hold m);
  mwW_bits : 0 <= m_bits m <= 39;
  mwW_in : m_in m = Zlength (m_inp m);
  mwW_out : urange (m_out m);
  mwW_ret : -5 <= m_ret m <= 2;
  mwW_leave : 0 <= m_leave m <= 1;
  mwW_adler : lrange (m_adler m);
  mwW_tin : lrange (m_tin m);
  mwW_tout : lrange (m_tout m);
  mwW_snx : 0 <= m_snx m <= Zlength (m_inp m);
  mwW_sow : 0 <= m_sow m <= Zlength (m_ow m);
  mwW_outeq : m_out m = m_aout m \/ m_mode m = LENGTH \/ m_mode m = DONE \/ m_mode m = BAD }.

(* the extra field's length (EXTRA) and the bit buffer before it is read (EXLEN) *)
Definition hdrW (m: mst) : Prop :=
  (m_mode m = EXLEN -> m_bits m < 16 /\ m_hold m < 2 ^ m_bits m) /\
  (m_mode m = EXTRA -> Z.land (i_flags (m_s m)) 1024 <> 0 -> i_length (m_s m) <= Int.max_signed).

(* the same for a saved state (strm->state between calls) *)
Definition swfW (s: istate) : Prop :=
  (i_mode s = EXLEN -> i_bits s < 16 /\ i_hold s < 2 ^ i_bits s) /\
  (i_mode s = EXTRA -> Z.land (i_flags s) 1024 <> 0 -> i_length s <= Int.max_signed).

Definition mwf3W (m: mst) : Prop := mwfW m /\ swf3 (m_s m) /\ hdrW m.

(* the narrow invariant is a special case *)
Lemma mwf_mwfW: forall m, mwf m -> mwfW m.
Proof.
  intros m W.
  assert (Int.max_signed <= Int.max_unsigned) by (cbv; discriminate).
  destruct (mw_inp m W). pose proof (mw_aout m W).
  constructor; try apply W; try split; auto; lia.
Qed.

Lemma mwf3_mwf3W: forall m, mwf3 m -> hdrW m -> mwf3W m.
Proof. intros m [W S] H. split; [apply mwf_mwfW; exact W | split; [exact S | exact H]]. Qed.

(* one pass of the switch (Model2.v) preserves mwf3W: CaseHyps5's stepf2_mwf3_stmt for wide machines *)
Definition stepf2_mwf3W_stmt : Prop :=
  forall flush m, mwf3W m -> m_leave m = 0 ->
  match stepf2 flush lenfix_list distfix_list m with IBrk m' => mwf3W m' | IRet _ m' => mwf3W m' end.
