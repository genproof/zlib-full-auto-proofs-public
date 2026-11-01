(* The statements of the parts of one pass of the switch: each case function c_X of Model.v (with the
   fixed tables and inflate_fast's model) preserves mwf3x (ICStep3Inv.v), for a machine in mode X with
   leave = 0.  Proved in ICStep3Fast.v (fast_stmt), ICStep3Decode.v (LEN_ .. LIT), ICStep3Tables.v (TABLE,
   LENLENS, CODELENS), ICStep3Header.v (HEAD .. DICT), ICStep3Block.v (TYPE .. COPY, CHECK .. BAD).  A part
   that falls through into a case of another file takes that case's statement as a hypothesis. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.harness.inflate_codes.ICStep3Kit.
Local Open Scope Z_scope.

Definition ok_at (md: Z) (f: mst -> iout) : Prop :=
  forall m, mwf3x m -> m_leave m = 0 -> m_mode m = md -> iout_ok mwf3x (f m).

(* LEN's fast path: inflate_fast and the `if (state->mode == TYPE) state->back = -1;` after it *)
Definition fast_stmt : Prop :=
  forall m, mwf3x m -> m_leave m = 0 -> m_mode m = LEN ->
    6 <= m_have m -> 258 <= m_left m -> m_bits m < 8 ->
    mwf3x (let m := fast lenfix_list distfix_list (restore m) in
          if m_mode m =? TYPE then upd_s m (fun s => set_i_back s (-1)) else m).

Definition ok_MATCH : Prop := ok_at MATCH c_MATCH.
Definition ok_DISTEXT : Prop := ok_at DISTEXT c_DISTEXT.
Definition ok_DIST : Prop := ok_at DIST (c_DIST lenfix_list distfix_list).
Definition ok_LENEXT : Prop := ok_at LENEXT (c_LENEXT lenfix_list distfix_list).
Definition ok_LIT : Prop := ok_at LIT c_LIT.
Definition ok_LEN : Prop := ok_at LEN (c_LEN lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_LEN_ : Prop := ok_at LEN_ (c_LEN_ lenfix_list distfix_list (fast lenfix_list distfix_list)).

Definition ok_CODELENS : Prop :=
  forall flush, ok_at CODELENS (c_CODELENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_LENLENS : Prop :=
  forall flush, ok_at LENLENS (c_LENLENS flush lenfix_list distfix_list (fast lenfix_list distfix_list)).
Definition ok_TABLE : Prop :=
  forall flush, ok_at TABLE (c_TABLE flush lenfix_list distfix_list (fast lenfix_list distfix_list)).

(* c_TYPE falls into c_TYPEDO without setting the mode *)
Definition ok_TYPEDO : Prop :=
  forall flush m, mwf3x m -> m_leave m = 0 -> (m_mode m = TYPE \/ m_mode m = TYPEDO) ->
    iout_ok mwf3x (c_TYPEDO flush m).
Definition ok_TYPE : Prop := forall flush, ok_at TYPE (c_TYPE flush).
Definition ok_STORED : Prop := forall flush, ok_at STORED (c_STORED flush).
Definition ok_COPY_ : Prop := ok_at COPY_ c_COPY_.
Definition ok_COPY : Prop := ok_at COPY c_COPY.
Definition ok_CHECK : Prop := ok_at CHECK c_CHECK.
Definition ok_LENGTH : Prop := ok_at LENGTH c_LENGTH.
Definition ok_DONE : Prop := ok_at DONE c_DONE.
Definition ok_BAD : Prop := ok_at BAD c_BAD.

Definition ok_HEAD : Prop := ok_at HEAD c_HEAD.
Definition ok_FLAGS : Prop := ok_at FLAGS c_FLAGS.
Definition ok_TIME : Prop := ok_at TIME c_TIME.
Definition ok_OS : Prop := ok_at OS c_OS.
Definition ok_EXLEN : Prop := ok_at EXLEN c_EXLEN.
Definition ok_EXTRA : Prop := ok_at EXTRA c_EXTRA.
Definition ok_NAME : Prop := ok_at NAME c_NAME.
Definition ok_COMMENT : Prop := ok_at COMMENT c_COMMENT.
Definition ok_HCRC : Prop := ok_at HCRC c_HCRC.
Definition ok_DICTID : Prop := forall flush, ok_at DICTID (c_DICTID flush).
Definition ok_DICT : Prop := forall flush, ok_at DICT (c_DICT flush).
