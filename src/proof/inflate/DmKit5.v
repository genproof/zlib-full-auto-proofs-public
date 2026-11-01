(* The cases DISTEXT (23) and MATCH (24) of inflate()'s switch (Cases5_DM.v), cut into parts:
   - DISTEXT: the Clight cut into its statements (dx_nb: NEEDBITS(state->extra), a loop that re-reads its bound
     state->extra; dx_rest: offset += BITS(extra), DROPBITS(extra), back += extra; dx_fin: mode = MATCH);
   - MATCH: the Clight cut into its statements (mt_lz: if (left == 0) { leave = 1; break; };
     mt_copy0: copy = out - left; mt_sel: where the bytes come from (window, with the BAD block, or output);
     mt_cl: if (copy > left) copy = left; mt_left: left -= copy; mt_len: length -= copy;
     mt_loop: do { *put++ = *from++; } while (--copy); mt_end: if (length == 0) mode = LEN; break;)
   - the statements of the parts (dx_*_stmt, mt_*_stmt), proved in Dx<Part>5.v / Mt<Part>5.v. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseHyps5.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight of DISTEXT                                                                          *)

Definition dx_body : statement := case_body 23.
(* if (state->extra) { NEEDBITS(state->extra); offset += BITS(extra); DROPBITS(extra); back += extra; } *)
Definition dx_head : statement := match dx_body with Ssequence h _ => h | _ => Sskip end.
(* state->mode = MATCH; *)
Definition dx_fin : statement := match dx_body with Ssequence _ f => f | _ => Sskip end.
Definition dx_ext : statement :=
  match dx_head with Ssequence _ (Sifthenelse _ e _) => e | _ => Sskip end.
(* NEEDBITS(state->extra): for (;;) { if (!(bits < state->extra)) break; PULLBYTE(); } *)
Definition dx_nb : statement := match dx_ext with Ssequence (Ssequence nb _) _ => nb | _ => Sskip end.
(* state->offset += BITS(state->extra); DROPBITS(state->extra); state->back += state->extra; *)
Definition dx_rest : statement := match dx_ext with Ssequence _ r => r | _ => Sskip end.

Definition dm_ifleave : statement := Sifthenelse (Etempvar _leave tint) Sbreak Sskip.

Lemma dx_body_eq: dx_body =
  Ssequence
    (Ssequence
       (Sset _t'166 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                               (Tstruct _inflate_state noattr)) _extra tuint))
       (Sifthenelse (Etempvar _t'166 tuint) (Ssequence (Ssequence dx_nb dm_ifleave) dx_rest) Sskip))
    dx_fin.
Proof. reflexivity. Qed.

Lemma dx_fin_eq: dx_fin =
  Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                     (Tstruct _inflate_state noattr)) _mode tint)
    (Econst_int (Int.repr 16204) tint).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the Clight of MATCH                                                                            *)

Definition mt_body : statement := case_body 24.
(* if (left == 0) { leave = 1; break; } *)
Definition mt_lz : statement := match mt_body with Ssequence a _ => a | _ => Sskip end.
Definition mt_r1 : statement := match mt_body with Ssequence _ r => r | _ => Sskip end.
(* copy = out - left; *)
Definition mt_copy0 : statement := match mt_r1 with Ssequence a _ => a | _ => Sskip end.
Definition mt_r2 : statement := match mt_r1 with Ssequence _ r => r | _ => Sskip end.
(* if (state->offset > copy) { window: copy, BAD, from, min length } else { from = put - offset; copy = length } *)
Definition mt_sel : statement := match mt_r2 with Ssequence a _ => a | _ => Sskip end.
Definition mt_r3 : statement := match mt_r2 with Ssequence _ r => r | _ => Sskip end.
(* if (copy > left) copy = left; *)
Definition mt_cl : statement := match mt_r3 with Ssequence a _ => a | _ => Sskip end.
Definition mt_r4 : statement := match mt_r3 with Ssequence _ r => r | _ => Sskip end.
(* left -= copy; *)
Definition mt_left : statement := match mt_r4 with Ssequence a _ => a | _ => Sskip end.
Definition mt_r5 : statement := match mt_r4 with Ssequence _ r => r | _ => Sskip end.
(* state->length -= copy; *)
Definition mt_len : statement := match mt_r5 with Ssequence a _ => a | _ => Sskip end.
Definition mt_r6 : statement := match mt_r5 with Ssequence _ r => r | _ => Sskip end.
(* do { *put++ = *from++; } while (--copy); *)
Definition mt_loop : statement := match mt_r6 with Ssequence a _ => a | _ => Sskip end.
(* if (state->length == 0) state->mode = LEN; break; *)
Definition mt_end : statement := match mt_r6 with Ssequence _ r => r | _ => Sskip end.

Lemma mt_body_eq: mt_body =
  Ssequence mt_lz (Ssequence mt_copy0 (Ssequence mt_sel (Ssequence mt_cl (Ssequence mt_left
    (Ssequence mt_len (Ssequence mt_loop mt_end)))))).
Proof. reflexivity. Qed.

Lemma mt_lz_eq: mt_lz =
  Sifthenelse (Ebinop Oeq (Etempvar _left tuint) (Econst_int (Int.repr 0) tint) tint)
    (Ssequence (Sset _leave (Econst_int (Int.repr 1) tint)) Sbreak) Sskip.
Proof. reflexivity. Qed.

Lemma mt_copy0_eq: mt_copy0 = Sset _copy (Ebinop Osub (Etempvar _out tuint) (Etempvar _left tuint) tuint).
Proof. reflexivity. Qed.

Lemma mt_cl_eq: mt_cl =
  Sifthenelse (Ebinop Ogt (Etempvar _copy tuint) (Etempvar _left tuint) tint) (Sset _copy (Etempvar _left tuint))
    Sskip.
Proof. reflexivity. Qed.

Lemma mt_left_eq: mt_left = Sset _left (Ebinop Osub (Etempvar _left tuint) (Etempvar _copy tuint) tuint).
Proof. reflexivity. Qed.

Lemma mt_loop_eq: mt_loop =
  Sloop
    (Ssequence
       (Ssequence
          (Ssequence
             (Ssequence (Sset _t'82 (Etempvar _put (tptr tuchar)))
                (Sset _put (Ebinop Oadd (Etempvar _t'82 (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))))
             (Sset _t'83 (Etempvar _from (tptr tuchar))))
          (Sset _from (Ebinop Oadd (Etempvar _t'83 (tptr tuchar)) (Econst_int (Int.repr 1) tint) (tptr tuchar))))
       (Ssequence
          (Sset _t'152 (Ederef (Etempvar _t'83 (tptr tuchar)) tuchar))
          (Sassign (Ederef (Etempvar _t'82 (tptr tuchar)) tuchar) (Etempvar _t'152 tuchar))))
    (Ssequence
       (Ssequence
          (Sset _t'81 (Ecast (Ebinop Osub (Etempvar _copy tuint) (Econst_int (Int.repr 1) tint) tuint) tuint))
          (Sset _copy (Etempvar _t'81 tuint)))
       (Sifthenelse (Etempvar _t'81 tuint) Sskip Sbreak)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the parts                                                                    *)

(* DISTEXT: NEEDBITS(state->extra) (DxNb5.v) *)
Definition dx_nb_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame) (m: mst),
  mwf m -> m_mode m = DISTEXT -> m_leave m = 0 ->
  semax Delta_cases5 (loop_state F m) dx_nb
    (normal_ret_assert (loop_state F (needbits (i_extra (m_s m)) m))).

(* DISTEXT: the whole case, from its NEEDBITS (DxCase5.v) *)
Definition dx_case_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok5 F MATCH 24 -> case_ok5 F DISTEXT 23.

(* the output object with the bytes ow written at lo *)
Definition mt_out (osh: share) (op: val) (olo on: Z) (oc: list val) (ow: list Z) : mpred :=
  data_at osh (tarray tuchar on) (sublist 0 olo oc ++ byte_vals ow ++ sublist (olo + Zlength ow) on oc) op.

(* MATCH: the copy loop, the bytes from the window (MtLoopW5.v): copy c >= 1 bytes from window[i ..] *)
Definition mt_loop_w_stmt : Prop :=
  forall {Espec: OracleKind} (osh: share) (op: val) (olo on: Z) (oc: list val) (ow: list Z)
    (winp: val) (wn: Z) (w: list Z) (i c: Z),
  writable_share osh -> isptr op -> 0 <= olo -> olo + Zlength ow + c <= on -> Zlength oc = on ->
  on <= Ptrofs.max_unsigned -> bytes_ok ow ->
  isptr winp -> Zlength w <= wn -> wn <= Ptrofs.max_unsigned -> bytes_ok w ->
  1 <= c <= Int.max_unsigned -> 0 <= i -> i + c <= Zlength w ->
  semax Delta_cases5
    (PROP () LOCAL (temp _put (offset_val (olo + Zlength ow) op); temp _from (offset_val i winp);
                    temp _copy (Vint (Int.repr c)))
     SEP (mt_out osh op olo on oc ow;
          data_at Ews (tarray tuchar wn) (byte_vals w ++ Zrepeat Vundef (wn - Zlength w)) winp))
    mt_loop
    (normal_ret_assert
      (PROP () LOCAL (temp _put (offset_val (olo + Zlength (fst (copy_bytes w (SWin i) c ow))) op))
       SEP (mt_out osh op olo on oc (fst (copy_bytes w (SWin i) c ow));
            data_at Ews (tarray tuchar wn) (byte_vals w ++ Zrepeat Vundef (wn - Zlength w)) winp))).

(* MATCH: the copy loop, the bytes from the output itself, d bytes back (MtLoopO5.v) *)
Definition mt_loop_o_stmt : Prop :=
  forall {Espec: OracleKind} (osh: share) (op: val) (olo on: Z) (oc: list val) (ow: list Z)
    (w: list Z) (d c: Z),
  writable_share osh -> isptr op -> 0 <= olo -> olo + Zlength ow + c <= on -> Zlength oc = on ->
  on <= Ptrofs.max_unsigned -> bytes_ok ow ->
  1 <= c <= Int.max_unsigned -> 1 <= d <= Zlength ow ->
  semax Delta_cases5
    (PROP () LOCAL (temp _put (offset_val (olo + Zlength ow) op);
                    temp _from (offset_val (olo + Zlength ow - d) op);
                    temp _copy (Vint (Int.repr c)))
     SEP (mt_out osh op olo on oc ow))
    mt_loop
    (normal_ret_assert
      (PROP () LOCAL (temp _put (offset_val (olo + Zlength (fst (copy_bytes w (SOut (Zlength ow - d)) c ow))) op))
       SEP (mt_out osh op olo on oc (fst (copy_bytes w (SOut (Zlength ow - d)) c ow))))).
