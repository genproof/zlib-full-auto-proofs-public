(* The header world of inflate()'s body against RTH9Spec.inflate_spec9: the header cases HEAD .. HCRC for calls
   of any uInt size that may return in a header mode or leave the header modes without passing the header.

   As in round 1 (RTH8Defs, RTH8W), the header is held next to the headless loop state RTHLoop.loop_stateH, and
   the machine invariant is that of the machine with the small header RTH8W.mcanon, here the WIDE InvW.mwf3W
   ([mwf3_9]: avail_in / avail_out up to 2^32 - 1), with RTH8Spec.hwf8 of the real header (buffers of any uInt
   size).  The header of a machine ([hd9], RTH9Spec.head_mem9 as a function of the machine):
   - in a header mode the partial RTHSpec.head_rep6 (RTHCase.hd6), the bytes copied so far: a call may now
     return there (NEEDBITS or a copy loop runs out of input);
   - past the header ([hd9a]) RTH8Spec.head_rep8a once the header is passed (HCRC writes done = 1), or, when the
     header modes were left without passing the header (an error in FLAGS or HCRC: mode BAD with done = 0; a
     zlib stream on an auto-detecting stream: HEAD writes done = -1), RTHSpec.hraw6 with done <> 1: only the
     pointer and size fields are known.
   [cases9h_all]: every header case, from a header machine with the partial header, ends (RA_normal: break of the
   switch, with leave = 0 or 1) in the machine of one pass of the model with its header [hd9]. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.roundtrip.RTH9Spec.
Require Export Zlib.proof.roundtrip.RTH8W.
Require Export Zlib.proof.roundtrip.RTH9Parts.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the header of a machine                                                                        *)

(* past the header modes: passed (head_rep8a), or left without passing the header (done <> 1, any contents) *)
Definition hd9a (F: frame) (m: mst) : mpred :=
  hd8a F m || !! (h_done (m_h m) <> 1) && hraw6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_h m).

Definition hd9 (F: frame) (m: mst) : mpred :=
  if hdr_mode (m_mode m) then hd6 F m else hd9a F m.

(* the wide machine invariant of the machine with the small header, and the real header's sizes any uInt *)
Definition mwf3_9 (m: mst) : Prop := mwf3W (mcanon m) /\ hwf8 (m_h m).

(* ---------------------------------------------------------------------------------------------- *)
(* the header cases                                                                               *)

Definition post9 (F: frame) (m: mst) : environ -> mpred :=
  loop_stateH F m * (fun _ => hd9 F m).

Definition case_post9 (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && post9 F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun _ _ => FF |}.

(* the lemma of header case i (mode Y) with the header attached *)
Definition case_ok9h {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m, m_mode m = Y -> m_leave m = 0 -> mwf3_9 m -> hd_ok F m -> i_head (m_s m) = true ->
    semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post9 F m)) (fun _ => hdr_tok F m)).

(* every header case: the switch's labels 0 .. 8 *)
Definition cases9h_all : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> forall i, (i <= 8)%nat ->
    case_ok9h F (IM.HEAD + Z.of_nat i) i.
