(* inflate()'s body against RTH8Spec.inflate_spec8 with an application header of any buffer sizes (RTH8Spec.hwf8).

   Spec5's machine invariant mwf (inflate/Inv.v) holds Spec5's header invariant hwf, which caps the header's buffer
   sizes at 65536; the stream of inflate_spec8 has hwf8 (any uInt sizes).  The parts of a call that do not read the
   header model (the modes after the header, and every mode when no header is attached: [hind]) run the same on the
   machine whose header model is replaced by the small [hcanon] (mcanon): the case lemmas with mwf3 are used on that
   machine and the run is transferred back ([sim_stmt]).  The header modes read the header, so their lemmas are
   stated with [mwf3_8]: mwf3 of the machine with the small header, and hwf8 of its own header ([cases8w_all],
   [hdr8_inv_stmt]).  hcanon keeps whether each buffer size is 0 (the zero-size buffers' malloc tokens, hdr_tok). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Import Zlib.proof.roundtrip.RTH8Spec.
Require Export Zlib.proof.roundtrip.RTH8Defs.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* the small header standing for the header model                                                 *)

Definition cz (n: Z) : Z := if n =? 0 then 0 else 1.

Definition hcanon (h: hstate) : hstate :=
  HS 0 0 0 0 false 0
     (cz (h_extra_max h)) (repeat 0 (Z.to_nat (cz (h_extra_max h))))
     false (cz (h_name_max h)) (repeat 0 (Z.to_nat (cz (h_name_max h))))
     false (cz (h_comm_max h)) (repeat 0 (Z.to_nat (cz (h_comm_max h))))
     0 0.

Definition mcanon (m: mst) : mst := set_m_h m (hcanon (m_h m)).

Definition lcanon (L: live) : live :=
  set_l_head L (hcanon (l_h L)) (l_headp L) (l_hsh L) (l_xb L) (l_nb L) (l_cb L).

(* the machine invariant with a header of any sizes *)
Definition mwf3_8 (m: mst) : Prop := mwf3 (mcanon m) /\ hwf8 (m_h m).

(* the parts of a run that do not read the header model: no header attached, or a mode after the header *)
Definition hind (m: mst) : Prop := i_head (m_s m) = false \/ hdr_mode (m_mode m) = false.

(* ---------------------------------------------------------------------------------------------- *)
(* the run does not read the header model where hind holds                                        *)

Definition out_h (o: iout) (h: hstate) : iout :=
  match o with IBrk m => IBrk (set_m_h m h) | IRet r m => IRet r (set_m_h m h) end.

Definition res_h (res: result) (h: hstate) : result :=
  Res (r_ret res) (set_m_h (r_m res) h) (r_dtype res).

(* one pass, the loop, the exit and the run from a machine with hind: with any other header model h the run
   is the same up to the header model, which the run keeps; hind is kept *)
Definition sim_stmt : Prop :=
  (forall flush m h, hind m ->
     match stepf2 flush lenfix_list distfix_list m with
     | IBrk m1 => stepf2 flush lenfix_list distfix_list (set_m_h m h) = IBrk (set_m_h m1 h) /\
                  m_h m1 = m_h m /\ hind m1
     | IRet r m1 => stepf2 flush lenfix_list distfix_list (set_m_h m h) = IRet r (set_m_h m1 h) /\
                    m_h m1 = m_h m /\ hind m1
     end) /\
  (forall flush m h o, hind m -> loop2 flush lenfix_list distfix_list m o ->
     loop2 flush lenfix_list distfix_list (set_m_h m h) (out_h o h) /\
     match o with IBrk m1 => m_h m1 = m_h m /\ hind m1 | IRet _ m1 => m_h m1 = m_h m /\ hind m1 end) /\
  (forall flush m h res, hind m -> inf_leave flush m res ->
     inf_leave flush (set_m_h m h) (res_h res h) /\ m_h (r_m res) = m_h m /\ hind (r_m res)) /\
  (forall flush m h res, hind m -> run2 flush lenfix_list distfix_list m res ->
     run2 flush lenfix_list distfix_list (set_m_h m h) (res_h res h) /\ m_h (r_m res) = m_h m).

(* ---------------------------------------------------------------------------------------------- *)
(* the header modes with a header of any sizes                                                     *)

(* one pass from a header mode keeps mwf3_8, the header's presence and sizes, the input and the loop's pure
   invariants (Body5Parts.stepf_inv5_stmt, stepf2_hdr_stmt for these machines) *)
Definition hdr8_inv_stmt : Prop :=
  forall flush m, mwf3_8 m -> m_leave m = 0 -> hdr_mode (m_mode m) = true -> out_inv m -> win_inv5 (m_s m) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => mwf3_8 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
               out_inv m' /\ i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  | IRet _ m' => mwf3_8 m' /\ hdr_same m m' /\ m_inp m' = m_inp m /\
                 i_win (m_s m') = i_win (m_s m) /\ win_inv5 (m_s m')
  end.

(* RTH8Defs.case_ok8 with mwf3_8 *)
Definition case_ok8w {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m n, m_mode m = Y -> m_leave m = 0 -> mwf3_8 m -> hd_ok F m -> i_head (m_s m) = true ->
    hpass8 (f_flush F) (S n) m ->
    semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post8 F m)) (fun _ => hdr_tok F m)).

Definition cases8w_all : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> forall i, (i <= 8)%nat ->
    case_ok8w F (IM.HEAD + Z.of_nat i) i.

(* ---------------------------------------------------------------------------------------------- *)
(* inflateGetHeader                                                                               *)

Definition gethdr8_stmt : Prop :=
  forall {Espec: OracleKind}, semax_body Vprog_inflate Gp_check f_inflateGetHeader inflateGetHeader_spec8.
