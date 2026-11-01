(* inflate()'s exit inf_leave, the store of data_type at the end of the tail, for calls of any uInt size
   (RTH9ExitEnd.v does the return code): the proof script of src/proof/hl/inflate_api/HlBody5ExitTail.v's
   et_end_ok_hl (copied by hand), cut after the store. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.hl.inflate_api.HlBody5Parts.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitKit.
Require Import Zlib.proof.hl.inflate_api.HlBody5ExitTail.
Require Import Zlib.proof.inflate_api.Body5ExitWin.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* the end of the tail (Body5ExitTail.et_end): the store of strm->data_type, then the return code and return *)
Definition et_dt : statement := match et_end with Ssequence d _ => d | _ => Sskip end.
Definition et_rc : statement := match et_end with Ssequence _ r => r | _ => Sskip end.

Lemma et_end_eq9: et_end = Ssequence et_dt et_rc.
Proof. reflexivity. Qed.

Lemma et_dt_ok9 {Espec: OracleKind} (F: frame) (X: mpred) (m0 m2: mst) (inn o: Z):
  frame_ok5 F -> i_bits (m_s m2) = m_bits m2 -> 0 <= m_bits m2 <= 39 -> 0 <= i_last (m_s m2) <= 1 ->
  HEAD <= i_mode (m_s m2) <= SYNC ->
  semax Delta_inflate5_hl (tst_hl F X m0 m2 inn o) et_dt
    (normal_ret_assert (tst_hl (set_f_winp_dt F (f_winp F) (lt_dt m2)) X m0 m2 inn o)).
Proof.
  intros FOK HB RB RL RM.
  unfold HEAD, SYNC in RM.
  pose proof FOK as ((HWS & HWH & HRG & HRT) & HFL).
  cbv beta iota zeta delta [et_dt et_end ex_tail inflate_exit f_inflate fn_body].
  unfold tst_hl, strm_e, strm_rep.
  abbreviate_semax. Intros.
  remember (f_gv F _zcalloc) as zca eqn:Hzca. remember (f_gv F _zcfree) as zcf eqn:Hzcf.
  forward.
  forward_if (temp _t'104 (Vint (Int.repr (if i_last (m_s m2) =? 0 then 0 else 64)))).
  { forward. entailer!. zfix. }
  { forward. entailer!. zfix. }
  forward.
  forward_if (temp _t'105 (Vint (Int.repr (if i_mode (m_s m2) =? Zlib.proof.inflate.Model.TYPE then 128 else 0)))).
  { forward. entailer!. zfix. }
  { forward. entailer!. zfix. }
  forward.
  forward_if (temp _t'106 (Vint (Int.repr (if ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool then 1 else 0)))).
  { forward. entailer!. zfix. }
  { forward. forward. entailer!. zfix.
    destruct (zeq (i_mode (m_s m2)) 16194) as [E|E];
      [rewrite E; reflexivity | rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity]. }
  forward_if (temp _t'107 (Vint (Int.repr (if ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool then 256 else 0)))).
  { forward. entailer!. bcase. }
  { forward. entailer!. bcase. }
  forward. forward.
  { entailer!.
    destruct (i_last (m_s m2) =? 0), (i_mode (m_s m2) =? Zlib.proof.inflate.Model.TYPE),
      ((i_mode (m_s m2) =? LEN_) || (i_mode (m_s m2) =? COPY_))%bool;
      rewrite !Int.signed_repr by rep_lia; rep_lia. }
  rewrite mem_rep_e_dt_hl, locals_rep_winp, hdr_tok_winp by reflexivity.
  unfold set_f_winp_dt, lt_dt.
  cbn [f_gv f_shs f_strmp f_sp f_ib f_ob f_tsh f_dt f_vres f_flush f_vhere f_vlast f_vhbuf].
  rewrite !add_repr, <- HB, <- Hzca, <- Hzcf.
  entailer!.
Qed.
