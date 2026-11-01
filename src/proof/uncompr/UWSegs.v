(* uncompress2_z's body for any sizes (USpecW.uncompress2_z_spec_w), cut into segments proved in separate files.

   The body is a chain of statements; uw_seg k is its suffix from the k-th statement (0-based):
     0  max = (uInt)-1;  the argument checks              (UWSegP1.v: up to 5)
     2  len = *sourceLen;  3  left = *destLen;
     4  if (left == 0 && dest == Z_NULL) dest = &stream.reserved;
     5  the stores into stream (next_in, avail_in, zalloc, zfree, opaque)   (UWSegP2.v: up to 10)
     10 err = inflateInit(&stream); if (err != Z_OK) return err;
     12 stream.next_out = dest; stream.avail_out = 0;     (UWSegP3.v: up to the loop invariant at 14)
     14 the do-while loop of inflate() calls               (UWSegLoop.v; its body: UWSegROut.v, UWSegRIn.v,
                                                            UWSegCall.v)
     15 the counters, *sourceLen, *destLen, inflateEnd and the return value   (UWSegExit.v)
   Each segment is stated in continuation style: from its precondition the rest of the body reaches the
   function's postcondition, given that the rest from the next cut does.  The loop body (no return, no break)
   is stated with its normal postcondition.

   Both cases of the destination are handled at once: the destination pointer of the code after statement 4 is
   [uw_dq dnull dp v] (dp, or the stream's member `reserved` at offset 104 when dest = Z_NULL), the output object
   of each inflate() call is [uw_ob] (USpecW.dest_ok_w: an object of dn bytes, or the empty object at that member,
   SpecWSelf.self_out).

   The loop's assertions follow UModelW.uncw_loop: before each call the stream holds (m, used, out) as the last
   call left it, with ai / ao its avail_in / avail_out and len = |src| - used - ai, left = cap - |out| - ao the
   code's counters; reach_w (UWKit.v) says that the loop from there is a continuation of the loop from the
   start. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Uncompr Zlib.units.Inflate.
Require Import Zlib.uncompr.code.
Require Export Zlib.proof.uncompr.USpecW.
Require Export Zlib.proof.inflate_api.SpecWSelf.
Require Export Zlib.proof.uncompr.UBodies5.
Require Export Zlib.proof.uncompr.UWKit.
Require Export Zlib.proof.uncompr.URunFrame.
Require Export Zlib.proof.uncompr.URunRet.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Uncompr.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* The segments of the body                                                                      *)

Fixpoint uw_drop (n: nat) (s: statement) : statement :=
  match n, s with
  | O, _ => s
  | S n', Ssequence _ b => uw_drop n' b
  | _, _ => Sskip
  end.

Ltac uw_get_seg k :=
  let x := eval cbv beta iota zeta delta [uw_drop f_uncompress2_z fn_body] in
    (uw_drop k (fn_body f_uncompress2_z)) in
  exact x.

Definition uw_seg0 : statement := ltac:(uw_get_seg 0%nat).
Definition uw_seg5 : statement := ltac:(uw_get_seg 5%nat).
Definition uw_seg10 : statement := ltac:(uw_get_seg 10%nat).
Definition uw_seg14 : statement := ltac:(uw_get_seg 14%nat).
Definition uw_seg15 : statement := ltac:(uw_get_seg 15%nat).

Lemma uw_seg0_eq : fn_body f_uncompress2_z = uw_seg0.
Proof. reflexivity. Qed.

(* the loop's body: avail_out's refill, avail_in's refill, the call; and its test *)
Ltac uw_get_loop f :=
  let x := eval cbv beta iota zeta delta [uw_seg14] in
    (match uw_seg14 with Ssequence (Sloop b i) _ => f b i | _ => Sskip end) in
  exact x.

Definition uw_rout : statement :=
  ltac:(uw_get_loop (fun (b i: statement) => match b with Ssequence r _ => r | _ => Sskip end)).
Definition uw_rin : statement :=
  ltac:(uw_get_loop (fun (b i: statement) => match b with Ssequence _ (Ssequence r _) => r | _ => Sskip end)).
Definition uw_call_st : statement :=
  ltac:(uw_get_loop (fun (b i: statement) => match b with Ssequence _ (Ssequence _ c) => c | _ => Sskip end)).
Definition uw_test : statement := ltac:(uw_get_loop (fun (b i: statement) => i)).

Lemma uw_seg14_eq : uw_seg14 = Ssequence (Sloop (Ssequence uw_rout (Ssequence uw_rin uw_call_st)) uw_test) uw_seg15.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The arguments                                                                                 *)

(* the WITH of uncompress2_z_spec_w *)
Record uwargs := UWA {
  a_gv: globals; a_dnull: bool; a_dsh: share; a_dp: val; a_dn: Z; a_dc: list val; a_cap: Z; a_dlp: val;
  a_dtok: bool; a_stok: bool; a_ssh: share; a_sp: val; a_sn: Z; a_sc: list val; a_src: list Z; a_slp: val;
  a_gsh: share; a_tsh: share }.

(* its PROP *)
Definition uw_facts (A: uwargs) : Prop :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
    dest_ok_w dnull dsh dp dn dc cap dtok /\
    readable_share ssh /\ isptr sp /\ (stok = false -> 0 < sn) /\ Zlength src <= sn /\ Zlength sc = sn /\
    sn <= Ptrofs.max_unsigned /\ sublist 0 (Zlength src) sc = byte_vals src /\ bytes_ok src /\
    readable_share gsh /\ readable_share tsh
  end.

Definition Delta_uw : tycontext := func_tycontext f_uncompress2_z Vprog_uncompr5 Gp_uncompress2_z_w nil.

(* the postcondition of the body after start_function *)
Definition POST_uw (A: uwargs) : ret_assert :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  frame_ret_assert
    (function_body_ret_assert tint
       (EX r: Z, EX slen: Z, EX dlen: Z, EX out: list Z,
        PROP (uncompressw_rel src cap r slen dlen out)
        RETURN (Vint (Int.repr r))
        SEP (dest_rep dnull dsh dp dn (dest_after dc dn out) dtok;
             data_at Tsh tulong (Vlong (Int64.repr dlen)) dlp;
             data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
             data_at Tsh tulong (Vlong (Int64.repr slen)) slp;
             uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv))%argsassert)
    (stackframe_of f_uncompress2_z)
  end.

(* the precondition of the body after start_function (v: the address of the local stream) *)
Definition PRE_uw (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  PROP ()
  LOCAL (lvar _stream (Tstruct _z_stream_s noattr) v; gvars gv; temp _dest dp; temp _destLen dlp;
         temp _source sp; temp _sourceLen slp)
  SEP (data_at_ Tsh (Tstruct _z_stream_s noattr) v; dest_rep dnull dsh dp dn dc dtok;
       data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
       data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
       data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
       uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv)
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The destination                                                                               *)

(* the code's dest after statement 4 *)
Definition uw_dq (dnull: bool) (dp v: val) : val := if dnull then offset_val 104 v else dp.

(* the output object of the calls, with out written: the destination object, or the empty object at the
   stream's member `reserved` (no token) *)
Definition uw_ob (dnull: bool) (dsh: share) (dp v: val) (dn: Z) (dc: list val) (out: list Z) : outbuf :=
  if dnull then OutBuf Tsh (offset_val 104 v) (Zlength out) dn (dest_after dc dn out)
  else OutBuf dsh dp (Zlength out) dn (dest_after dc dn out).
Definition uw_otok (dnull dtok: bool) : bool := if dnull then false else dtok.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertions                                                                                *)

(* "1.3.2", the version literal of uncompr.c *)
Definition uw_lit (gv: globals) : mpred :=
  data_at Ers (tarray tschar 6)
    [Vint (Int.repr 49); Vint (Int.repr 46); Vint (Int.repr 51); Vint (Int.repr 46);
     Vint (Int.repr 50); Vint (Int.repr 0)] (gv ___stringlit_uncompr_1).

(* the locals that do not change after statement 4 *)
Definition uw_lcl (A: uwargs) (v: val) : list localdef :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  [temp _max (Vint (Int.neg (Int.repr 1))); lvar _stream (Tstruct _z_stream_s noattr) v; gvars gv;
   temp _dest (uw_dq dnull dp v); temp _destLen dlp; temp _source sp; temp _sourceLen slp]
  end.

(* the resources that the loop does not touch (the counters *destLen, *sourceLen, the source, the globals) *)
Definition uw_fr (A: uwargs) : list mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  [uw_lit gv; version_lit gv; mem_mgr gv; zfuncs gv;
   data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
   data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
   data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
   tables_rep gsh gv; crc_table_at tsh gv]
  end.

(* before statement 5: len and left read, dest fixed *)
Definition uw_A5 (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  PROPx []
  (LOCALx (temp _len (Vlong (Int64.repr (Zlength src))) :: temp _left (Vlong (Int64.repr cap)) :: uw_lcl A v)
  (SEPx [data_at_ Tsh (Tstruct _z_stream_s noattr) v; dest_rep dnull dsh dp dn dc dtok;
         data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv]))
  end.

(* before statement 10 (inflateInit): next_in = source, avail_in = 0, zalloc = zfree = opaque = 0 *)
Definition uw_A10 (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  PROPx []
  (LOCALx (temp _len (Vlong (Int64.repr (Zlength src))) :: temp _left (Vlong (Int64.repr cap)) :: uw_lcl A v)
  (SEPx [raw_strm gv Tsh v (RF sp (Vint (Int.repr 0)) Vundef Vundef Vundef Vundef Vundef Vundef Vundef)
           Vundef Vundef nullval nullval nullval;
         dest_rep dnull dsh dp dn dc dtok;
         data_at Tsh tulong (Vlong (Int64.repr cap)) dlp;
         data_at ssh (tarray tuchar sn) sc sp; if stok then malloc_token Ews (tarray tuchar sn) sp else emp;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength src))) slp;
         uversion_lit gv; inflate_globals gsh tsh gv; mem_mgr gv]))
  end.

(* the facts of the loop's stream (m, used, out) in z and L, ai / ao the avail_in / avail_out of the last call *)
Definition uw_sfacts (A: uwargs) (v: val) (m: mst) (used: Z) (out: list Z) (z: zfields) (L: live)
    (ai ao: Z) : Prop :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  i_head (m_s m) = false /\ l_s L = m_s m /\ l_h L = m_h m /\ zf_adler z = m_adler m /\ zf_msg z = m_msg m /\
  zf_tin z = m_tin m /\ zf_tout z = m_tout m /\
  zf_ni z = offset_val used sp /\ zf_no z = offset_val (Zlength out) (uw_dq dnull dp v) /\
  0 <= used /\ used + ai <= Zlength src /\ 0 <= ai <= uw_max /\ 0 <= ao <= uw_max /\ Zlength out + ao <= cap /\
  raw_live (Some L) = false /\ swfW (l_s L)
  end.

(* the stream and the destination with out written *)
Definition uw_sep (A: uwargs) (v: val) (out: list Z) (z: zfields) (L: live) : list mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  istream gv Tsh v z (Some L) :: dest_rep dnull dsh dp dn (dest_after dc dn out) dtok :: uw_fr A
  end.

(* the loop invariant (before avail_out's refill) *)
Definition uw_inv (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROPx [reach_w src cap m used out ai ao; vmode (i_mode (m_s m)); uw_sfacts A v m used out z L ai ao;
         zf_ai z = ai; zf_ao z = ao]
  (LOCALx (temp _len (Vlong (Int64.repr (Zlength src - used - ai))) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: uw_lcl A v)
  (SEPx (uw_sep A v out z L)))
  end.

(* after avail_out's refill: avail_out is the next call's offer uw_aout *)
Definition uw_M1 (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROPx [reach_w src cap m used out ai ao; vmode (i_mode (m_s m)); uw_sfacts A v m used out z L ai ao;
         zf_ai z = ai; zf_ao z = uw_aout cap out ao]
  (LOCALx (temp _len (Vlong (Int64.repr (Zlength src - used - ai))) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - uw_aout cap out ao))) :: uw_lcl A v)
  (SEPx (uw_sep A v out z L)))
  end.

(* after avail_in's refill: avail_in is the next call's offer uw_ain *)
Definition uw_M2 (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROPx [reach_w src cap m used out ai ao; vmode (i_mode (m_s m)); uw_sfacts A v m used out z L ai ao;
         zf_ai z = uw_ain src used ai; zf_ao z = uw_aout cap out ao]
  (LOCALx (temp _len (Vlong (Int64.repr (Zlength src - used - uw_ain src used ai))) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - uw_aout cap out ao))) :: uw_lcl A v)
  (SEPx (uw_sep A v out z L)))
  end.

(* after the call err = inflate(&stream, Z_NO_FLUSH): the stream as the call left it; the loop goes on from
   there when err = Z_OK, and has ended otherwise *)
Definition uw_LC (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  EX err: Z, EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROPx [-5 <= err <= 2;
         err = Z_OK -> reach_w src cap m used out ai ao /\ vmode (i_mode (m_s m));
         err <> Z_OK -> uncw_loop src cap m_first 0 [] 0 0 err used out;
         uw_sfacts A v m used out z L ai ao; zf_ai z = ai; zf_ao z = ao]
  (LOCALx (temp _err (Vint (Int.repr err)) ::
           temp _len (Vlong (Int64.repr (Zlength src - used - ai))) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: uw_lcl A v)
  (SEPx (uw_sep A v out z L)))
  end.

(* after the loop: the loop of the model from the start has ended with err *)
Definition uw_brk (A: uwargs) (v: val) : environ -> mpred :=
  match A with UWA gv dnull dsh dp dn dc cap dlp dtok stok ssh sp sn sc src slp gsh tsh =>
  EX err: Z, EX m: mst, EX used: Z, EX out: list Z, EX z: zfields, EX L: live, EX ai: Z, EX ao: Z,
  PROPx [err <> Z_OK; -5 <= err <= 2; uncw_loop src cap m_first 0 [] 0 0 err used out;
         uw_sfacts A v m used out z L ai ao; zf_ai z = ai; zf_ao z = ao]
  (LOCALx (temp _err (Vint (Int.repr err)) ::
           temp _len (Vlong (Int64.repr (Zlength src - used - ai))) ::
           temp _left (Vlong (Int64.repr (cap - Zlength out - ao))) :: uw_lcl A v)
  (SEPx (uw_sep A v out z L)))
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The segment statements                                                                        *)

(* statements 0-4: the checks (they pass), len, left, dest *)
Definition uw_p1_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A ->
  semax Delta_uw (uw_A5 A v) uw_seg5 (POST_uw A) ->
  semax Delta_uw (PRE_uw A v) uw_seg0 (POST_uw A).

(* statements 5-9: the stores into the stream *)
Definition uw_p2_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A ->
  semax Delta_uw (uw_A10 A v) uw_seg10 (POST_uw A) ->
  semax Delta_uw (uw_A5 A v) uw_seg5 (POST_uw A).

(* statements 10-13: inflateInit (Z_MEM_ERROR returns), next_out, avail_out; the loop's entry *)
Definition uw_p3_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_inv A v) uw_seg14 (POST_uw A) ->
  semax Delta_uw (uw_A10 A v) uw_seg10 (POST_uw A).

(* the loop *)
Definition uw_loop_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_brk A v) uw_seg15 (POST_uw A) ->
  semax Delta_uw (uw_inv A v) uw_seg14 (POST_uw A).

(* the loop's body *)
Definition uw_rout_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_inv A v) uw_rout (normal_ret_assert (uw_M1 A v)).
Definition uw_rin_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_M1 A v) uw_rin (normal_ret_assert (uw_M2 A v)).
Definition uw_call_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_M2 A v) uw_call_st (normal_ret_assert (uw_LC A v)).

(* statements 15-: after the loop *)
Definition uw_exit_stmt : Prop :=
  forall {Espec: OracleKind} (A: uwargs) (v: val), uw_facts A -> isptr v ->
  semax Delta_uw (uw_brk A v) uw_seg15 (POST_uw A).
