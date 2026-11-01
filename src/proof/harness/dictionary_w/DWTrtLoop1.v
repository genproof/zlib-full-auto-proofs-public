(* Law rt_dictionary, main (DWKit.v), statement 32: the do-while of inflate(Z_FINISH) calls, cut for DWTrtLoop.v.
   Its body is (1) in_rest = compressed_len - (next_in - compressed), (2) out_rest = data_len - (next_out - out),
   (3) avail_in = clip(in_rest), (4) avail_out = clip(out_rest), (5) code = inflate(&decompressor, Z_FINISH) and
   `return 0` on Z_MEM_ERROR; its test `code == Z_BUF_ERROR && (in_rest > UINT_MAX || out_rest > UINT_MAX)`.
   This file: the pieces of the statement, the assertions between them (trt_mid0 after (2), trt_mid1 after (4),
   trt_cont at the test) and the proof of the test (trt_incr_ok): Z_BUF_ERROR goes on with RI, Z_STREAM_END leaves
   the loop with RB.  DWTrtLoop2.v proves (5), DWTrtLoop3.v (3)-(5), DWTrtLoop.v the loop. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.clip_streams.CS.
Require Import Zlib.proof.harness.clip_streams.Globals.
Require Import Zlib.proof.harness.clip_streams.RTKit.
Require Import Zlib.proof.harness.clip_streams.RTLoop.
Require Import Zlib.proof.harness.dictionary_w.DWCS.
Require Import Zlib.proof.harness.dictionary_w.DWFacts.
Require Import Zlib.proof.harness.dictionary_w.DWIFacts.
Require Import Zlib.proof.harness.dictionary_w.DWMainDefs.
Require Import Zlib.proof.harness.dictionary_w.DWKit.
Import DWKit.DRT.
#[local] Existing Instance CS.CS.
Local Open Scope logic.

Ltac simplify_remove_localdef_temp ::= rt_rlt.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The pieces of statement 32 *)

(* the loop's test *)
Definition trt_incr : statement :=
  ltac:(let s := eval unfold trt_loop in trt_loop in match s with Sloop _ ?i => exact i end).
(* the body from (3) on *)
Definition trt_clips : statement :=
  ltac:(let s := eval unfold trt_loop in trt_loop in
        match s with Sloop (Ssequence _ (Ssequence _ ?r)) _ => exact r end).
(* (5): the call and its Z_MEM_ERROR test *)
Definition trt_call : statement :=
  ltac:(let s := eval unfold trt_loop in trt_loop in
        match s with Sloop (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?c)))) _ => exact c end).

(* ---------------------------------------------------------------------------------------------- *)
(** ** Helpers *)

(* clip()'s value, as DWIFacts states the pieces (DFacts.clipz) *)
Lemma trt_clipz k: Z.min k Int.max_unsigned = DFacts.clipz k.
Proof. unfold DFacts.clipz, RTDIface.umax. reflexivity. Qed.

(* in_rest = m - (size_t) (p + k - p), out_rest likewise, as the loop computes the bytes left *)
Lemma trt_rest (p: val) k m: isptr p -> 0 <= k <= m -> m <= Ptrofs.max_unsigned ->
  force_val (sem_binary_operation' Osub tulong tulong (Vlong (Int64.repr m))
    (eval_cast tlong tulong (eval_binop Osub (tptr tuchar) (tptr tuchar) (offset_val k p) p)))
  = Vlong (Int64.repr (m - k)).
Proof.
  intros Pp Hk Hm. rewrite <- (rtl_ptr_sub p k m) by auto.
  destruct p; try contradiction. reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The assertions inside the loop *)

Section Mid.
Context (P : dinv_t) (wbits n b : Z) (D O dict : list Z) (dp op ddp cp : val) (gv : globals) (vc vd : val).

(* after (2): in_rest and out_rest computed from the stream (z, L) at position pos, out written *)
Definition trt_mid0 (pos : Z) (out : list Z) (z : zfields) (L : live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _out_rest (Vlong (Int64.repr (n - Zlength out))); temp _t'37 (offset_val (Zlength out) op);
         temp _in_rest (Vlong (Int64.repr (Zlength O - pos))); temp _t'38 (offset_val pos cp);
         temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _data_len (Vlong (Int64.repr n));
         temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at Tsh t_zsl (rtl_tup gv z (adler_v (raw_live (Some L)) z Vundef) (l_sp L)) vd; state_mem gv vd L;
       zfuncs gv; mem_mgr gv; R_of lit_drt gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

(* after (4): avail_in = clip(in_rest), avail_out = clip(out_rest) stored *)
Definition trt_mid1 (pos : Z) (out : list Z) (z : zfields) (L : live) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'30 (Vint (Int.repr (Z.min (n - Zlength out) Int.max_unsigned)));
         temp _t'29 (Vint (Int.repr (Z.min (Zlength O - pos) Int.max_unsigned)));
         temp _out_rest (Vlong (Int64.repr (n - Zlength out))); temp _t'37 (offset_val (Zlength out) op);
         temp _in_rest (Vlong (Int64.repr (Zlength O - pos))); temp _t'38 (offset_val pos cp);
         temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _data_len (Vlong (Int64.repr n));
         temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (data_at Tsh t_zsl
         (offset_val pos cp, (Vint (Int.repr (Z.min (Zlength O - pos) Int.max_unsigned)),
          (Vlong (Int64.repr (zf_tin z)), (offset_val (Zlength out) op,
           (Vint (Int.repr (Z.min (n - Zlength out) Int.max_unsigned)),
            (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (l_sp L, (gv Zlib.inflate.code._zcalloc,
             (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)),
              (adler_v (raw_live (Some L)) z Vundef, zf_res z))))))))))))) vd;
       state_mem gv vd L;
       zfuncs gv; mem_mgr gv; R_of lit_drt gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

(* at the loop's test, after a call that did not run out of memory: Z_STREAM_END (1) with all of O read and D
   written, or Z_BUF_ERROR (-5) from a call offered less than the rest (in_rest or out_rest above UINT_MAX) with
   the theory's invariant at the new position; the gz_header memory of the live state is kept (emp under P) *)
Definition trt_cont : environ -> mpred :=
  EX r : Z, EX pos : Z, EX out : list Z, EX z : zfields, EX L : live, EX ir : Z, EX orr : Z,
  PROP ((r = 1 /\ pos = Zlength O /\ out = D) \/
        (r = -5 /\ (4294967295 < ir \/ 4294967295 < orr) /\ P wbits dict D O pos out z L /\ swfW (l_s L));
        zf_ni z = offset_val pos cp; zf_no z = offset_val (Zlength out) op;
        0 <= ir <= Int64.max_unsigned; 0 <= orr <= Int64.max_unsigned)
  LOCAL (temp _code (Vint (Int.repr r)); temp _in_rest (Vlong (Int64.repr ir));
         temp _out_rest (Vlong (Int64.repr orr));
         temp _compressed_len (Vlong (Int64.repr (Zlength O))); temp _data_len (Vlong (Int64.repr n));
         temp _data dp; temp _out op; temp _compressed cp;
         lvar _compressor t_zsl vc; lvar _decompressor t_zsl vd; gvars gv)
  SEP (istreamA gv Tsh vd z Vundef (Some L); head_mem L;
       zfuncs gv; mem_mgr gv; R_of lit_drt gv;
       malloc_token Ews (tarray tuchar (Zlength dict)) ddp;
       data_at Ews (tarray tuchar (Zlength dict)) (bytes_rep dict) ddp;
       malloc_token Ews (tarray tuchar n) dp; data_at Ews (tarray tuchar n) (bytes_rep D) dp;
       malloc_token Ews (tarray tuchar n) op;
       data_at Ews (tarray tuchar n) (bytes_rep out ++ Zrepeat Vundef (n - Zlength out)) op;
       malloc_token Ews (tarray tuchar b) cp;
       data_at Ews (tarray tuchar b) (bytes_rep O ++ Zrepeat Vundef (b - Zlength O)) cp;
       data_at_ Tsh t_zsl vc; TT).

End Mid.

(* ---------------------------------------------------------------------------------------------- *)
(** ** The loop's test *)

Ltac trt_ifk t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t (Vint (Int.repr v)) :: Q) (SEPx R))) end.

Lemma trt_incr_ok {Espec : OracleKind} Q P gv vc vd wbits n b D O dict dp op ddp cp Rn Rb Rc Rr :
  dict_ifacts Q P -> dw_hf wbits n b D O dict dp op ddp cp -> 6 <= Zlength O ->
  semax Delta_drt (trt_cont P wbits n b D O dict dp op ddp cp gv vc vd) trt_incr
    (loop2_ret_assert (RI lit_drt gv vc vd P wbits n b D O dict dp op ddp cp)
       (overridePost (RB lit_drt gv vc vd wbits n b D O dict dp op ddp cp)
          {| RA_normal := Rn; RA_break := Rb; RA_continue := Rc; RA_return := Rr |})).
Proof.
  intros PF HF H6O.
  pose proof HF as HF'. destruct HF' as (DF & CF & HO & Hb & BD & BO & Pcp).
  destruct CF as (Hn & HD & ID & Pdp & Pop & Hdl & IDd & Pddp & Hw).
  unfold trt_incr, Delta_drt. abbreviate_semax.
  unfold trt_cont. Intros r pos out z L ir orr.
  destruct H as [(Er & Ep & Eo) | (Er & Hbig & HP & Hsw)].
  - (* Z_STREAM_END: the test fails, the loop ends *)
    subst r pos out.
    trt_ifk _t'28 0.
    { exfalso. rewrite Int.neg_repr in H. apply repr_inj_signed in H; [lia | rep_lia | rep_lia]. }
    { forward. entailer!. }
    forward_if.
    { exfalso. apply H; reflexivity. }
    forward.
    unfold RB. Exists z L.
    rewrite <- HD, Z.sub_diag, Zrepeat_0, app_nil_r. rewrite HD in *.
    entailer!.
  - (* Z_BUF_ERROR from a clipped call: the loop goes on *)
    subst r.
    destruct (di_ok _ _ PF _ _ _ _ _ _ _ _ HP) as (Hhd & Hwr & Hpos & rest & Erest). clear Erest rest.
    trt_ifk _t'28 1.
    { forward_if.
      - forward. entailer!.
      - forward. forward. entailer!.
        assert (Ho: 4294967295 < orr) by (rewrite Int.unsigned_repr in H4 by rep_lia; lia).
        simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (zlt 4294967295 orr); [reflexivity | lia]. }
    { exfalso. apply H; reflexivity. }
    forward_if.
    { forward. unfold RI. Exists pos out z L.
      replace (head_mem L) with emp by (unfold head_mem; rewrite Hhd; reflexivity).
      entailer!. }
    { exfalso. apply Int.one_not_zero. exact H. }
Qed.
