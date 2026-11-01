(* Law deflate_api: the kit of main's body proof (Main.v): main's type context and postcondition, the suffixes
   of main's body after the call of deflate_run, and the assertion MA there (a successful run: the run's
   result run_ok_at (RunSpec.v), main's halves (comp Ews) of R and s, and b).  Parts (continuation-passing):
     main_checks (MainChecks.v): msuf 1 (c = R.clen; the checks of the zlib / gzip output) -> msuf 4 (bad = ...)
     main_tail   (MainTail.v):   msuf 4 (the calls after Z_STREAM_END and after deflateEnd) -> return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.harness.deflate_api.ApiCS Zlib.proof.harness.deflate_api9.RunSpec
               Zlib.proof.harness.deflate_api9.ApiConv Zlib.proof.harness.deflate_api9.RunKit.
Require Import Zlib.harness.x_deflate_api.code.
#[local] Existing Instance ApiCS.CS.
Local Open Scope logic.

(* main's resources (GlobalsInit.globals_of) *)
Definition Rm (gv : globals) : mpred := deflate_globals gv * version_at gv vlit.

Definition main_body : statement := ltac:(let x := eval cbv beta iota zeta delta [f_main fn_body] in
                                          (fn_body f_main) in exact x).
(* main's body is Ssequence m0 (return 0); m0's statements: the call of deflate_run and its test, c = R.clen,
   o = R.comp, the checks, bad = ..., ... , return 0 *)
Definition main_m0 : statement := ltac:(let x := eval cbv beta iota zeta delta [main_body] in
  (match main_body with Ssequence a _ => a | _ => Sskip end) in exact x).
Ltac get_msuf k := let x := eval cbv beta iota zeta delta [suf main_m0] in (suf k main_m0) in exact x.
Definition msuf1 : statement := ltac:(get_msuf 1%nat).
Definition msuf4 : statement := ltac:(get_msuf 4%nat).

Definition Delta_m (I : api_inv) (Iend : dstate -> Prop) : tycontext :=
  func_tycontext f_main (QPvarspecs p) (Gmain I Iend) nil.

Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* after a successful run (deflate_run returned 1 and R.init is Z_OK) *)
Definition MA (I : api_inv) (Iend : dstate -> Prop) (rf : rfinal) (vR vs vb : val) (gv : globals)
    : environ -> mpred :=
  PROP (rf_ok Iend vR rf; api_facts I Iend)
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _b (tarray tuchar 1) vb; gvars gv)
  SEP (run_ok_at rf vR vs gv; mem_mgr gv; deflate_globals gv;
       data_at_ (Share.comp Ews) t_drun vR; data_at_ (Share.comp Ews) t_strmL vs;
       data_at_ Tsh (tarray tuchar 1) vb).
