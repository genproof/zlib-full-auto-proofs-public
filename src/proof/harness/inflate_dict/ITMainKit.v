(* Law inflate_dict, main: the kit shared by the two halves of main's proof (as inflate_codes/MainKit.v).
   - Gmain_k (main's callees), Delta_m (main's type context), POST_m (main's postcondition after start_function);
   - hist_spec (the harness's static hist(), body: ITHist.v);
   - seg_inf: the statements of f_main after `const unsigned slen = w.len;` (the inflate half);
   - enc_done: the assertion at that point (the encoder half's result: the ghost G of ITFacts.v);
   - the two halves, continuation style: `main_enc_stmt` (main's body from the encoder half and ANY proof of
     seg_inf from enc_done; ITMainEnc.v) and `main_inf_stmt I` (seg_inf from enc_done for an invariant I with
     it_facts I; ITMainInf.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

(* hist(dict, dlen, data, k): byte k of dict ++ data (data: an object whose first bytes hold pre) *)
Definition hist_spec :=
  DECLARE _hist
  WITH dsh: share, dp: val, dict: list Z, ash: share, ap: val, N: Z, acont: list val, pre: list Z, k: Z
  PRE [ tptr tuchar, tuint, tptr tuchar, tuint ]
    PROP (readable_share dsh; readable_share ash; 0 <= k < Zlength dict + Zlength pre;
          Zlength dict + Zlength pre <= Int.max_unsigned; Zlength acont = N; Zlength pre <= N;
          sublist 0 (Zlength pre) acont = bytes_rep pre; is_bytes dict; is_bytes pre)
    PARAMS (dp; Vint (Int.repr (Zlength dict)); ap; Vint (Int.repr k))
    SEP (data_at dsh (tarray tuchar (Zlength dict)) (bytes_rep dict) dp; data_at ash (tarray tuchar N) acont ap)
  POST [ tuchar ]
    PROP () RETURN (Vint (Int.repr (Znth k (dict ++ pre))))
    SEP (data_at dsh (tarray tuchar (Zlength dict)) (bytes_rep dict) dp; data_at ash (tarray tuchar N) acont ap).

Definition Gmain_k : funspecs :=
  [inflateInit2__spec; inflate_spec; inflateSetDictionary_spec; inflateGetDictionary_spec; inflateEnd_spec;
   zcalloc_i; zcfree_i;
   ref_adler32_spec; bytes_copy_spec; bytes_same_spec; exact_copy_spec; exact_space_spec; stream_defaults_spec;
   bw_bits_spec; bw_byte_spec; bw_align_spec; bw_fixed_spec; bw_fixed_match_spec it_tabs; hist_spec;
   (_quickproof_malloc, malloc_spec'); (_quickproof_free, free_spec');
   nondet_u32_spec; nondet_u8_spec; nondet_bytes_spec; gp_assert_spec; gp_assume_spec].

Definition Delta_m : tycontext := func_tycontext f_main (QPvarspecs p) Gmain_k nil.

(* main's postcondition after start_function (main_core_spec) *)
Definition POST_m : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* ---------------------------------------------------------------------------------------------- *)
(* The inflate half of f_main's body                                                              *)

(* the statement after the first `Ssequence (Sset x _) rest` *)
Fixpoint find_after_set (x: ident) (s: statement) : option statement :=
  match s with
  | Ssequence (Sset y _) rest => if Pos.eqb x y then Some rest else find_after_set x rest
  | Ssequence a b => match find_after_set x a with Some r => Some r | None => find_after_set x b end
  | Sifthenelse _ a b => match find_after_set x a with Some r => Some r | None => find_after_set x b end
  | Sloop a b => match find_after_set x a with Some r => Some r | None => find_after_set x b end
  | _ => None
  end.

Definition seg_inf : statement :=
  ltac:(let x := eval vm_compute in (match find_after_set _slen (fn_body f_main) with Some r => r | None => Sskip end)
        in exact x).

(* the windowBits the harness gives inflateInit2 *)
Definition iw_of (zlib: bool) (wb isel: Z) : Z :=
  if zlib then (if isel <? 85 then wb else if isel <? 170 then 0 else 32 + wb) else - wb.

(* ---------------------------------------------------------------------------------------------- *)
(* The assertion after the encoder half                                                           *)

(* Ghost values: gv; the addresses of the local variables w (vw), s (vs), osnap (vosn), dl (vdl); the objects
   dict (dictp, dlen bytes: the dictionary), bad (badp: it_bad G), data (datap, 2^18 bytes: the data first),
   src (srcp, 2^19 bytes: the stream first); the drawn isel, wsel; G (ITFacts.v). *)
Definition enc_done (gv: globals) (vw vs vosn vdl dictp badp datap srcp: val) (G: it_ghost) (isel wsel: Z)
    (dcont scont: list val) : environ -> mpred :=
  PROP (it_ok G; g_iw G = iw_of (g_zlib G) (g_wb G) isel; 0 <= isel <= 255; 0 <= wsel <= 255;
        Zlength dcont = 2 ^ 18; sublist 0 (Zlength (it_data G)) dcont = bytes_rep (it_data G);
        Zlength scont = 2 ^ 19; sublist 0 (Zlength (it_src G)) scont = bytes_rep (it_src G);
        is_bytes (g_dict G);
        isptr dictp; isptr badp; isptr datap; isptr srcp)
  LOCAL (temp _zlib (Vint (Int.repr (if g_zlib G then 1 else 0)));
         temp _wb (Vint (Int.repr (g_wb G))); temp _isel (Vint (Int.repr isel));
         temp _wsel (Vint (Int.repr wsel));
         temp _dlen (Vint (Int.repr (Zlength (g_dict G)))); temp _dict dictp;
         temp _bad badp; temp _blen (Vint (Int.repr (Zlength (it_bad G))));
         temp _dictid (Vlong (Int64.repr (it_dictid G)));
         temp _data datap; temp _src srcp;
         temp _n (Vint (Int.repr (Zlength (it_data G))));
         temp _maxd (Vint (Int.repr (2 ^ g_wb G)));
         temp _slen (Vint (Int.repr (Zlength (it_src G))));
         lvar _w (Tstruct _bw noattr) vw; lvar _s (Tstruct _z_stream_s noattr) vs;
         lvar _osnap (tptr tuchar) vosn; lvar _dl tuint vdl; gvars gv)
  SEP (mem_mgr gv; zfuncs gv;
       tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; it_hversion_lit gv; dref_tabs gv Ers it_tabs;
       malloc_token Ews (tarray tuchar (Zlength (g_dict G))) dictp;
       data_at Ews (tarray tuchar (Zlength (g_dict G))) (bytes_rep (g_dict G)) dictp;
       malloc_token Ews (tarray tuchar (Zlength (it_bad G))) badp;
       data_at Ews (tarray tuchar (Zlength (it_bad G))) (bytes_rep (it_bad G)) badp;
       malloc_token Ews (tarray tuchar (2 ^ 18)) datap; data_at Ews (tarray tuchar (2 ^ 18)) dcont datap;
       malloc_token Ews (tarray tuchar (2 ^ 19)) srcp; data_at Ews (tarray tuchar (2 ^ 19)) scont srcp;
       data_at_ Tsh (Tstruct _bw noattr) vw; data_at_ Tsh (Tstruct _z_stream_s noattr) vs;
       data_at_ Tsh (tptr tuchar) vosn; data_at_ Tsh tuint vdl).

(* the inflate half from enc_done, for every value *)
Definition seg_inf_ok {Espec: OracleKind} (P: it_ghost -> Prop) : Prop :=
  forall gv vw vs vosn vdl dictp badp datap srcp G isel wsel dcont scont,
    P G ->
    semax Delta_m (enc_done gv vw vs vosn vdl dictp badp datap srcp G isel wsel dcont scont) seg_inf POST_m.

(* the encoder half: main's body, given the inflate half *)
Definition main_enc_stmt {Espec: OracleKind} : Prop :=
  (forall Es: OracleKind, @seg_inf_ok Es (fun _ => True)) -> semax_body (QPvarspecs p) Gmain_k f_main (_main, main_core_spec R).

(* the inflate half *)
Definition main_inf_stmt {Espec: OracleKind} (I: it_inv) : Prop := it_facts I -> seg_inf_ok (fun _ => True).
