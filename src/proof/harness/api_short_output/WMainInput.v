(* Law api_short_output (data of any length), main (WMain.v): the input of uncompress2, `suffix_len = 0; if
   (compressed_len < PTRDIFF_MAX) suffix_len = upto(PTRDIFF_MAX - compressed_len); source =
   alloc_any_bytes(compressed_len + suffix_len); if (source == NULL) return 0;`; then WMainCopy.w_copy_ok (the copy of
   the stream into input).  main's proof is cut there to keep each file's check short. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec Zlib.proof.harness.laws_common.BytesEqNull.
Require Import Zlib.proof.roundtrip.RTC2W Zlib.proof.roundtrip.RTC2WFinal Zlib.proof.uncompr.UTheoryW.
Require Zlib.proof.roundtrip.RTCLFacts.
Require Import Zlib.proof.harness.api_short_output.WLawCS Zlib.proof.harness.api_short_output.WMainDefs.
Require Import Zlib.proof.harness.api_short_output.WMainTail.
Require Import Zlib.proof.harness.api_short_output.WMainCopy.
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

(* the statements from `suffix_len = 0` *)
Definition w_input : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 16 (w_chain (fn_body f_main))) in exact x).

(* before `suffix_len = 0`: compress2 returned Z_OK, its output out (in compressed, cb bytes) is the zlib stream of
   the data bs; original_copy holds the copy of the data made before compress2; the output space outp of cap bytes,
   Z_NULL (dnull) only when cap = 0 *)
Definition w_input_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (cap cb : Z) (compp outp expp : val)
    (ob : list Z) (dnull : bool) (out : list Z) : environ -> mpred :=
  PROP (Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None bs out; is_bytes bs;
        1 <= Zlength bs <= 9223372036854775807; 0 <= cap <= Zlength bs - 1; Zlength ob = cap;
        if dnull then outp = nullval else outp <> nullval; dnull = true -> cap = 0; dnull = false -> isptr outp;
        13 <= cb <= Int64.max_unsigned; Zlength out <= cb; isptr compp; isptr expp)
  LOCAL (temp _decompressed outp; temp _original_copy expp; temp _compressed compp; temp _decompressed_size (Vlong (Int64.repr cap));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
  SEP (data_at Ews (tarray tuchar cb) (map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) compp;
       data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       data_at Tsh tulong (vl (Zlength out)) vcl;
       cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
       if dnull then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       tables_rep Ers gv; version_lit gv; uversion_lit gv).

Lemma w_input_ok {Espec : OracleKind} (UF : uw_theory_stmt) gv vcl vol vul bs cap cb compp outp expp ob dnull out :
  semax Delta_w (w_input_pre gv vcl vol vul bs cap cb compp outp expp ob dnull out) w_input POST_wB.
Proof.
  unfold w_input, w_input_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into Hok, H0 into Hbs, H1 into Hn, H2 into Hcap, H3 into Hob, H4 into Hdn, H5 into Hd0, H6 into Po,
    H7 into Hcb, H8 into Hoc, Pcompp into Pc, Pexpp into Pe.
  assert (Hol: 0 <= Zlength out) by apply Zlength_nonneg.
  unfold vl.
  (* suffix_len = 0; if (compressed_len < PTRDIFF_MAX) suffix_len = upto(PTRDIFF_MAX - compressed_len); *)
  forward. forward.
  forward_if (EX a : Z,
    PROP (0 <= a; Zlength out + a <= Int64.max_unsigned)
    LOCAL (temp _suffix_len (Vlong (Int64.repr a)); temp _decompressed outp; temp _original_copy expp; temp _compressed compp;
           temp _decompressed_size (Vlong (Int64.repr cap));
           lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
    SEP (data_at Ews (tarray tuchar cb) (map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) compp;
         data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
         data_at Tsh tulong (Vlong (Int64.repr (Zlength out))) vcl;
         cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
         if dnull then emp
         else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
         Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
         tables_rep Ers gv; version_lit gv; uversion_lit gv)).
  { forward. forward_call (9223372036854775807 - Zlength out). Intros a. forward. Exists a. entailer!. }
  { forward. Exists 0. entailer!. }
  Intros a.
  (* source = alloc_any_bytes(compressed_len + suffix_len); if (source == NULL) return 0; *)
  forward. forward_call (Zlength out + a, gv).
  Intros vret. destruct vret as [inp ib]. simpl fst in *; simpl snd in *.
  asw_law.
  forward.
  destruct (eq_dec inp nullval) as [PI|PI].
  { subst inp. forward_if. { ret0. } { asw_bad. } }
  Intros.
  forward_if. { contradiction. }
  assert_PROP (isptr inp) as Pi by entailer!.
  match goal with H: Zlength ib = Zlength out + a |- _ => rewrite <- H end.
  replace a with (Zlength ib - Zlength out) by lia.
  (* the rest: WMainCopy.w_copy_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [| apply (w_copy_ok UF gv vcl vol vul bs cap cb compp outp expp inp ob dnull out ib)].
  unfold w_copy_pre. entailer!.
Qed.
