(* Law api_short_output (data of any length), main (WMain.v): the segment of the test `if (original_copy == NULL ||
   compressed == NULL || (decompressed == NULL && decompressed_size > 0)) return 0;` on the results of copy_of, malloc
   and alloc_any_bytes; when it falls through, the output space is Z_NULL only with decompressed_size 0 (the flag dnull of
   uncompress2's and bytes_eq's specifications); then WMainC2.w_mid_ok. *)
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
Require Import Zlib.proof.harness.api_short_output.WMainTail Zlib.proof.harness.api_short_output.WMainC2.
Require Import Zlib.proof.harness.api_short_output.WMainCopy.
Require Import Zlib.proof.harness.api_short_output.WMainInput.
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

(* the statements from the test `if (original_copy == NULL || compressed == NULL || (decompressed == NULL &&
   decompressed_size > 0))` *)
Definition w_null : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 11 (w_chain (fn_body f_main))) in exact x).

(* before that test: the inputs drawn (original_len n, original bs, decompressed_size cap, level v - 1), the data an
   object, copy_of, malloc and alloc_any_bytes returned, each result Z_NULL or an object *)
Definition w_null_pre (gv : globals) (vcl vol vul : val) (n : Z) (bs : list Z) (cap v : Z)
    (datap compp outp expp : val) (ob : list Z) : environ -> mpred :=
  PROP (Zlength bs = n; is_bytes bs; 1 <= n <= 9223372036854775807; 0 <= cap <= n - 1; 0 <= v <= 10;
        Zlength ob = cap; isptr datap)
  LOCAL (temp _decompressed outp; temp _compressed compp; temp _original_copy expp; temp _original datap;
         temp _compressed_bound (Vlong (Int64.repr (c_compressBound n)));
         temp _level (Vint (Int.repr (v - 1))); temp _decompressed_size (Vlong (Int64.repr cap));
         temp _original_len (Vlong (Int64.repr n));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
  SEP (mem_mgr gv;
       if eq_dec outp nullval then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       if eq_dec compp nullval then emp
       else malloc_token Ews (tarray tuchar (c_compressBound n)) compp *
            data_at_ Ews (tarray tuchar (c_compressBound n)) compp;
       if eq_dec expp nullval then emp
       else malloc_token Ews (tarray tuchar n) expp * data_at Ews (tarray tuchar n) (bytes_rep bs) expp;
       malloc_token Ews (tarray tuchar n) datap; data_at Ews (tarray tuchar n) (bytes_rep bs) datap;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       data_at_ Tsh tulong vcl; deflate_globals gv; cversion_lit gv; tables_rep Ers gv; version_lit gv;
       uversion_lit gv).

Lemma w_null_ok {Espec : OracleKind} (CB : c2w_bound_stmt) (CF : c2w_final_stmt) (UF : uw_theory_stmt)
    gv vcl vol vul n bs cap v datap compp outp expp ob :
  semax Delta_w (w_null_pre gv vcl vol vul n bs cap v datap compp outp expp ob) w_null POST_wB.
Proof.
  unfold w_null, w_null_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into H1', H0 into H2, H1 into Hn, H2 into H, H3 into H0, H4 into H3. rename H1' into H1.
  pose proof (asw_cb_range n ltac:(rep_lia)) as Hcb.
  set (cb := c_compressBound n) in *.
  (* if (original_copy == NULL || compressed == NULL || (decompressed == NULL && decompressed_size > 0)) return 0; *)
  destruct (eq_dec expp nullval) as [PE|PE].
  { subst expp.
    ifpost _t'10 (Int.repr 1).
    { forward. entailer!. }
    { asw_bad. }
    ifpost _t'11 (Int.repr 1).
    { forward. entailer!. }
    { asw_bad. }
    forward_if. { ret0. } { asw_bad. } }
  Intros.
  destruct (eq_dec compp nullval) as [PC|PC].
  { subst compp.
    ifpost _t'10 (Int.repr 1).
    { asw_bad. }
    { forward. entailer!; asw_cmp. }
    ifpost _t'11 (Int.repr 1).
    { forward. entailer!. }
    { asw_bad. }
    forward_if. { ret0. } { asw_bad. } }
  Intros.
  ifpost _t'10 (Int.repr 0).
  { asw_bad. }
  { forward. entailer!; asw_cmp. }
  (* out is Z_NULL (dnull) or an object of cap bytes *)
  assert (Hdn: exists dnull: bool, if dnull then outp = nullval else outp <> nullval)
    by (destruct (eq_dec outp nullval); [exists true | exists false]; auto).
  destruct Hdn as [dnull Hdn].
  rewrite (asw_if_null dnull outp) by exact Hdn.
  ifpost _t'11 (Int.repr (if (dnull && (0 <? cap))%bool then 1 else 0)).
  { asw_bad. }
  { destruct dnull.
    - subst outp. forward_if.
      + forward. forward. entailer!.
        simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
        destruct (zlt 0 (Zlength ob)), (Z.ltb_spec 0 (Zlength ob)); try lia; reflexivity.
      + asw_bad.
    - Intros. forward_if.
      + asw_bad.
      + forward. entailer!. }
  forward_if. { ret0. }
  assert (Hd0: dnull = true -> cap = 0).
  { intros ->. destruct (Z.ltb_spec 0 cap); [cbn [andb] in *; asw_bad | lia]. }
  subst n.
  assert_PROP (isptr compp) as Pc by entailer!.
  assert_PROP (isptr expp) as Pe by entailer!.
  assert_PROP (dnull = false -> isptr outp) as Po by (destruct dnull; entailer!).
  (* the rest: w_mid_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (w_mid_ok CB CF UF gv vcl vol vul bs cap v datap compp outp expp ob dnull)].
  unfold w_mid_pre. entailer!.
Qed.
