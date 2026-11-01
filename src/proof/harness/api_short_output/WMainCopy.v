(* Law api_short_output (data of any length), main (WMain.v): the loop that copies compress2's output into the
   input of uncompress2, `for (size_t i = 0; i < compressed_len; i++) source[i] = compressed[i];`: afterwards
   source holds the zlib stream out followed by the last |source| - |out| bytes it had; then WMainTail.w_tail_ok.
   main's proof is cut there to keep each file's check short. *)
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
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

(* the loop `for (size_t i = 0; i < compressed_len; i++) source[i] = compressed[i]` and what follows it *)
Definition w_copy : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 20 (w_chain (fn_body f_main))) in exact x).

(* before the loop: compress2 returned Z_OK with the zlib stream out of the data bs in compressed (cb bytes); source is
   an object of |ib| >= |out| bytes holding the bytes ib, suffix_len = |ib| - |out|; original_copy holds the copy of
   the data made before compress2; the output space outp of cap bytes, Z_NULL (dnull) only when cap = 0 *)
Definition w_copy_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (cap cb : Z) (compp outp expp inp : val)
    (ob : list Z) (dnull : bool) (out ib : list Z) : environ -> mpred :=
  PROP (Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None bs out; is_bytes bs;
        1 <= Zlength bs <= 9223372036854775807; 0 <= cap <= Zlength bs - 1; Zlength ob = cap;
        if dnull then outp = nullval else outp <> nullval; dnull = true -> cap = 0; dnull = false -> isptr outp;
        13 <= cb <= Int64.max_unsigned; Zlength out <= cb;
        is_bytes ib; Zlength out <= Zlength ib <= Int64.max_unsigned; isptr compp; isptr expp; isptr inp)
  LOCAL (temp _decompressed outp; temp _original_copy expp; temp _source inp; temp _compressed compp;
         temp _suffix_len (Vlong (Int64.repr (Zlength ib - Zlength out)));
         temp _decompressed_size (Vlong (Int64.repr cap));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
  SEP (data_at Ews (tarray tuchar (Zlength ib)) (bytes_rep ib) inp;
       malloc_token Ews (tarray tuchar (Zlength ib)) inp;
       data_at Ews (tarray tuchar cb) (map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) compp;
       data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       data_at Tsh tulong (vl (Zlength out)) vcl;
       cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
       if dnull then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       tables_rep Ers gv; version_lit gv; uversion_lit gv).

Lemma w_copy_ok {Espec : OracleKind} (UF : uw_theory_stmt) gv vcl vol vul bs cap cb compp outp expp inp ob dnull
    out ib :
  semax Delta_w (w_copy_pre gv vcl vol vul bs cap cb compp outp expp inp ob dnull out ib) w_copy POST_wB.
Proof.
  unfold w_copy, w_copy_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into Hok.
  assert (Hob: bytes_ok out) by exact (Zlib.proof.roundtrip.RTCLFacts.rtcl_dfinal_bytes _ _ Hok).
  set (dc := map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) in *.
  assert (Hdc: Zlength dc = cb) by (unfold dc, Zrepeat; list_solve).
  set (n := Zlength ib) in *. set (m := Zlength out) in *.
  forward.
  (* after i rounds, source holds the first i bytes of out followed by what it had from i on *)
  forward_loop
    (EX i : Z,
     PROP (0 <= i <= m)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _decompressed outp; temp _original_copy expp; temp _source inp;
            temp _compressed compp; temp _suffix_len (Vlong (Int64.repr (n - m)));
            temp _decompressed_size (Vlong (Int64.repr cap));
            lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
     SEP (data_at Ews (tarray tuchar n) (bytes_rep (sublist 0 i out ++ sublist i n ib)) inp;
          malloc_token Ews (tarray tuchar n) inp;
          data_at Ews (tarray tuchar cb) dc compp;
          data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
          data_at Tsh tulong (vl m) vcl;
          cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
          if dnull then emp
          else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
          zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
          tables_rep Ers gv; version_lit gv; uversion_lit gv))
  continue:
    (EX i : Z,
     PROP (0 <= i < m)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _decompressed outp; temp _original_copy expp; temp _source inp;
            temp _compressed compp; temp _suffix_len (Vlong (Int64.repr (n - m)));
            temp _decompressed_size (Vlong (Int64.repr cap));
            lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
     SEP (data_at Ews (tarray tuchar n) (bytes_rep (sublist 0 (i + 1) out ++ sublist (i + 1) n ib)) inp;
          malloc_token Ews (tarray tuchar n) inp;
          data_at Ews (tarray tuchar cb) dc compp;
          data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
          data_at Tsh tulong (vl m) vcl;
          cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
          if dnull then emp
          else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
          zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
          tables_rep Ers gv; version_lit gv; uversion_lit gv))
  break:
    (PROP ()
     LOCAL (temp _decompressed outp; temp _original_copy expp; temp _source inp;
            temp _suffix_len (Vlong (Int64.repr (n - m)));
            temp _decompressed_size (Vlong (Int64.repr cap));
            lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
     SEP (data_at Ews (tarray tuchar n) (bytes_rep (out ++ sublist m n ib)) inp;
          malloc_token Ews (tarray tuchar n) inp;
          data_at Ews (tarray tuchar cb) dc compp;
          data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
          data_at Tsh tulong (vl m) vcl;
          cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
          if dnull then emp
          else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
          zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
          tables_rep Ers gv; version_lit gv; uversion_lit gv)).
  - Exists 0. entailer!. simpl app. rewrite sublist_same by lia. cancel.
  - Intros i. forward.
    forward_if.
    + assert (Hz: Znth i dc = vi (Znth i out))
        by (unfold dc; rewrite Znth_app1 by list_solve; rewrite Znth_map by lia; reflexivity).
      assert (Hr: 0 <= Znth i out <= Byte.max_unsigned) by (apply (is_bytes_Znth out i Hob); lia).
      forward.
      { entailer!. unfold dc. rewrite Znth_app1 by list_solve. rewrite Znth_map by lia. unfold vi; simpl.
        rewrite Int.unsigned_repr by rep_lia. rep_lia. }
      (* the load's default element is Vundef, Hz's is Inhabitant_val: the same value *)
      replace (@Znth val Vundef i dc) with (vi (Znth i out)) by exact (eq_sym Hz).
      forward.
      Exists i. entailer!.
      apply sepcon_derives; [ | auto]. apply derives_refl'. f_equal.
      unfold bytes_rep. list_solve.
    + forward. entailer!.
      assert (i = Zlength out) by lia. subst i. rewrite sublist_same by lia. apply derives_refl.
  - Intros i. forward. Exists (i + 1). entailer!.
  - eapply semax_pre; [ | apply (w_tail_ok UF gv vcl vol vul bs cap outp expp inp ob dnull out (sublist m n ib))].
    unfold w_tail_pre.
    replace (Zlength out + Zlength (sublist m n ib)) with n by list_solve.
    entailer!.
    split; [apply is_bytes_sublist; auto | ].
    rewrite Zlength_sublist by (pose proof (Zlength_nonneg out); unfold m, n in *; lia). reflexivity.
Qed.
