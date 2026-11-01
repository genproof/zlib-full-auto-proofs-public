(* Law rt_roundtrip (data of any length), main (WMain.v): the source of uncompress2, `suffix_len = 0; if
   (compressed_len < PTRDIFF_MAX) suffix_len = upto(PTRDIFF_MAX - compressed_len); source =
   alloc_any_bytes(compressed_len + suffix_len); if (source == NULL) return 0;`; then WMainCopy.w_copy_ok (the copy
   of the stream into source).  main's proof is
   cut there to keep each file's check short. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.EnvBodies.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.roundtrip.RTCSpec.
Require Import Zlib.proof.roundtrip.RTCSpecW.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.uncompr.USpecW.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.roundtrip.RTC2W.
Require Import Zlib.proof.roundtrip.RTC2WFinal.
Require Import Zlib.proof.uncompr.UTheoryW.
Require Import Zlib.proof.harness.rt_roundtrip.WCS.
Require Import Zlib.proof.harness.rt_roundtrip.WMainDefs.
Require Import Zlib.proof.harness.rt_roundtrip.WMainTail.
Require Import Zlib.proof.harness.rt_roundtrip.WMainCopy.
Require Import Zlib.harness.rt_roundtrip.code.
#[local] Existing Instance Zlib.proof.harness.rt_roundtrip.WCS.CS.
Local Open Scope logic.

(* the statements from `suffix_len = 0` *)
Definition w_input : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 19 (w_chain (fn_body f_main))) in exact x).

(* before `suffix_len = 0`: compress2 returned Z_OK, its output out (in compressed, cb bytes) is the zlib stream of
   the data bs; original_copy, decompressed and decompressed_copy as WMainTail.w_tail_pre has them *)
Definition w_input_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (cb : Z) (en dn bn : bool)
    (compp outp expp q : val) (ob : list Z) (out : list Z) : environ -> mpred :=
  PROP (Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None bs out; is_bytes bs;
        Zlength bs <= Zlength ob <= 9223372036854775807; is_bytes ob;
        13 <= cb <= Int64.max_unsigned; Zlength out <= cb; isptr compp;
        if en then expp = nullval /\ bs = [] else isptr expp;
        if dn then outp = nullval /\ ob = [] else isptr outp;
        if bn then q = nullval /\ ob = [] else isptr q)
  LOCAL (temp _decompressed_copy q; temp _decompressed outp; temp _original_copy expp; temp _compressed compp;
         temp _decompressed_size (Vlong (Int64.repr (Zlength ob)));
         temp _original_len (Vlong (Int64.repr (Zlength bs)));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl;
         gvars gv)
  SEP (data_at Ews (tarray tuchar cb) (map vi out ++ sublist (Zlength out) cb (Zrepeat Vundef cb)) compp;
       if en then emp else data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       if bn then emp else data_at Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) q;
       data_at Tsh tulong (vl (Zlength out)) vcl;
       cversion_lit gv; deflate_globals gv; mem_mgr gv; TT;
       if dn then emp else malloc_token Ews (tarray tuchar (Zlength ob)) outp;
       if dn then emp else data_at Ews (tarray tuchar (Zlength ob)) (bytes_rep ob) outp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       tables_rep Ers gv; version_lit gv; uversion_lit gv).

Lemma w_input_ok {Espec : OracleKind} (UF : uw_theory_stmt) gv vcl vol vul bs cb en dn bn compp outp expp q ob
    out :
  semax Delta_w (w_input_pre gv vcl vol vul bs cb en dn bn compp outp expp q ob out) w_input POST_wB.
Proof.
  unfold w_input, w_input_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  unfold vl.
  (* suffix_len = 0; if (compressed_len < PTRDIFF_MAX) suffix_len = upto(PTRDIFF_MAX - compressed_len); *)
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward; forward;
    forward_if (EX a : Z, PROPx [0 <= a; Zlength out + a <= Int64.max_unsigned]
                  (LOCALx (temp _suffix_len (Vlong (Int64.repr a)) :: Q) (SEPx R))) end.
  - forward.
    forward_call (9223372036854775807 - Zlength out).
    Intros a. forward. Exists a. entailer!.
  - forward. Exists 0. entailer!.
  - Intros a.
    (* source = alloc_any_bytes(compressed_len + suffix_len); if (source == NULL) return 0; *)
    forward.
    forward_call (Zlength out + a, gv).
    Intros vret. destruct vret as [inp ib]. simpl fst in *; simpl snd in *.
    rtw_law. forward.
    destruct (eq_dec inp nullval) as [PI|PI].
    { subst inp. forward_if. { ret0. } { rtw_bad. } }
    Intros.
    forward_if. { contradiction. }
    assert_PROP (isptr inp) as Pi by entailer!.
    (* the rest: WMainCopy.w_copy_ok *)
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (w_copy_ok UF gv vcl vol vul bs cb en dn bn compp outp expp q inp ob out ib)].
    unfold w_copy_pre, vl.
    replace (Zlength ib - Zlength out) with a by lia.
    replace (Zlength ib) with (Zlength out + a) by lia.
    entailer!.
Qed.
