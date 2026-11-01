(* Law api_short_output (data of any length), main (WMain.v): its middle segment, the call of compress2
   (`compressed_len = compressed_bound; code = compress2(compressed, &compressed_len, original, original_len, level)`,
   the test of Z_MEM_ERROR and `gp_assert(code == Z_OK && compressed_len <= compressed_bound)`), from
   RTC2W.c2w_bound_stmt (the run exists for every allocation outcome and ends with Z_OK or Z_MEM_ERROR) and
   RTC2WFinal.c2w_final_stmt (on Z_OK the output is the zlib stream of the data); then WMainInput.w_input_ok. It also
   holds compressBound's range for the sizes main draws. *)
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
Require Import Zlib.proof.harness.api_short_output.WMainInput.
Require Import Zlib.harness.api_short_output.code.
#[local] Existing Instance Zlib.proof.harness.api_short_output.WLawCS.CS.
Local Open Scope logic.

(* compressBound(n) of a size an object can have (n <= PTRDIFF_MAX): no wrap-around, at least 13 *)
Lemma asw_cb_range n : 0 <= n <= 9223372036854775807 -> 13 <= c_compressBound n <= Int64.max_unsigned.
Proof.
  intros Hn. unfold c_compressBound, compressBound_z.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 12) with 4096. change (2 ^ 14) with 16384. change (2 ^ 25) with 33554432.
  assert (0 <= n / 4096 <= 2251799813685248) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (0 <= n / 16384 <= n / 4096) by (split; [apply Z.div_pos | apply Z.div_le_compat_l]; lia).
  assert (0 <= n / 33554432 <= n / 4096) by (split; [apply Z.div_pos | apply Z.div_le_compat_l]; lia).
  unfold Zlib.proof.huffman.Model.u64. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (n + n / 4096 + n / 16384 + n / 33554432 + 13) n); rep_lia.
Qed.

(* compress2's precondition for destLen = compressBound(n), from c2w_bound_stmt *)
Lemma asw_c2_pre (CB: c2w_bound_stmt) lvl gv dp dlp sp src :
  isptr dp -> is_pointer_or_null sp -> rbytes src -> Zlength src <= 9223372036854775807 -> -1 <= lvl <= 9 ->
  fold_right_and True
    (c2w_pre lvl gv dp (Zrepeat Vundef (c_compressBound (Zlength src))) (c_compressBound (Zlength src)) dlp Ews
       sp src).
Proof.
  intros Hd Hs Hb Hn Hl. assert (0 <= Zlength src) by apply Zlength_nonneg.
  pose proof (asw_cb_range (Zlength src) ltac:(lia)) as Hcb.
  unfold c2w_pre. simpl. unfold Zrepeat. rewrite Zlength_repeat by rep_lia.
  split; [exact Hd | ]. split; [reflexivity | ]. split; [rep_lia | ]. split; [lia | ]. split; [auto | ].
  split; [exact Hs | ]. split; [rep_lia | ]. split; [exact Hb | ]. split; [unfold rs32; lia | ]. split; [ | exact I].
  intros. apply (proj1 (CB src lvl a1 a2 a3 a4 a5 _ Hb Hn Hl)).
Qed.

(* compress2's outcome: Z_OK with the zlib stream of the data, or Z_MEM_ERROR *)
Lemma asw_c2_post (CB: c2w_bound_stmt) (CF: c2w_final_stmt) src lvl a1 a2 a3 a4 a5 r out :
  rbytes src -> Zlength src <= 9223372036854775807 -> -1 <= lvl <= 9 ->
  c2_res src (c_compressBound (Zlength src)) lvl a1 a2 a3 a4 a5 Zlib.proof.deflate.DSpec9.zrst0 r out ->
  (r = Z_OK \/ r = Z_MEM_ERROR) /\ (r = Z_OK -> Zlib.proof.roundtrip.RTFinal.dfinal [] 1 15 None src out).
Proof.
  intros Hb Hn Hl Hr. split.
  - exact (proj1 (proj2 (CB src lvl a1 a2 a3 a4 a5 _ Hb Hn Hl) r out Hr)).
  - exact (CF src lvl a1 a2 a3 a4 a5 _ r out Hb Hn Hl Hr).
Qed.

(* the statements from `compressed_len = compressed_bound` *)
Definition w_mid : statement :=
  ltac:(let x := eval cbv beta iota zeta delta [w_drop w_chain f_main fn_body] in
          (w_drop 12 (w_chain (fn_body f_main))) in exact x).

(* before `compressed_len = compressed_bound`: the inputs drawn (original bs, decompressed_size cap, level v - 1), the
   four objects made (original_copy the copy of the data); the output space outp of cap bytes, Z_NULL (dnull) only when
   cap = 0 *)
Definition w_mid_pre (gv : globals) (vcl vol vul : val) (bs : list Z) (cap v : Z) (datap compp outp expp : val)
    (ob : list Z) (dnull : bool) : environ -> mpred :=
  PROP (is_bytes bs; 1 <= Zlength bs <= 9223372036854775807; 0 <= cap <= Zlength bs - 1; 0 <= v <= 10;
        Zlength ob = cap; if dnull then outp = nullval else outp <> nullval;
        dnull = true -> cap = 0; isptr compp; isptr datap; isptr expp; dnull = false -> isptr outp)
  LOCAL (temp _decompressed outp; temp _compressed compp; temp _original_copy expp; temp _original datap;
         temp _compressed_bound (Vlong (Int64.repr (c_compressBound (Zlength bs))));
         temp _level (Vint (Int.repr (v - 1))); temp _decompressed_size (Vlong (Int64.repr cap));
         temp _original_len (Vlong (Int64.repr (Zlength bs)));
         lvar _source_consumed_len tulong vul; lvar _decompressed_len tulong vol; lvar _compressed_len tulong vcl; gvars gv)
  SEP (mem_mgr gv;
       if dnull then emp
       else malloc_token Ews (tarray tuchar cap) outp * data_at Ews (tarray tuchar cap) (bytes_rep ob) outp;
       malloc_token Ews (tarray tuchar (c_compressBound (Zlength bs))) compp;
       data_at_ Ews (tarray tuchar (c_compressBound (Zlength bs))) compp;
       malloc_token Ews (tarray tuchar (Zlength bs)) datap;
       data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) datap;
       malloc_token Ews (tarray tuchar (Zlength bs)) expp;
       data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) expp;
       Zlib.proof.inflate.Callees.zfuncs gv; data_at_ Tsh tulong vul; data_at_ Tsh tulong vol;
       data_at_ Tsh tulong vcl; deflate_globals gv; cversion_lit gv; tables_rep Ers gv; version_lit gv;
       uversion_lit gv).

Lemma w_mid_ok {Espec : OracleKind} (CB : c2w_bound_stmt) (CF : c2w_final_stmt) (UF : uw_theory_stmt)
    gv vcl vol vul bs cap v datap compp outp expp ob dnull :
  semax Delta_w (w_mid_pre gv vcl vol vul bs cap v datap compp outp expp ob dnull) w_mid POST_wB.
Proof.
  unfold w_mid, w_mid_pre, POST_wB, POST_w. abbreviate_semax.
  Intros.
  rename H into H2, H0 into Hn, H1 into H, H2 into H0, H4 into Hdn, H5 into Hd0, Pcompp into Pc,
    Pdatap into Pd, Pexpp into Pe, H6 into Po.
  pose proof (asw_cb_range (Zlength bs) ltac:(rep_lia)) as Hcb.
  set (cb := c_compressBound (Zlength bs)) in *.
  (* compressed_len = compressed_bound;
     code = compress2(compressed, &compressed_len, original, original_len, level) *)
  forward.
  replace (data_at_ Ews (tarray tuchar cb) compp) with (data_at Ews (tarray tuchar cb) (Zrepeat Vundef cb) compp)
    by reflexivity.
  assert (Hrb: rbytes bs) by (eapply Forall_impl; [ | exact H2]; simpl; intros; rep_lia).
  change (data_at Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) datap)
    with (data_at Ews (tarray tuchar (Zlength bs)) (map vi bs) datap).
  rewrite <- (asw_bytes_compress Ews cb _ compp), <- (asw_bytes_compress Ews (Zlength bs) _ datap),
    <- (asw_ulong_compress Tsh _ vcl).
  rewrite <- (c2_src_obj Ews datap bs Pd).
  forward_call (gv, compp, Zrepeat Vundef cb, cb, vcl, Ews, datap, bs, v - 1).
  asw_sep_cancel c2w_sep_pre.
  apply (asw_c2_pre CB); [exact Pc | destruct datap; try contradiction; exact I | exact Hrb | rep_lia | lia].
  unfold c2w_sep_post. simpl app.
  Intros vret. destruct vret as [[[[[[a1 a2] a3] a4] a5] r] out]. simpl fst in *; simpl snd in *.
  asw_law.
  match goal with H: c2_res _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into Hc2 end.
  destruct (asw_c2_post CB CF bs (v - 1) a1 a2 a3 a4 a5 r out Hrb ltac:(rep_lia) ltac:(lia) Hc2) as (Hr & Hok).
  change (vi r) with (Vint (Int.repr r)).
  (* if (code == Z_MEM_ERROR) return 0; *)
  forward_if.
  { ret0. }
  (* compress2 returned Z_OK *)
  assert (r = Z_OK).
  { destruct Hr as [Hr | Hr]; [exact Hr | ].
    subst r. exfalso. match goal with H: Int.repr Z_MEM_ERROR <> _ |- _ => apply H; reflexivity end. }
  subst r. specialize (Hok eq_refl). clear Hr.
  (* gp_assert(code == Z_OK && compressed_len <= compressed_bound) *)
  ifpost _t'13 (Int.repr 1).
  { forward. forward. entailer!.
    unfold Int64.cmpu, Int64.ltu. rewrite !Int64.unsigned_repr by (pose proof (Zlength_nonneg out); rep_lia).
    destruct (zlt _ _); [lia | reflexivity]. }
  { asw_bad. }
  forward_call (Int.repr 1).
  (* the rest: WMainInput.w_input_ok *)
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (w_input_ok UF gv vcl vol vul bs cap cb compp outp expp ob dnull out)].
  unfold w_input_pre. entailer!.
Qed.
