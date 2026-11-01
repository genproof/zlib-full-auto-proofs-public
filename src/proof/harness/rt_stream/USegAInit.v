(* Law rt_stream (data of any length), main's setup segment from new_stream on (statements 13-20 of main's body,
   USegAKit.segA_init): new_stream and deflateInit2_ on the compressor, the return when deflateInit2_ runs out of
   memory and gp_assert(code == Z_OK): with parameters in zlib.h's ranges (main's gp_assume) deflateInit2_ returns
   Z_OK or Z_MEM_ERROR (UDFacts.ud_init_code); the stores after Z_OK are USegAStores.sa_stores.  Round 1's
   MainSegAInit.v with the sizes of round 2's harness and the model facts of UDFacts.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.DSpec9.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.harness.rt_stream.UDFacts.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_stream.LawCS.
Require Import Zlib.proof.harness.rt_stream.UMainStmt.
Require Import Zlib.proof.harness.rt_stream.UMainKit.
Require Import Zlib.proof.harness.rt_stream.USegAKit.
Require Import Zlib.proof.harness.rt_stream.USegAStrm.
Require Import Zlib.proof.harness.rt_stream.USegAStores.
Require Import Zlib.harness.rt_stream.code.
Require Zlib.deflate.code.
Require Zlib.proof.harness.deflate_bound.MainInit.
#[local] Existing Instance LawCS.CS.
Local Open Scope logic.

Lemma sa_init {Espec : OracleKind} J gv vc vd va lv wv mv sv data cap bd od be oe bc oc bout oout :
  urts_dfacts J ->
  0 <= lv <= Int.max_unsigned -> 0 <= wv <= Int.max_unsigned -> 0 <= mv <= Int.max_unsigned ->
  0 <= sv <= Int.max_unsigned -> 0 <= Zlength data <= max_size -> 0 <= cap <= max_size -> is_bytes data ->
  rparams_ok (Int.signed (Int.repr lv)) 8 (Int.signed (Int.repr wv)) (Int.signed (Int.repr mv))
    (Int.signed (Int.repr sv)) = true ->
  semax Delta_m (PRE_init gv vc vd va lv wv mv sv data cap bd od be oe bc oc bout oout) segA_init
    (overridePost (EX u : setup, EX l : dls, DI gv vc vd va J u l) POST_m).
Proof.
  intros JF H H0 H1 H2 H3 H4 H6 Hpar0. unfold PRE_init, segA_init, POST_m.
  unfold Delta_m; simplify_func_tycontext. abbreviate_semax.
  rewrite !sa_vi_signed.
  pose proof (Int.signed_range (Int.repr lv)). pose proof (Int.signed_range (Int.repr wv)).
  pose proof (Int.signed_range (Int.repr mv)). pose proof (Int.signed_range (Int.repr sv)).
  set (lvl := Int.signed (Int.repr lv)) in *. set (wb := Int.signed (Int.repr wv)) in *.
  set (mem := Int.signed (Int.repr mv)) in *. set (str := Int.signed (Int.repr sv)) in *.
  clearbody lvl wb mem str.
  rewrite (BoundKit.data_at__Tsh_split t_z vc).
  sep_apply (sa_strm_undef vc).
  forward_call (vc, Ews, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef, Vundef,
                Vundef, Vundef, Vundef, Vundef).
  sep_apply (sa_new_stream_split vc).
  unfold Rm. rewrite sa_version_cs.
  assert (Hr : rs32 lvl /\ rs32 wb /\ rs32 mem /\ rs32 str) by (unfold rs32; rep_lia).
  destruct Hr as (Hlev & Hwb & Hmem & Hstr).
  pose proof (fun a1 a2 a3 a4 a5 => ud_init _ JF lvl wb mem str a1 a2 a3 a4 a5 zrst0 Hlev Hwb Hmem Hstr) as FIN.
  forward_call (vc, lvl, 8, wb, mem, str, gv ___stringlit_rt_stream_1, Ers,
                [49; 46; 51; 46; 50; 0], 112, nullval, Vundef, Vundef, Vundef, Vundef, nullval, Vundef, Vundef, gv).
  { cancel. }
  { split; [unfold s32_ok; rep_lia|]. split; [unfold s32_ok; rep_lia|]. split; [list_solve|]. split; [cbn; rep_lia|].
    intros a1 a2 a3 a4 a5. exact (proj1 (FIN a1 a2 a3 a4 a5)). }
  Intros vret. destruct vret as [[[[[a1 a2] a3] a4] a5] [[os z'] code]]. cbn [fst snd] in *.
  match goal with H : c_deflateInit2_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ |- _ => rename H into HI end.
  change (Znth 0 [49; 46; 51; 46; 50; 0] =? 49) with true in HI; change (112 =? 112) with true in HI.
  Intros msgv'.
  pose proof (ud_init_code _ JF _ _ _ _ _ _ _ _ _ _ _ _ _ Hpar0 HI) as Hcode.
  destruct Hcode as [Hc | Hc]; subst code.
  2:{ (* deflateInit2_ ran out of memory (no state): the local back, return 0 *)
    destruct (Zlib.proof.harness.deflate_bound.MainInit.pi_init_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ HI)
      as [Hc | [Hos _]]; [discriminate Hc | subst os].
    forward_if.
    2:{ exfalso. match goal with H : Int.repr _ <> _ |- _ => apply H; reflexivity end. }
    Intros st za zf op dt.
    sep_apply (sa_fields_back vc nullval (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_total_in z') Vundef)
                 (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_total_out z') Vundef) msgv'
                 (rfv (Z_MEM_ERROR =? DState.Z_OK) (z_adler z') Vundef) (vi 0) nullval (vi 0) st za zf op dt).
    sep_apply (sa_rejoin vc).
    forward. Exists (Int.repr 0). entailer!. }
  destruct (proj2 (FIN _ _ _ _ _) _ _ _ HI eq_refl) as (Hpar & s & -> & HJ).
  forward_if.
  { exfalso. match goal with H : Int.repr _ = _ |- _ => inversion H end. }
  forward_call (Int.one).
  eapply semax_pre;
    [ | exact (sa_stores J gv vc vd va lvl wb mem str data cap bd od be oe bc oc bout oout s z' msgv' JF H3 H4 H6
                 Hlev Hwb Hmem Hstr Hpar HJ H10)].
  unfold PRE_stores. entailer!.
Qed.
