(* Law deflate_bound, main: part_run (MainKit.v): the stream's input and output fields, r = deflate(&s,
   Z_FINISH) and its checks, deflateEnd(&s), return 0 (msuf 45 -> the end). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.deflate_bound.MainKit.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma pr_af_fold (sp ni : val) (ai ti : Z) (no : val) (ao to : Z) (m : val) (ad : Z) :
  u32_ok ai -> u64_ok ti -> u32_ok ao -> u64_ok to -> u64_ok ad ->
  field_at Ews t_strm (DOT deflate.code._next_in) ni sp *
  field_at Ews t_strm (DOT deflate.code._avail_in) (vi ai) sp *
  field_at Ews t_strm (DOT deflate.code._total_in) (vl ti) sp *
  field_at Ews t_strm (DOT deflate.code._next_out) no sp *
  field_at Ews t_strm (DOT deflate.code._avail_out) (vi ao) sp *
  field_at Ews t_strm (DOT deflate.code._total_out) (vl to) sp *
  field_at Ews t_strm (DOT deflate.code._msg) m sp *
  field_at Ews t_strm (DOT deflate.code._adler) (vl ad) sp
  |-- api_fields sp ni ai ti no ao to m ad.
Proof. intros. unfold api_fields. entailer!. Qed.

Lemma pr_data_at_ (b : Z) (p : val) :
  0 <= b ->
  @data_at_ DCS.CS Ews (tarray tuchar b) p =
  @data_at DCS.CS Ews (tarray tuchar (Zlength (Zrepeat Vundef b))) (Zrepeat Vundef b) p.
Proof. intros. rewrite Zlength_Zrepeat by lia. reflexivity. Qed.

Lemma pr_dstream_sp (lvl : Z) (os : option dstate) (sp ghp spp : val) (gv : globals) :
  dstream_sp lvl os sp ghp spp gv |-- dstream lvl os sp ghp gv.
Proof. rewrite dstream_sp_eq. Exists spp. cancel. Qed.

(* the stream's memory after deflateEnd, whatever it returned, back to the local's Tsh: needs the stream's
   padding, which the kit's srest holds (srest := data_at_ (Share.comp Ews) t_strm vs * BoundKit.strm_pad vs);
   then by BoundKit.dstream_end_data_at_ / dstream_none_data_at_ and data_at__Tsh_split *)
Lemma run_close (o : option dstate) (s' : dstate) (vs : val) (gv : globals) (nin : val) (ain tin : Z)
    (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  match o with None => dstream 2 None vs nullval gv | Some _ => dstream_end (Some s') vs gv end *
  api_fields vs nin ain tin nout aout tout msgv adler * srest vs
  |-- data_at_ Tsh t_strm vs * TT.
Proof.
  unfold srest.
  destruct o;
    [ sep_apply (Zlib.proof.harness.bound_common.BoundKit.dstream_end_data_at_ (Some s') vs gv nin ain tin nout
                   aout tout msgv adler)
    | sep_apply (Zlib.proof.harness.bound_common.BoundKit.dstream_none_data_at_ vs nullval gv nin ain tin nout
                   aout tout msgv adler) ];
  rewrite (Zlib.proof.harness.bound_common.BoundKit.data_at__Tsh_split t_strm vs);
  unfold Zlib.proof.harness.bound_common.BoundKit.Ecomp; cancel.
Qed.

Lemma part_run {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vs vh : val)
    (bs : bsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred) (b : Z) (obp : val) :
  ob_dstream_to_end ->
  semax Delta_m (A4 Bpre Brun gv vs vh bs st ghp hx Hr b obp) msuf45 POST_m.
Proof.
  intros HOB.
  unfold msuf45, A4.
  abbreviate_semax.
  Intros.
  pose proof H as BS.
  destruct BS as (_ & _ & _ & _ & _ & Hn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                  Hdl & Hdb & _ & _ & _ & _ & _ & _ & _ & _ & Pd & _).
  destruct (bf_once _ _ H0 (b_n bs) b (st_s st) (st_tin st) (st_tout st) (st_adler st) (b_data bs) (st_msg st)
              H1 Hdb Hdl) as (s' & z' & Hrun & Ha & Ht & Hg).
  unfold st_fields, api_fields. Intros.
  forward. forward. forward. forward.
  replace (Int64.Z_mod_modulus b) with b by (rewrite Int64.Z_mod_modulus_eq, Z.mod_small; rep_lia).
  forward_call Int.one.
  { entailer!. arg_cmp. }
  rewrite dstream_sp_eq. Intros sp.
  unfold obj.
  rewrite (pr_data_at_ b obp) by lia.
  change (@malloc_token DCS.CS Ews (tarray tuchar b) obp) with (wv_at (WVtok (tarray tuchar b)) obp).
  sep_apply (pr_af_fold vs (b_datap bs) (b_n bs) (st_tin st) obp b (st_tout st) (st_msgv st) (st_adler st)).
  { unfold u32_ok; rep_lia. }
  replace (api_fields vs (b_datap bs) (b_n bs) (st_tin st) obp b (st_tout st) (st_msgv st) (st_adler st))
    with (api_fields vs (offset_val 0 (b_datap bs)) (b_n bs) (st_tin st) obp (Zlength (Zrepeat Vundef b))
            (st_tout st) (st_msgv st) (st_adler st))
    by (rewrite isptr_offset_val_zero, Zlength_Zrepeat by (auto; lia); reflexivity).
  forward_call (Some (st_s st), vs, ghp, sp, hx, b_datap bs, Ews, b_data bs, 0, b_n bs, st_tin st, obp,
                Zrepeat Vundef b, WVtok (tarray tuchar b), st_tout st, st_msgv st, st_msg st, st_adler st,
                Z_FINISH, (Some s', z', Z_STREAM_END), gv).
  { rewrite Zlength_Zrepeat by lia. split; [| split; [| split]].
    - intros ->. simpl. lia.
    - unfold s32_ok, Z_FINISH. rep_lia.
    - unfold strm_ranges, zmk; simpl. rewrite ?Hdl. unfold bytes in Hdb. unfold u32_ok, u64_ok in *.
      rewrite Zlength_nil. repeat split; auto; rep_lia.
    - exists (fun f => f). split; [ apply ef_ok_id | ].
      unfold on_state, c_on_state. rewrite c_deflate_g_id.
      change (zmk ?a ?c ?d ?e ?f ?g ?h ?i) with (zcall a c d e f g h i). rewrite Hrun. reflexivity. }
  simpl fst; simpl snd. Intros msgv'.
  forward_call Int.one.
  unfold api_fields. Intros.
  forward. forward_call Int.one.
  { entailer!. rewrite Ha. reflexivity. }
  forward. forward_call Int.one.
  { entailer!. unfold u64_ok in *. arg_cmp. }
  sep_apply (pr_dstream_sp 2 (Some s') vs ghp sp gv).
  sep_apply (HOB (Some s') vs ghp gv).
  assert (Hend : exists r, c_deflateEnd s' z' = Some r)
    by (unfold c_deflateEnd; destruct (bad_state s'); eauto).
  destruct Hend as [r Hend].
  forward_call (Some s', vs, offset_val (z_next_in z') (b_datap bs), z', r, gv).
  sep_apply (pr_af_fold vs (offset_val (z_next_in z') (b_datap bs)) (z_avail_in z') (z_total_in z')
               (offset_val (Zlength (z_out z')) obp) (z_avail_out z') (z_total_out z') msgv' (z_adler z')).
  sep_apply (run_close (fst (fst r)) s' vs gv (offset_val (z_next_in z') (b_datap bs)) (z_avail_in z')
               (z_total_in z') (offset_val (Zlength (z_out z')) obp) (z_avail_out z') (z_total_out z') msgv'
               (z_adler z')).
  sep_apply (H4 (st_s st) eq_refl).
  forward.
  Exists (Int.repr 0). entailer!.
Qed.
