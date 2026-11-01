(* Law deflate_bound_split, main: the contents (nondet_bytes, draw_nonzero_bytes, the two zero bytes) and stream_defaults(&s), then the split of s (statements 27..34) (SplitKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.harness.x_deflate_bound_split.code.
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitMain Zlib.proof.harness.deflate_bound_split_v9.SplitKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma pf_nzobj_split sh n p : 0 <= n -> isptr p -> field_compatible (tarray tuchar (n+1)) [] p ->
  @data_at_ DCS.CS sh (tarray tuchar (n+1)) p =
  @data_at_ DCS.CS sh (tarray tuchar n) p *
  @data_at_ DCS.CS sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p).
Proof.
  intros. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh (n+1) n p) by (auto; lia).
  replace (n + 1 - n) with 1 by lia. reflexivity.
Qed.

Lemma pf_nzobj_join sh n (l : list val) p : Zlength l = n ->
  @data_at DCS.CS sh (tarray tuchar n) l p *
  @data_at_ DCS.CS sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p)
  |-- @data_at DCS.CS sh (tarray tuchar (n+1)) (l ++ [Vundef]) p.
Proof.
  intros. rewrite (split2_data_at_Tarray_app n (n+1) sh tuchar l [Vundef] p) by (auto; list_solve).
  replace (n + 1 - n) with 1 by lia. apply derives_refl.
Qed.

Lemma pf_upd_last_zero (l : list Z) :
  upd_Znth (Zlength l) (bytes_rep l ++ [Vundef]) (Vint (Int.zero_ext 8 (Int.repr 0))) = map vi (l ++ [0]).
Proof.
  unfold bytes_rep. rewrite upd_Znth_app2 by (rewrite Zlength_map; list_solve).
  rewrite Zlength_map, Z.sub_diag, map_app. reflexivity.
Qed.

Lemma pf_Zlength_snoc0 (l : list Z) : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app. reflexivity. Qed.

Lemma part_fill {Espec : OracleKind} Bpre Brun sp hp vosn gv bd :
  (forall bs f dt, bs_d bs = bd -> semax Delta_m (A2 Bpre Brun sp hp vosn gv bs f dt) msuf35 Rm_ret) ->
  semax Delta_m (A1 Bpre Brun sp hp vosn gv bd) msuf27 Rm_ret.
Proof.
  intros HK. unfold A1, msuf27, draw_locals. abbreviate_semax. Intros.
  destruct bd as [lv wv mv sv n dlen xlen nl cl mtime dsel hsel text os hcrc xsel nsel csel
                  datap dictp xfp nfp cfp].
  cbn [bd_level bd_wbits bd_mem bd_strategy bd_n bd_dlen bd_xlen bd_nl bd_cl bd_mtime bd_dsel bd_hsel bd_text
       bd_os bd_hcrc bd_xsel bd_nsel bd_csel bd_datap bd_dictp bd_xfp bd_nfp bd_cfp] in *.
  pose proof H as BD. unfold bd_ok in H; cbn [bd_level bd_wbits bd_mem bd_strategy bd_n bd_dlen bd_xlen bd_nl bd_cl bd_mtime bd_dsel bd_hsel bd_text
       bd_os bd_hcrc bd_xsel bd_nsel bd_csel bd_datap bd_dictp bd_xfp bd_nfp bd_cfp] in H.
  destruct H as (Slv & Swv & Smv & Ssv & Hp & Hn & Hdl & Hxl & Hnl & Hcl & Hmt & Hds & Hhs & Htx & Hos & Hhc &
                 Hxs & Hns & Hcs & Pd & Pdi & Px & Pnf & Pcf).
  forward_call (datap, n, Ews).
  { rewrite if_false by (destruct datap; try contradiction; discriminate). cancel. }
  Intros data. rewrite if_false by (destruct datap; try contradiction; discriminate).
  forward_call (dictp, dlen, Ews).
  { rewrite if_false by (destruct dictp; try contradiction; discriminate). cancel. }
  Intros dict. rewrite if_false by (destruct dictp; try contradiction; discriminate).
  forward_call (xfp, xlen, Ews).
  { rewrite if_false by (destruct xfp; try contradiction; discriminate). cancel. }
  Intros xf. rewrite if_false by (destruct xfp; try contradiction; discriminate).
  assert_PROP (field_compatible (tarray tuchar (nl + 1)) [] nfp) as FCn by entailer!.
  rewrite (pf_nzobj_split Ews nl nfp) by (auto; lia). Intros.
  forward_call (nfp, nl, Ews).
  Intros nm.
  sep_apply (pf_nzobj_join Ews nl (bytes_rep nm) nfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
  forward.
  assert_PROP (field_compatible (tarray tuchar (cl + 1)) [] cfp) as FCc by entailer!.
  rewrite (pf_nzobj_split Ews cl cfp) by (auto; lia). Intros.
  forward_call (cfp, cl, Ews).
  Intros cm.
  sep_apply (pf_nzobj_join Ews cl (bytes_rep cm) cfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
  forward.
  forward_call (sp, Tsh, Vundef, Vundef).
  Intros vret. destruct vret as [[[[tin tout] adler] dt] rsv]. cbn [fst snd] in *.
  sep_apply (data_at_Tsh_split t_strm
    (nullval, (vi 0, (vl tin, (nullval, (vi 0, (vl tout, (Vundef, (Vundef,
     (nullval, (nullval, (nullval, (vi dt, (vl adler, vl rsv))))))))))))) sp).
  sep_apply (defaults_split sp Vundef Vundef tin tout adler dt rsv).
  all: try (unfold u64_ok, u64r in *; rep_lia).
  Intros.
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (HK (mkBS (mkBD lv wv mv sv n dlen xlen nl cl mtime dsel hsel text os hcrc xsel nsel
      csel datap dictp xfp nfp cfp) data dict xf nm cm) (mkSF nullval 0 tin nullval 0 tout None Vundef adler) dt
      eq_refl) ].
  unfold A2, draw_locals, hmem, sf_at, obj, api_fields_r.
  cbn [bs_d bd_level bd_wbits bd_mem bd_strategy bd_n bd_dlen bd_xlen bd_nl bd_cl bd_mtime bd_dsel bd_hsel bd_text
       bd_os bd_hcrc bd_xsel bd_nsel bd_csel bd_datap bd_dictp bd_xfp bd_nfp bd_cfp bs_data bs_dict bs_xf bs_nm
       bs_cm sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler af_nin af_ain af_tin af_nout
       af_aout af_tout af_msgv af_adler andb].
  subst n dlen xlen nl cl.
  rewrite !pf_upd_last_zero, !pf_Zlength_snoc0.
  entailer!.
  - unfold bs_ok; cbn [bs_d bd_n bd_dlen bd_xlen bd_nl bd_cl bs_data bs_dict bs_xf bs_nm bs_cm].
    split; [exact BD|].
    unfold bytes.
    assert (B : forall l : list Z, Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
                Forall (fun b => 0 <= b < 256) l)
      by (intros l Fl; eapply Forall_impl; [ | exact Fl ]; cbv beta; rep_lia).
    repeat split; auto.
  - apply derives_refl.
Qed.
