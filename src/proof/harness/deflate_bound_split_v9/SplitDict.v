(* Law deflate_bound_split, main: if (dsel == 0 && wbits <= 15) gp_assert(deflateSetDictionary(&s, dict, dlen) == Z_OK); (statement 37) (SplitKit.v). *)
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

Lemma part_dict {Espec : OracleKind} Bpre Brun sp hp vosn gv bs s f :
  (forall s' f', semax Delta_m (SA Bpre Brun sp hp vosn gv bs (dset bs) false s' f') msuf38 Rm_ret) ->
  semax Delta_m (SA Bpre Brun sp hp vosn gv bs false false s f) msuf37 Rm_ret.
Proof.
  intros HB. destruct f as [nin ain tin nout aout tout msg msgv adler].
  unfold SA, msuf37, Rm_ret, POST_m, Delta_m, draw_locals, live, sf_at. simplify_func_tycontext.
  cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler app].
  Intros.
  match goal with Hp : is_pointer_or_null nin |- _ => rename Hp into Hnin end.
  assert_PROP (u32_ok ain /\ u32_ok aout) as Ua by (unfold api_fields; entailer!).
  destruct Ua as [Uain Uaout].
  pose proof H as OK. unfold bs_ok, bd_ok in OK.
  destruct OK as ((_ & Hwb & _ & _ & _ & _ & Hdl & _ & _ & _ & _ & Hds & _) & _ & Hdz & _ & _ & _ & _ & Hdb & _).
  unfold s32 in *.
  ifpost _t'34 (Int.repr (if dset bs then 1 else 0)).
  { forward. entailer!.
    try (apply repr_inj_unsigned in H5; [ | rep_lia | rep_lia ]).
    unfold dset. rewrite H5. simpl.
    unfold Int.lt. rewrite ?Int.signed_repr by rep_lia.
    destruct (Z.leb_spec (bd_wbits (bs_d bs)) 15); destruct (zlt 15 (bd_wbits (bs_d bs))); try lia; reflexivity. }
  { forward. entailer!.
    unfold dset. destruct (Z.eqb_spec (bd_dsel (bs_d bs)) 0); [ rewrite e in H5; contradiction | reflexivity ]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  simpl andb in H3.
  forward_if (EX s' : dstate, EX f' : sfields, SA Bpre Brun sp hp vosn gv bs (dset bs) false s' f').
  { destruct (dset bs) eqn:Eds; [ | exfalso; apply H5; reflexivity ].
    pose proof Eds as Ew. unfold dset in Ew. apply andb_prop in Ew. destruct Ew as [_ Ew].
    apply Z.leb_le in Ew.
    destruct (bf_dict _ _ H0 _ _ _ _ _ _ _ _ (bs_dict bs) ain aout msg H2 Ew Hdb ltac:(lia) Uain Uaout)
      as (s' & z' & Hc & Hgz & Hbp).
    rewrite (obj_opt_obj (bd_dictp (bs_d bs)) (bs_dict bs) Hdb).
    unfold obj_rest. Intros.
    forward_call (Some s, sp, ghp_of hp bs false, nin, ain, tin, nout, aout, tout, msgv, msg, adler,
                  bd_dictp (bs_d bs), Ews, bs_dict bs, (Some s', z', Z_OK), gv).
    all: try (entailer!; rewrite Hdz; reflexivity).
    { try (split; [ | exact Hnin ]).
      unfold on_state, c_on_state. change (zmk [] 0 ain tin aout tout adler msg)
        with (zcall [] 0 ain tin aout tout adler msg). rewrite Hc. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward_call Int.one.
    Exists s' (mkSF nin (z_avail_in z') (z_total_in z') nout (z_avail_out z') (z_total_out z') (z_msg z')
              msgv' (z_adler z')).
    unfold SA, draw_locals, live, sf_at.
    cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler app].
    simpl andb. rewrite Hgz, H3.
    entailer!. unfold hdr_at. rewrite Hgz, H3.
    rewrite (obj_opt_obj (bd_dictp (bs_d bs)) (bs_dict bs) Hdb). unfold obj_rest. cancel. }
  { forward. Exists s (mkSF nin ain tin nout aout tout msg msgv adler).
    unfold SA, draw_locals, live, sf_at.
    cbn [sf_nin sf_ain sf_tin sf_nout sf_aout sf_tout sf_msg sf_msgv sf_adler app].
    destruct (dset bs) eqn:Eds; [ discriminate | ].
    simpl andb. entailer!. }
  apply extract_exists_pre; intro s'. apply extract_exists_pre; intro f'. apply HB.
Qed.
