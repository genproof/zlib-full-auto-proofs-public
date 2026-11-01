(* Law deflate_bound, main: part_dict (MainKit.v): dict_set = 0; if (dsel == 0 && wbits <= 15)
   { gp_assert(deflateSetDictionary(&s, dict, dlen) == Z_OK); dict_set = 1; } (msuf 37 -> msuf 39). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.harness.x_deflate_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma part_dict {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vs vh : val)
    (bs : bsetup) (st : bstrm) :
  (forall st', semax Delta_m (A2b Bpre Brun gv vs vh bs st') msuf39 POST_m) ->
  semax Delta_m (A2 Bpre Brun gv vs vh bs st) msuf37 POST_m.
Proof.
  intros HB. destruct st as [s tin tout adler ain aout msg msgv].
  unfold A2, msuf37, POST_m, Delta_m, st_fields, bs_locals. simplify_func_tycontext.
  cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
  Intros.
  assert_PROP (u32_ok ain /\ u32_ok aout) as Ua by (unfold api_fields; entailer!).
  destruct Ua as [Uain Uaout].
  pose proof H as OK. unfold bs_ok in OK. destruct OK as (_ & Hwb & _ & _ & _ & _ & Hdl & _ & _ & _ & _ & Hds & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdz & Hdb & _).
  unfold byte8, s32 in *.
  forward.
  ifpost _t'34 (Int.repr (if ds_of bs then 1 else 0)).
  { forward. entailer!.
    unfold ds_of. rewrite H4. simpl.
    unfold Int.lt. rewrite ?Int.signed_repr by rep_lia.
    destruct (Z.leb_spec (b_wbits bs) 15); destruct (zlt 15 (b_wbits bs)); try lia; reflexivity. }
  { forward. entailer!.
    unfold ds_of. destruct (Z.eqb_spec (b_dsel bs) 0); [ subst; congruence | reflexivity ]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  forward_if (EX st' : bstrm, A2b Bpre Brun gv vs vh bs st').
  { destruct (ds_of bs) eqn:Eds; [ | exfalso; apply H4; reflexivity ].
    pose proof Eds as Ew. unfold ds_of in Ew. apply andb_prop in Ew. destruct Ew as [_ Ew].
    apply Z.leb_le in Ew.
    destruct (bf_dict _ _ H0 _ _ _ _ _ _ _ _ (b_dict bs) ain aout msg H1 Ew Hdb ltac:(lia) Uain Uaout)
      as (s' & z' & Hc & Hgz & Hbp).
    unfold objs.
    change (obj (b_dictp bs) (b_dict bs)) with (Zlib.proof.harness.bound_common.BoundKit.obj (b_dictp bs) (b_dict bs)).
    rewrite (Zlib.proof.harness.bound_common.BoundKit.obj_opt_obj (b_dictp bs) (b_dict bs) Hdb).
    unfold obj. Intros.
    forward_call (Some s, vs, nullval, nullval, ain, tin, nullval, aout, tout, msgv, msg, adler,
                  b_dictp bs, Ews, b_dict bs, (Some s', z', Z_OK), gv).
    { entailer!. rewrite Hdz. reflexivity. }
    { unfold on_state, c_on_state. change (zmk [] 0 ain tin aout tout adler msg)
        with (zcall [] 0 ain tin aout tout adler msg). rewrite Hc. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward_call Int.one.
    forward.
    Exists (mkSt s' (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z') (z_msg z')
              msgv').
    unfold A2b, st_fields, bs_locals.
    cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
    rewrite Eds. entailer!. unfold objs.
    change (obj (b_dictp bs) (b_dict bs)) with (Zlib.proof.harness.bound_common.BoundKit.obj (b_dictp bs) (b_dict bs)).
    rewrite (Zlib.proof.harness.bound_common.BoundKit.obj_opt_obj (b_dictp bs) (b_dict bs) Hdb).
    unfold obj. cancel. }
  { forward. Exists (mkSt s tin tout adler ain aout msg msgv).
    unfold A2b, st_fields, bs_locals.
    cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
    destruct (ds_of bs) eqn:Eds; [ discriminate | ].
    entailer!. }
  apply extract_exists_pre; intro st'. apply HB.
Qed.