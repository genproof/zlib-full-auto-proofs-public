(* Law res_bound, main: part_dict (RBKit.v): if ((choice & 1) && window_bits <= 15) gp_assert(deflateSetDictionary(&strm, dict, (uInt) dict_len) == Z_OK) (msuf 30 -> msuf 31). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.LawFactsW Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Zlib.proof.harness.bound_common.BoundKit Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.res_bound.RBCS Zlib.proof.harness.res_bound.RBString Zlib.proof.harness.res_bound.RBKit.
Require Import Zlib.harness.res_bound.code.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

(* statement 30: when ds_of rs, deflateSetDictionary right after deflateInit2 returns Z_OK (bw_dict) and leaves
   the state's gzhead, hence the header's memory, as it was; otherwise nothing happens *)
Lemma part_dict : part_dict_stmt.
Proof.
  intros Espec Bpre Brun gv vh vs rs st ghp hx Hr BF HB.
  destruct st as [s tin tout adler ain aout msg msgv].
  unfold A4, msuf30, POST_m, Delta_m, MainKit.st_fields, rs_locals. simplify_func_tycontext.
  cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
       MainKit.st_msg MainKit.st_msgv app].
  Intros.
  assert_PROP (u32_ok ain /\ u32_ok aout) as Ua by (unfold api_fields; entailer!).
  destruct Ua as [Uain Uaout].
  pose proof H as OK. unfold rs_ok in OK.
  destruct OK as (_ & Hwb & _ & _ & _ & Hch & Hdl & _ & _ & _ & _ & _ & Hdz & Hdb & _).
  unfold s32 in *.
  ifpost _t'32 (Int.repr (if ds_of rs then 1 else 0)).
  { forward. entailer!.
    rewrite !Int.unsigned_repr in H3' by rep_lia. unfold ds_of, has.
    destruct (Z.eqb_spec (Z.land (r_choice rs) 1) 0); [contradiction | ]. simpl.
    destruct (Z.leb_spec (r_wbits rs) 15); destruct (zlt 15 (r_wbits rs)); try lia; reflexivity. }
  { forward. entailer!.
    apply (f_equal Int.unsigned) in H3. unfold Int.and in H3.
    rewrite (Int.unsigned_repr 1), (Int.unsigned_repr (r_choice rs)) in H3 by rep_lia.
    change 1 with (Z.ones 1) in H3 at 1. rewrite Z.land_ones in H3 by lia.
    pose proof (Z.mod_pos_bound (r_choice rs) (2^1) ltac:(lia)).
    rewrite Int.unsigned_repr in H3 by rep_lia. rewrite <- Z.land_ones in H3 by lia.
    change (Z.ones 1) with 1 in H3. unfold ds_of, has. rewrite H3. reflexivity. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  forward_if (EX st' : bstrm, A5 Bpre gv vh vs rs st' ghp hx Hr).
  { destruct (ds_of rs) eqn:Eds; [ | exfalso; apply H3; reflexivity ].
    pose proof Eds as Ew. unfold ds_of in Ew. apply andb_prop in Ew. destruct Ew as [_ Ew].
    apply Z.leb_le in Ew.
    destruct (bw_dict _ _ BF _ _ _ _ _ _ _ _ (r_dict rs) ain aout msg H0 Ew Hdb ltac:(lia) Uain Uaout)
      as (s' & z' & Hc & Hgz & Hbp).
    unfold obj.
    rewrite (Zlib.proof.harness.bound_common.BoundKit.obj_opt_obj (r_dictp rs) (r_dict rs) Hdb).
    Intros.
    forward_call (Some s, vs, ghp, nullval, ain, tin, nullval, aout, tout, msgv, msg, adler,
                  r_dictp rs, Ews, r_dict rs, (Some s', z', Z_OK), gv).
    { entailer!. rewrite Hdz. simpl. unfold vl, vi. rewrite Int64.Z_mod_modulus_eq, Z.mod_small by rep_lia. reflexivity. }
    { unfold on_state, c_on_state. change (zmk [] 0 ain tin aout tout adler msg)
        with (zcall [] 0 ain tin aout tout adler msg). rewrite Hc. reflexivity. }
    cbn [fst snd]. Intros msgv'.
    forward_call Int.one.
    Exists (MainKit.mkSt s' (z_total_in z') (z_total_out z') (z_adler z') (z_avail_in z') (z_avail_out z')
              (z_msg z') msgv').
    unfold A5, MainKit.st_fields, rs_locals.
    cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
         MainKit.st_msg MainKit.st_msgv app].
    assert (Hh : hdr_at (Some s') ghp hx = hdr_at (Some s) ghp hx) by (unfold hdr_at; rewrite Hgz; reflexivity).
    rewrite Hh.
    rewrite Eds. entailer!.
    { unfold hclose, MainKit.hclose in *. intros s'' E. apply H2. congruence. }
    unfold obj. cancel. }
  { forward. Exists (MainKit.mkSt s tin tout adler ain aout msg msgv).
    unfold A5, MainKit.st_fields, rs_locals.
    cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
         MainKit.st_msg MainKit.st_msgv app].
    destruct (ds_of rs) eqn:Eds; [ discriminate | ].
    entailer!. }
  apply extract_exists_pre; intro st'. apply HB.
Qed.
