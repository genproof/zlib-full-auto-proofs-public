(* Law res_bound, main: part_head (RBKit.v): if ((choice & 1) && window_bits > 15) gp_assert(deflateSetHeader(&strm, &head) == Z_OK) (msuf 29 -> msuf 30). *)
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

(* a selected object (its bit of choice clear: none, Z_NULL) as the header's optional object and what it does
   not hold: the whole object when not selected, its token otherwise *)
Definition sel_rest (rs : rsetup) (m : Z) (q : val) (l : list Z) : mpred :=
  if has rs m then BoundKit.obj_rest q l else obj q l.

Lemma obj_sel (rs : rsetup) (m : Z) (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l ->
  obj q l |-- opt_obj Ews (selo rs m l) (selp rs m q) * sel_rest rs m q l.
Proof.
  intros HB. unfold selo, selp, sel_rest. destruct (has rs m).
  - unfold obj. rewrite (BoundKit.obj_opt_obj q l HB). apply derives_refl.
  - unfold opt_obj. entailer!.
Qed.

(* the name and the comment with their zero byte are bytes *)
Lemma nz_bytes0 (l : list Z) : nzbytes l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof.
  intros H. apply Forall_app. split; [ | constructor; [lia | constructor]].
  eapply Forall_impl; [ | exact H]. intros; simpl in *; lia.
Qed.

(* the header given to deflateSetHeader is one deflateSetHeader accepts, and its fields are C values *)
Lemma hdr_of_ok (rs : rsetup) (hv : hvals) :
  rs_ok rs -> hv_ok hv -> hdr_ok_w (hdr_of rs hv) /\ gzh_ok (hdr_of rs hv).
Proof.
  intros OK HV. unfold rs_ok in OK. pose proof str_max_range as Hsm.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & Hxl & Hnl & Hcl & _ & _ & _ & _ & Hxz & Hxb & Hnz & Hnb & Hcz & Hcb & _).
  destruct HV as (Htx & Hmt & Hos & Hhc). unfold s32, u32r in *.
  split.
  - unfold hdr_ok_w, hdr_of, selo; cbn [gz_text gz_time gz_os gz_extra gz_extra_len gz_name gz_comment gz_hcrc].
    split; [ unfold s32; lia | ]. split; [ unfold s32; lia | ]. split; [ unfold s32; lia | ].
    split; [ unfold u32r; lia | ]. split; [ lia | ]. split; [ | split ].
    + intros x Ex. destruct (has rs 2); inversion Ex; subst; auto.
    + unfold cstr_ok_w. intros l El. destruct (has rs 4); inversion El; subst.
      exists (r_nm rs). split; [ reflexivity | ]. split; [ lia | exact Hnb ].
    + unfold cstr_ok_w. intros l El. destruct (has rs 8); inversion El; subst.
      exists (r_cm rs). split; [ reflexivity | ]. split; [ lia | exact Hcb ].
  - unfold gzh_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra_len gz_hcrc]. rep_lia.
Qed.

(* head's stored fields and the three selected objects: the header [hdr_of rs hv] *)
Lemma head_stores (rs : rsetup) (hv : hvals) (hp : val) :
  Forall (fun x => 0 <= x < 256) (r_xf rs) -> Forall (fun x => 0 <= x < 256) (r_nm rs ++ [0]) ->
  Forall (fun x => 0 <= x < 256) (r_cm rs ++ [0]) -> gzh_ok (hdr_of rs hv) ->
  data_at Ews t_gzh (hval rs hv) hp *
  obj (r_xp rs) (r_xf rs) * obj (r_np rs) (r_nm rs ++ [0]) * obj (r_cp rs) (r_cm rs ++ [0])
  |-- gzh_at Ews (hdr_of rs hv) hp (selp rs 2 (r_xp rs)) (selp rs 4 (r_np rs)) (selp rs 8 (r_cp rs)) *
      BoundKit.gzh_pad hp *
      sel_rest rs 2 (r_xp rs) (r_xf rs) * sel_rest rs 4 (r_np rs) (r_nm rs ++ [0]) *
      sel_rest rs 8 (r_cp rs) (r_cm rs ++ [0]).
Proof.
  intros Bx Bn Bc Gok.
  sep_apply (obj_sel rs 2 (r_xp rs) (r_xf rs) Bx).
  sep_apply (obj_sel rs 4 (r_np rs) (r_nm rs ++ [0]) Bn).
  sep_apply (obj_sel rs 8 (r_cp rs) (r_cm rs ++ [0]) Bc).
  sep_apply (BoundKit.gzh_of_stores (hdr_of rs hv) hp (selp rs 2 (r_xp rs)) (selp rs 4 (r_np rs))
    (selp rs 8 (r_cp rs)) Vundef Vundef Vundef Vundef Vundef Gok).
  cancel.
Qed.

(* choice & 1 *)
Lemma and1_repr (x : Z) : 0 <= x < 256 -> Int.and (Int.repr x) (Int.repr 1) = Int.repr (Z.land x 1).
Proof.
  intros Hx. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma land1_01 (x : Z) : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  assert (E : Z.land x 1 = x mod 2) by (apply (Z.land_ones x 1); lia).
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma gz_set (s : dstate) (x : option gzh) : d_gzhead (set_d_gzhead s x) = x.
Proof. reflexivity. Qed.

Lemma part_head : part_head_stmt.
Proof.
  intros Espec Bpre Brun gv vh vs rs hv st BF HB.
  destruct st as [s tin tout adler ain aout msg msgv].
  unfold A3, msuf29, POST_m, Delta_m, st_fields, rs_locals. simplify_func_tycontext.
  cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout MainKit.st_msg MainKit.st_msgv app].
  Intros.
  pose proof H as OK. unfold rs_ok in OK.
  destruct OK as (Hl & Hwb & Hm & Hst & Hn & Hch & Hdl & Hxl & Hnl & Hcl & _ & _ & _ & _ & Hxz & Hxb & Hnz & Hnb &
    Hcz & Hcb & Pd & Pdc & Px & Pn & Pc).
  unfold s32 in *.
  pose proof (land1_01 (r_choice rs)) as E1.
  ifpost _t'30 (Int.repr (if hs_of rs then 1 else 0)).
  { forward. entailer!.
    unfold hs_of, has. rewrite and1_repr in H4 by lia.
    destruct E1 as [E1 | E1]; rewrite E1 in *; [ exfalso; apply H4; reflexivity | ]. simpl.
    unfold Int.lt. rewrite ?Int.signed_repr by rep_lia.
    destruct (Z.ltb_spec 15 (r_wbits rs)); destruct (zlt 15 (r_wbits rs)); try lia; reflexivity. }
  { forward. entailer!.
    unfold hs_of, has. rewrite and1_repr in H4 by lia. apply repr_inj_unsigned in H4; [ | rep_lia | rep_lia ].
    rewrite H4. reflexivity. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  forward_if (EX st' : bstrm, EX ghp : val, EX hx : share * val * val * val, EX Hr : mpred,
    A4 Bpre gv vh vs rs st' ghp hx Hr).
  { destruct (hs_of rs) eqn:Ehs; [ | exfalso; apply H4; reflexivity ].
    pose proof Ehs as Ew. unfold hs_of in Ew. apply andb_prop in Ew. destruct Ew as [Eh Ew].
    apply Z.ltb_lt in Ew.
    destruct (hdr_of_ok rs hv H H0) as [Hok Gok].
    destruct (bw_head _ _ BF _ _ _ _ _ s tin tout adler (hdr_of rs hv) (zmk [] 0 ain tin aout tout adler msg)
      H1 Ew Hok) as [Hc Hbp].
    sep_apply (BoundKit.data_at_Tsh_split t_gzh (hval rs hv) vh).
    unfold objs. sep_apply (head_stores rs hv vh Hxb (nz_bytes0 _ Hnb) (nz_bytes0 _ Hcb) Gok).
    unfold api_fields. Intros.
    forward_call (Some s, vs, nullval, nullval, vh, hdr_of rs hv, selp rs 2 (r_xp rs),
      selp rs 4 (r_np rs), selp rs 8 (r_cp rs),
      (Some (set_d_gzhead s (Some (hdr_of rs hv))), zmk [] 0 ain tin aout tout adler msg, Z_OK),
      zmk [] 0 ain tin aout tout adler msg, gv).
    all: try (unfold on_state, c_on_state; rewrite Hc; reflexivity).
    cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
    forward_call Int.one.
    Exists (MainKit.mkSt (set_d_gzhead s (Some (hdr_of rs hv))) tin tout adler ain aout msg msgv) vh
      (Ews, selp rs 2 (r_xp rs), selp rs 4 (r_np rs), selp rs 8 (r_cp rs))
      (data_at_ BoundKit.Ecomp t_gzh vh * BoundKit.gzh_pad vh * sel_rest rs 2 (r_xp rs) (r_xf rs) *
       sel_rest rs 4 (r_np rs) (r_nm rs ++ [0]) * sel_rest rs 8 (r_cp rs) (r_cm rs ++ [0])).
    unfold A4, st_fields, rs_locals, api_fields.
    cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
      MainKit.st_msg MainKit.st_msgv app].
    unfold hdr_at. rewrite gz_set. entailer!.
    { intros s' Hs'. unfold hdr_at. rewrite Hs', gz_set.
      sep_apply (BoundKit.gzh_at_back (hdr_of rs hv) vh (selp rs 2 (r_xp rs)) (selp rs 4 (r_np rs))
        (selp rs 8 (r_cp rs))).
      rewrite (BoundKit.data_at__Tsh_split t_gzh vh). cancel. } }
  { (* no header *)
    forward. Exists (MainKit.mkSt s tin tout adler ain aout msg msgv) nullval (Ews, nullval, nullval, nullval)
      (data_at Tsh t_gzh (hval rs hv) vh).
    unfold A4, st_fields, rs_locals.
    cbn [MainKit.st_s MainKit.st_tin MainKit.st_tout MainKit.st_adler MainKit.st_ain MainKit.st_aout
      MainKit.st_msg MainKit.st_msgv app].
    unfold hdr_at. rewrite H2. entailer!.
    { intros s' Hs'. unfold hdr_at. rewrite Hs', H2. Intros.
      sep_apply (data_at_data_at_ Tsh t_gzh (hval rs hv) vh). cancel. }
    unfold objs. cancel. }
  Intros st' ghp hx Hr. apply HB.
Qed.
