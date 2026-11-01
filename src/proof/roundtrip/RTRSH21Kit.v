(* Law deflate_roundtrip (gzip header, part H21): helpers of RTRSH21.rmh_seg21 (R->h as the field h of struct
   drun for main's reads, bytes_same's buffers, struct drun at main's return). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec Zlib.proof.roundtrip.RTRRunKit Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRMainSpec.
Require Import Zlib.proof.roundtrip.RTIIface.
Require Import Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTHIfDefs.
Require Import Zlib.harness.x_deflate_roundtrip.code.
Require Import Zlib.proof.roundtrip.RTRMKit Zlib.proof.roundtrip.RTRSKit.
Require Zlib.proof.uncompr.URunFrame.
Require Zlib.proof.roundtrip.RTRRunMem.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

(* as RTRRunOpts.h_field_dcs / gzh_split *)
Lemma rmh_h_field_dcs (Rp : val) (v : reptype t_gzh) :
  field_at Ews t_drun (DOT _h) v Rp = @data_at DCS.CS Ews t_gzh v (hp_of Rp).
Proof.
  rewrite field_at_data_at. unfold hp_of. change (nested_field_type t_drun (DOT _h)) with t_gzh.
  symmetry. apply equal_f. apply (@data_at_change_composite _ _ CC_dcs); [apply JMeq_refl | reflexivity].
Qed.

Lemma rmh_gzh_split (hp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) :
  @data_at DCS.CS Ews t_gzh (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) hp =
  @field_at DCS.CS Ews t_gzh (DOT _text) a1 hp * @field_at DCS.CS Ews t_gzh (DOT _time) a2 hp *
  @field_at DCS.CS Ews t_gzh (DOT _xflags) a3 hp * @field_at DCS.CS Ews t_gzh (DOT _os) a4 hp *
  @field_at DCS.CS Ews t_gzh (DOT _extra) a5 hp * @field_at DCS.CS Ews t_gzh (DOT _extra_len) a6 hp *
  @field_at DCS.CS Ews t_gzh (DOT _extra_max) a7 hp * @field_at DCS.CS Ews t_gzh (DOT _name) a8 hp *
  @field_at DCS.CS Ews t_gzh (DOT _name_max) a9 hp * @field_at DCS.CS Ews t_gzh (DOT _comment) a10 hp *
  @field_at DCS.CS Ews t_gzh (DOT _comm_max) a11 hp * @field_at DCS.CS Ews t_gzh (DOT _hcrc) a12 hp *
  @field_at DCS.CS Ews t_gzh (DOT _done) a13 hp * gzh_pad hp.
Proof.
  unfold gzh_pad. unfold_data_at (@data_at DCS.CS _ _ _ hp). apply pred_ext; cancel.
Qed.

(* a whole object as bytes_same's buffer *)
Lemma rmh_cb (p : val) (l : list Z) (n : Z) (c : list val) :
  isptr p -> Forall (fun x => 0 <= x < 256) l -> n = Zlength l -> c = byte_vals l ->
  cbuf_ok false p Ews p 0 n n c l.
Proof.
  intros Hp Hb -> ->. unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
  split3; [ reflexivity | auto with share | ]. split3; [ lia | lia | ]. split3; [ lia | | ].
  - unfold is_bytes. eapply Forall_impl; [ | exact Hb]. intros; simpl in *; rep_lia.
  - rewrite sublist_same by (unfold byte_vals; rewrite ?Zlength_map; lia). reflexivity.
Qed.

Lemma rmh_nz0 (l : list Z) : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app. reflexivity. Qed.

(* struct drun at main's return: the fields, R->h and main's half *)
Lemma rmh_R_ret rs init wrap wb nf dset hset clen ended Rp (v : reptype t_gzh) :
  drun_rest rs init wrap wb nf dset hset clen ended Rp * field_at Ews t_drun (DOT _h) v Rp *
  data_at_ (Share.comp Ews) t_drun Rp |-- data_at_ Tsh t_drun Rp.
Proof.
  sep_apply (field_at_field_at_ Ews t_drun (DOT _h) v Rp).
  sep_apply (RTRRunMem.drun_fields rs init wrap wb nf dset hset clen ended Rp).
  rewrite <- (data_at__share_join Ews (Share.comp Ews) Tsh) by apply join_comp_Tsh.
  cancel.
Qed.

Lemma rmh_R_ret_flat rs init wrap wb nf dset hset clen ended Rp (v : reptype t_gzh) :
  ltac:(let t := eval cbv beta zeta delta [drun_rest] in
          (drun_rest rs init wrap wb nf dset hset clen ended Rp * field_at Ews t_drun (DOT _h) v Rp *
           data_at_ (Share.comp Ews) t_drun Rp |-- data_at_ Tsh t_drun Rp) in exact t).
Proof. apply rmh_R_ret. Qed.

(* R->h (the header deflateSetHeader got) as the field h of struct drun, for main's reads R.h.text etc. *)
Lemma rmh_h_fold (h : gzh) (xp np cp Rp : val) :
  gzh_at Ews h (hp_of Rp) xp np cp * gzh_pad (hp_of Rp)
  |-- EX v3 : val, EX v7 : val, EX v9 : val, EX v11 : val, EX v13 : val,
      !! gzh_ok h &&
      field_at Ews t_drun (DOT _h)
        (vi (gz_text h), (vl (gz_time h), (v3, (vi (gz_os h), (xp, (vi (gz_extra_len h),
         (v7, (np, (v9, (cp, (v11, (vi (gz_hcrc h), v13)))))))))))) Rp *
      opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp.
Proof.
  unfold gzh_at. Intros v13 v11 v9 v7 v3. Exists v3 v7 v9 v11 v13.
  rewrite rmh_h_field_dcs, rmh_gzh_split.
  entailer!.
Qed.

(** ** The header checks (the then-branch of `if (R.head_set)`), in five parts *)
Definition rmh_chk (s : statement) : statement :=
  match s with Ssequence (Ssequence _ (Sifthenelse _ b _)) _ => b | _ => Sskip end.
Definition chk21 : statement := ltac:(let x := eval cbv beta iota delta [rmh_chk seg21] in (rmh_chk seg21) in exact x).
Definition chkX1 : statement := ltac:(let x := eval cbv beta iota delta [rm_first chk21] in (rm_first chk21) in exact x).
Definition chkX2 : statement :=
  ltac:(let x := eval cbv beta iota delta [rm_first rm_second chk21] in (rm_first (rm_second chk21)) in exact x).
Definition chkX3 : statement :=
  ltac:(let x := eval cbv beta iota delta [rm_first rm_second chk21] in (rm_first (rm_second (rm_second chk21))) in
        exact x).
Definition chkX4 : statement :=
  ltac:(let x := eval cbv beta iota delta [rm_first rm_second chk21] in
          (rm_first (rm_second (rm_second (rm_second chk21)))) in exact x).
Definition chkX5 : statement :=
  ltac:(let x := eval cbv beta iota delta [rm_first rm_second chk21] in
          (rm_second (rm_second (rm_second (rm_second chk21)))) in exact x).

Lemma chk21_eq : chk21 = Ssequence chkX1 (Ssequence chkX2 (Ssequence chkX3 (Ssequence chkX4 chkX5))).
Proof. reflexivity. Qed.

(* the state during the header checks: R->h, the fields of R main reads, ih with the header inflate reported, its
   buffers and R's objects xf, nf_, cf (at the compspecs of bytes_same), and the rest (F1..F4) *)
Definition PH21 (rs : rsetup) (vR vs vt vih : val) (gv : globals) (v3 v7 v9 v11 v13 : val) (xfl : Z)
    (xb nb cb : val) (F1 F2 F3 F4 : mpred) : environ -> mpred :=
  PROP ()
  LOCAL (temp _t'31 (vi 1); lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih;
         gvars gv)
  SEP (field_at Ews t_drun (DOT _h)
         (vi (Z.land (rs_text rs) 1), (vl (rs_mtime rs), (v3, (vi (rs_os rs), (rs_xfp rs,
          (vi (Zlength (rs_xf rs)), (v7, (rs_nfp rs, (v9, (rs_cfp rs, (v11, (vi (Z.land (rs_hcrc rs) 1),
           v13)))))))))))) vR;
       field_at Ews t_drun (DOT _xf) (rs_xfp rs) vR;
       field_at Ews t_drun (DOT _nf_) (rs_nfp rs) vR;
       field_at Ews t_drun (DOT _cf) (rs_cfp rs) vR;
       field_at Ews t_drun (DOT _xlen) (vi (Zlength (rs_xf rs))) vR;
       field_at Ews t_drun (DOT _nl) (vi (Zlength (rs_nm rs))) vR;
       field_at Ews t_drun (DOT _cl) (vi (Zlength (rs_cm rs))) vR;
       data_at Tsh t_gzhL
         (Vint (Int.repr (Z.land (rs_text rs) 1)), (Vlong (Int64.repr (rs_mtime rs)), (Vint (Int.repr xfl),
          (Vint (Int.repr (rs_os rs)), (xb, (Vint (Int.repr (Zlength (rs_xf rs))),
          (Vint (Int.repr (Zlength (rs_xf rs))), (nb, (Vint (Int.repr (Zlength (rs_nm rs) + 1)), (cb,
          (Vint (Int.repr (Zlength (rs_cm rs) + 1)), (Vint (Int.repr (Z.land (rs_hcrc rs) 1)),
           Vint (Int.repr 1))))))))))))) vih;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_xf rs))) (byte_vals (rs_xf rs)) xb;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_xf rs))) (map vi (rs_xf rs)) (rs_xfp rs);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_nm rs) + 1)) (byte_vals (rs_nm rs ++ [0])) nb;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_nm rs) + 1)) (map vi (rs_nm rs ++ [0]))
         (rs_nfp rs);
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_cm rs) + 1)) (byte_vals (rs_cm rs ++ [0])) cb;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (rs_cm rs) + 1)) (map vi (rs_cm rs ++ [0]))
         (rs_cfp rs);
       F1; F2; F3; F4).

(* the pure facts the parts use *)
Definition PH21_ok (rs : rsetup) (xb nb cb : val) : Prop :=
  rs_ok rs /\ isptr xb /\ isptr nb /\ isptr cb.

Lemma nz_bytes0' (l : list Z) : Forall (fun b => 0 < b < 256) l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof.
  intros H. apply Forall_app; split.
  - eapply Forall_impl; [| exact H]. simpl; intros; lia.
  - repeat constructor; lia.
Qed.

(** ** After the header checks: inflateEnd(&t); return 0; *)
Definition tail21 : statement := ltac:(let x := eval cbv beta iota delta [rm_second seg21] in (rm_second seg21) in exact x).

Definition PT21 (vR vs vt vih : val) (gv : globals) (z1 : zfields) (L1 : live) : environ -> mpred :=
  PROP ()
  LOCAL (lvar _R t_drun vR; lvar _s t_strmL vs; lvar _t t_strmL vt; lvar _ih t_gzhL vih; gvars gv)
  SEP (istream gv Tsh vt z1 (Some L1); data_at_ Tsh t_drun vR; data_at_ Tsh t_strmL vs; data_at_ Tsh t_gzhL vih;
       mem_mgr gv; zfuncs gv; TT).
