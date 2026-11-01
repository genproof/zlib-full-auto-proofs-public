(* Law deflate_bound, main: part_head (MainKit.v): if (hsel == 0 && wbits > 15) { the fields of the local
   gz_header h; gp_assert(deflateSetHeader(&s, &h) == Z_OK); } (msuf 39 -> msuf 40). *)
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

(* the memory facts of h (the same as bound_common/BoundKit.v's, proved here so that this part stands alone) *)
Definition Ecomp : share := Share.comp Ews.

Lemma data_at__Tsh_split {cs : compspecs} (t : type) (q : val) :
  @data_at_ cs Tsh t q = @data_at_ cs Ews t q * @data_at_ cs Ecomp t q.
Proof. symmetry. apply data_at__share_join. apply join_comp_Tsh. Qed.

Definition obj_rest (q : val) (l : list Z) : mpred :=
  if Zlength l =? 0 then emp else malloc_token Ews (tarray tuchar (Zlength l)) q.

Lemma obj_opt_obj (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l -> MainKit.obj q l = opt_obj Ews (Some l) q * obj_rest q l.
Proof.
  intros HB. unfold MainKit.obj, opt_obj, obj_rest. rewrite prop_true_andp by exact HB. destruct (Zlength l =? 0) eqn:E; [apply Z.eqb_eq in E; rewrite E |];
  apply pred_ext; cancel.
Qed.

Definition gzh_pad (hp : val) : mpred := spacer Ews 4 8 hp * spacer Ews 52 56 hp * spacer Ews 76 80 hp.

Lemma gzh_of_stores (h : gzh) (hp xp np cp xv xm nm cm dn : val) :
  gzh_ok h ->
  data_at Ews t_gzh (vi (gz_text h), (vl (gz_time h), (xv, (vi (gz_os h), (xp, (vi (gz_extra_len h),
    (xm, (np, (nm, (cp, (cm, (vi (gz_hcrc h), dn)))))))))))) hp *
  opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp
  |-- gzh_at Ews h hp xp np cp * gzh_pad hp.
Proof.
  intros. unfold gzh_at, gzh_pad. unfold_data_at (data_at _ _ _ hp). Exists dn cm nm xm xv.
  entailer!.
Qed.

Lemma gzh_at_back (h : gzh) (hp xp np cp : val) :
  gzh_at Ews h hp xp np cp * gzh_pad hp
  |-- data_at_ Ews t_gzh hp *
      opt_obj Ews (gz_extra h) xp * opt_obj Ews (gz_name h) np * opt_obj Ews (gz_comment h) cp.
Proof.
  unfold gzh_at, gzh_pad. Intros v1 v2 v3 v4 v5. unfold_data_at (data_at_ _ _ hp). cancel.
Qed.

(* text & 1, hcrc & 1 *)
Lemma and1_repr (x : Z) : 0 <= x < 256 -> Int.and (Int.repr x) (Int.repr 1) = Int.repr (Z.land x 1).
Proof.
  intros Hx. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma land1_01 (x : Z) : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  assert (E : Z.land x 1 = x mod 2) by (apply (Z.land_ones x 1); lia).
  rewrite E. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(* a selected object (sel = 0: none, Z_NULL) as the header's optional object and what it does not hold *)
Definition sel_ptr (sel : Z) (q : val) : val := if sel =? 0 then nullval else q.
Definition sel_opt (sel : Z) (l : list Z) : option (list Z) := if sel =? 0 then None else Some l.
Definition sel_rest (sel : Z) (q : val) (l : list Z) : mpred :=
  if sel =? 0 then MainKit.obj q l else obj_rest q l.

Lemma obj_sel (sel : Z) (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l ->
  MainKit.obj q l |-- opt_obj Ews (sel_opt sel l) (sel_ptr sel q) * sel_rest sel q l.
Proof.
  intros HB. unfold sel_opt, sel_ptr, sel_rest. destruct (sel =? 0).
  - unfold opt_obj. entailer!.
  - rewrite (obj_opt_obj q l HB). apply derives_refl.
Qed.

(* v6: the name and the comment with their zero byte are bytes *)
Lemma nz_bytes0 (l : list Z) : Forall (fun b => 0 < b < 256) l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof. intros H. apply Forall_app. split; [ | constructor; [lia | constructor]]. eapply Forall_impl; [ | exact H]. intros; simpl in *; lia. Qed.

Definition hdr_of (bs : bsetup) : gzh :=
  mkGZ (Z.land (b_text bs) 1) (b_mtime bs) (b_os bs) (sel_opt (b_xsel bs) (b_xf bs)) (b_xlen bs)
    (sel_opt (b_nsel bs) (b_nm bs ++ [0])) (sel_opt (b_csel bs) (b_cm bs ++ [0])) (Z.land (b_hcrc bs) 1).


Lemma gz_set (s : dstate) (x : option gzh) : d_gzhead (set_d_gzhead s x) = x.
Proof. reflexivity. Qed.

Lemma hdr_of_ok (bs : bsetup) : bs_ok bs -> hdr_ok (hdr_of bs) /\ gzh_ok (hdr_of bs).
Proof.
  intros OK. unfold bs_ok in OK.
  destruct OK as (_ & _ & _ & _ & _ & _ & _ & Hxl & Hnl & Hcl & Hmt & _ & _ & Htx & Hos & Hhc & _ & _ & _ &
    _ & _ & _ & _ & Hxz & Hxb & Hnz & Hnb & Hcz & Hcb & _).
  unfold byte8, u32r in *.
  pose proof (land1_01 (b_text bs)) as Et. pose proof (land1_01 (b_hcrc bs)) as Ec.
  split.
  - unfold hdr_ok, hdr_of, sel_opt; cbn [gz_text gz_time gz_os gz_extra gz_extra_len gz_name gz_comment gz_hcrc].
    split; [ exact Et | ]. split; [ exact Ec | ]. split; [ lia | ]. split; [ unfold u32r; lia | ].
    split; [ lia | ]. split; [ | split ].
    + intros x Ex. destruct (b_xsel bs =? 0); inversion Ex; subst; auto.
    + unfold cstr_ok. intros l El. destruct (b_nsel bs =? 0); inversion El; subst.
      exists (b_nm bs). split; [ reflexivity | ]. split; [ lia | exact Hnb ].
    + unfold cstr_ok. intros l El. destruct (b_csel bs =? 0); inversion El; subst.
      exists (b_cm bs). split; [ reflexivity | ]. split; [ lia | exact Hcb ].
  - unfold gzh_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra_len gz_hcrc]. rep_lia.
Qed.

(* the 13 stores of h and the three selected objects: the header of [hdr_of bs] *)
Lemma head_stores (bs : bsetup) (hp : val) :
  Forall (fun x => 0 <= x < 256) (b_xf bs) -> Forall (fun x => 0 <= x < 256) (b_nm bs ++ [0]) ->
  Forall (fun x => 0 <= x < 256) (b_cm bs ++ [0]) ->
  0 <= b_text bs < 256 -> 0 <= b_hcrc bs < 256 -> gzh_ok (hdr_of bs) ->
  data_at Ews t_gzh
     (Vint (Int.and (Int.repr (b_text bs)) (Int.repr 1)),
      (vl (b_mtime bs),
       (Vint (Int.repr 0),
        (Vint (Int.repr (b_os bs)),
         (sel_ptr (b_xsel bs) (b_xfp bs),
          (Vint (Int.repr (b_xlen bs)),
           (Vint (Int.repr 0),
            (sel_ptr (b_nsel bs) (b_nfp bs),
             (Vint (Int.repr 0),
              (sel_ptr (b_csel bs) (b_cfp bs),
               (Vint (Int.repr 0),
                (Vint (Int.and (Int.repr (b_hcrc bs)) (Int.repr 1)),
                 Vint (Int.repr 0))))))))))))) hp *
  MainKit.obj (b_xfp bs) (b_xf bs) * MainKit.obj (b_nfp bs) (b_nm bs ++ [0]) *
  MainKit.obj (b_cfp bs) (b_cm bs ++ [0])
  |-- gzh_at Ews (hdr_of bs) hp (sel_ptr (b_xsel bs) (b_xfp bs)) (sel_ptr (b_nsel bs) (b_nfp bs))
        (sel_ptr (b_csel bs) (b_cfp bs)) * gzh_pad hp *
      sel_rest (b_xsel bs) (b_xfp bs) (b_xf bs) * sel_rest (b_nsel bs) (b_nfp bs) (b_nm bs ++ [0]) *
      sel_rest (b_csel bs) (b_cfp bs) (b_cm bs ++ [0]).
Proof.
  intros Bx Bn Bc Htx Hhc Gok. rewrite !and1_repr by assumption.
  sep_apply (obj_sel (b_xsel bs) (b_xfp bs) (b_xf bs) Bx).
  sep_apply (obj_sel (b_nsel bs) (b_nfp bs) (b_nm bs ++ [0]) Bn).
  sep_apply (obj_sel (b_csel bs) (b_cfp bs) (b_cm bs ++ [0]) Bc).
  sep_apply (gzh_of_stores (hdr_of bs) hp (sel_ptr (b_xsel bs) (b_xfp bs)) (sel_ptr (b_nsel bs) (b_nfp bs))
    (sel_ptr (b_csel bs) (b_cfp bs)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0))
    (Vint (Int.repr 0)) (Vint (Int.repr 0)) Gok).
  cancel.
Qed.

Ltac selp := unfold sel_ptr; match goal with |- context [?x =? 0] => destruct (Z.eqb_spec x 0) end;
  first [reflexivity | congruence].

Ltac ifptr t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Lemma part_head {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vs vh : val)
    (bs : bsetup) (st : bstrm) :
  (forall st' ghp hx Hr, semax Delta_m (A3 Bpre Brun gv vs vh bs st' ghp hx Hr) msuf40 POST_m) ->
  semax Delta_m (A2b Bpre Brun gv vs vh bs st) msuf39 POST_m.
Proof.
  intros HB. destruct st as [s tin tout adler ain aout msg msgv].
  unfold A2b, msuf39, POST_m, Delta_m, st_fields, bs_locals. simplify_func_tycontext.
  cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
  Intros.
  pose proof H as OK. unfold bs_ok in OK.
  destruct OK as (_ & Hwb & _ & _ & _ & _ & _ & Hxl & Hnl & Hcl & Hmt & _ & Hhs & Htx & Hos & Hhc & Hxs & Hns & Hcs &
    _ & _ & _ & _ & Hxz & Hxb & Hnz & Hnb & Hcz & Hcb & _ & _ & Pxf & Pnf & Pcf).
  unfold byte8, s32 in *.
  ifpost _t'39 (Int.repr (if hs_of bs then 1 else 0)).
  { forward. entailer!.
    unfold hs_of. rewrite H4. simpl.
    unfold Int.lt. rewrite ?Int.signed_repr by rep_lia.
    destruct (Z.ltb_spec 15 (b_wbits bs)); destruct (zlt 15 (b_wbits bs)); try lia; reflexivity. }
  { forward. entailer!.
    unfold hs_of. destruct (Z.eqb_spec (b_hsel bs) 0); [ subst; congruence | reflexivity ]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  forward_if (EX st' : bstrm, EX ghp : val, EX hx : share * val * val * val, EX Hr : mpred,
    A3 Bpre Brun gv vs vh bs st' ghp hx Hr).
  { destruct (hs_of bs) eqn:Ehs; [ | exfalso; apply H4; reflexivity ].
    pose proof Ehs as Ew. unfold hs_of in Ew. apply andb_prop in Ew. destruct Ew as [Eh Ew].
    apply Z.ltb_lt in Ew. apply Z.eqb_eq in Eh.
    rewrite data_at__Tsh_split. Intros.
    forward. forward. forward. forward.
    ifptr _t'35 (sel_ptr (b_xsel bs) (b_xfp bs)); [ forward; entailer!; selp .. | ].
    forward. forward. forward.
    ifptr _t'36 (sel_ptr (b_nsel bs) (b_nfp bs)); [ forward; entailer!; selp .. | ].
    forward. forward.
    ifptr _t'37 (sel_ptr (b_csel bs) (b_cfp bs)); [ forward; entailer!; selp .. | ].
    forward. forward. forward. forward.
    destruct (hdr_of_ok bs H) as [Hok Gok].
    destruct (bf_head _ _ H0 _ _ _ _ _ s tin tout adler (hdr_of bs) (zmk [] 0 ain tin aout tout adler msg)
      H1 Ew Hok) as [Hc Hbp].
    unfold objs. sep_apply (head_stores bs vh ltac:(assumption) ltac:(apply nz_bytes0; assumption) ltac:(apply nz_bytes0; assumption) Htx Hhc Gok).
    unfold api_fields. Intros.
    forward_call (Some s, vs, nullval, nullval, vh, hdr_of bs, sel_ptr (b_xsel bs) (b_xfp bs),
      sel_ptr (b_nsel bs) (b_nfp bs), sel_ptr (b_csel bs) (b_cfp bs),
      (Some (set_d_gzhead s (Some (hdr_of bs))), zmk [] 0 ain tin aout tout adler msg, Z_OK),
      zmk [] 0 ain tin aout tout adler msg, gv).
    all: try (unfold on_state, c_on_state; rewrite Hc; reflexivity).
    cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
    forward_call Int.one.
    Exists (mkSt (set_d_gzhead s (Some (hdr_of bs))) tin tout adler ain aout msg msgv) vh
      (Ews, sel_ptr (b_xsel bs) (b_xfp bs), sel_ptr (b_nsel bs) (b_nfp bs), sel_ptr (b_csel bs) (b_cfp bs))
      (data_at_ Ecomp t_gzh vh * gzh_pad vh * sel_rest (b_xsel bs) (b_xfp bs) (b_xf bs) *
       sel_rest (b_nsel bs) (b_nfp bs) (b_nm bs ++ [0]) * sel_rest (b_csel bs) (b_cfp bs) (b_cm bs ++ [0])).
    unfold A3, st_fields, bs_locals, api_fields.
    cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
    unfold hdr_at. rewrite gz_set. entailer!.
    { intros s' Hs'. unfold hdr_at. rewrite Hs', gz_set.
      sep_apply (gzh_at_back (hdr_of bs) vh (sel_ptr (b_xsel bs) (b_xfp bs)) (sel_ptr (b_nsel bs) (b_nfp bs))
        (sel_ptr (b_csel bs) (b_cfp bs))).
      rewrite data_at__Tsh_split. cancel. } }
  { (* no header *)
    forward. Exists (mkSt s tin tout adler ain aout msg msgv) nullval (Ews, nullval, nullval, nullval)
      (data_at_ Tsh t_gzh vh).
    unfold A3, st_fields, bs_locals.
    cbn [st_s st_tin st_tout st_adler st_ain st_aout st_msg st_msgv app].
    unfold hdr_at. rewrite H2. entailer!.
    { intros s' Hs'. unfold hdr_at. rewrite Hs', H2. entailer!. }
    unfold objs. cancel. }
  Intros st' ghp hx Hr. apply HB.
Qed.
