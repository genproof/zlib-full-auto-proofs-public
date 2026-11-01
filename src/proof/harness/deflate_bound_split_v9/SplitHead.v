(* Law deflate_bound_split, main: if (hsel == 0 && wbits > 15) { the 13 stores into h; gp_assert(deflateSetHeader(&s, &h) == Z_OK); } (statement 38) (SplitKit.v). *)
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
Require Import Zlib.proof.harness.deflate_bound_split_v9.SplitAf.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

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
  if sel =? 0 then obj q l else obj_rest q l.

Lemma obj_sel (sel : Z) (q : val) (l : list Z) :
  Forall (fun x => 0 <= x < 256) l ->
  obj q l |-- opt_obj Ews (sel_opt sel l) (sel_ptr sel q) * sel_rest sel q l.
Proof.
  intros HB. unfold sel_opt, sel_ptr, sel_rest. destruct (sel =? 0).
  - unfold opt_obj. entailer!.
  - rewrite (obj_opt_obj q l HB). apply derives_refl.
Qed.

(* v6: the name and the comment with their zero byte are bytes *)
Lemma nz_bytes0 (l : list Z) : Forall (fun b => 0 < b < 256) l -> Forall (fun x => 0 <= x < 256) (l ++ [0]).
Proof. intros H. apply Forall_app. split; [ | constructor; [lia | constructor]]. eapply Forall_impl; [ | exact H]. intros; simpl in *; lia. Qed.

Lemma gz_set (s : dstate) (x : option gzh) : d_gzhead (set_d_gzhead s x) = x.
Proof. reflexivity. Qed.

Lemma hdr_of_ok (bs : bsetup) : bs_ok bs -> hdr_ok (hdr_of bs) /\ gzh_ok (hdr_of bs).
Proof.
  intros OK. destruct OK as (BD & _ & _ & Hxl & Hnl & Hcl & _ & _ & Hxb & Hnb & Hcb).
  destruct BD as (_ & _ & _ & _ & _ & _ & _ & Hxr & Hnr & Hcr & Hmt & _ & _ & Htx & Hos & Hhc & _).
  unfold u32r in *.
  pose proof (land1_01 (bd_text (bs_d bs))) as Et. pose proof (land1_01 (bd_hcrc (bs_d bs))) as Ec.
  split.
  - unfold hdr_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra gz_extra_len gz_name gz_comment gz_hcrc].
    split; [ exact Et | ]. split; [ exact Ec | ]. split; [ lia | ]. split; [ unfold u32r; lia | ].
    split; [ lia | ]. split; [ | split ].
    + intros x Ex. destruct (bd_xsel (bs_d bs) =? 0); inversion Ex; subst; auto.
    + unfold cstr_ok. intros l El. destruct (bd_nsel (bs_d bs) =? 0); inversion El; subst.
      exists (bs_nm bs). split; [ reflexivity | ]. split; [ lia | exact Hnb ].
    + unfold cstr_ok. intros l El. destruct (bd_csel (bs_d bs) =? 0); inversion El; subst.
      exists (bs_cm bs). split; [ reflexivity | ]. split; [ lia | exact Hcb ].
  - unfold gzh_ok, hdr_of; cbn [gz_text gz_time gz_os gz_extra_len gz_hcrc]. rep_lia.
Qed.

(* the 13 stores of h and the three selected objects: the header of [hdr_of bs] *)
Lemma head_stores (bs : bsetup) (hp : val) :
  Forall (fun x => 0 <= x < 256) (bs_xf bs) -> Forall (fun x => 0 <= x < 256) (bs_nm bs ++ [0]) ->
  Forall (fun x => 0 <= x < 256) (bs_cm bs ++ [0]) ->
  0 <= bd_text (bs_d bs) < 256 -> 0 <= bd_hcrc (bs_d bs) < 256 -> gzh_ok (hdr_of bs) ->
  data_at Ews t_gzh
     (Vint (Int.and (Int.repr (bd_text (bs_d bs))) (Int.repr 1)),
      (vl (bd_mtime (bs_d bs)),
       (Vint (Int.repr 0),
        (Vint (Int.repr (bd_os (bs_d bs))),
         (sel_ptr (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)),
          (Vint (Int.repr (bd_xlen (bs_d bs))),
           (Vint (Int.repr 0),
            (sel_ptr (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs)),
             (Vint (Int.repr 0),
              (sel_ptr (bd_csel (bs_d bs)) (bd_cfp (bs_d bs)),
               (Vint (Int.repr 0),
                (Vint (Int.and (Int.repr (bd_hcrc (bs_d bs))) (Int.repr 1)),
                 Vint (Int.repr 0))))))))))))) hp *
  obj (bd_xfp (bs_d bs)) (bs_xf bs) * obj (bd_nfp (bs_d bs)) (bs_nm bs ++ [0]) *
  obj (bd_cfp (bs_d bs)) (bs_cm bs ++ [0])
  |-- gzh_at Ews (hdr_of bs) hp (sel_ptr (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)))
        (sel_ptr (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs))) (sel_ptr (bd_csel (bs_d bs)) (bd_cfp (bs_d bs))) *
      gzh_pad hp *
      sel_rest (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)) (bs_xf bs) *
      sel_rest (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs)) (bs_nm bs ++ [0]) *
      sel_rest (bd_csel (bs_d bs)) (bd_cfp (bs_d bs)) (bs_cm bs ++ [0]).
Proof.
  intros Bx Bn Bc Htx Hhc Gok. rewrite !and1_repr by assumption.
  sep_apply (obj_sel (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)) (bs_xf bs) Bx).
  sep_apply (obj_sel (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs)) (bs_nm bs ++ [0]) Bn).
  sep_apply (obj_sel (bd_csel (bs_d bs)) (bd_cfp (bs_d bs)) (bs_cm bs ++ [0]) Bc).
  pose proof (gzh_of_stores (hdr_of bs) hp (sel_ptr (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)))
    (sel_ptr (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs))) (sel_ptr (bd_csel (bs_d bs)) (bd_cfp (bs_d bs)))
    (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) (Vint (Int.repr 0)) Gok) as G.
  set (H0 := hdr_of bs) in *. set (G0 := gzh_at Ews H0 hp _ _ _) in *.
  subst H0. cbv beta zeta iota delta [hdr_of gz_text gz_time gz_os gz_extra gz_extra_len gz_name gz_comment
    gz_hcrc vi] in G.
  unfold sel_opt. sep_apply G. cancel.
Qed.

Ltac selp := unfold sel_ptr; match goal with |- context [?x =? 0] => destruct (Z.eqb_spec x 0) end;
  first [reflexivity | congruence].

Ltac ifptr t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

Lemma part_head {Espec : OracleKind} Bpre Brun sp hp vosn gv bs s f :
  (forall s' f', semax Delta_m (SA Bpre Brun sp hp vosn gv bs (dset bs) true s' f') msuf39 Rm_ret) ->
  semax Delta_m (SA Bpre Brun sp hp vosn gv bs (dset bs) false s f) msuf38 Rm_ret.
Proof.
  intros HB. unfold SA, msuf38, Rm_ret, POST_m, Delta_m, draw_locals. simplify_func_tycontext. Intros.
  pose proof H as OK. destruct OK as (BD & _).
  destruct BD as (_ & Hwb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhs & Htx & Hos & Hhc & Hxs & Hns & Hcs & _).
  unfold s32 in *.
  ifpost _t'39 (Int.repr (if hset bs then 1 else 0)).
  { forward. entailer!.
    unfold hset. destruct (Z.eqb_spec (bd_hsel (bs_d bs)) 0); [ | lia ]. simpl.
    destruct (Z.gtb_spec (bd_wbits (bs_d bs)) 15); destruct (zlt 15 (bd_wbits (bs_d bs))); try lia; reflexivity. }
  { forward. entailer!.
    unfold hset. destruct (Z.eqb_spec (bd_hsel (bs_d bs)) 0); [ congruence | reflexivity ]. }
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  unfold live, hmem, ghp_of. cbn [andb] in *.
  forward_if (EX s' : dstate, EX f' : sfields, SA Bpre Brun sp hp vosn gv bs (dset bs) true s' f').
  { destruct (hset bs) eqn:Ehs;
      [ | exfalso; match goal with Hc : Int.repr 0 <> Int.zero |- _ => apply Hc; reflexivity end ].
    pose proof Ehs as Ew. unfold hset in Ew. apply andb_prop in Ew. destruct Ew as [Eh Ew].
    apply Z.gtb_lt in Ew. apply Z.eqb_eq in Eh.
    unfold hdr_at at 1. rewrite H3. rewrite (data_at__Tsh_split t_gzh hp). Intros.
    forward. forward. forward. forward.
    ifptr _t'35 (sel_ptr (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs))); [ forward; entailer!; selp .. | ].
    forward. forward. forward.
    ifptr _t'36 (sel_ptr (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs))); [ forward; entailer!; selp .. | ].
    forward. forward.
    ifptr _t'37 (sel_ptr (bd_csel (bs_d bs)) (bd_cfp (bs_d bs))); [ forward; entailer!; selp .. | ].
    forward. forward. forward. forward.
    destruct (hdr_of_ok bs H) as [Hok Gok].
    set (z := zmk [] 0 (sf_ain f) (sf_tin f) (sf_aout f) (sf_tout f) (sf_adler f) (sf_msg f)).
    destruct (bf_head _ _ H0 _ _ _ _ _ s (sf_tin f) (sf_tout f) (sf_adler f) (hdr_of bs) z H2 Ew Hok) as [Hc Hbp].
    pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & Bxf & Bnm & Bcm).
    sep_apply (head_stores bs hp Bxf ltac:(apply nz_bytes0; exact Bnm) ltac:(apply nz_bytes0; exact Bcm) Htx Hhc Gok).
    rewrite (sf_split sp f). Intros.
    forward_call (Some s, sp, sf_nin f, nullval, hp, hdr_of bs, sel_ptr (bd_xsel (bs_d bs)) (bd_xfp (bs_d bs)),
      sel_ptr (bd_nsel (bs_d bs)) (bd_nfp (bs_d bs)), sel_ptr (bd_csel (bs_d bs)) (bd_cfp (bs_d bs)),
      (Some (set_d_gzhead s (Some (hdr_of bs))), z, Z_OK), z, gv).
    all: try (cancel; fail).
    all: try (unfold on_state, c_on_state; rewrite Hc; reflexivity).
    cbn [fst snd]. simpl (Z_OK =? Z_OK). cbv iota.
    forward_call Int.one.
    sep_apply (af_join sp (sf_nin f) (sf_ain f) (sf_tin f) (sf_nout f) (sf_aout f) (sf_tout f) (sf_msgv f) (sf_adler f)).
    fold (sf_at sp f).
    Exists (set_d_gzhead s (Some (hdr_of bs))) f.
    unfold SA, live, hmem, ghp_of. rewrite Ehs. cbn [andb].
    unfold hdr_at. rewrite gz_set. unfold hx_of, draw_locals. unfold sel_rest, sel_ptr in *. entailer!. }
  { forward. Exists s f. unfold SA, live, hmem, ghp_of. cbn [andb].
    destruct (hset bs) eqn:Ehs;
      [ exfalso; match goal with Hc : Int.repr 1 = Int.zero |- _ => apply Int.one_not_zero; exact Hc end | ].
    unfold draw_locals. entailer!. }
  Intros s' f'. apply HB.
Qed.
