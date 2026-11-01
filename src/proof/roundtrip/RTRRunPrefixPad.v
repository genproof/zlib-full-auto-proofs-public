(* Law deflate_roundtrip (port of deflate_api9/RunPrefixPad.v), deflate_run: the draws, the allocations and R's fields, up to stream_defaults (RunKit.v),
   against kit v2 (struct drun's padding, drun_pad, at the end of drun_rest): run_prefix_pad is RunPrefix.run_prefix_ok
   with A1 replaced by A1p = A1 whose first SEP item is drun_rest .. Rp * (spacer Ews 68 72 Rp * spacer Ews 188 192 Rp)
   (kit v2's A1 after unfolding drun_rest and drun_pad). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.roundtrip.RTXFacts.
Require Import Zlib.proof.roundtrip.RTRCS Zlib.proof.roundtrip.RTRRunSpec
               Zlib.proof.roundtrip.RTRApiConv Zlib.proof.roundtrip.RTRRunKit
               Zlib.proof.roundtrip.RTRDrunSplit.
Require Import Zlib.harness.x_deflate_roundtrip.code.
#[local] Existing Instance RTRCS.CS.
Local Open Scope logic.

Lemma nzobj_split sh n p : 0 <= n -> isptr p -> field_compatible (tarray tuchar (n+1)) [] p ->
  data_at_ sh (tarray tuchar (n+1)) p =
  data_at_ sh (tarray tuchar n) p *
  data_at_ sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p).
Proof.
  intros. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh (n+1) n p) by (auto; lia).
  replace (n + 1 - n) with 1 by lia. reflexivity.
Qed.

Lemma nzobj_join sh n (l : list val) p : Zlength l = n ->
  data_at sh (tarray tuchar n) l p *
  data_at_ sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p)
  |-- data_at sh (tarray tuchar (n+1)) (l ++ [Vundef]) p.
Proof.
  intros. rewrite (split2_data_at_Tarray_app n (n+1) sh tuchar l [Vundef] p) by (auto; list_solve).
  replace (n + 1 - n) with 1 by lia. apply derives_refl.
Qed.

Lemma upd_last_zero (l : list Z) :
  upd_Znth (Zlength l) (bytes_rep l ++ [Vundef]) (Vint (Int.zero_ext 8 (Int.repr 0))) = map vi (l ++ [0]).
Proof.
  unfold bytes_rep. rewrite upd_Znth_app2 by (rewrite Zlength_map; list_solve).
  rewrite Zlength_map, Z.sub_diag, map_app. reflexivity.
Qed.

Lemma Zlength_snoc0 (l : list Z) : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app. reflexivity. Qed.

Lemma vi_signed (u : Z) : vi (Int.signed (Int.repr u)) = Vint (Int.repr u).
Proof. unfold vi. rewrite Int.repr_signed. reflexivity. Qed.

Lemma vi_method (b : bool) (u : Z) :
  vi (if b then Int.signed (Int.repr u) else 8) = Vint (Int.repr (if b then u else 8)).
Proof. destruct b; [apply vi_signed | reflexivity]. Qed.

Lemma bytes_of (l : list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> bytes l.
Proof. intros F. unfold bytes. eapply Forall_impl; [ | exact F]. cbv beta. rep_lia. Qed.

Lemma comp_nil p :
  data_at_ Ews (tarray tuchar COMP_MAX) p =
  data_at Ews (tarray tuchar COMP_MAX) (map vi [] ++ Zrepeat Vundef (COMP_MAX - Zlength (@nil Z))) p.
Proof.
  rewrite data_at__tarray. rewrite Zlength_nil, Z.sub_0_r, app_nil_l. reflexivity.
Qed.

Ltac shl_norm :=
  try change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 15))) with 32768 in *;
  try change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 12))) with 4096 in *;
  try change (Int.unsigned (Int.shl (Int.repr 1) (Int.repr 20))) with 1048576 in *.

(* the value of a comparison temp *)
Ltac cmpv :=
  unfold bool2val, Int.ltu; shl_norm;
  rewrite ?Int.unsigned_repr by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
  try lia; reflexivity.

(* a branch excluded by a comparison *)
Ltac hcmp := shl_norm; rewrite ?Int.unsigned_repr in * by rep_lia; lia.

(* a branch excluded by the value of its test *)
Ltac nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* return 0 (an allocation failed): R and s back as run_post 0 *)
Ltac thaw_any := match goal with F : list _ |- _ => thaw F end.
Ltac ret0r := (match goal with P : ret_assert |- _ => subst P end); unfold abbreviate; thaw_any; forward; Exists 0; entailer!; unfold run_post; simpl Z.eqb; cbv iota;
  rewrite drun_split; cancel.

(* the NULL test chain once one pointer was NULL: every later test is 1, then return 0 *)
Ltac exit_chain :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ => ifpost t Int.one; [forward; entailer! | nob | ]
  | |- semax _ _ (Ssequence (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _) _ =>
      ifpost t Int.one; [forward; entailer! | nob | ]
  end;
  forward_if False; [ret0r | nob].

(* A1 with the padding of struct drun (RTRRunKit's A1 cannot hold it) *)
Definition A1p I Iend Rp sp api vosn gv (rs : rsetup) : environ -> mpred :=
  PROP (rs_ok rs; api_facts I Iend; s32 api; rt_extra I)
  LOCAL (temp _t1 (vi (rs_t1 rs)); temp _t2 (vi (rs_t2 rs)); temp _t3 (vi (rs_t3 rs)); temp _t4 (vi (rs_t4 rs));
         temp _mtime (vl (rs_mtime rs)); temp _tsel (vi (rs_tsel rs)); temp _dsel (vi (rs_dsel rs));
         temp _hsel (vi (rs_hsel rs)); temp _text (vi (rs_text rs)); temp _os (vi (rs_os rs));
         temp _hcrc (vi (rs_hcrc rs));
         temp _R Rp; temp _s sp; temp _api (vi api); lvar _osnap (tptr tuchar) vosn; gvars gv)
  SEP (drun_rest rs Vundef Vundef Vundef (Zlength (rs_data rs)) 0 0 0 0 Rp;
       field_at_ Ews t_drun (DOT _h) Rp;
       data_at_ Ews t_strmL sp; allobjs rs; mem_mgr gv; deflate_globals gv; version_at gv vlit;
       data_at_ Tsh (tptr tuchar) vosn).

Lemma run_prefix_pad {Espec : OracleKind} I Iend Rp sp api vosn gv :
  (forall rs, semax Delta_r (A1p I Iend Rp sp api vosn gv rs) rsuf45 (POST_r Iend Rp sp gv)) ->
  semax Delta_r (PRE0 I Iend Rp sp api vosn gv) run_body (POST_r Iend Rp sp gv).
Proof.
  intros HA1. unfold Delta_r, PRE0, run_body, POST_r. simplify_func_tycontext.
  rewrite drun_split. Intros.
  forward_call tt. Intros u_level. forward.
  forward_call tt. Intros u_mval.
  forward_call tt. Intros u_wbits. forward.
  forward_call tt. Intros u_mem. forward.
  forward_call tt. Intros u_strat. forward.
  forward_call tt. Intros n. forward.
  forward_call tt. Intros dlen. forward.
  forward_call tt. Intros u1.
  forward_call tt. Intros u2.
  forward_call tt. Intros u3.
  forward_call tt. Intros u4.
  forward_call tt. Intros xlen. forward.
  forward_call tt. Intros nl. forward.
  forward_call tt. Intros cl. forward.
  rewrite <- !seq_assoc. forward_call tt. Intros mtime. forward.
  forward_call tt. Intros msel.
  forward_call tt. Intros tsel.
  forward_call tt. Intros dsel.
  forward_call tt. Intros hsel.
  forward_call tt. Intros text.
  forward_call tt. Intros os.
  forward_call tt. Intros hcrc.
  rewrite Int.unsigned_repr by rep_lia.
  (* the gp_assume's *)
  forward.
  destruct (Z_le_gt_dec n 1048576) as [Hn | Hn].
  2:{ ifpost _t'23 Int.zero. { hcmp. } { forward. entailer!. }
      forward_call Int.zero. Intros. contradiction. }
  ifpost _t'23 (Int.repr (if dlen <=? 32768 then 1 else 0)).
  { forward. forward. entailer!. cmpv. }
  { hcmp. }
  forward_call (Int.repr (if dlen <=? 32768 then 1 else 0)).
  assumed. apply Z.leb_le in E.
  forward.
  destruct (Z_le_gt_dec xlen 4096) as [Hx|Hx].
  2:{ ifpost _t'24 Int.zero. { hcmp. } { forward. entailer!. }
      ifpost _t'25 Int.zero. { nob. } { forward. entailer!. }
      forward_call Int.zero. Intros. contradiction. }
  destruct (Z_le_gt_dec nl 4096) as [Hnl|Hnl].
  2:{ ifpost _t'24 Int.zero. { forward. forward. entailer!. cmpv. } { hcmp. }
      ifpost _t'25 Int.zero. { nob. } { forward. entailer!. }
      forward_call Int.zero. Intros. contradiction. }
  ifpost _t'24 Int.one. { forward. forward. entailer!. cmpv. } { hcmp. }
  ifpost _t'25 (Int.repr (if cl <=? 4096 then 1 else 0)). { forward. forward. entailer!. cmpv. } { nob. }
  forward_call (Int.repr (if cl <=? 4096 then 1 else 0)).
  assumed. apply Z.leb_le in E0.
  (* the method *)
  ifpost _t'26 (Int.repr (if msel =? 0 then u_mval else 8)).
  { forward. subst msel. entailer!. }
  { forward. rewrite (proj2 (Z.eqb_neq _ _) H24). entailer!. }
  forward.
  deadvars!.
  (* the six objects *)
  forward.
  forward_call (tarray tuchar n, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros datap. forward.
  forward.
  forward_call (tarray tuchar dlen, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros dictp. forward.
  forward.
  forward_call (tarray tuchar xlen, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros xfp. forward.
  forward.
  forward_call (tarray tuchar (nl + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros nfp. forward.
  forward.
  forward_call (tarray tuchar (cl + 1), gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros cfp. forward.
  forward_call (tarray tuchar COMP_MAX, gv).
  { unfold COMP_MAX. simpl. rep_lia. }
  Intros compp. forward.
  deadvars!.
  (* the NULL tests (the rest frozen: valid_pointer's auto search is exponential in the SEP size) *)
  freeze [0;7;8;9;10;11;12;13;14;16;17;19;20;21;22;26;27;28;30;31;32;33;34;35;36;37;38] FR.
  destruct (eq_dec datap nullval) as [Pd | Pd]; Intros.
  { subst datap. forward; try entailer!.
    ifpost _t'33 Int.one; [forward; entailer! | nob | ]. exit_chain. }
  forward.
  destruct (eq_dec dictp nullval) as [Pdi | Pdi]; Intros.
  { subst dictp. ifpost _t'33 Int.one; [nob | forward; forward; entailer! | ]. exit_chain. }
  ifpost _t'33 Int.zero; [nob | forward; forward; entailer!; destruct dictp; try contradiction; reflexivity | ].
  destruct (eq_dec xfp nullval) as [Px | Px]; Intros.
  { subst xfp. ifpost _t'34 Int.one; [nob | forward; forward; entailer! | ]. exit_chain. }
  ifpost _t'34 Int.zero; [nob | forward; forward; entailer!; destruct xfp; try contradiction; reflexivity | ].
  destruct (eq_dec nfp nullval) as [Pnf | Pnf]; Intros.
  { subst nfp. ifpost _t'35 Int.one; [nob | forward; forward; entailer! | ]. exit_chain. }
  ifpost _t'35 Int.zero; [nob | forward; forward; entailer!; destruct nfp; try contradiction; reflexivity | ].
  destruct (eq_dec cfp nullval) as [Pcf | Pcf]; Intros.
  { subst cfp. ifpost _t'36 Int.one; [nob | forward; forward; entailer! | ]. exit_chain. }
  ifpost _t'36 Int.zero; [nob | forward; forward; entailer!; destruct cfp; try contradiction; reflexivity | ].
  destruct (eq_dec compp nullval) as [Pcp | Pcp]; Intros.
  { subst compp. ifpost _t'37 Int.one; [nob | forward; forward; entailer! | ]. exit_chain. }
  ifpost _t'37 Int.zero; [nob | forward; forward; entailer!; destruct compp; try contradiction; reflexivity | ].
  ifsame; [nob | forward; entailer! | ].
  thaw FR.
  deadvars!.
  (* the contents *)
  forward. forward.
  forward_call (datap, n, Ews).
  { rewrite if_false by auto. cancel. }
  Intros data. rewrite if_false by auto.
  forward. forward.
  forward_call (dictp, dlen, Ews).
  { rewrite if_false by auto. cancel. }
  Intros dict. rewrite if_false by auto.
  forward. forward.
  forward_call (xfp, xlen, Ews).
  { rewrite if_false by auto. cancel. }
  Intros xf. rewrite if_false by auto.
  assert_PROP (field_compatible (tarray tuchar (nl + 1)) [] nfp /\ isptr nfp) as FCnx by entailer!.
  destruct FCnx as [FCn Pn].
  rewrite (nzobj_split Ews nl nfp) by (auto; lia). Intros.
  forward. forward.
  rewrite (data_at__tuchar_cs CS DCS.CS Ews nl nfp).
  forward_call (nfp, nl, Ews).
  Intros nm. rewrite (data_at_tuchar_cs DCS.CS CS).
  sep_apply (nzobj_join Ews nl (bytes_rep nm) nfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
  forward. forward. forward.
  match goal with Hz : Zlength nm = nl |- _ => rewrite <- Hz end. rewrite upd_last_zero.
  assert_PROP (field_compatible (tarray tuchar (cl + 1)) [] cfp /\ isptr cfp) as FCcx by entailer!.
  destruct FCcx as [FCc Pc].
  rewrite (nzobj_split Ews cl cfp) by (auto; lia). Intros.
  forward. forward.
  rewrite (data_at__tuchar_cs CS DCS.CS Ews cl cfp).
  forward_call (cfp, cl, Ews).
  Intros cm. rewrite (data_at_tuchar_cs DCS.CS CS).
  sep_apply (nzobj_join Ews cl (bytes_rep cm) cfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
  forward. forward. forward.
  match goal with Hz : Zlength cm = cl |- _ => rewrite <- Hz end. rewrite upd_last_zero.
  (* R's flags and nf *)
  forward. forward. forward. forward. forward.
  forward. forward.
  (* A1 *)
  assert_PROP (isptr datap /\ isptr dictp /\ isptr xfp /\ isptr compp) as PPx by entailer!.
  destruct PPx as (Pdp & Pdip & Pxp & Pcpp).
  set (rs := mkRS (Int.signed (Int.repr u_level)) (if msel =? 0 then Int.signed (Int.repr u_mval) else 8)
                  (Int.signed (Int.repr u_wbits)) (Int.signed (Int.repr u_mem)) (Int.signed (Int.repr u_strat))
                  (Int.signed (Int.repr u1)) (Int.signed (Int.repr u2)) (Int.signed (Int.repr u3))
                  (Int.signed (Int.repr u4)) mtime tsel dsel hsel text os hcrc data dict xf nm cm
                  datap dictp xfp nfp cfp compp).
  assert (OK : rs_ok rs).
  { unfold rs_ok, s32, u32r; cbn.
    assert (SR : forall u, -2147483648 <= Int.signed (Int.repr u) <= 2147483647)
      by (intros; pose proof (Int.signed_range (Int.repr u)); rep_lia).
    repeat split; try apply SR; try apply bytes_of; auto; try rep_lia.
    all: destruct (msel =? 0); [apply SR | lia]. }
  eapply semax_pre; [ | apply (HA1 rs) ].
  unfold A1p, allobjs, obj, comp_at, drun_rest, drun_pad. subst rs.
  cbn [rs_level rs_method rs_wbits rs_mem rs_strategy rs_t1 rs_t2 rs_t3 rs_t4 rs_mtime rs_tsel rs_dsel rs_hsel
       rs_text rs_os rs_hcrc rs_data rs_dict rs_xf rs_nm rs_cm rs_datap rs_dictp rs_xfp rs_nfp rs_cfp rs_compp].
  rewrite !vi_signed, vi_method.
  subst n dlen xlen nl cl. rewrite !Zlength_snoc0.
  rewrite <- comp_nil.
  entailer!.
Qed.
