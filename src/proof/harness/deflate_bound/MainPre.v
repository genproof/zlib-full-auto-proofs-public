(* Law deflate_bound, main: part_pre (MainKit.v): the draws, the gp_assumes, the five mallocs and their NULL
   test, the bytes of the objects (msuf 0 -> msuf 34). *)
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

Lemma nzobj_split sh n p : 0 <= n -> isptr p -> field_compatible (tarray tuchar (n+1)) [] p ->
  @data_at_ DCS.CS sh (tarray tuchar (n+1)) p =
  @data_at_ DCS.CS sh (tarray tuchar n) p *
  @data_at_ DCS.CS sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p).
Proof.
  intros. unfold tarray. rewrite (split2_data_at__Tarray_tuchar sh (n+1) n p) by (auto; lia).
  replace (n + 1 - n) with 1 by lia. reflexivity.
Qed.

Lemma nzobj_join sh n (l : list val) p : Zlength l = n ->
  @data_at DCS.CS sh (tarray tuchar n) l p *
  @data_at_ DCS.CS sh (tarray tuchar 1) (field_address0 (tarray tuchar (n+1)) [ArraySubsc n] p)
  |-- @data_at DCS.CS sh (tarray tuchar (n+1)) (l ++ [Vundef]) p.
Proof.
  intros. rewrite (split2_data_at_Tarray_app n (n+1) sh tuchar l [Vundef] p) by (auto; list_solve).
  replace (n + 1 - n) with 1 by lia. apply derives_refl.
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

Lemma upd_last_zero (l : list Z) :
  upd_Znth (Zlength l) (bytes_rep l ++ [Vundef]) (Vint (Int.zero_ext 8 (Int.repr 0))) = map vi (l ++ [0]).
Proof.
  unfold bytes_rep. rewrite upd_Znth_app2 by (rewrite Zlength_map; list_solve).
  rewrite Zlength_map, Z.sub_diag, map_app. reflexivity.
Qed.

Lemma Zlength_snoc0 (l : list Z) : Zlength (l ++ [0]) = Zlength l + 1.
Proof. rewrite Zlength_app. reflexivity. Qed.

(* the NULL test chain once one pointer was NULL: every later test is 1, then return 0 *)
Ltac exit_ones :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ => ifpost t Int.one; [forward; entailer! | nob | ]
  | |- semax _ _ (Ssequence (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _) _ =>
      ifpost t Int.one; [forward; entailer! | nob | ]
  end;
  forward_if False; [ret0 | nob].

Lemma part_pre {Espec : OracleKind} (gv : globals) (vs vh : val) :
  (forall bs, semax Delta_m (A1 gv vs vh bs) msuf34 POST_m) ->
  semax Delta_m (PRE0 gv vs vh) msuf0 POST_m.
Proof.
  intros HA1. unfold Delta_m, PRE0, msuf0, POST_m, R. simplify_func_tycontext. Intros.
  forward_call tt. Intros u_level.
  forward_call tt. Intros u_wbits.
  forward_call tt. Intros u_mem.
  forward_call tt. Intros u_strat.
  forward_call tt. Intros n.
  forward_call tt. Intros dlen.
  forward_call tt. Intros xlen.
  forward_call tt. Intros nl.
  forward_call tt. Intros cl.
  rewrite <- !seq_assoc. forward_call tt. Intros mtime. forward.
  forward_call tt. Intros dsel.
  forward_call tt. Intros hsel.
  forward_call tt. Intros text.
  forward_call tt. Intros os.
  forward_call tt. Intros hcrc.
  forward_call tt. Intros xsel.
  forward_call tt. Intros nsel.
  forward_call tt. Intros csel.
  rewrite Int.unsigned_repr by rep_lia.
  assert (Elv : Vint (Int.repr u_level) = vi (Int.signed (Int.repr u_level)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Ewv : Vint (Int.repr u_wbits) = vi (Int.signed (Int.repr u_wbits)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Emv : Vint (Int.repr u_mem) = vi (Int.signed (Int.repr u_mem)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  assert (Esv : Vint (Int.repr u_strat) = vi (Int.signed (Int.repr u_strat)))
    by (unfold vi; rewrite Int.repr_signed; reflexivity).
  rewrite Elv, Ewv, Emv, Esv. clear Elv Ewv Emv Esv.
  assert (Slv := Int.signed_range (Int.repr u_level)).
  assert (Swv := Int.signed_range (Int.repr u_wbits)).
  assert (Smv := Int.signed_range (Int.repr u_mem)).
  assert (Ssv := Int.signed_range (Int.repr u_strat)).
  remember (Int.signed (Int.repr u_level)) as lv eqn:Hlv; clear Hlv H u_level.
  remember (Int.signed (Int.repr u_wbits)) as wv eqn:Hwv; clear Hwv H0 u_wbits.
  remember (Int.signed (Int.repr u_mem)) as mv eqn:Hmv; clear Hmv H1 u_mem.
  remember (Int.signed (Int.repr u_strat)) as sv eqn:Hsv; clear Hsv H2 u_strat.
  forward_call (lv, 8, wv, mv, sv).
  { unfold s32; rep_lia. }
  forward_call (Int.repr (if params_ok lv 8 wv mv sv then 1 else 0)).
  assumed.
  destruct (Z_le_gt_dec n 1048576) as [Hn | Hn].
  2:{ ifpost _t'20 Int.zero. { hcmp. } { forward. entailer!. }
      forward_call Int.zero. Intros. contradiction. }
    ifpost _t'20 (Int.repr (if dlen <=? 32768 then 1 else 0)).
    { forward. entailer!. cmpv. }
    { hcmp. }
    forward_call (Int.repr (if dlen <=? 32768 then 1 else 0)).
    assumed. apply Z.leb_le in E0.
    (* xlen, nl, cl *)
    destruct (Z_le_gt_dec xlen 4096) as [Hx | Hx].
    2:{ ifpost _t'21 Int.zero. { hcmp. } { forward. entailer!. }
        ifpost _t'22 Int.zero. { nob. } { forward. entailer!. }
        forward_call Int.zero. Intros. contradiction. }
    destruct (Z_le_gt_dec nl 4096) as [Hnl | Hnl].
    2:{ ifpost _t'21 Int.zero. { forward. entailer!. cmpv. } { hcmp. }
        ifpost _t'22 Int.zero. { nob. } { forward. entailer!. }
        forward_call Int.zero. Intros. contradiction. }
    ifpost _t'21 Int.one. { forward. entailer!. cmpv. } { hcmp. }
    ifpost _t'22 (Int.repr (if cl <=? 4096 then 1 else 0)). { forward. entailer!. cmpv. } { nob. }
    forward_call (Int.repr (if cl <=? 4096 then 1 else 0)).
    assumed. apply Z.leb_le in E1.
    (* the five objects *)
    forward_call (tarray tuchar n, gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros datap.
    forward_call (tarray tuchar dlen, gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros dictp.
    forward_call (tarray tuchar xlen, gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros xfp.
    forward_call (tarray tuchar (nl + 1), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros nfp.
    forward_call (tarray tuchar (cl + 1), gv).
    { simpl. rewrite Z.max_r by lia. rep_lia. }
    Intros cfp.
    (* the NULL tests *)
    destruct (eq_dec datap nullval) as [Pd | Pd]; Intros.
    { subst datap. ifpost _t'28 Int.one; [forward; entailer! | nob | ]. exit_ones. }
    destruct (eq_dec dictp nullval) as [Pdi | Pdi]; Intros.
    { subst dictp. ifpost _t'28 Int.one; [nob | forward; entailer! | ]. exit_ones. }
    ifpost _t'28 Int.zero; [nob | forward; entailer!; destruct dictp; try contradiction; reflexivity | ].
    destruct (eq_dec xfp nullval) as [Px | Px]; Intros.
    { subst xfp. ifpost _t'29 Int.one; [nob | forward; entailer! | ]. exit_ones. }
    ifpost _t'29 Int.zero; [nob | forward; entailer!; destruct xfp; try contradiction; reflexivity | ].
    destruct (eq_dec nfp nullval) as [Pnf | Pnf]; Intros.
    { subst nfp. ifpost _t'30 Int.one; [nob | forward; entailer! | ]. exit_ones. }
    ifpost _t'30 Int.zero; [nob | forward; entailer!; destruct nfp; try contradiction; reflexivity | ].
    destruct (eq_dec cfp nullval) as [Pcf | Pcf]; Intros.
    { subst cfp. ifpost _t'31 Int.one; [nob | forward; entailer! | ]. exit_ones. }
    ifpost _t'31 Int.zero; [nob | forward; entailer!; destruct cfp; try contradiction; reflexivity | ].
    ifsame; [nob | forward; entailer! | ].
    (* the contents *)
    forward_call (datap, n, Ews).
    { rewrite if_false by auto. cancel. }
    Intros data. rewrite if_false by auto.
    forward_call (dictp, dlen, Ews).
    { rewrite if_false by auto. cancel. }
    Intros dict. rewrite if_false by auto.
    forward_call (xfp, xlen, Ews).
    { rewrite if_false by auto. cancel. }
    Intros xf. rewrite if_false by auto.
    assert_PROP (field_compatible (tarray tuchar (nl + 1)) [] nfp /\ isptr nfp) as FCnx by entailer!.
    destruct FCnx as [FCn Pn].
    rewrite (nzobj_split Ews nl nfp) by (auto; lia). Intros.
    forward_call (nfp, nl, Ews).
    Intros nm.
    sep_apply (nzobj_join Ews nl (bytes_rep nm) nfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
    forward.
    assert_PROP (field_compatible (tarray tuchar (cl + 1)) [] cfp /\ isptr cfp) as FCcx by entailer!.
    destruct FCcx as [FCc Pc].
    rewrite (nzobj_split Ews cl cfp) by (auto; lia). Intros.
    forward_call (cfp, cl, Ews).
    Intros cm.
    sep_apply (nzobj_join Ews cl (bytes_rep cm) cfp ltac:(unfold bytes_rep; rewrite Zlength_map; auto)).
    forward.
    (* A1 *)
    assert_PROP (isptr datap /\ isptr dictp /\ isptr xfp) as PPx by entailer!.
    destruct PPx as (Pdp & Pdip & Pxp).
    unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
    set (bs := mkBS lv wv mv sv n dlen xlen nl cl mtime dsel hsel text os hcrc xsel nsel csel
                    datap dictp xfp nfp cfp data dict xf nm cm).
    assert (OK : bs_ok bs).
    { unfold bs_ok, byte8, bytes, nzbytes, s32, u32r; cbn.
      assert (B : forall l : list Z, Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
                  Forall (fun b => 0 <= b < 256) l)
        by (intros l Fl; eapply Forall_impl; [ | exact Fl ]; cbv beta; rep_lia).
      repeat split; auto; try rep_lia. }
    eapply semax_pre; [ | apply (HA1 bs) ].
    unfold A1, objs, obj, bs_locals. subst bs. cbn [b_level b_wbits b_mem b_strategy b_n b_dlen b_xlen b_nl b_cl
      b_mtime b_dsel b_hsel b_text b_os b_hcrc b_xsel b_nsel b_csel b_datap b_dictp b_xfp b_nfp b_cfp
      b_data b_dict b_xf b_nm b_cm app].
    subst n dlen xlen nl cl.
    rewrite !upd_last_zero, !Zlength_snoc0.
    entailer!.
Qed.
