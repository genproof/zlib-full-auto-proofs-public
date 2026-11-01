(* Law deflate_bound_split, main: the 18 draws, deflate_params_ok and the assumes, the five mallocs and their NULL check (statements 0..26 of mbody) (SplitKit.v). *)
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

(* return 0 from main: the locals back to Tsh, everything else to TT *)
Ltac dret0 := forward; Exists (Int.repr 0); entailer!.

(* the NULL test chain once one pointer was NULL: every later test is 1, then return 0 *)
Ltac exit_ones :=
  repeat match goal with
  | |- semax _ _ (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _ => ifpost t Int.one; [forward; entailer! | nob | ]
  | |- semax _ _ (Ssequence (Ssequence (Sifthenelse _ (Sset ?t _) _) _) _) _ =>
      ifpost t Int.one; [forward; entailer! | nob | ]
  end;
  forward_if False; [dret0 | nob].

Lemma part_draws {Espec : OracleKind} Bpre Brun sp hp vosn gv :
  (forall bd, semax Delta_m (A1 Bpre Brun sp hp vosn gv bd) msuf27 Rm_ret) ->
  semax Delta_m (PRE0 Bpre Brun sp hp vosn gv) mbody Rm_ret.
Proof.
  intros HA1. unfold Delta_m, PRE0, mbody, Rm_ret, POST_m, Rm. simplify_func_tycontext. Intros.
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
  remember (Int.signed (Int.repr u_level)) as lv eqn:Hlv; clear Hlv H1 u_level.
  remember (Int.signed (Int.repr u_wbits)) as wv eqn:Hwv; clear Hwv H2 u_wbits.
  remember (Int.signed (Int.repr u_mem)) as mv eqn:Hmv; clear Hmv H3 u_mem.
  remember (Int.signed (Int.repr u_strat)) as sv eqn:Hsv; clear Hsv H4 u_strat.
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
  (* A1 *)
  assert_PROP (isptr datap /\ isptr dictp /\ isptr xfp /\ isptr nfp /\ isptr cfp) as PPx by entailer!.
  destruct PPx as (Pdp & Pdip & Pxp & Pnp & Pcp).
  unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
  eapply semax_pre; [ | apply (HA1 (mkBD lv wv mv sv n dlen xlen nl cl mtime dsel hsel text os hcrc xsel nsel csel
                                         datap dictp xfp nfp cfp)) ].
  unfold A1, draw_locals. cbn [bd_level bd_wbits bd_mem bd_strategy bd_n bd_dlen bd_xlen bd_nl bd_cl
    bd_mtime bd_dsel bd_hsel bd_text bd_os bd_hcrc bd_xsel bd_nsel bd_csel bd_datap bd_dictp bd_xfp bd_nfp bd_cfp].
  entailer!.
  unfold bd_ok, s32, u32r; cbn. repeat split; auto; rep_lia.
Qed.
