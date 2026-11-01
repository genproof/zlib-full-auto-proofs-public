(* Law inflate_dict, main, inflate half: the loop body up to the null check of ib / ob (ITMainInfKit.v it_pre_stmt): the draws of step, aout, flush, gp_assume(aout <= 2^20), lim, ain = lim - pos, ib = exact_copy(src + pos, ain), ob = exact_space(aout, &osnap), `if (ib == NULL || ob == NULL) return 0;`; then seg_L1 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITMainInfKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.
Local Open Scope logic.

Ltac itpre_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                | match goal with H: _ |- _ => solve [discriminate H] end
                                | contradiction
                                | lia ].

(* hides an equation from entailer!'s subst *)
Definition itpre_hide (P: Prop) : Prop := P.

(* a slice of the source object (its first Zlength src bytes are src) as exact_copy takes it *)
Lemma itpre_cbuf sh p scont src N lo hi:
  readable_share sh -> is_bytes src -> 0 <= lo <= hi -> hi <= Zlength src -> Zlength src <= N ->
  Zlength scont = N -> sublist 0 (Zlength src) scont = bytes_rep src ->
  cbuf_ok false (offset_val lo p) sh p lo N (hi - lo) scont (sublist lo hi src).
Proof.
  intros Hsh Hb Hlo Hhi HN Hsc Hsub. unfold cbuf_ok.
  split; [reflexivity | ]. split; [exact Hsh | ]. split; [lia | ]. split; [lia | ].
  split; [rewrite Zlength_sublist; lia | ]. split; [apply is_bytes_sublist; exact Hb | ].
  rewrite <- sublist_bytes_rep, <- Hsub, sublist_sublist by lia. f_equal; lia.
Qed.

Lemma it_pre {Espec: OracleKind} : it_pre_stmt.
Proof.
  intros I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr Inv Brk pos lim opos dset z L
    GL HI Hlim K.
  pose proof GL as GL'.
  destruct GL' as (CF & Gok & Hws & Hdc & Hdsub & Hsc & Hssub & Bd & Bdat & Bsrc & Pd & Pb & Pdat & Psrc).
  destruct (it_range I CF _ _ _ _ _ _ _ HI) as (_ & Hpos & Hopos).
  unfold it_at, seg_loop, Delta_m, Gmain_k, it_PL, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros step.
  forward_call tt. Intros aout.
  forward_call tt. Intros flu.
  assert (Ef: Int.repr flu = Int.repr (Int.signed (Int.repr flu))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr flu)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  forward_call (Int.repr (if aout <=? 2 ^ 20 then 1 else 0)).
  { entailer!.
    match goal with |- context [Int.shl ?a ?b] => change (Int.shl a b) with (Int.repr (2 ^ 20)) end. arg_cmp. }
  assumed. apply Z.leb_le in E.
  assert (Hsl: Zlength (it_src G) <= 2 ^ 19) by (destruct Gok as (_ & _ & _ & _ & X & _); exact X).
  set (lim' := if step <? Zlength (it_src G) - lim then lim + step else Zlength (it_src G)).
  assert (Hlim': lim <= lim' <= Zlength (it_src G))
    by (subst lim'; destruct (Z.ltb_spec step (Zlength (it_src G) - lim)); lia).
  ifpost _t'37 (Int.repr lim').
  { forward. entailer!. subst lim'. destruct (Z.ltb_spec step (Zlength (it_src G) - lim)); [ | lia]. reflexivity. }
  { forward. entailer!. subst lim'. destruct (Z.ltb_spec step (Zlength (it_src G) - lim)); [lia | ]. reflexivity. }
  clearbody lim'.
  forward. forward.
  rewrite sub_repr.
  assert (Hsrc32: Zlength (it_src G) <= Int.max_unsigned) by rep_lia.
  (* keep the object sizes 2^19, 2^18 abstract: forward_call overflows the stack on them *)
  remember (2 ^ 19) as N19 eqn:HN19. remember (2 ^ 18) as N18 eqn:HN18.
  assert (HN: itpre_hide (N19 = 2 ^ 19 /\ N18 = 2 ^ 18)) by (split; assumption). clear HN19 HN18.
  forward_call (offset_val pos srcp, Ews, srcp, pos, N19, scont, lim' - pos, sublist pos lim' (it_src G), gv).
  (* the frame first: entailer! on the argument goal would subst N19 into the frame's evar *)
  swap 1 2. { rewrite it_bytes_adler_cs. cancel. }
  { apply itpre_cbuf; auto; lia. }
  Intros ibp.
  forward_call (aout, vosn, Tsh, gv).
  { rewrite it_ptr_adler_cs_. cancel. }
  Intros vret. destruct vret as [[obp q] bs]. simpl fst in *. simpl snd in *.
  rewrite it_ptr_adler_cs.
  match goal with Hb: Zlength bs = aout |- _ => rename Hb into Hbs end. subst aout.
  destruct (eq_dec ibp nullval) as [IN|IN].
  { subst ibp.
    ifpost _t'40 (Int.repr 1). { forward. entailer!. } { itpre_infeas. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply it_istream_to_undef. entailer!. }
    { itpre_infeas. } }
  Intros.
  (* at the law's compspecs first: then forward_if proves ib's comparison with NULL by itself, quickly *)
  rewrite (it_bytes_adler_cs Ews (lim' - pos) _ ibp), (it_tok_adler_cs Ews (lim' - pos) ibp),
    (it_bytes_adler_cs Ews (Zlength bs) _ obp), (it_tok_adler_cs Ews (Zlength bs) obp),
    (it_bytes_adler_cs Ews (Zlength bs) _ q), (it_tok_adler_cs Ews (Zlength bs) q).
  destruct (eq_dec obp nullval) as [ON|ON].
  { subst obp.
    ifpost _t'40 (Int.repr 1).
    { itpre_infeas. }
    { forward. entailer!. }
    forward_if. { forward. Exists (Int.repr 0). sep_apply it_istream_to_undef. entailer!. }
    { itpre_infeas. } }
  Intros.
  assert_PROP (isptr obp /\ isptr ibp /\ isptr q) as Pob by entailer!. destruct Pob as (Pob & Pib & Pq).
  ifpost _t'40 (Int.repr 0).
  { itpre_infeas. }
  { forward. entailer!. destruct obp; try contradiction; reflexivity. }
  forward_if.
  { itpre_infeas. }
  assert (BF: it_buf_facts I G pos lim' opos dset z L (Zlength bs) flush ibp obp q bs).
  { unfold it_buf_facts. split; [exact HI | ]. repeat split; auto; lia. }
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K lim' (Zlength bs) flush ibp obp q bs BF)].
  destruct HN as [HN19 HN18].
  unfold it_buf. rewrite <- HN19. replace (2 ^ 18) with N18 by exact HN18. clear HN18 HN19. entailer!.
Qed.
