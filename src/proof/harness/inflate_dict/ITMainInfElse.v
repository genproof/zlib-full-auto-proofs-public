(* Law inflate_dict, main, inflate half: the branch r != Z_NEED_DICT (ITMainInfKit.v it_else_stmt): gp_asserts on r and made, bytes_same(ob, data + opos, made), opos += made; then seg_L3 (given). *)
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

Lemma itel_eq_s a b: Int.min_signed <= a <= Int.max_signed -> Int.min_signed <= b <= Int.max_signed ->
  Int.eq (Int.repr a) (Int.repr b) = (a =? b).
Proof.
  intros. destruct (Z.eqb_spec a b).
  - subst. apply Int.eq_true.
  - apply Int.eq_false. intro X. apply repr_inj_signed in X; auto.
Qed.

Ltac itel_inteq := repeat match goal with |- context [Int.eq (Int.repr ?a) (Int.repr ?b)] =>
  rewrite (itel_eq_s a b) by rep_lia end.

Ltac itel_fin := entailer!; try (rewrite ?Int.neg_repr; itel_inteq; cbn [Z.opp Z.eqb]; reflexivity);
  try (exfalso; match goal with H: Int.repr _ = _ |- _ =>
         apply (f_equal Int.unsigned) in H; vm_compute in H; discriminate end).

Lemma it_else {Espec: OracleKind} : it_else_stmt.
Proof.
  intros I gv vw vs vosn vdl dictp badp datap srcp G wsel dcont scont Fr Inv Brk
         pos lim opos dset aout ibp obp q bs r pos2 made z' L' ow cont GL MF Hnd K.
  pose proof GL as GL'. destruct GL' as (CF & Gok & Hws & Hdc & Hdcs & Hsc & Hscs & Hdb & Hdab & Hsb & Pd & Pb & Pda & Psr).
  pose proof MF as MF'.
  destruct MF' as (Hpos & Hlim & Hopos & Haout & Hbsl & Hbsb & Pib & Pob & Pq & Hpos2 & Hmade & CP & Hnm & Hr & LV & Zok & Hcl & Hcs).
  unfold it_mid, it_PL. unfold seg_L2, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  unfold it_post in CP. cbv zeta in CP.
  destruct CP as (Hai & Hao & Hlow & Hob & [(Er & _) | (Hr3 & Hmd & How & Hend & Hnend)]); [contradiction | ].
  apply semax_if_seq.
  unfold Z_OK, Z_BUF_ERROR, Z_STREAM_END, Z_NEED_DICT, Z_MEM_ERROR in Hr3, Hnd, Hnm.
  forward_if.
  { exfalso. apply Hnd. apply repr_inj_signed; [rep_lia | rep_lia | assumption]. }
  assert (Hr4: exists t1 t2, (r = 0 /\ t1 = 1 /\ t2 = 1) \/ (r = -5 /\ t1 = 1 /\ t2 = 1) \/ (r = 1 /\ t1 = 0 /\ t2 = 1)).
  { destruct Hr3 as [E|[E|E]]; subst; [exists 1, 1; left | exists 1, 1; right; left | exists 0, 1; right; right]; auto. }
  destruct Hr4 as (t1 & t2 & Hr4).
  ifpost 173%positive (Int.repr t1).
  { forward. destruct Hr4 as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; subst; itel_fin. }
  { forward. destruct Hr4 as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; subst; itel_fin. }
  ifpost 174%positive (Int.repr t2).
  { forward. destruct Hr4 as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; subst; itel_fin. }
  { forward. destruct Hr4 as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; subst; itel_fin. }
  assert (t2 = 1) by (destruct Hr4 as [(? & ? & ?)|[(? & ? & ?)|(? & ? & ?)]]; auto). subst t2.
  forward_call (Int.repr 1).
  assert (Hdl: Zlength (it_data G) <= 2 ^ 18) by (destruct Gok as (_ & _ & _ & ? & _); auto).
  forward_call (Int.repr 1).
  { entailer!. simpl. unfold Int.ltu. rewrite !Int.unsigned_repr by rep_lia.
    destruct (zlt _ _); [lia | reflexivity]. }
  rewrite <- (it_bytes_adler_cs Ews aout cont obp), <- (it_bytes_adler_cs Ews (2 ^ 18) dcont datap).
  assert (Hdo: sublist opos (opos + made) dcont = bytes_rep ow).
  { rewrite How, <- Hmade.
    replace (sublist opos (opos + made) dcont)
      with (sublist opos (opos + made) (sublist 0 (Zlength (it_data G)) dcont))
      by (rewrite sublist_sublist by lia; f_equal; lia).
    rewrite Hdcs. unfold bytes_rep. rewrite sublist_map. reflexivity. }
  forward_call (obp, Ews, obp, 0, aout, cont, ow, offset_val opos datap, Ews, datap, opos, 2 ^ 18, dcont, ow, made).
  { assert (is_bytes ow) by (rewrite How; apply Forall_sublist; exact Hdab).
    split; repeat split; auto with share; try lia.
    rewrite isptr_offset_val_zero; auto. }
  rewrite (it_bytes_adler_cs Ews aout cont obp), (it_bytes_adler_cs Ews (2 ^ 18) dcont datap).
  destruct (list_eq_dec Z.eq_dec ow ow) as [_ | X]; [ | contradiction X; reflexivity].
  forward_call (Int.repr 1).
  forward.
  rewrite add_repr.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  assert (MF2: it_mid2_facts I G pos2 lim (opos + made) dset r z' L' (lim - pos) aout ibp obp q
                 (bytes_rep (sublist pos lim (it_src G))) cont (bytes_rep bs)).
  { subst pos2 made. unfold it_mid2_facts, Z_STREAM_END.
    rewrite !Zlength_bytes_rep, Zlength_sublist by lia.
    repeat match goal with |- _ /\ _ => split end; auto; try lia. }
  eapply semax_pre; [ | apply (K _ _ _ _ _ MF2)].
  unfold it_mid2. entailer!.
Qed.
