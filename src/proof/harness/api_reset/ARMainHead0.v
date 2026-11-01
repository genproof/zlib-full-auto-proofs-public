(* Law api_reset, main: the do-while body in phase 0 (ARMainKit.seg_dbody): the piece and the output space
   (take, room, flush), the four objects (copy_of x2, malloc x2); then the test against NULL
   (ARMainHead0Null*.v), offer() on both streams, inflate(&used) and the test of Z_MEM_ERROR
   (ARMainHead0Call.v), and the rest of the body, tail0_stmt. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.EnvBodies QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.api_reset.ARMainDefs Zlib.proof.harness.api_reset.ARMainKit.
Require Import Zlib.proof.harness.api_reset.ARMainHead0Call.
Require Import Zlib.proof.harness.api_reset.ARMainHead0NullA.
Require Import Zlib.proof.harness.api_reset.ARMainHead0Null.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.api_reset.code.
Local Open Scope logic.

Lemma body0_of : tail0_stmt -> body_stmt 0.
Proof.
  intros TAIL0. pose proof (null0_of (call0_of TAIL0)) as NULL0.
  unfold body_stmt. intros Espec J0 J1 gv va vb w inp src pos za La zb Lb GF.
  unfold seg_dbody, Delta_m, Gmain, dpost, POST_m, dinv_at, fresh_mem. simpl (0 =? 0).
  simplify_func_tycontext. abbreviate_semax. Intros.
  match goal with H: dprop _ _ _ _ _ _ _ _ _ _ |- _ => rename H into DP end.
  unfold dprop in DP. simpl (0 =? 0) in DP. destruct DP as (Sw & Rl & HJ & Zb).
  pose proof GF as GF0. destruct GF as (AF & Wok & Hw & Hn & Hsb & Pinp & Pva & Pvb).
  (* take = upto(clip(input_len - read)); room = nondet_u32(); flush = (int) nondet_u32() *)
  forward_call (Zlength src - pos).
  forward_call (Z.min (Zlength src - pos) Int.max_unsigned). Intros take.
  forward.
  rewrite <- !seq_assoc. forward_call tt. Intros room. forward.
  rewrite Int.unsigned_repr by rep_lia.
  forward_call tt. Intros u.
  assert (Ef: Int.repr u = Int.repr (Int.signed (Int.repr u))) by (rewrite Int.repr_signed; auto).
  rewrite Ef. clear Ef. set (flush := Int.signed (Int.repr u)).
  assert (Hfl: Int.min_signed <= flush <= Int.max_signed) by apply Int.signed_range. clearbody flush.
  assert (Htk: 0 <= take /\ pos + take <= Zlength src /\ take <= Int.max_unsigned).
  { pose proof (Z.le_min_l (Zlength src - pos) Int.max_unsigned).
    pose proof (Z.le_min_r (Zlength src - pos) Int.max_unsigned). lia. }
  (* in_used = copy_of(input + read, take); in_fresh = the same *)
  assert (CB: cbuf_ok false (offset_val pos inp) Ews inp pos (Zlength src) take (bytes_rep src)
                (sublist pos (pos + take) src)).
  { unfold cbuf_ok. rewrite Zlength_sublist by lia.
    repeat split; auto; try lia; [apply Forall_sublist; auto | ].
    unfold bytes_rep. rewrite sublist_map. reflexivity. }
  rewrite <- bytes_adler_cs.
  forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, sublist pos (pos + take) src, gv).
  Intros iu.
  forward_call (offset_val pos inp, Ews, inp, pos, Zlength src, bytes_rep src, take, sublist pos (pos + take) src, gv).
  Intros ifr.
  (* out_used = malloc(room); out_fresh = malloc(room) *)
  split_call. forward_call (tarray tuchar room, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ou.
  forward.
  split_call. forward_call (tarray tuchar room, gv). { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros ofr.
  forward.
  rewrite !bytes_adler_cs, !tok_adler_cs.
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (NULL0 Espec J0 J1 gv va vb w inp src pos take room flush iu ifr ou ofr za La zb)].
  { unfold null0_pre, opt_obj, objb, rest0. rewrite <- !malloc_bytes. entailer!. }
  unfold hd0_facts. refine (conj GF0 (conj HJ (conj Sw (conj Rl (conj Zb _))))). rep_lia.
Qed.
