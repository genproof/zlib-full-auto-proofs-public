(** * cf_still, part stored: the first phase of deflate_stored from strstart = block_start = 0.
    [ds_body] never moves strstart, and moves block_start only by copied window bytes (none when
    left = 0); next_in + avail_in is constant and next_in only grows. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDLTCStill.
Require Import Zlib.proof.roundtrip.RTDLTCStoredKit.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Lemma u32_nn x : 0 <= u32 x.
Proof. unfold u32. apply Z.mod_pos_bound. lia. Qed.

Lemma u32_0 : u32 0 = 0.
Proof. reflexivity. Qed.

Ltac brk H :=
  repeat (cbn [bind] in H; match type of H with
  | bind ?x _ = _ => let E := fresh "E" in destruct x eqn:E; [|discriminate H]
  | match ?p with pair _ _ => _ end = _ => destruct p
  | (if ?b then _ else _) = _ => let E := fresh "B" in destruct b eqn:E
  | Some _ = Some _ => injection H as H
  end).

Ltac brk1 := match goal with
 | H : bind (Some _) _ = _ |- _ => cbn [bind] in H
 | H : bind None _ = _ |- _ => discriminate H
 | H : bind ?x _ = _ |- _ => let E := fresh "E" in destruct x eqn:E
 | H : match ?p with pair _ _ => _ end = _ |- _ => destruct p
 | H : (if ?b then _ else _) = Some _ |- _ => let E := fresh "B" in destruct b eqn:E
 | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
 | H : None = Some _ |- _ => discriminate H
 end.

Lemma out_put_still z l z' :
  out_put z l = Some z' -> z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z.
Proof. unfold out_put. intros H. brk H; subst; [cbn; auto|discriminate]. Qed.

Ltac oput := repeat match goal with E : out_put _ _ = Some _ |- _ =>
  apply out_put_still in E; destruct E as [?E ?E] end.

Lemma fp_still s z s' z' :
  c_flush_pending s z = Some (s', z') ->
  d_strstart s' = d_strstart s /\ d_block_start s' = d_block_start s /\ d_w_size s' = d_w_size s /\
  z_next_in z' = z_next_in z /\ z_avail_in z' = z_avail_in z.
Proof.
  unfold c_flush_pending. intros H. brk H; subst;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; oput; auto.
Qed.

Lemma rb_still s z n z' data :
  0 <= n -> 0 <= z_avail_in z -> c_read_buf s z n = Some (z', data) ->
  z_next_in z' = z_next_in z + Z.min n (z_avail_in z) /\
  z_avail_in z' = z_avail_in z - Z.min n (z_avail_in z).
Proof.
  intros Hn Ha. unfold c_read_buf.
  replace (if z_avail_in z >? n then n else z_avail_in z) with (Z.min n (z_avail_in z))
    by (destruct (Z.gtb_spec (z_avail_in z) n); lia).
  intros H. brk H; subst.
  - apply Z.eqb_eq in B. rewrite B. lia.
  - repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; lia.
Qed.

Lemma pb_wr_still s i v s' :
  c_pb_wr s i v = Some s' ->
  d_strstart s' = d_strstart s /\ d_block_start s' = d_block_start s /\ d_w_size s' = d_w_size s.
Proof. unfold c_pb_wr. intros H. brk H; subst. cbn. auto. Qed.

(** The invariant of the first phase. *)
Definition sv (N M ws : Z) (a : dstate * strm) : Prop :=
  d_strstart (fst a) = 0 /\ d_block_start (fst a) = 0 /\ d_w_size (fst a) = ws /\
  z_next_in (snd a) + z_avail_in (snd a) = N /\ 0 <= z_avail_in (snd a) /\ M <= z_next_in (snd a).

Lemma body_sv N M ws flush mb a r :
  sv N M ws a -> ds_body flush mb a = Some r ->
  match r with inl a' => sv N M ws a' | inr (s', z', _) => sv N M ws (s', z') end.
Proof.
  destruct a as [s z]. intros Hs H. pose proof Hs as (Hst & Hbs & Hws & HN & Ha & HM). cbn [fst snd] in *.
  unfold ds_body in H. rewrite Hst, Hbs in H. cbn zeta in H. change (u32 (0 - 0)) with 0 in H.
  rewrite Z.eqb_refl in H.
  match type of H with context [(?L <? mb) && _] => set (len := L) in H end.
  assert (Hl : 0 <= len) by (unfold len; repeat match goal with |- context [if ?b then _ else _] => destruct b end;
                             try apply u32_nn; cbv; congruence).
  clearbody len. repeat brk1;
  repeat match goal with
   | E : c_pb_wr _ _ _ = Some _ |- _ => apply pb_wr_still in E; destruct E as (?&?&?)
   | E : c_flush_pending _ _ = Some _ |- _ => apply fp_still in E; destruct E as (?&?&?&?&?)
   | E : c_read_buf _ _ _ = Some _ |- _ => apply rb_still in E; [destruct E as (?&?)| lia | lia]
   end; oput; unfold sv in *; cbn in *; lia.
Qed.

Lemma runs_sv N M ws flush mb a r :
  runs (ds_body flush mb) a r -> sv N M ws a -> let '(s', z', _) := r in sv N M ws (s', z').
Proof.
  induction 1 as [a r H|a a' r H _ IH]; intros Hs.
  - pose proof (body_sv N M ws flush mb a (inr r) Hs H) as X. destruct r as [[s' z'] l]. exact X.
  - apply IH. exact (body_sv N M ws flush mb a (inl a') Hs H).
Qed.

(** ** The rest of c_deflate_stored *)

Lemma win0_still s z s' : c_ds_window s z 0 = Some s' -> s' = s.
Proof. unfold c_ds_window. cbn. congruence. Qed.

Lemma uhw_still s : d_strstart (upd_high_water s) = d_strstart s /\ d_block_start (upd_high_water s) = d_block_start s /\
  d_w_size (upd_high_water s) = d_w_size s.
Proof. unfold upd_high_water. destruct (_ <? _); cbn; auto. Qed.

Lemma fill2_still {A : Type} s z (K : dstate -> strm -> option A) r :
  0 <= z_avail_in z -> ds_fill2 s z K = Some r ->
  exists s2 z2, K s2 z2 = Some r /\ z_next_in z <= z_next_in z2 /\ 0 <= z_avail_in z2 /\
    ((d_block_start s >=? d_w_size s) = false -> z_next_in z2 = z_next_in z -> d_strstart s2 = d_strstart s).
Proof.
  intros Ha H. unfold ds_fill2 in H. cbn zeta in H.
  destruct (_ && _) eqn:Bc in H;
  [destruct (mb_move _ _ _ _) as [m|] eqn:Em; cbn [bind] in H; [|discriminate H]|cbn [bind] in H];
  (match type of H with context [if ?X >? z_avail_in z then z_avail_in z else ?X] =>
     assert (Hhv: 0 <= (if X >? z_avail_in z then z_avail_in z else X) <= z_avail_in z)
       by (pose proof (u32_nn (X - 0)); destruct (Z.gtb_spec X (z_avail_in z)); [lia|]; split; [|lia];
           unfold u32 in *; apply Z.mod_pos_bound; lia);
     set (hv := if X >? z_avail_in z then z_avail_in z else X) in H, Hhv end);
  clearbody hv; destruct (hv =? 0) eqn:Bh; cbn [bind] in H;
  try (eexists _, _; split; [exact H|]; split; [lia|]; split; [lia|]; intros Hb _;
       first [rewrite Hb, andb_false_r in Bc; discriminate Bc | apply uhw_still]);
  (match type of H with context [c_read_buf ?a z ?h] => destruct (c_read_buf a z h) as [[z2 data]|] eqn:E end;
   cbn [bind] in H; [|discriminate H];
   match type of H with context [mb_write ?a ?b ?d] => destruct (mb_write a b d) eqn:E' end;
   cbn [bind] in H; [|discriminate H];
   eexists _, _; split; [exact H|]; apply rb_still in E; [|lia|lia]; apply Z.eqb_neq in Bh;
   split; [lia|]; split; [lia|]; intros; lia).
Qed.

Lemma blk2_still {A : Type} s z flush (K : dstate -> strm -> Z -> option A) r :
  ds_blk2 s z flush K = Some r ->
  exists s2 z2 l, K s2 z2 l = Some r /\ z_next_in z2 = z_next_in z /\ d_strstart s2 = d_strstart s.
Proof.
  intros H. unfold ds_blk2 in H. cbn zeta in H. repeat brk1;
  repeat match goal with
   | E : c_flush_pending _ _ = Some _ |- _ => apply fp_still in E; destruct E as (?&?&?&?&?)
   end; eexists _, _, _; (split; [exact H|]); cbn in *; split; congruence.
Qed.
