(* Law rj_bad_checksum: a pass of the switch in a mode of the blocks (TYPE .. LIT, inflate_fast included) ends
   in a mode of the blocks, in CHECK (after the last block) or in BAD: never in a mode of the header (HEAD ..
   DICT) nor in LENGTH / DONE.  The raw stream's decode theory (Kd at a loop head) does not exclude HEAD and
   DONE by itself; the block loop of BadLoop.v needs this to stay among the block modes until CHECK. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The modes from TYPE on: the modes of the blocks, CHECK, and BAD                                *)

Definition late (md: Z) : Prop := Zlib.proof.inflate.Model.TYPE <= md <= CHECK \/ md = BAD.
Definition late_out (o: iout) : Prop :=
  match o with IBrk m => late (m_mode m) | IRet _ _ => True end.

(* the primitives keep the mode *)
Lemma bm_md_needbits_f k n m : m_mode (needbits_f k n m) = m_mode m.
Proof.
  revert m; induction k as [|k IH]; intros m; [reflexivity|]. cbn [needbits_f].
  destruct (m_bits m <? n); [|reflexivity]. destruct (m_have m =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bm_md_needbits n m : m_mode (needbits n m) = m_mode m.
Proof. apply bm_md_needbits_f. Qed.
Lemma bm_imd_needbits n m : i_mode (m_s (needbits n m)) = i_mode (m_s m).
Proof. apply bm_md_needbits_f. Qed.

Lemma bm_md_lookup1_f k fx dx t nb m :
  m_mode (snd (fst (lookup1_f k fx dx t nb m))) = m_mode m.
Proof.
  revert m; induction k as [|k IH]; intros m; [reflexivity|]. cbn [lookup1_f].
  destruct (_ <=? _); [reflexivity|]. destruct (m_have m =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bm_md_lookup1 fx dx t nb m r : lookup1 fx dx t nb m = r -> m_mode (snd (fst r)) = m_mode m.
Proof. intros <-. apply bm_md_lookup1_f. Qed.

Lemma bm_md_lookup2_f k fx dx t l m :
  m_mode (snd (fst (lookup2_f k fx dx t l m))) = m_mode m.
Proof.
  revert m; induction k as [|k IH]; intros m; [reflexivity|]. cbn [lookup2_f].
  destruct (_ <=? _); [reflexivity|]. destruct (m_have m =? 0); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bm_md_lookup2 fx dx t l m r : lookup2 fx dx t l m = r -> m_mode (snd (fst r)) = m_mode m.
Proof. intros <-. apply bm_md_lookup2_f. Qed.

Lemma bm_md_lenlens_loop k m : m_mode (lenlens_loop k m) = m_mode m.
Proof.
  revert m; induction k as [|k IH]; intros m; [reflexivity|]. cbn [lenlens_loop].
  destruct (_ <? _); [|reflexivity]. destruct (m_leave (needbits 3 m) =? 1); [apply bm_md_needbits|].
  rewrite IH. cbn. apply bm_imd_needbits.
Qed.
Lemma bm_imd_lenlens_loop k m : i_mode (m_s (lenlens_loop k m)) = i_mode (m_s m).
Proof. apply bm_md_lenlens_loop. Qed.

Lemma bm_imd_lens_fill k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k as [|k IH]; intros s; [reflexivity|]. cbn [lens_fill]. rewrite IH. reflexivity. Qed.

(* the machine of a pass of the CODELENS loop *)
Definition cl_m (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.

(* destruct every closed if / match of the goal, innermost scrutinee first *)
Ltac bm_dest x :=
  lazymatch x with
  | match ?c with _ => _ end => bm_dest c
  | context [match ?c with _ => _ end] => bm_dest c
  | _ => tryif is_var x then destruct x else (let E := fresh "E" in destruct x eqn:E)
  end.
Ltac bm_split :=
  repeat (cbv beta iota zeta; match goal with |- context [match ?x with _ => _ end] => bm_dest x end).

Lemma bm_md_fwalk fx dx k il t h m : m_mode (snd (fwalk_f fx dx k il t h m)) = m_mode m.
Proof.
  revert h m; induction k as [|k IH]; intros h m; cbn [fwalk_f]; cbv zeta; [reflexivity|].
  destruct (il _); [rewrite IH|]; reflexivity.
Qed.

Lemma bm_md_fwalk_eq fx dx k il t h m r : fwalk_f fx dx k il t h m = r -> m_mode (snd r) = m_mode m.
Proof. intros <-. apply bm_md_fwalk. Qed.

(* the facts on the machines of the destructed calls; then the mode of the result by arithmetic *)
Ltac bm_facts := repeat match goal with
  | E: lookup1 _ _ _ _ _ = _ |- _ => apply bm_md_lookup1 in E; cbn [fst snd] in E
  | E: lookup2 _ _ _ _ _ = _ |- _ => apply bm_md_lookup2 in E; cbn [fst snd] in E
  | E: fwalk_f _ _ _ _ _ _ _ = _ |- _ => apply bm_md_fwalk_eq in E; cbn [fst snd] in E
  | E: Z.eqb _ _ = true |- _ => apply Z.eqb_eq in E
  | E: @eq bool _ _ |- _ => clear E
  | E: @eq (prod _ _) _ _ |- _ => clear E
  end.

Ltac bm_leaf :=
  bm_facts;
  unfold late_out, late, m_mode, upd_s, set_mode, set_bad in *;
  cbn -[needbits lookup1 lookup2 fast fast_iter fwalk_f codelens_loop codelens_iter lenlens_loop lenlens_zero
        call_table copy_bytes lens_fill] in *;
  rewrite ?bm_imd_lens_fill, ?bm_imd_lenlens_loop, ?bm_imd_needbits in *;
  cbn -[needbits lookup1 lookup2 fast fast_iter fwalk_f codelens_loop codelens_iter lenlens_loop lenlens_zero
        call_table copy_bytes lens_fill] in *;
  unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, BAD in *; lia.

(* a pass of the CODELENS loop keeps the mode, or sets BAD *)
Lemma bm_md_codelens_iter fx dx m :
  m_mode (cl_m (codelens_iter fx dx m)) = m_mode m \/ m_mode (cl_m (codelens_iter fx dx m)) = BAD.
Proof. unfold codelens_iter. bm_split; bm_leaf. Qed.

Lemma bm_md_codelens_loop_eq fx dx k m r : codelens_loop fx dx k m = r ->
  m_mode (cl_m r) = m_mode m \/ m_mode (cl_m r) = BAD.
Proof.
  intros <-. revert m; induction k as [|k IH]; intros m; cbn [codelens_loop]; cbv zeta; [left; reflexivity|].
  destruct (_ <? _); [|left; reflexivity].
  pose proof (bm_md_codelens_iter fx dx m) as F.
  destruct (codelens_iter fx dx m) as [m1|m1|m1]; cbn [cl_m] in *; [|exact F|exact F].
  destruct (IH m1) as [I|I]; rewrite I; [exact F|right; reflexivity].
Qed.

(* inflate_fast keeps the mode, or sets TYPE (end of block) or BAD *)
Definition bk (md: Z) (m: mst) : Prop := m_mode m = md \/ m_mode m = Zlib.proof.inflate.Model.TYPE \/ m_mode m = BAD.

Lemma bk_fpull md m : bk md m -> bk md (fpull m).
Proof. exact (fun H => H). Qed.
Lemma bk_ow md m x : bk md m -> bk md (set_m_ow m x).
Proof. exact (fun H => H). Qed.
Lemma bk_hold md m x : bk md m -> bk md (set_m_hold m x).
Proof. exact (fun H => H). Qed.
Lemma bk_bits md m x : bk md m -> bk md (set_m_bits m x).
Proof. exact (fun H => H). Qed.
Lemma bk_nx md m x : bk md m -> bk md (set_m_nx m x).
Proof. exact (fun H => H). Qed.
Lemma bk_restore md m : bk md m -> bk md (restore m).
Proof. exact (fun H => H). Qed.
Lemma bk_if md (b: bool) x y : bk md x -> bk md y -> bk md (if b then x else y).
Proof. destruct b; auto. Qed.
Lemma bk_fwalk md fx dx k il t h m h' m' : fwalk_f fx dx k il t h m = (h', m') -> bk md m -> bk md m'.
Proof. intros E. apply bm_md_fwalk_eq in E. cbn [snd] in E. unfold bk. rewrite E. auto. Qed.
Lemma bk_trans md m m' : bk md m -> bk (m_mode m) m' -> bk md m'.
Proof. unfold bk. intros A [B|B]; [rewrite B; exact A|auto]. Qed.

Ltac bkt := repeat match goal with
  | H: bk ?a ?b |- bk ?a ?b => exact H
  | |- bk _ (fpull _) => apply bk_fpull
  | |- bk _ (set_m_ow _ _) => apply bk_ow
  | |- bk _ (set_m_hold _ _) => apply bk_hold
  | |- bk _ (set_m_bits _ _) => apply bk_bits
  | |- bk _ (set_m_nx _ _) => apply bk_nx
  | |- bk _ (set_mode _ Zlib.proof.inflate.Model.TYPE) => right; left; reflexivity
  | |- bk _ (set_bad _ _) => right; right; reflexivity
  | |- bk _ (if _ then _ else _) => apply bk_if
  | E: fwalk_f _ _ _ _ _ _ _ = (_, ?mm) |- bk _ ?mm => apply (bk_fwalk _ _ _ _ _ _ _ _ _ _ E)
  end.

Lemma bm_fast_iter fx dx m : bk (m_mode m) (snd (fast_iter fx dx m)).
Proof.
  assert (H : bk (m_mode m) m) by (left; reflexivity).
  unfold fast_iter. cbv beta iota zeta.
  repeat match goal with
  | |- bk _ (snd (if ?b then _ else _)) => destruct b
  | |- bk _ (snd (match ?p with (_, _) => _ end)) => destruct p as [?x ?y] eqn:?
  end; cbn [snd].
  all: repeat match goal with
  | E: @eq (Z * mst) (if ?b then _ else _) (_, _) |- _ => destruct b; injection E; clear E; intros; subst
  end.
  all: bkt.
Qed.

Lemma bm_fast_loop fx dx k m : bk (m_mode m) (fast_loop fx dx k m).
Proof.
  revert m; induction k as [|k IH]; intros m; cbn [fast_loop]; [left; reflexivity|].
  pose proof (bm_fast_iter fx dx m) as A.
  destruct (fast_iter fx dx m) as [go m1]; cbn [snd] in A.
  destruct (_ && _ && _); [eapply bk_trans; [exact A|apply IH]|exact A].
Qed.

Lemma bm_fast fx dx m : bk (m_mode m) (fast fx dx m).
Proof. unfold fast. cbv beta zeta. apply bk_restore, bk_bits, bk_hold, bk_nx, bm_fast_loop. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases of the blocks, in the order of their fallthroughs                                    *)

(* the head constant of a term *)
Ltac bm_head t := lazymatch t with ?f _ => bm_head f | _ => t end.

(* a fallthrough into the case c, whose lemma is lem; the test of the head keeps apply from unfolding the
   other leaves (inflate_fast) *)
Ltac bm_fall c lem :=
  lazymatch goal with |- late_out ?t => let h := bm_head t in constr_eq h c; apply lem; bm_leaf end.

Section Cases.
Variables (flush: Z) (fx dx: list entry).

Lemma bm_MATCH m : late (m_mode m) -> late_out (c_MATCH m).
Proof. intros H. unfold c_MATCH. bm_split; bm_leaf. Qed.

Lemma bm_DISTEXT m : late (m_mode m) -> late_out (c_DISTEXT m).
Proof. intros H. unfold c_DISTEXT. bm_split; try bm_fall c_MATCH bm_MATCH; bm_leaf. Qed.

Lemma bm_DIST m : late (m_mode m) -> late_out (c_DIST fx dx m).
Proof. intros H. unfold c_DIST. bm_split; try bm_fall c_DISTEXT bm_DISTEXT; bm_leaf. Qed.

Lemma bm_LENEXT m : late (m_mode m) -> late_out (c_LENEXT fx dx m).
Proof. intros H. unfold c_LENEXT. bm_split; try bm_fall c_DIST bm_DIST; bm_leaf. Qed.

Lemma bm_LIT m : late (m_mode m) -> late_out (c_LIT m).
Proof. intros H. unfold c_LIT. bm_split; bm_leaf. Qed.

(* LEN for any fast path ff with the property of inflate_fast (bm_fast); keeping ff a variable keeps the
   kernel check of the proof short *)
Lemma bm_LEN_ff (ff: mst -> mst) m : late (m_mode m) -> bk (m_mode (restore m)) (ff (restore m)) ->
  late_out (c_LEN fx dx ff m).
Proof.
  intros H F. unfold c_LEN. unfold bk in F.
  set (M := ff (restore m)) in *. clearbody M.
  bm_split. all: first [bm_fall c_LENEXT bm_LENEXT | bm_leaf].
Qed.

Lemma bm_LEN m : late (m_mode m) -> late_out (c_LEN fx dx (fast fx dx) m).
Proof. intros H. apply bm_LEN_ff; [exact H|apply bm_fast]. Qed.

Lemma bm_LEN_ m : late (m_mode m) -> late_out (c_LEN_ fx dx (fast fx dx) m).
Proof. intros H. unfold c_LEN_. apply bm_LEN. bm_leaf. Qed.

Lemma bm_CODELENS m : late (m_mode m) -> late_out (c_CODELENS flush fx dx (fast fx dx) m).
Proof.
  intros H. unfold c_CODELENS. bm_split;
  try match goal with E: codelens_loop _ _ _ _ = _ |- _ => apply bm_md_codelens_loop_eq in E; cbn [cl_m] in E end;
  try bm_fall c_LEN_ bm_LEN_; bm_leaf.
Qed.

Lemma bm_LENLENS m : late (m_mode m) -> late_out (c_LENLENS flush fx dx (fast fx dx) m).
Proof. intros H. unfold c_LENLENS. bm_split; try bm_fall c_CODELENS bm_CODELENS; bm_leaf. Qed.

Lemma bm_TABLE m : late (m_mode m) -> late_out (c_TABLE flush fx dx (fast fx dx) m).
Proof. intros H. unfold c_TABLE. bm_split; try bm_fall c_LENLENS bm_LENLENS; bm_leaf. Qed.

Lemma bm_COPY m : late (m_mode m) -> late_out (c_COPY m).
Proof. intros H. unfold c_COPY. bm_split; bm_leaf. Qed.

Lemma bm_COPY_ m : late (m_mode m) -> late_out (c_COPY_ m).
Proof. intros H. unfold c_COPY_. apply bm_COPY. bm_leaf. Qed.

Lemma bm_STORED m : late (m_mode m) -> late_out (c_STORED flush m).
Proof. intros H. unfold c_STORED. bm_split; try bm_fall c_COPY_ bm_COPY_; bm_leaf. Qed.

Lemma bm_TYPEDO m : late (m_mode m) -> late_out (c_TYPEDO flush m).
Proof. intros H. unfold c_TYPEDO. bm_split; bm_leaf. Qed.

Lemma bm_TYPE m : late (m_mode m) -> late_out (c_TYPE flush m).
Proof. intros H. unfold c_TYPE. bm_split; try bm_fall c_TYPEDO bm_TYPEDO; bm_leaf. Qed.

End Cases.

(* the modes TYPE .. LIT are the modes of the blocks (one case per mode: lia on the whole disjunction is
   exponential) *)
Ltac bm_disj := first [reflexivity | left; bm_disj | right; bm_disj].

Lemma bm_blk_range md : Zlib.proof.inflate.Model.TYPE <= md <= LIT -> blk_mode md.
Proof.
  unfold blk_mode, md_type, md_tab, md_dec.
  unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT.
  intros R.
  repeat match goal with
  | R: ?a <= md <= 16205 |- _ =>
      destruct (Z.eq_dec md a) as [->|N]; [bm_disj|];
      assert (a + 1 <= md <= 16205) by lia; clear R N; cbn [Z.add] in *
  end.
  lia.
Qed.

Lemma bm_late_blk md : blk_mode md -> late md.
Proof.
  unfold blk_mode, md_type, md_tab, md_dec, late.
  unfold Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN,
    LENEXT, DIST, DISTEXT, MATCH, LIT, CHECK, BAD.
  intros B. left. repeat destruct B as [B|B]; subst; lia.
Qed.

Lemma bad_blk_next flush m : blk_mode (m_mode m) ->
  match stepf2 flush lenfix_list distfix_list m with
  | IBrk m' => blk_mode (m_mode m') \/ m_mode m' = CHECK \/ m_mode m' = BAD
  | IRet _ _ => True
  end.
Proof.
  intros B. pose proof (bm_late_blk _ B) as L.
  assert (O : late_out (stepf2 flush lenfix_list distfix_list m)).
  { unfold blk_mode, md_type, md_tab, md_dec in B. unfold stepf2, step2.
    destruct B as [[E|[E|[E|[E|E]]]]|[[E|[E|E]]|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E;
    cbn -[c_TYPE c_TYPEDO c_STORED c_COPY_ c_COPY c_TABLE c_LENLENS c_CODELENS c_LEN_ c_LEN c_LENEXT c_DIST
          c_DISTEXT c_MATCH c_LIT fast lenfix_list distfix_list];
    lazymatch goal with
    | |- late_out (c_TYPE _ _) => apply bm_TYPE
    | |- late_out (c_TYPEDO _ _) => apply bm_TYPEDO
    | |- late_out (c_STORED _ _) => apply bm_STORED
    | |- late_out (c_COPY_ _) => apply bm_COPY_
    | |- late_out (c_COPY _) => apply bm_COPY
    | |- late_out (c_TABLE _ _ _ _ _) => apply bm_TABLE
    | |- late_out (c_LENLENS _ _ _ _ _) => apply bm_LENLENS
    | |- late_out (c_CODELENS _ _ _ _ _) => apply bm_CODELENS
    | |- late_out (c_LEN_ _ _ _ _) => apply bm_LEN_
    | |- late_out (c_LEN _ _ _ _) => apply bm_LEN
    | |- late_out (c_LENEXT _ _ _) => apply bm_LENEXT
    | |- late_out (c_DIST _ _ _) => apply bm_DIST
    | |- late_out (c_DISTEXT _) => apply bm_DISTEXT
    | |- late_out (c_MATCH _) => apply bm_MATCH
    | |- late_out (c_LIT _) => apply bm_LIT
    end; exact L. }
  destruct (stepf2 flush lenfix_list distfix_list m) as [m'|r m']; [|exact I].
  destruct O as [R|R]; [|right; right; exact R].
  destruct (Z.eq_dec (m_mode m') CHECK) as [C|C]; [right; left; exact C|].
  left. apply bm_blk_range. unfold LIT, CHECK in *. lia.
Qed.
