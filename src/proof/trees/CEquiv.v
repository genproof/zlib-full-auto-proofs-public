(** * The checked model of trees.c computes what the model computes

    For every checked function [c_X] of CModel.v: when [c_X args] is [Some r], the model part of [r] is
    [Model.X args].  The statements are instances of the class [CRel proj c m]:
    [forall r, c = Some r -> proj r = m] ([proj] = [id], or [fst] for a [cout] / [cstate] result, or
    [fun r => (fst (fst r), snd r)] for a [cstate * _] result).

    For the output functions (they only append to pending_buf), the mask: [CApp m p c] says that when [c] is
    [Some (o', m')], [m'] is [m] with [p, o_pending o') set to true, [p <= o_pending o'], and [m'] has the length
    of [m] ([mask_after]). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.trees.CModel.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** Basic facts *)

Lemma rd_Some l i x : rd l i = Some x -> x = Znth i l /\ 0 <= i < Zlength l.
Proof.
  unfold rd, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:E; intros H; inversion H.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in E. split; [reflexivity | lia].
Qed.

Lemma wr_Some l i v l' : wr l i v = Some l' -> l' = upd_Znth i l v /\ 0 <= i < Zlength l.
Proof.
  unfold wr, in_range. destruct ((0 <=? i) && (i <? Zlength l)) eqn:E; intros H; inversion H.
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in E. split; [reflexivity | lia].
Qed.

Lemma some_inj {A} (a b : A) : Some a = Some b -> a = b.
Proof. congruence. Qed.

Lemma pair_inj {A B} (a c : A) (b d : B) : (a, b) = (c, d) -> a = c /\ b = d.
Proof. intros H; inversion H; auto. Qed.

Lemma guard_Some b u : guard b = Some u -> b = true.
Proof. destruct b; easy. Qed.

Lemma Zlength_upd_Znth_any {A} i (l : list A) v : Zlength (upd_Znth i l v) = Zlength l.
Proof.
  destruct (Z_le_gt_dec 0 i); [destruct (Z_lt_ge_dec i (Zlength l))|].
  - apply upd_Znth_Zlength; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
  - rewrite upd_Znth_out_of_range; auto; lia.
Qed.

(** ** The equivalence class and the tactic *)

Class CRel {A B : Type} (proj : A -> B) (c : option A) (m : B) : Prop :=
  crel : forall r, c = Some r -> proj r = m.

(** Instance resolution matches the head function only (no unfolding of the checked functions). *)
#[export] Typeclasses Opaque rd wr guard bind
  c_set_fc c_set_dl c_rd_pb c_smaller c_pqdownheap_loop c_pqdownheap c_gen_bitlen_pass1 c_find_nonzero_down c_gen_bitlen_repair c_gen_bitlen_reassign_inner c_gen_bitlen_reassign c_gen_bitlen c_bi_reverse_loop c_bi_reverse c_gen_next_code c_gen_codes_loop c_gen_codes c_bt_init c_bt_force c_bt_heapify c_pqremove c_store_removed c_new_node c_merge_body c_bt_merge c_build_tree c_scan_tree_loop c_scan_tree c_find_max_blindex c_build_bl_tree c_put_byte c_put_short c_send_bits c_send_code c_bi_flush c_bi_windup c_send_codes c_send_tree_loop c_send_tree c_send_bl_lens c_send_all_trees c_d_code c_send_symbol c_compress_loop c_compress_block c_zero_fc c_init_block c_tr_init c_put_sym c_incr_lfreq c_incr_dfreq c_tr_tally c_tr_tally_lit c_tr_tally_dist c_dd_block c_dd_allow c_detect_data_type c_tr_stored_block c_tr_flush_bits c_tr_align c_tr_flush_block.

Notation cid := (fun x => x).

Definition proj_sk {S M K : Type} (r : (S * M) * K) : S * K := (fst (fst r), snd r).

Ltac cstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cout |- _ => destruct x
  | x : cstate |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply some_inj in H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : false = true |- _ => discriminate H
  | H : true = false |- _ => discriminate H
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | E : rd _ _ = Some ?x |- _ =>
      apply rd_Some in E; destruct E as [E ?]; first [subst x | idtac]
  | E : wr _ _ _ = Some ?x |- _ =>
      apply wr_Some in E; destruct E as [E ?]; first [subst x | idtac]
  | E : guard _ = Some _ |- _ => apply guard_Some in E
  | E : ?c = Some ?r |- _ =>
      let Q := fresh "Q" in
      pose proof (crel r E) as Q; clear E; cbv beta iota zeta delta [fst snd proj_sk] in Q
  | Q : ?x = ?m |- _ => is_var x; subst x
  | Q : (_, _) = (_, _) |- _ => apply pair_inj in Q; destruct Q; subst
  | Q : (_, _) = ?m |- _ => let Em := fresh "Em" in destruct m eqn:Em
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac cnorm := cbv beta iota zeta delta [andb orb negb fst snd proj_sk] in *.

Ltac rw_bools :=
  repeat match goal with
  | Hb : ?b = true |- context [?b] => rewrite Hb
  | Hb : ?b = false |- context [?b] => rewrite Hb
  | Hb : ?b = (_, _) |- context [?b] => rewrite Hb
  end.

Ltac crun :=
  cnorm; repeat (cstep; cnorm);
  repeat (progress rw_bools; cnorm);
  try reflexivity;
  try (repeat match goal with Em : _ = (_, _) |- _ => rewrite <- Em; clear Em end; reflexivity).

Ltac cstart := intros ? ?; cbv beta iota zeta delta [fst snd proj_sk] in *.

(** ** Tree updates, pending_buf reads *)

#[export] Instance crel_set_fc t i v : CRel cid (c_set_fc t i v) (set_fc t i v).
Proof. cstart. unfold c_set_fc in *. crun. Qed.

#[export] Instance crel_set_dl t i v : CRel cid (c_set_dl t i v) (set_dl t i v).
Proof. cstart. unfold c_set_dl in *. crun. Qed.

#[export] Instance crel_rd_pb o m i : CRel cid (c_rd_pb (o, m) i) (Znth i (o_buf o)).
Proof. cstart. unfold c_rd_pb in *. crun. Qed.

(** ** pqdownheap *)

#[export] Instance crel_smaller t d n m : CRel cid (c_smaller t d n m) (smaller t d n m).
Proof. cstart. unfold c_smaller, smaller in *. crun. Qed.

#[export] Instance crel_pqdownheap_loop : forall fuel t depth hl v heap k j,
  CRel cid (c_pqdownheap_loop fuel t depth hl v heap k j) (pqdownheap_loop fuel t depth hl v heap k j).
Proof.
  induction fuel; intros; cstart; cbn [c_pqdownheap_loop pqdownheap_loop] in *; crun.
Qed.

#[export] Instance crel_pqdownheap t w k : CRel cid (c_pqdownheap t w k) (pqdownheap t w k).
Proof. cstart. unfold c_pqdownheap, pqdownheap in *. crun. Qed.

(** ** gen_bitlen *)

#[export] Instance crel_gen_bitlen_pass1 : forall fuel sd max_code t w overflow h,
  CRel cid (c_gen_bitlen_pass1 fuel sd max_code t w overflow h) (gen_bitlen_pass1 fuel sd max_code t w overflow h).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_bitlen_pass1 gen_bitlen_pass1] in *; crun.
Qed.

#[export] Instance crel_find_nonzero_down : forall fuel bl_count bits,
  CRel cid (c_find_nonzero_down fuel bl_count bits) (find_nonzero_down fuel bl_count bits).
Proof.
  induction fuel; intros; cstart; cbn [c_find_nonzero_down find_nonzero_down] in *; crun.
Qed.

#[export] Instance crel_gen_bitlen_repair : forall fuel max_length bl_count overflow,
  CRel cid (c_gen_bitlen_repair fuel max_length bl_count overflow) (gen_bitlen_repair fuel max_length bl_count overflow).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_bitlen_repair gen_bitlen_repair] in *; crun.
Qed.

#[export] Instance crel_gen_bitlen_reassign_inner : forall fuel max_code bits heap t opt_len h n,
  CRel cid (c_gen_bitlen_reassign_inner fuel max_code bits heap t opt_len h n)
           (gen_bitlen_reassign_inner fuel max_code bits heap t opt_len h n).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_bitlen_reassign_inner gen_bitlen_reassign_inner] in *; crun.
Qed.

#[export] Instance crel_gen_bitlen_reassign : forall fuel max_code heap bl_count t opt_len h bits,
  CRel cid (c_gen_bitlen_reassign fuel max_code heap bl_count t opt_len h bits)
           (gen_bitlen_reassign fuel max_code heap bl_count t opt_len h bits).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_bitlen_reassign gen_bitlen_reassign] in *; crun.
Qed.

#[export] Instance crel_gen_bitlen sd max_code t w :
  CRel cid (c_gen_bitlen sd max_code t w) (gen_bitlen sd max_code t w).
Proof. cstart. unfold c_gen_bitlen, gen_bitlen in *. crun. Qed.

(** ** gen_codes, bi_reverse *)

#[export] Instance crel_bi_reverse_loop : forall fuel code res len,
  CRel cid (c_bi_reverse_loop fuel code res len) (bi_reverse_loop fuel code res len).
Proof.
  induction fuel; intros; cstart; cbn [c_bi_reverse_loop bi_reverse_loop] in *; crun.
Qed.

#[export] Instance crel_bi_reverse code len : CRel cid (c_bi_reverse code len) (bi_reverse code len).
Proof. cstart. unfold c_bi_reverse, bi_reverse in *. crun. Qed.

#[export] Instance crel_gen_next_code : forall fuel bl_count next_code code bits,
  CRel cid (c_gen_next_code fuel bl_count next_code code bits) (gen_next_code fuel bl_count next_code code bits).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_next_code gen_next_code] in *; crun.
Qed.

#[export] Instance crel_gen_codes_loop : forall fuel max_code t next_code n,
  CRel cid (c_gen_codes_loop fuel max_code t next_code n) (gen_codes_loop fuel max_code t next_code n).
Proof.
  induction fuel; intros; cstart; cbn [c_gen_codes_loop gen_codes_loop] in *; crun.
Qed.

#[export] Instance crel_gen_codes t max_code bl_count :
  CRel cid (c_gen_codes t max_code bl_count) (gen_codes t max_code bl_count).
Proof. cstart. unfold c_gen_codes, gen_codes in *. crun. Qed.

(** ** build_tree *)

#[export] Instance crel_bt_init : forall fuel elems t w max_code n,
  CRel cid (c_bt_init fuel elems t w max_code n) (bt_init fuel elems t w max_code n).
Proof.
  induction fuel; intros; cstart; cbn [c_bt_init bt_init] in *; crun.
Qed.

#[export] Instance crel_bt_force : forall fuel sd t w max_code,
  CRel cid (c_bt_force fuel sd t w max_code) (bt_force fuel sd t w max_code).
Proof.
  induction fuel; intros; cstart; cbn [c_bt_force bt_force] in *; crun.
Qed.

#[export] Instance crel_bt_heapify : forall fuel t w n,
  CRel cid (c_bt_heapify fuel t w n) (bt_heapify fuel t w n).
Proof.
  induction fuel; intros; cstart; cbn [c_bt_heapify bt_heapify] in *; crun.
Qed.

#[export] Instance crel_pqremove t w : CRel cid (c_pqremove t w) (pqremove t w).
Proof. cstart. unfold c_pqremove, pqremove in *. crun. Qed.

#[export] Instance crel_store_removed w x : CRel cid (c_store_removed w x) (store_removed w x).
Proof. cstart. unfold c_store_removed, store_removed in *. crun. Qed.

#[export] Instance crel_new_node t w n m node : CRel cid (c_new_node t w n m node) (new_node t w n m node).
Proof. cstart. unfold c_new_node, new_node in *. crun. Qed.

#[export] Instance crel_merge_body t w node : CRel cid (c_merge_body t w node) (merge_body t w node).
Proof. cstart. unfold c_merge_body, merge_body in *. crun. Qed.

#[export] Instance crel_bt_merge : forall fuel t w node,
  CRel cid (c_bt_merge fuel t w node) (bt_merge fuel t w node).
Proof.
  induction fuel; intros; cstart; cbn [c_bt_merge bt_merge] in *; crun.
Qed.

#[export] Instance crel_build_tree sd t w : CRel cid (c_build_tree sd t w) (build_tree sd t w).
Proof. cstart. unfold c_build_tree, build_tree in *. crun. Qed.

(** ** scan_tree, build_bl_tree *)

#[export] Instance crel_scan_tree_loop : forall fuel t max_code blf n prevlen nextlen count max_count min_count,
  CRel cid (c_scan_tree_loop fuel t max_code blf n prevlen nextlen count max_count min_count)
           (scan_tree_loop fuel t max_code blf n prevlen nextlen count max_count min_count).
Proof.
  induction fuel; intros; cstart; cbn [c_scan_tree_loop scan_tree_loop] in *; crun.
Qed.

#[export] Instance crel_scan_tree t max_code bl : CRel cid (c_scan_tree t max_code bl) (scan_tree t max_code bl).
Proof. cstart. unfold c_scan_tree, scan_tree in *. crun. Qed.

#[export] Instance crel_find_max_blindex : forall fuel bl i,
  CRel cid (c_find_max_blindex fuel bl i) (find_max_blindex fuel bl i).
Proof.
  induction fuel; intros; cstart; cbn [c_find_max_blindex find_max_blindex] in *; crun.
Qed.

#[export] Instance crel_build_bl_tree s : CRel cid (c_build_bl_tree s) (build_bl_tree s).
Proof. cstart. unfold c_build_bl_tree, build_bl_tree in *. crun. Qed.

(** ** Bit output *)

(** put_byte: the checked write, exactly. *)
Lemma c_put_byte_spec o m c :
  c_put_byte (o, m) c =
  if in_range (o_pending o) (Zlength (o_buf o)) then Some (put_byte o c, upd_Znth (o_pending o) m true) else None.
Proof. unfold c_put_byte, wr, put_byte. destruct (in_range (o_pending o) (Zlength (o_buf o))); reflexivity. Qed.

#[export] Instance crel_put_byte o m c : CRel fst (c_put_byte (o, m) c) (put_byte o c).
Proof. cstart. unfold c_put_byte, put_byte in *. crun. Qed.

#[export] Instance crel_put_short o m w : CRel fst (c_put_short (o, m) w) (put_short o w).
Proof. cstart. unfold c_put_short, put_short in *. crun. Qed.

#[export] Instance crel_send_bits o m v l : CRel fst (c_send_bits (o, m) v l) (send_bits o v l).
Proof. cstart. unfold c_send_bits, send_bits in *. crun. Qed.

#[export] Instance crel_send_code o m c codes lens : CRel fst (c_send_code (o, m) c codes lens) (send_code o c codes lens).
Proof. cstart. unfold c_send_code, send_code in *. crun. Qed.

#[export] Instance crel_bi_flush o m : CRel fst (c_bi_flush (o, m)) (bi_flush o).
Proof. cstart. unfold c_bi_flush, bi_flush in *. crun. Qed.

#[export] Instance crel_bi_windup o m : CRel fst (c_bi_windup (o, m)) (bi_windup o).
Proof. cstart. unfold c_bi_windup, bi_windup in *. crun. Qed.

(** ** send_tree, send_all_trees *)

Lemma c_send_codes_gen : forall fuel o m c codes lens count r,
  c_send_codes fuel (o, m) c codes lens count = Some r ->
  1 <= count /\ fst r = Nat.iter (Z.to_nat count) (fun o => send_code o c codes lens) o.
Proof.
  induction fuel; intros o m c codes lens count r H; cbn [c_send_codes] in H; [discriminate H|].
  destruct (c_send_code (o, m) c codes lens) as [[o1 m1]|] eqn:E; unfold bind at 1 in H; [|discriminate H].
  apply crel in E. cbv [fst] in E. subst o1.
  destruct (count - 1 =? 0) eqn:Hc; cbv [negb] in H.
  - apply some_inj in H. subst r. apply Z.eqb_eq in Hc.
    replace count with 1 by lia. split; [lia | reflexivity].
  - apply IHfuel in H. destruct H as [H1 H2]. apply Z.eqb_neq in Hc. split; [lia|].
    rewrite H2. replace (Z.to_nat count) with (S (Z.to_nat (count - 1))) by lia.
    rewrite Nat.iter_succ_r. reflexivity.
Qed.

#[export] Instance crel_send_codes o m c codes lens count :
  CRel fst (c_send_codes (Z.to_nat count) (o, m) c codes lens count)
           (Nat.iter (Z.to_nat count) (fun o => send_code o c codes lens) o).
Proof. intros r H. apply c_send_codes_gen in H. apply H. Qed.

#[export] Instance crel_send_tree_loop : forall fuel t max_code blc bll o m n prevlen nextlen count max_count min_count,
  CRel fst (c_send_tree_loop fuel t max_code blc bll (o, m) n prevlen nextlen count max_count min_count)
           (send_tree_loop fuel t max_code blc bll o n prevlen nextlen count max_count min_count).
Proof.
  induction fuel; intros; cstart; cbn [c_send_tree_loop send_tree_loop] in *; crun.
Qed.

#[export] Instance crel_send_tree o m t max_code bl : CRel fst (c_send_tree (o, m) t max_code bl) (send_tree o t max_code bl).
Proof. cstart. unfold c_send_tree, send_tree in *. crun. Qed.

#[export] Instance crel_send_bl_lens : forall fuel bl o m rank blcodes,
  CRel fst (c_send_bl_lens fuel bl (o, m) rank blcodes) (send_bl_lens fuel bl o rank blcodes).
Proof.
  induction fuel; intros; cstart; cbn [c_send_bl_lens send_bl_lens] in *; crun.
Qed.

#[export] Instance crel_send_all_trees o m lt dt bl lcodes dcodes blcodes :
  CRel fst (c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes) (send_all_trees o lt dt bl lcodes dcodes blcodes).
Proof. cstart. unfold c_send_all_trees, send_all_trees in *. crun. Qed.

(** ** compress_block *)

#[export] Instance crel_d_code dist : CRel cid (c_d_code dist) (d_code dist).
Proof. cstart. unfold c_d_code, d_code in *. crun. Qed.

#[export] Instance crel_send_symbol o m lcodes llens dcodes dlens dist lc :
  CRel fst (c_send_symbol (o, m) lcodes llens dcodes dlens dist lc) (send_symbol o lcodes llens dcodes dlens dist lc).
Proof. cstart. unfold c_send_symbol, send_symbol in *. crun. Qed.

#[export] Instance crel_compress_loop : forall fuel lit_bufsize sym_next lcodes llens dcodes dlens o m sx,
  CRel fst (c_compress_loop fuel lit_bufsize sym_next lcodes llens dcodes dlens (o, m) sx)
           (compress_loop fuel lit_bufsize sym_next lcodes llens dcodes dlens o sx).
Proof.
  induction fuel; intros; cstart; cbn [c_compress_loop compress_loop] in *; crun.
Qed.

#[export] Instance crel_compress_block o m lit_bufsize sym_next lcodes llens dcodes dlens :
  CRel fst (c_compress_block (o, m) lit_bufsize sym_next lcodes llens dcodes dlens)
           (compress_block o lit_bufsize sym_next lcodes llens dcodes dlens).
Proof. cstart. unfold c_compress_block, compress_block in *. crun. Qed.

(** ** init_block, _tr_init, _tr_tally, detect_data_type *)

#[export] Instance crel_zero_fc : forall fuel t n hi, CRel cid (c_zero_fc fuel t n hi) (zero_fc fuel t n hi).
Proof.
  induction fuel; intros; cstart; cbn [c_zero_fc zero_fc] in *; crun.
Qed.

#[export] Instance crel_init_block s : CRel cid (c_init_block s) (init_block s).
Proof. cstart. unfold c_init_block, init_block in *. crun. Qed.

#[export] Instance crel_tr_init s m : CRel fst (c_tr_init (s, m)) (tr_init s).
Proof. cstart. unfold c_tr_init, tr_init in *. crun. Qed.

#[export] Instance crel_put_sym s m b : CRel fst (c_put_sym (s, m) b) (put_sym s b).
Proof. cstart. unfold c_put_sym, put_sym in *. crun. Qed.

#[export] Instance crel_incr_lfreq s i : CRel cid (c_incr_lfreq s i) (incr_lfreq s i).
Proof. cstart. unfold c_incr_lfreq, incr_lfreq in *. crun. Qed.

#[export] Instance crel_incr_dfreq s i : CRel cid (c_incr_dfreq s i) (incr_dfreq s i).
Proof. cstart. unfold c_incr_dfreq, incr_dfreq in *. crun. Qed.

#[export] Instance crel_tr_tally s m dist lc : CRel proj_sk (c_tr_tally (s, m) dist lc) (tr_tally s dist lc).
Proof. cstart. unfold c_tr_tally, tr_tally in *. crun. Qed.

#[export] Instance crel_tr_tally_lit s m c : CRel proj_sk (c_tr_tally_lit (s, m) c) (tr_tally_lit s c).
Proof. cstart. unfold c_tr_tally_lit, tr_tally_lit in *. crun. Qed.

#[export] Instance crel_tr_tally_dist s m distance length :
  CRel proj_sk (c_tr_tally_dist (s, m) distance length) (tr_tally_dist s distance length).
Proof. cstart. unfold c_tr_tally_dist, tr_tally_dist in *. crun. Qed.

#[export] Instance crel_dd_block : forall fuel lf n, CRel cid (c_dd_block fuel lf n) (dd_block fuel lf n).
Proof.
  induction fuel; intros; cstart; cbn [c_dd_block dd_block] in *; crun.
Qed.

#[export] Instance crel_dd_allow : forall fuel lf n, CRel cid (c_dd_allow fuel lf n) (dd_allow fuel lf n).
Proof.
  induction fuel; intros; cstart; cbn [c_dd_allow dd_allow] in *; crun.
Qed.

#[export] Instance crel_detect_data_type lf : CRel cid (c_detect_data_type lf) (detect_data_type lf).
Proof. cstart. unfold c_detect_data_type, detect_data_type in *. crun. Qed.

(** ** _tr_stored_block, _tr_flush_bits, _tr_align, _tr_flush_block *)

#[export] Instance crel_tr_stored_block o m buf stored_len last :
  CRel fst (c_tr_stored_block (o, m) buf stored_len last) (tr_stored_block o buf stored_len last).
Proof. cstart. unfold c_tr_stored_block, tr_stored_block in *. crun. Qed.

#[export] Instance crel_tr_flush_bits o m : CRel fst (c_tr_flush_bits (o, m)) (tr_flush_bits o).
Proof. cstart. unfold c_tr_flush_bits, tr_flush_bits in *. crun. Qed.

#[export] Instance crel_tr_align o m : CRel fst (c_tr_align (o, m)) (tr_align o).
Proof. cstart. unfold c_tr_align, tr_align in *. crun. Qed.

#[export] Instance crel_tr_flush_block s m buf stored_len last :
  CRel proj_sk (c_tr_flush_block (s, m) buf stored_len last) (tr_flush_block s buf stored_len last).
Proof. cstart. unfold c_tr_flush_block, tr_flush_block in *. crun. Qed.

(** * Masks: the output functions only append to pending_buf *)

(** [m'] is [m] with [lo, hi) set to true, of the same length. *)
Definition mask_after (m m' : list bool) (lo hi : Z) : Prop :=
  lo <= hi /\ Zlength m' = Zlength m /\
  forall i, 0 <= i < Zlength m -> Znth i m' = (if (lo <=? i) && (i <? hi) then true else Znth i m).

Lemma mask_after_refl m p : mask_after m m p p.
Proof.
  split; [lia | split; [reflexivity|]]. intros i Hi.
  destruct (Z.leb_spec p i), (Z.ltb_spec i p); simpl; auto; lia.
Qed.

Lemma mask_after_trans m1 m2 m3 a b c :
  mask_after m1 m2 a b -> mask_after m2 m3 b c -> mask_after m1 m3 a c.
Proof.
  intros [Hab [L1 P1]] [Hbc [L2 P2]]. split; [lia | split; [lia|]]. intros i Hi.
  rewrite P2 by lia. rewrite P1 by lia.
  destruct (Z.leb_spec b i), (Z.ltb_spec i c), (Z.leb_spec a i), (Z.ltb_spec i b); simpl; auto; lia.
Qed.

Lemma mask_after_upd m p : mask_after m (upd_Znth p m true) p (p + 1).
Proof.
  split; [lia | split; [apply Zlength_upd_Znth_any|]]. intros i Hi.
  destruct (Z.eq_dec i p) as [->|Hne].
  - rewrite upd_Znth_same by lia. destruct (Z.leb_spec p p), (Z.ltb_spec p (p + 1)); simpl; auto; lia.
  - replace ((p <=? i) && (i <? p + 1)) with false
      by (destruct (Z.leb_spec p i), (Z.ltb_spec i (p + 1)); simpl; auto; lia).
    destruct (Z_le_gt_dec 0 p); [destruct (Z_lt_ge_dec p (Zlength m))|].
    + apply upd_Znth_diff; lia.
    + rewrite upd_Znth_out_of_range by lia. reflexivity.
    + rewrite upd_Znth_out_of_range by lia. reflexivity.
Qed.

Lemma mask_set_n_after : forall n m p, mask_after m (mask_set_n n m p) p (p + Z.of_nat n).
Proof.
  induction n; intros m p; cbn [mask_set_n].
  - rewrite Z.add_0_r. apply mask_after_refl.
  - eapply mask_after_trans; [apply mask_after_upd|].
    replace (p + Z.of_nat (S n)) with (p + 1 + Z.of_nat n) by lia. apply IHn.
Qed.

Class CApp (m : list bool) (p : Z) (c : option cout) : Prop :=
  capp : forall o' m', c = Some (o', m') -> mask_after m m' p (o_pending o').

Ltac mstep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cout |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply some_inj in H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : false = true |- _ => discriminate H
  | H : true = false |- _ => discriminate H
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | Q : (_, _) = (_, _) |- _ => apply pair_inj in Q; destruct Q; subst
  | E : guard _ = Some _ |- _ => apply guard_Some in E
  | E : _ = Some (_, _) |- _ => let A := fresh "A" in pose proof (capp _ _ E) as A; clear E
  | E : _ = Some ?r |- _ =>
      lazymatch type of r with Z => clear E | unit => clear E | bool => clear E | list Z => clear E end
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Ltac mchain :=
  repeat match goal with
  | A1 : mask_after ?m1 ?m2 ?a ?b, A2 : mask_after ?m2 ?m3 ?b ?c |- _ =>
      pose proof (mask_after_trans _ _ _ _ _ _ A1 A2); clear A1 A2
  end.

Ltac mrun :=
  repeat (mstep; cbv beta iota zeta delta [andb orb negb fst snd] in *);
  cbn [o_pending set_bits fst snd] in *; mchain;
  try assumption; try apply mask_after_refl.

Ltac mstart := intros ? ? ?.

#[export] Instance capp_put_byte o m c : CApp m (o_pending o) (c_put_byte (o, m) c).
Proof. mstart. unfold c_put_byte in *. mrun. apply mask_after_upd. Qed.

#[export] Instance capp_put_short o m w : CApp m (o_pending o) (c_put_short (o, m) w).
Proof. mstart. unfold c_put_short in *. mrun. Qed.

#[export] Instance capp_send_bits o m v l : CApp m (o_pending o) (c_send_bits (o, m) v l).
Proof. mstart. unfold c_send_bits in *. mrun. Qed.

#[export] Instance capp_send_code o m c codes lens : CApp m (o_pending o) (c_send_code (o, m) c codes lens).
Proof. mstart. unfold c_send_code in *. mrun. Qed.

#[export] Instance capp_bi_flush o m : CApp m (o_pending o) (c_bi_flush (o, m)).
Proof. mstart. unfold c_bi_flush in *. mrun. Qed.

#[export] Instance capp_bi_windup o m : CApp m (o_pending o) (c_bi_windup (o, m)).
Proof. mstart. unfold c_bi_windup in *. mrun. Qed.

#[export] Instance capp_send_codes : forall fuel o m c codes lens count,
  CApp m (o_pending o) (c_send_codes fuel (o, m) c codes lens count).
Proof. induction fuel; intros; mstart; cbn [c_send_codes] in *; mrun. Qed.

#[export] Instance capp_send_tree_loop : forall fuel t max_code blc bll o m n prevlen nextlen count max_count min_count,
  CApp m (o_pending o) (c_send_tree_loop fuel t max_code blc bll (o, m) n prevlen nextlen count max_count min_count).
Proof. induction fuel; intros; mstart; cbn [c_send_tree_loop] in *; mrun. Qed.

#[export] Instance capp_send_tree o m t max_code bl : CApp m (o_pending o) (c_send_tree (o, m) t max_code bl).
Proof. mstart. unfold c_send_tree in *. mrun. Qed.

#[export] Instance capp_send_bl_lens : forall fuel bl o m rank blcodes,
  CApp m (o_pending o) (c_send_bl_lens fuel bl (o, m) rank blcodes).
Proof. induction fuel; intros; mstart; cbn [c_send_bl_lens] in *; mrun. Qed.

#[export] Instance capp_send_all_trees o m lt dt bl lcodes dcodes blcodes :
  CApp m (o_pending o) (c_send_all_trees (o, m) lt dt bl lcodes dcodes blcodes).
Proof. mstart. unfold c_send_all_trees in *. mrun. Qed.

#[export] Instance capp_send_symbol o m lcodes llens dcodes dlens dist lc :
  CApp m (o_pending o) (c_send_symbol (o, m) lcodes llens dcodes dlens dist lc).
Proof. mstart. unfold c_send_symbol in *. mrun. Qed.

#[export] Instance capp_compress_loop : forall fuel lit_bufsize sym_next lcodes llens dcodes dlens o m sx,
  CApp m (o_pending o) (c_compress_loop fuel lit_bufsize sym_next lcodes llens dcodes dlens (o, m) sx).
Proof. induction fuel; intros; mstart; cbn [c_compress_loop] in *; mrun. Qed.

#[export] Instance capp_compress_block o m lit_bufsize sym_next lcodes llens dcodes dlens :
  CApp m (o_pending o) (c_compress_block (o, m) lit_bufsize sym_next lcodes llens dcodes dlens).
Proof. mstart. unfold c_compress_block in *. mrun. Qed.

#[export] Instance capp_tr_flush_bits o m : CApp m (o_pending o) (c_tr_flush_bits (o, m)).
Proof. mstart. unfold c_tr_flush_bits in *. mrun. Qed.

#[export] Instance capp_tr_align o m : CApp m (o_pending o) (c_tr_align (o, m)).
Proof. mstart. unfold c_tr_align in *. mrun. Qed.

#[export] Instance capp_tr_stored_block o m buf stored_len last :
  CApp m (o_pending o) (c_tr_stored_block (o, m) buf stored_len last).
Proof.
  mstart. unfold c_tr_stored_block in *. mrun.
  all: repeat match goal with H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H end.
  all: repeat match goal with
       | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
       | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
       | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
       end.
  - eapply mask_after_trans; [eassumption|].
    pose proof (mask_set_n_after (Z.to_nat stored_len) l2 (o_pending o3)) as M.
    rewrite Z2Nat.id in M by lia. exact M.
  - subst stored_len. rewrite Z.add_0_r. assumption.
Qed.

(** Functions that do not touch pending_buf leave [tr_out] alone. *)
Ltac ostep :=
  match goal with
  | x : (_ * _)%type |- _ => destruct x
  | x : cstate |- _ => destruct x
  | x : cout |- _ => destruct x
  | H : Some _ = Some _ |- _ => apply some_inj in H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : bind ?a _ = Some _ |- _ =>
      let E := fresh "E" in
      destruct a eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [| discriminate H]
  | Q : (_, _) = (_, _) |- _ => apply pair_inj in Q; destruct Q; subst
  | E : _ = Some _ |- _ => clear E
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Lemma c_init_block_out s s' : c_init_block s = Some s' -> tr_out s' = tr_out s.
Proof. intros H. unfold c_init_block in H. repeat ostep. reflexivity. Qed.

Lemma c_build_bl_tree_out s s' x : c_build_bl_tree s = Some (s', x) -> tr_out s' = tr_out s.
Proof. intros H. unfold c_build_bl_tree in H. repeat ostep. reflexivity. Qed.

Lemma c_tr_flush_block_mask s m buf stored_len last s' m' k :
  c_tr_flush_block (s, m) buf stored_len last = Some ((s', m'), k) ->
  mask_after m m' (o_pending (tr_out s)) (o_pending (tr_out s')).
Proof.
  intros H. unfold c_tr_flush_block in H.
  (* the trees part leaves tr_out alone *)
  destruct (if tr_level s >? 0 then _ else _) as [[[[s1 ol] sl] mb]|] eqn:E1;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (O1 : tr_out s1 = tr_out s).
  { destruct (tr_level s >? 0); [|apply some_inj in E1; inversion E1; reflexivity].
    repeat match goal with
    | E : bind ?a _ = Some _ |- _ =>
        let E' := fresh "E" in
        destruct a eqn:E'; unfold bind at 1 in E; cbv beta iota zeta in E; [| discriminate E]
    | x : (_ * _)%type |- _ => destruct x
    | E : (if ?b then _ else _) = Some _ |- _ => destruct b
    end.
    all: repeat match goal with E : Some _ = Some _ |- _ => apply some_inj in E end.
    all: repeat match goal with E : (_, _) = (_, _) |- _ => apply pair_inj in E; destruct E end.
    all: subst.
    all: repeat match goal with E : c_build_bl_tree _ = Some _ |- _ => apply c_build_bl_tree_out in E end.
    all: match goal with E : tr_out _ = tr_out _ |- _ => rewrite E; reflexivity end. }
  rewrite <- O1. clear E1 O1.
  destruct (match buf with Some _ => _ | None => _ end) as [[[o2 m2] kd]|] eqn:E2;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  assert (A2 : mask_after m m2 (o_pending (tr_out s1)) (o_pending o2)).
  { clear H. repeat mstep. all: cbn [o_pending set_bits fst snd] in *; mchain; assumption. }
  destruct (c_init_block (set_out s1 o2)) as [s3|] eqn:E3;
    unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  apply c_init_block_out in E3. cbn [tr_out set_out] in E3.
  destruct (negb (last =? 0)).
  - destruct (c_bi_windup (tr_out s3, m2)) as [[o4 m4]|] eqn:E4;
      cbv beta iota zeta delta [bind] in H; [|discriminate H].
    apply some_inj in H. inversion H; subst. apply capp in E4.
    cbn [tr_out set_out]. eapply mask_after_trans; eassumption.
  - cbv beta iota zeta delta [bind] in H.
    apply some_inj in H. inversion H; subst. assumption.
Qed.

(** ** The mask keeps its length: the functions that write the symbol buffer *)

Lemma c_put_sym_len s m b s' m' : c_put_sym (s, m) b = Some (s', m') -> Zlength m' = Zlength m.
Proof. intros H. unfold c_put_sym in H. repeat ostep. apply Zlength_upd_Znth_any. Qed.

Ltac lstep :=
  match goal with
  | E : c_put_sym (_, _) _ = Some (_, _) |- _ => apply c_put_sym_len in E
  | _ => ostep
  end.

Lemma c_tr_tally_len s m dist lc s' m' fl : c_tr_tally (s, m) dist lc = Some ((s', m'), fl) -> Zlength m' = Zlength m.
Proof. intros H. unfold c_tr_tally in H. repeat lstep; congruence. Qed.

Lemma c_tr_tally_lit_len s m c s' m' fl : c_tr_tally_lit (s, m) c = Some ((s', m'), fl) -> Zlength m' = Zlength m.
Proof. intros H. unfold c_tr_tally_lit in H. repeat lstep; congruence. Qed.

Lemma c_tr_tally_dist_len s m d l s' m' fl :
  c_tr_tally_dist (s, m) d l = Some ((s', m'), fl) -> Zlength m' = Zlength m.
Proof. intros H. unfold c_tr_tally_dist in H. repeat lstep; congruence. Qed.

Lemma c_tr_init_mask s m s' m' : c_tr_init (s, m) = Some (s', m') -> m' = m /\ tr_out s' = mkOut (o_buf (tr_out s)) (o_pending (tr_out s)) 0 0 0.
Proof.
  intros H. unfold c_tr_init in H.
  destruct (c_init_block _) eqn:E; unfold bind at 1 in H; cbv beta iota zeta in H; [|discriminate H].
  apply some_inj in H. inversion H; subst. apply c_init_block_out in E. rewrite E. split; reflexivity.
Qed.
