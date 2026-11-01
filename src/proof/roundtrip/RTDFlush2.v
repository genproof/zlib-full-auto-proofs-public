(* RT-D: _tr_flush_block emits one Format block (stored, fixed or dynamic) of the block's symbols
   (spec: RTDFix.flush_block_fspec2, interface v2; the original RTDBits.flush_block_fspec is false for a stored
   block of non-bytes).  The parts (interface RTDFlushDefs.v, RTDFlushDefs2.v) are proved in RTDFlush<Part>.v. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDFix.
Require Import Zlib.proof.roundtrip.RTDFlushDefs2.
Require Import Zlib.proof.roundtrip.RTDFlushW Zlib.proof.roundtrip.RTDFlushTab2 Zlib.proof.roundtrip.RTDFlushComp2 Zlib.proof.roundtrip.RTDFlushCanon Zlib.proof.roundtrip.RTDFlushHdr Zlib.proof.roundtrip.RTDFlushToks Zlib.proof.roundtrip.RTDFlushDyn2.
Import ListNotations.
Local Open Scope Z_scope.

Require Import Zlib.proof.trees.CEquiv.
Require Zlib.proof.huffman.FlushStatic.
Open Scope cmodel_scope.

(** ** The checked _tr_flush_block, split at the trees *)
Definition cf_prep (s : tstate) (stored_len : Z) : option (tstate * Z * Z * Z) :=
  if tr_level s >? 0 then
    let* s := (if tr_data_type s =? Z_UNKNOWN then
                 let* dt := c_detect_data_type (fc (tr_ltree s)) in Some (set_data_type s dt)
               else Some s) in
    let* (lt, lmax, w) := c_build_tree static_l_desc (tr_ltree s) (tr_wk s) in
    let s := set_wk (set_lmax (set_ltree s lt) lmax) w in
    let* (dt, dmax, w) := c_build_tree static_d_desc (tr_dtree s) (tr_wk s) in
    let s := set_wk (set_dmax (set_dtree s dt) dmax) w in
    let* (s, max_blindex) := c_build_bl_tree s in
    let opt_lenb := Z.shiftr (u64 (w_opt_len (tr_wk s) + 3 + 7)) 3 in
    let static_lenb := Z.shiftr (u64 (w_static_len (tr_wk s) + 3 + 7)) 3 in
    let opt_lenb := if (static_lenb <=? opt_lenb) || (tr_strategy s =? Z_FIXED) then static_lenb else opt_lenb in
    Some (s, opt_lenb, static_lenb, max_blindex)
  else Some (s, u64 (stored_len + 5), u64 (stored_len + 5), 0).

Lemma cf_prep_rel : forall s sl r, cf_prep s sl = Some r -> r = flush_prep s sl.
Proof. intros s sl r H. unfold cf_prep, flush_prep in *. crun. Qed.

Lemma cf_split : forall s m buf stored_len last,
  c_tr_flush_block (s, m) buf stored_len last =
  let* (s, opt_lenb, static_lenb, max_blindex) := cf_prep s stored_len in
  let* (om, kind) :=
    (match buf with
     | Some b =>
       if u64 (stored_len + 4) <=? opt_lenb then
         let* _ := guard (0 <? Zlength b) in
         let* om := c_tr_stored_block (tr_out s, m) b stored_len last in Some (om, BK_stored)
       else if static_lenb =? opt_lenb then
         let* _ := guard (last <=? 2147483645) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
         Some (om, BK_static)
       else
         let* _ := guard (last <=? 2147483643) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl DYN_TREES 1 + last) 3 in
         let* om := c_send_all_trees om (tr_ltree s) (tr_dtree s) (tr_bltree s)
                      (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1) in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)) in
         Some (om, BK_dynamic)
     | None =>
       if static_lenb =? opt_lenb then
         let* _ := guard (last <=? 2147483645) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
         Some (om, BK_static)
       else
         let* _ := guard (last <=? 2147483643) in
         let* om := c_send_bits (tr_out s, m) (Z.shiftl DYN_TREES 1 + last) 3 in
         let* om := c_send_all_trees om (tr_ltree s) (tr_dtree s) (tr_bltree s)
                      (tr_lmax s + 1) (tr_dmax s + 1) (max_blindex + 1) in
         let* om := c_compress_block om (tr_lit_bufsize s) (tr_sym_next s)
                      (fc (tr_ltree s)) (dl (tr_ltree s)) (fc (tr_dtree s)) (dl (tr_dtree s)) in
         Some (om, BK_dynamic)
     end) in
  let '(o, m) := om in
  let* s := c_init_block (set_out s o) in
  let* (s, m) := (if negb (last =? 0) then
                     let* (o, m) := c_bi_windup (tr_out s, m) in Some (set_out s o, m)
                   else Some (s, m)) in
  Some ((s, m), kind).
Proof. reflexivity. Qed.

(** ** Bit lengths *)
Lemma Zlength_bits_le : forall v n, 0 <= n -> Zlength (F.bits_le v n) = n.
Proof. intros. unfold F.bits_le. rewrite Zlength_map, Zlength_correct, ?seq_length, ?length_seq. lia. Qed.

Lemma Zlength_bytes_bits : forall l, Zlength (F.bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. unfold F.bytes_bits in *. cbn [flat_map].
  rewrite Zlength_app, IH, Zlength_bits_le, Zlength_cons by lia. lia.
Qed.

Lemma obits_len : forall o, bits_ok o -> o_pending o <= Zlength (o_buf o) ->
  Zlength (obits o) = 8 * o_pending o + o_bi_valid o.
Proof.
  intros o [Hv [Hb Hp]] Hl. unfold obits.
  rewrite Zlength_app, Zlength_bytes_bits, Zlength_sublist, Zlength_bits_le by lia. lia.
Qed.

Lemma pad_of_len : forall o0 o3 e p,
  bits_ok o0 -> o_pending o0 = 0 -> (p - o_bi_valid o0) mod 8 = 0 ->
  bits_ok o3 -> o_pending o3 <= Zlength (o_buf o3) -> obits o3 = obits o0 ++ e ->
  F.pad8 (p + Zlength e) = F.pad8 (o_bi_valid o3).
Proof.
  intros o0 o3 e p H0 P0 Hm H3 P3 E.
  assert (L0 := obits_len o0 H0 ltac:(pose proof (Zlength_nonneg (o_buf o0)); lia)).
  assert (L3 := obits_len o3 H3 P3).
  rewrite E, Zlength_app, L0, P0 in L3.
  assert (Hk : p - o_bi_valid o0 = 8 * ((p - o_bi_valid o0) / 8)) by (apply Z_div_exact_full_2; lia).
  unfold F.pad8. f_equal. f_equal.
  replace (p + Zlength e) with (o_bi_valid o3 + (o_pending o3 + (p - o_bi_valid o0) / 8) * 8) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma enc_out_one : forall p blk fin, enc_out p [blk] fin =
  F.enc_block p fin blk ++ (if fin then F.zeros (F.pad8 (p + Zlength (F.enc_block p fin blk))) else []).
Proof.
  intros. unfold enc_out. cbn [enc_from]. rewrite andb_true_r, app_nil_r. destruct fin; [reflexivity|].
  rewrite app_nil_r. reflexivity.
Qed.

(** ** Symbols *)
Lemma syms_rok_in : forall wmax syms out x, syms_rok wmax out syms -> In x syms ->
  if fst x =? 0 then 0 <= snd x < 256 else 0 <= snd x <= 255 /\ 1 <= fst x.
Proof.
  induction syms as [|y r IH]; intros out x H Hin; [destruct Hin|].
  cbn [syms_rok] in H. destruct H as [Hy Hr]. destruct Hin as [->|Hin].
  - destruct (fst x =? 0); [exact Hy|lia].
  - eapply IH; eauto.
Qed.

Lemma zsyms_of : forall wmax out syms, syms_rok wmax out syms ->
  (forall x, In x syms -> valid_sym (fst x) (snd x)) -> zsyms_ok syms.
Proof.
  intros wmax out syms Hr Hv x Hx. pose proof (syms_rok_in _ _ _ _ Hr Hx) as H.
  destruct (Hv x Hx) as [_ D]. destruct (fst x =? 0); lia.
Qed.

(** ** The Huffman branches *)
Lemma huff_room : forall L syms o lc ll dc dlz,
  overlay_ok L syms (o, lc, ll, dc, dlz) -> (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  Zlength syms <= L - 1 ->
  let o' := compress_sep o lc ll dc dlz syms in
  0 <= o_pending o /\ o_pending o' + 2 <= Zlength (o_buf o) /\
  o_pending (send_code o' END_BLOCK lc ll) <= Zlength (o_buf (send_code o' END_BLOCK lc ll)).
Proof.
  intros L syms o lc ll dc dlz Hov Hv Hn o'.
  destruct Hov as [Hok [Hlen [_ [Hc [Hend Hb]]]]].
  destruct (compress_sep_spec syms o lc ll dc dlz Hok (fun x Hx => conj (Hv x Hx) (Hc x Hx))) as [[W [Ok' _]] _].
  fold o' in W, Ok'.
  assert (B := Hb (length syms) (le_n _)). rewrite firstn_all in B. fold o' in B.
  destruct (send_code_spec o' END_BLOCK lc ll Ok' Hend) as [_ [_ [_ [P W2]]]].
  destruct W as [_ [Wl _]]. destruct W2 as [_ [Wl2 _]].
  destruct Ok' as [V' _]. destruct Hok as [_ [_ P0]]. unfold bitpos in B. rewrite <- Zlength_correct in B.
  split; [lia|]. split; [lia|]. rewrite Wl2, Wl. lia.
Qed.

Definition branch_ok (wmax : Z) (out : list Z) (syms : list (Z * Z)) (p : Z) (fin : bool) (o0 o3 : outbuf) : Prop :=
  exists blk, F.block_ok wmax out blk /\ F.block_data out blk = F.syms_data out (map fsym syms) /\
    bits_ok o3 /\ obits o3 = obits o0 ++ F.enc_block p fin blk /\
    F.pad8 (p + Zlength (F.enc_block p fin blk)) = F.pad8 (o_bi_valid o3).

Lemma bits3_static : forall last, 0 <= last <= 1 ->
  F.bits_le (Z.shiftl STATIC_TREES 1 + last) 3 = [last =? 1; true; false].
Proof. intros last H. assert (last = 0 \/ last = 1) as [-> | ->] by lia; reflexivity. Qed.

Lemma bits3_dyn : forall last, 0 <= last <= 1 ->
  F.bits_le (Z.shiftl DYN_TREES 1 + last) 3 = [last =? 1; false; true].
Proof. intros last H. assert (last = 0 \/ last = 1) as [-> | ->] by lia; reflexivity. Qed.

Lemma static_branch : wsend_stmt -> tabs2_stmt -> comp_stmt -> symsok_stmt ->
  forall t syms o1 last wmax out p,
  flush_pre t syms -> 0 <= last <= 1 -> syms_rok wmax out syms -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
  bits_ok o1 -> obits o1 = obits (tr_out t) ++ F.bits_le (Z.shiftl STATIC_TREES 1 + last) 3 ->
  overlay_ok (tr_lit_bufsize t) syms (o1, static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len) ->
  branch_ok wmax out syms p (last =? 1) (tr_out t)
    (compress_block o1 (tr_lit_bufsize t) (3 * Zlength syms)
       static_ltree_code static_ltree_len static_dtree_code static_dtree_len).
Proof.
  intros Hws Htab Hcomp Hsok t syms o1 last wmax out p Hfp Hlast Hrok Hpm Hok1 E1 Hov.
  pose proof Hfp as [_ [Hok0 [Hp0 [Hbv0 Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  destruct (overlay_compress _ _ _ _ _ _ _ Hval Hov) as [Ec _]. rewrite Ec.
  destruct (huff_room _ _ _ _ _ _ _ Hov Hval Hn) as [P1 [R1 R3]].
  destruct Htab as [Tl [Td [Tlen Tdist]]].
  assert (Hz : zsyms_ok syms) by (eapply zsyms_of; eauto).
  assert (Hci : syms_cimpl static_ltree_code static_ltree_len static_dtree_code static_dtree_len
                  F.fixed_ll F.fixed_dl syms).
  { intros x Hx. pose proof (Hz x Hx) as Zx. destruct (fst x =? 0).
    - apply Tl. lia.
    - destruct (Tlen (snd x) ltac:(lia)) as [Ec1 [Hr1 _]]. destruct (Tdist (fst x) ltac:(lia)) as [Ec2 [Hr2 _]].
      split; [apply Tl | apply Td]; lia. }
  destruct (Hcomp o1 _ _ _ _ F.fixed_ll F.fixed_dl syms Hok1 Hz Hci
              (Tl 256 ltac:(lia)) P1 R1) as [Ok3 E3].
  exists (F.Fixed (map fsym syms)). split; [|split; [reflexivity|]].
  - cbn [F.block_ok]. apply Hsok; auto. intros x Hx. pose proof (Hz x Hx) as Zx.
    assert (Ll : Zlength F.fixed_ll = 288) by reflexivity.
    assert (Ld : Zlength F.fixed_dl = 32) by reflexivity.
    destruct (fst x =? 0).
    + destruct (Tl (snd x) ltac:(lia)) as [A [B _]]. lia.
    + destruct (Tlen (snd x) ltac:(lia)) as [Ec1 [Hr1 _]]. destruct (Tdist (fst x) ltac:(lia)) as [Ec2 [Hr2 _]].
      destruct (Tl (257 + F.len_code (snd x + 3)) ltac:(lia)) as [A [B _]].
      destruct (Td (F.dist_code (fst x)) ltac:(lia)) as [A' [B' _]]. lia.
  - assert (Ee : obits (send_code (compress_sep o1 static_ltree_code static_ltree_len static_dtree_code
                                     static_dtree_len syms) END_BLOCK static_ltree_code static_ltree_len) =
                 obits (tr_out t) ++ F.enc_block p (last =? 1) (F.Fixed (map fsym syms))).
    { rewrite E3, E1, bits3_static by lia. cbn [F.enc_block]. rewrite <- app_assoc. reflexivity. }
    split; [exact Ok3|]. split; [exact Ee|].
    exact (pad_of_len (tr_out t) _ _ p Hok0 Hp0 Hpm Ok3 R3 Ee).
Qed.

Lemma dyn_branch : dyn_stmt -> forall t syms sl s' olb slb mbi o1 last wmax out p,
  flush_pre t syms -> 0 < tr_level t -> 0 <= last <= 1 -> flush_prep t sl = (s', olb, slb, mbi) ->
  syms_rok wmax out syms -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
  bits_ok o1 -> Zlength (o_buf o1) = 4 * tr_lit_bufsize t ->
  obits o1 = obits (tr_out t) ++ F.bits_le (Z.shiftl DYN_TREES 1 + last) 3 ->
  overlay_ok (tr_lit_bufsize t) syms
    (send_all_trees o1 (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1),
     fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')) ->
  branch_ok wmax out syms p (last =? 1) (tr_out t)
    (compress_block
       (send_all_trees o1 (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1))
       (tr_lit_bufsize t) (3 * Zlength syms) (fc (tr_ltree s')) (dl (tr_ltree s')) (fc (tr_dtree s')) (dl (tr_dtree s'))).
Proof.
  intros Hdyn t syms sl s' olb slb mbi o1 last wmax out p Hfp Hlev Hlast Ep Hrok Hpm Hok1 L1 E1 Hov.
  pose proof Hfp as [_ [Hok0 [Hp0 [Hbv0 Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  destruct (overlay_compress _ _ _ _ _ _ _ Hval Hov) as [Ec _]. rewrite Ec.
  destruct (huff_room _ _ _ _ _ _ _ Hov Hval Hn) as [_ [_ R3]].
  assert (P1 : 0 <= o_pending o1) by (destruct Hok1 as [_ [_ ?]]; lia).
  destruct (Hdyn t syms sl s' olb slb mbi wmax out o1 Hfp Hlev Ep Hrok Hok1 P1 L1 Hov)
    as (nlen & ndist & clsent & toks & Bok & H3).
  cbv zeta in H3. destruct H3 as [Ok3 E3].
  exists (F.Dynamic nlen ndist clsent toks (map fsym syms)). split; [exact Bok|]. split; [reflexivity|].
  match type of E3 with obits ?o3 = _ =>
    assert (Ee : obits o3 = obits (tr_out t) ++ F.enc_block p (last =? 1) (F.Dynamic nlen ndist clsent toks (map fsym syms)))
      by (rewrite E3, E1, bits3_dyn, enc_block_dyn by lia; rewrite <- app_assoc; reflexivity) end.
  split; [exact Ok3|]. split; [exact Ee|].
  exact (pad_of_len (tr_out t) _ _ p Hok0 Hp0 Hpm Ok3 R3 Ee).
Qed.

Lemma pad_stored : forall p k, 0 <= k -> F.pad8 (p + Z.succ (2 + (F.pad8 (p + 3) + (16 + (16 + 8 * k))))) = F.pad8 0.
Proof. intros p k Hk. unfold F.pad8. Z.to_euclidean_division_equations. lia. Qed.

Lemma stored_branch : stored_block_fspec -> forall o m b sl last o3 m3 wmax out syms p,
  bits_ok o -> 0 <= last <= 1 -> 0 <= p -> (p - o_bi_valid o) mod 8 = 0 ->
  Zlength b = sl -> sl <= 65535 -> Forall F.byte_ok b -> F.syms_data out (map fsym syms) = out ++ b ->
  c_tr_stored_block (o, m) b sl last = Some (o3, m3) ->
  o_bi_valid o3 = 0 /\ branch_ok wmax out syms p (last =? 1) o o3.
Proof.
  intros Hst o m b sl last o3 m3 wmax out syms p Hok Hlast Hp Hpm Hbl Hs Hbb Hdat Hc.
  pose proof (Zlength_nonneg b).
  assert (Hb' : Forall F.byte_ok (sublist 0 sl b)) by (rewrite sublist_same by lia; exact Hbb).
  assert (Hr1 : 0 <= sl <= 65535) by lia. assert (Hr2 : sl = 0 \/ sl <= Zlength b) by lia.
  destruct (Hst o m b sl last o3 m3 p Hok Hlast Hr1 Hr2 Hb' Hp Hpm Hc) as [Ok3 [V3 E3]].
  rewrite sublist_same in E3 by lia.
  split; [exact V3|]. exists (F.Stored b).
  split; [cbn [F.block_ok]; split; [lia|exact Hbb]|]. split; [cbn [F.block_data]; symmetry; exact Hdat|].
  split; [exact Ok3|]. split; [exact E3|]. rewrite V3.
  unfold F.enc_block. rewrite Zlength_cons, !Zlength_app, Zlength_bytes_bits, !Zlength_bits_le by lia.
  assert (Zz : Zlength (F.zeros (F.pad8 (p + 3))) = F.pad8 (p + 3)).
  { unfold F.zeros. rewrite Zlength_correct, repeat_length, Z2Nat.id; [reflexivity|].
    unfold F.pad8. apply Z.mod_pos_bound. lia. }
  rewrite Zz. change (Zlength [false; false]) with 2.
  exact (pad_stored p (Zlength b) H).
Qed.

(** ** The checked runs of the branches *)
Ltac bstep H :=
  match type of H with
  | bind ?a _ = Some _ =>
      let E := fresh "E" in destruct a eqn:E; [cbn [bind] in H|discriminate H]
  | match ?x with (_, _) => _ end = Some _ => destruct x
  end.

Lemma static_run : overlay_statement -> writer_fspec -> wsend_stmt -> tabs2_stmt -> comp_stmt -> symsok_stmt ->
  forall t m buf sl last s2 olb slb mbi o3 m3 k3 syms wmax out p,
  flush_pre t syms -> 0 <= last <= 1 -> syms_rok wmax out syms -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
  flush_prep t sl = (s2, olb, slb, mbi) ->
  flush_call t buf sl last = Some (send_bits (tr_out s2) (Z.shiftl STATIC_TREES 1 + last) 3,
                                   static_ltree_code, static_ltree_len, static_dtree_code, static_dtree_len) ->
  (let* _ := guard (last <=? 2147483645) in
   let* om := c_send_bits (tr_out s2, m) (Z.shiftl STATIC_TREES 1 + last) 3 in
   let* om := c_compress_block om (tr_lit_bufsize s2) (tr_sym_next s2)
                static_ltree_code static_ltree_len static_dtree_code static_dtree_len in
   Some (om, BK_static)) = Some ((o3, m3), k3) ->
  branch_ok wmax out syms p (last =? 1) (tr_out t) o3.
Proof.
  intros Hov Hw Hws Htab Hcomp Hsok t m buf sl last s2 olb slb mbi o3 m3 k3 syms wmax out p
         Hfp Hlast Hrok Hpm Ep Hcall Hrun.
  pose proof Hfp as [_ [Hok0 [Hp0 [Hbv0 Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  pose proof (FlushStatic.flush_prep_keeps t sl) as K. rewrite Ep in K. cbn [fst] in K. destruct K as [Ko [KL Ks]].
  bstep Hrun. bstep Hrun. destruct c as [o1 m1]. bstep Hrun. destruct c as [o3' m3'].
  injection Hrun as Ho3 Hm3 Hk3. subst o3.
  destruct Hw as [Wsend _].
  rewrite Ko in E0.
  destruct (Wsend (tr_out t) m (Z.shiftl STATIC_TREES 1 + last) 3 o1 m1 Hok0 ltac:(lia)
              ltac:(unfold STATIC_TREES; simpl; lia) E0) as [Ok1 E1'].
  pose proof (crel_send_bits _ _ _ _ _ E0) as Q0. cbn [fst] in Q0.
  pose proof (crel_compress_block _ _ _ _ _ _ _ _ _ E1) as Q1. cbn [fst] in Q1.
  rewrite KL, Ks, Hsn in Q1. rewrite Q1.
  rewrite Ko, <- Q0 in Hcall.
  apply static_branch; auto.
  exact (Hov t syms buf sl last Hfp Hlast _ Hcall).
Qed.

Lemma dyn_run : overlay_statement -> writer_fspec -> dyn_stmt ->
  forall t m buf sl last s2 olb slb mbi o3 m3 k3 syms wmax out p,
  flush_pre t syms -> 0 < tr_level t -> 0 <= last <= 1 -> syms_rok wmax out syms ->
  (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
  flush_prep t sl = (s2, olb, slb, mbi) ->
  flush_call t buf sl last =
    Some (send_all_trees (send_bits (tr_out s2) (Z.shiftl DYN_TREES 1 + last) 3)
            (tr_ltree s2) (tr_dtree s2) (tr_bltree s2) (tr_lmax s2 + 1) (tr_dmax s2 + 1) (mbi + 1),
          fc (tr_ltree s2), dl (tr_ltree s2), fc (tr_dtree s2), dl (tr_dtree s2)) ->
  (let* _ := guard (last <=? 2147483643) in
   let* om := c_send_bits (tr_out s2, m) (Z.shiftl DYN_TREES 1 + last) 3 in
   let* om := c_send_all_trees om (tr_ltree s2) (tr_dtree s2) (tr_bltree s2)
                (tr_lmax s2 + 1) (tr_dmax s2 + 1) (mbi + 1) in
   let* om := c_compress_block om (tr_lit_bufsize s2) (tr_sym_next s2)
                (fc (tr_ltree s2)) (dl (tr_ltree s2)) (fc (tr_dtree s2)) (dl (tr_dtree s2)) in
   Some (om, BK_dynamic)) = Some ((o3, m3), k3) ->
  branch_ok wmax out syms p (last =? 1) (tr_out t) o3.
Proof.
  intros Hov Hw Hdyn t m buf sl last s2 olb slb mbi o3 m3 k3 syms wmax out p
         Hfp Hlev Hlast Hrok Hpm Ep Hcall Hrun.
  pose proof Hfp as [_ [Hok0 [Hp0 [Hbv0 Hob]]] [Hsn [Hn [Hval Hsy]]] _ _ _ _].
  pose proof (FlushStatic.flush_prep_keeps t sl) as K. rewrite Ep in K. cbn [fst] in K. destruct K as [Ko [KL Ks]].
  bstep Hrun. bstep Hrun. destruct c as [o1 m1]. bstep Hrun. destruct c as [o2 m2].
  bstep Hrun. destruct c as [o3' m3'].
  injection Hrun as Ho3 Hm3 Hk3. subst o3.
  destruct Hw as [Wsend _].
  rewrite Ko in E0.
  destruct (Wsend (tr_out t) m (Z.shiftl DYN_TREES 1 + last) 3 o1 m1 Hok0 ltac:(lia)
              ltac:(unfold DYN_TREES; simpl; lia) E0) as [Ok1 E1'].
  pose proof (crel_send_bits _ _ _ _ _ E0) as Q0. cbn [fst] in Q0.
  pose proof (crel_send_all_trees _ _ _ _ _ _ _ _ _ E1) as Q1. cbn [fst] in Q1.
  pose proof (crel_compress_block _ _ _ _ _ _ _ _ _ E2) as Q2. cbn [fst] in Q2.
  rewrite KL, Ks, Hsn in Q2. rewrite Q2, Q1.
  rewrite Ko, <- Q0 in Hcall.
  assert (L1 : Zlength (o_buf o1) = 4 * tr_lit_bufsize t).
  { rewrite Q0. destruct (send_bits_spec (tr_out t) (Z.shiftl DYN_TREES 1 + last) 3 Hok0 ltac:(lia)
                            ltac:(unfold DYN_TREES; simpl; lia)) as [_ [_ [_ [_ [_ [W _]]]]]].
    rewrite W. exact Hob. }
  apply (dyn_branch Hdyn t syms sl s2 olb slb mbi o1 last wmax out p); auto.
  exact (Hov t syms buf sl last Hfp Hlast _ Hcall).
Qed.

(** ** _tr_flush_block, when the window bytes of a stored block are bytes *)
Theorem flush_ok_bytes : overlay_statement -> writer_fspec -> stored_block_fspec ->
  forall t m buf sl last t' m' kind syms out wmax p,
    flush_pre t syms -> 0 <= last <= 1 -> 0 <= p -> (p - o_bi_valid (tr_out t)) mod 8 = 0 ->
    syms_rok wmax out syms ->
    (forall b, buf = Some b -> Zlength b = sl /\ sl <= 65535 /\ Forall F.byte_ok b /\
                               F.syms_data out (map fsym syms) = out ++ b) ->
    c_tr_flush_block (t, m) buf sl last = Some ((t', m'), kind) ->
    exists blk,
      F.block_ok wmax out blk /\ F.block_data out blk = F.syms_data out (map fsym syms) /\
      bits_ok (tr_out t') /\ (last = 1 -> o_bi_valid (tr_out t') = 0) /\
      obits (tr_out t') = obits (tr_out t) ++ enc_out p [blk] (last =? 1).
Proof.
  intros Hov Hw Hst t m buf sl last t' m' kind syms out wmax p Hfp Hlast Hp Hpm Hrok Hbuf Hrun.
  assert (Hws := rtd_fw_ok Hw). assert (Htab := rtd_tabs2_ok).
  destruct (rtd_comp2_ok Hws Htab) as [Hcomp Hsok].
  assert (Hdyn := rtd_dyn2_ok Hws Htab Hcomp Hsok rtd_canon_ok (rtd_hdr_ok Hws) rtd_toks_ok).
  pose proof Hfp as [_ [Hok0 [Hp0 [Hbv0 Hob]]] _ _ _ _ _].
  rewrite cf_split in Hrun.
  destruct (cf_prep t sl) as [[[[s2 olb] slb] mbi]|] eqn:Ep; [|discriminate Hrun].
  cbn [bind] in Hrun. apply cf_prep_rel in Ep. symmetry in Ep.
  pose proof (FlushStatic.flush_prep_keeps t sl) as K. rewrite Ep in K. cbn [fst] in K. destruct K as [Ko [KL Ks]].
  assert (Hlev0 : tr_level t <= 0 -> slb = olb).
  { intros Hl. unfold flush_prep in Ep.
    replace (tr_level t >? 0) with false in Ep by (symmetry; rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
    injection Ep as _ E1 E2 _. congruence. }
  match type of Hrun with bind ?X _ = _ =>
    destruct X as [[[o3 m3] k3]|] eqn:EM; [cbn [bind] in Hrun|discriminate Hrun] end.
  assert (BR : branch_ok wmax out syms p (last =? 1) (tr_out t) o3).
  { destruct buf as [b|].
    - destruct (Hbuf b eq_refl) as (Hbl & Hs65 & Hbb & Hdat).
      destruct (u64 (sl + 4) <=? olb) eqn:Es.
      + bstep EM. bstep EM. destruct c as [o3' m3']. injection EM as -> -> _.
        rewrite Ko in E0.
        exact (proj2 (stored_branch Hst (tr_out t) m b sl last o3 m3 wmax out syms p
                        Hok0 Hlast Hp Hpm Hbl Hs65 Hbb Hdat E0)).
      + destruct (slb =? olb) eqn:Est.
        * eapply (static_run Hov Hw Hws Htab Hcomp Hsok t m (Some b)); eauto.
          unfold flush_call. rewrite Ep. cbv beta iota zeta. rewrite Es, Est. reflexivity.
        * destruct (Z_lt_le_dec 0 (tr_level t)) as [Hlev|Hlev];
            [|rewrite (Hlev0 Hlev), Z.eqb_refl in Est; discriminate Est].
          eapply (dyn_run Hov Hw Hdyn t m (Some b)); eauto.
          unfold flush_call. rewrite Ep. cbv beta iota zeta. rewrite Es, Est. reflexivity.
    - destruct (slb =? olb) eqn:Est.
      * eapply (static_run Hov Hw Hws Htab Hcomp Hsok t m None); eauto.
        unfold flush_call. rewrite Ep. cbv beta iota zeta. rewrite Est. reflexivity.
      * destruct (Z_lt_le_dec 0 (tr_level t)) as [Hlev|Hlev];
          [|rewrite (Hlev0 Hlev), Z.eqb_refl in Est; discriminate Est].
        eapply (dyn_run Hov Hw Hdyn t m None); eauto.
        unfold flush_call. rewrite Ep. cbv beta iota zeta. rewrite Est. reflexivity. }
  destruct (c_init_block (set_out s2 o3)) as [s4|] eqn:Ei; cbn [bind] in Hrun; [|discriminate Hrun].
  pose proof (c_init_block_out _ _ Ei) as Hi. cbn in Hi.
  destruct BR as (blk & Bok & Bdat & Ok3 & E3 & Pad).
  exists blk. split; [exact Bok|]. split; [exact Bdat|]. rewrite enc_out_one.
  destruct (Z.eqb_spec last 0) as [L0|L0].
  - subst last. cbn [negb Z.eqb] in Hrun. cbn [bind] in Hrun. injection Hrun as <- <- <-.
    rewrite Hi. cbn [Z.eqb Pos.eqb]. rewrite app_nil_r.
    split; [exact Ok3|]. split; [intros; lia|]. exact E3.
  - assert (L1 : last = 1) by lia. subst last.
    cbn [negb Z.eqb] in Hrun.
    destruct (c_bi_windup (tr_out s4, m3)) as [[o4 m4]|] eqn:Ew; cbn [bind] in Hrun; [|discriminate Hrun].
    injection Hrun as <- <- <-.
    destruct Hw as (_ & _ & _ & Wwin). rewrite Hi in Ew.
    destruct (Wwin o3 m3 o4 m4 Ok3 Ew) as (Ok4 & V4 & E4).
    cbn [tr_out set_out]. cbn [Z.eqb Pos.eqb] in *.
    split; [exact Ok4|]. split; [intros; exact V4|].
    rewrite E4, E3, Pad, app_assoc. reflexivity.
Qed.

Theorem rtd_flush_ok2 :
  Zlib.proof.huffman.Overlay.overlay_statement -> writer_fspec -> stored_block_fspec -> flush_block_fspec2.
Proof.
  intros Hov Hw Hst t m buf sl last t' m' kind syms out wmax p A B C D E G R.
  exact (flush_ok_bytes Hov Hw Hst t m buf sl last t' m' kind syms out wmax p A B C D E G R).
Qed.
