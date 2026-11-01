(** * _tr_flush_block with level > 0: the block-level summary used by lemmas (i) and (ii)

    [dyn_sum s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E] states, for
    [flush_prep s stored_len = (s', olb, slb, mbi)], everything the overlay bound and the cost bound use, in terms of
    the block's symbol counts [lfreq] / [dfreq]:
    - [ll] / [dl0]: the literal/length and distance code lengths built by build_tree (the Len fields before
      scan_tree stored its guard 0xffff at max_code + 1): range, max codes, used codes, forced codes, Kraft, proper
      codes;
    - [Hh]: the size of the tree header after the 3 block-type bits (send_all_trees), crude and, for
      lit_bufsize <= 256, against every bit-length code (repair overhead of the bit-length tree 75);
    - opt_lenb / static_lenb from the exact opt_len = Hh + dyn data + E (E >= 0: the forced nodes) and
      static_len = static data;
    - [dd] / [dd0]: the unlimited Huffman depths (rearranged among equal frequencies) with Kraft equality at 2^30,
      the Fibonacci caps, optimality against every code with Kraft sum <= 1 (distance lengths >= 2: with a forced
      distance node the tree has at most three leaves), at most the cost of the actual lengths
      (up to E), the repair overhead 540 * X <= 632 * (lit_bufsize + 2), and dd = the actual lengths when
      lit_bufsize <= 2048 (no length-limit repair);
    - the costs of the block under the actual (guarded) and static codes. *)

From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.huffman.Model Zlib.proof.huffman.HuffAbs Zlib.proof.huffman.Bits
               Zlib.proof.huffman.Overlay Zlib.proof.huffman.Header Zlib.proof.huffman.BlockFacts.
Require Zlib.proof.huffman.FlushDyn Zlib.proof.huffman.TreeDD.
Import ListNotations.
Local Open Scope Z_scope.

(** Extra bits of a literal/length code and of a distance code. *)
Definition xl (c : Z) : Z := if 257 <=? c then Znth (c - 257) extra_lbits else 0.
Definition xd (d : Z) : Z := Znth d extra_dbits.

(** The data bits of the block (all symbols and END_BLOCK, with extra bits) under code lengths [ll] / [dl0], and
    under the static trees. *)
Definition dyn_data (syms : list (Z * Z)) (ll dl0 : list Z) : Z :=
  zsum L_CODES (fun c => lfreq syms c * (Znth c ll + xl c)) +
  zsum D_CODES (fun d => dfreq syms d * (Znth d dl0 + xd d)).
Definition stat_data (syms : list (Z * Z)) : Z :=
  zsum L_CODES (fun c => lfreq syms c * (Znth c static_ltree_len + xl c)) +
  zsum D_CODES (fun d => dfreq syms d * (5 + xd d)).

Record dyn_sum (s : tstate) (syms : list (Z * Z)) (stored_len : Z) (s' : tstate) (olb slb mbi : Z)
    (ll dl0 dd dd0 : list Z) (Hh E : Z) : Prop := {
  ds_prep : flush_prep s stored_len = (s', olb, slb, mbi);
  ds_keep : tr_out s' = tr_out s /\ tr_lit_bufsize s' = tr_lit_bufsize s /\ tr_sym_next s' = tr_sym_next s /\
            tr_strategy s' = tr_strategy s;
  ds_lists : Zlength ll = HEAP_SIZE /\ Zlength dl0 = 2 * D_CODES + 1 /\
             Zlength dd = L_CODES /\ Zlength dd0 = D_CODES;
  ds_guard : dl (tr_ltree s') = upd_Znth (tr_lmax s' + 1) ll 65535 /\
             dl (tr_dtree s') = upd_Znth (tr_dmax s' + 1) dl0 65535;
  ds_lmax : END_BLOCK <= tr_lmax s' < L_CODES /\ Znth (tr_lmax s') ll <> 0;
  ds_dmax : 0 <= tr_dmax s' < D_CODES /\ Znth (tr_dmax s') dl0 <> 0;
  ds_llen : forall c, 0 <= c < L_CODES ->
              0 <= Znth c ll <= 15 /\ (tr_lmax s' < c -> Znth c ll = 0) /\
              (0 < lfreq syms c -> Znth c ll <> 0) /\ (syms <> [] -> Znth c ll <> 0 -> 0 < lfreq syms c);
  ds_dlen : forall d, 0 <= d < D_CODES ->
              0 <= Znth d dl0 <= 15 /\ (tr_dmax s' < d -> Znth d dl0 = 0) /\ (0 < dfreq syms d -> Znth d dl0 <> 0);
  ds_forced : let used := zsum D_CODES (fun d => if 0 <? dfreq syms d then 1 else 0) in
              let forced := zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then 1 else 0) in
              forced <= 2 /\ (0 < forced -> used <= 1);
  ds_kraft : zsum L_CODES (fun c => if Znth c ll =? 0 then 0 else 2 ^ (15 - Znth c ll)) = 2 ^ 15 /\
             zsum D_CODES (fun d => if Znth d dl0 =? 0 then 0 else 2 ^ (15 - Znth d dl0)) <= 2 ^ 15;
  ds_codes : (forall c, 0 <= c < L_CODES -> Znth c ll <> 0 -> code_ok (fc (tr_ltree s')) (dl (tr_ltree s')) c) /\
             (forall d, 0 <= d < D_CODES -> Znth d dl0 <> 0 -> code_ok (fc (tr_dtree s')) (dl (tr_dtree s')) d);
  (* the tree header *)
  ds_hdr : forall o, bits_ok o ->
             let o' := send_all_trees o (tr_ltree s') (tr_dtree s') (tr_bltree s')
                         (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1) in
             bits_ok o' /\ bitpos o' = bitpos o + Hh /\ writes o o';
  ds_H : 26 <= Hh <= 2283;
  ds_tau : tr_lit_bufsize s <= 256 -> forall tau, tau_ok tau ->
             Hh <= 71 + charge tau ll (tr_lmax s' + 1) + charge tau dl0 (tr_dmax s' + 1) + 75;
  (* opt_lenb, static_lenb *)
  ds_lenb : slb = (stat_data syms + 10) / 8 /\
            olb = (if (slb <=? (Hh + dyn_data syms ll dl0 + E + 10) / 8) || (tr_strategy s =? Z_FIXED)
                   then slb else (Hh + dyn_data syms ll dl0 + E + 10) / 8);
  ds_E : 0 <= E <= 64 /\
         zsum L_CODES (fun c => if (0 <? Znth c ll) && (lfreq syms c =? 0) then Znth c ll - 1 else 0) +
         zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then Znth d dl0 - 1 else 0) <= E;
  (* the costs of the block's symbols *)
  ds_cost_guard : forall k, cost_sum (dl (tr_ltree s')) (dl (tr_dtree s')) (firstn k syms) =
                            cost_sum ll dl0 (firstn k syms);
  ds_cost_dyn : cost_sum ll dl0 syms + Znth END_BLOCK ll = dyn_data syms ll dl0;
  ds_cost_stat : cost_sum static_ltree_len static_dtree_len syms + Znth END_BLOCK static_ltree_len = stat_data syms;
  (* the unlimited Huffman depths *)
  ds_dd_len : (forall c, 0 <= c < L_CODES ->
                 0 <= Znth c dd <= 30 /\ (syms <> [] -> (0 < lfreq syms c <-> Znth c dd <> 0))) /\
              (forall d, 0 <= d < D_CODES -> 0 <= Znth d dd0 <= 30 /\ (0 < dfreq syms d -> Znth d dd0 <> 0));
  ds_dd_kraft : (syms <> [] -> zsum L_CODES (fun c => if Znth c dd =? 0 then 0 else 2 ^ (30 - Znth c dd)) = 2 ^ 30) /\
                zsum D_CODES (fun d => if Znth d dd0 =? 0 then 0 else 2 ^ (30 - Znth d dd0)) <= 2 ^ 30;
  ds_dd_caps : (forall c, 0 <= c < L_CODES -> 0 < lfreq syms c ->
                  lfreq syms c * fib (Znth c dd + 1) <= tr_lit_bufsize s + 1) /\
               (forall d, 0 <= d < D_CODES -> 0 < dfreq syms d ->
                  dfreq syms d * fib (Znth d dd0 + 1) <= tr_lit_bufsize s + 1);
  ds_dd_opt : forall el ed : Z -> Z,
                (forall c, 0 <= c < L_CODES -> 1 <= el c <= 30) -> (forall d, 0 <= d < D_CODES -> 2 <= ed d <= 30) ->
                zsum L_CODES (fun c => 2 ^ (30 - el c)) <= 2 ^ 30 -> zsum D_CODES (fun d => 2 ^ (30 - ed d)) <= 2 ^ 30 ->
                syms <> [] ->
                zsum L_CODES (fun c => lfreq syms c * Znth c dd) <= zsum L_CODES (fun c => lfreq syms c * el c) /\
                zsum D_CODES (fun d => dfreq syms d * Znth d dd0) <= zsum D_CODES (fun d => dfreq syms d * ed d);
  ds_dd_le : zsum L_CODES (fun c => lfreq syms c * Znth c dd) + zsum D_CODES (fun d => dfreq syms d * Znth d dd0) <=
             zsum L_CODES (fun c => lfreq syms c * Znth c ll) + zsum D_CODES (fun d => dfreq syms d * Znth d dl0) + E;
  ds_dd_repair : 540 * (zsum L_CODES (fun c => lfreq syms c * Z.max 0 (Znth c ll - Znth c dd)) +
                        zsum D_CODES (fun d => dfreq syms d * Z.max 0 (Znth d dl0 - Znth d dd0)))
                 <= 632 * (tr_lit_bufsize s + 2);
  ds_dd_small : tr_lit_bufsize s <= 2048 -> syms <> [] ->
                (forall c, 0 <= c < L_CODES -> Znth c dd = Znth c ll) /\
                (forall d, 0 <= d < D_CODES -> Znth d dd0 = Znth d dl0)
}.

Definition dyn_sum_statement : Prop := forall s syms stored_len, flush_pre s syms -> 0 < tr_level s ->
  exists s' olb slb mbi ll dl0 dd dd0 Hh E, dyn_sum s syms stored_len s' olb slb mbi ll dl0 dd dd0 Hh E.

(** ** The proof: a context with every object and fact of [FlushDyn.dyn_prep], then one lemma per group of
    fields of [dyn_sum]. *)

Require Import Zlib.proof.huffman.Heap Zlib.proof.huffman.BtSpec.
Require Zlib.proof.huffman.BuildPre Zlib.proof.huffman.Repair Zlib.proof.huffman.FlushTree
        Zlib.proof.huffman.FlushHdr Zlib.proof.huffman.FlushStream Zlib.proof.huffman.Cert.
Module Hd := Zlib.proof.huffman.Header.
Module FT := Zlib.proof.huffman.FlushTree.
Module FH := Zlib.proof.huffman.FlushHdr.
Module FS := Zlib.proof.huffman.FlushStream.
Module CT := Zlib.proof.huffman.Cert.
Require Zlib.proof.huffman.BuildThm Zlib.proof.huffman.GenCodes Zlib.proof.huffman.Bitlen
        Zlib.proof.huffman.BuildTree.

(** The objects of one _tr_flush_block call (level > 0) and of [FlushDyn.dyn_prep_statement]. *)
Record dvars := mkDV {
  v_s : tstate; v_syms : list (Z * Z); v_stored : Z; v_s' : tstate; v_olb : Z; v_slb : Z; v_mbi : Z;
  v_Sl : list Z; v_Fl : list Z; v_ordl : list Z; v_Rl : item; v_lt0 : tree; v_wl : work;
  v_Sd : list Z; v_Fd : list Z; v_ordd : list Z; v_Rd : item; v_dt0 : tree; v_wd : work;
  v_blt : tree; v_Sb : list Z; v_Fb : list Z; v_ordb : list Z; v_Rb : item; v_wb : work
}.

(** The facts: [flush_pre], level > 0, and the conclusion of [FlushDyn.dyn_prep_statement]. *)
Record dctx (v : dvars) : Prop := {
  dc_pre : flush_pre (v_s v) (v_syms v);
  dc_level : 0 < tr_level (v_s v);
  dc_prep : flush_prep (v_s v) (v_stored v) = (v_s' v, v_olb v, v_slb v, v_mbi v);
  dc_btl : bt_facts static_l_desc (tr_ltree (v_s v)) (tr_wk (v_s v)) (v_Sl v) (v_Fl v) (v_ordl v) (v_Rl v)
             (v_lt0 v) (tr_lmax (v_s' v)) (v_wl v);
  dc_btd : bt_facts static_d_desc (tr_dtree (v_s v)) (v_wl v) (v_Sd v) (v_Fd v) (v_ordd v) (v_Rd v)
             (v_dt0 v) (tr_dmax (v_s' v)) (v_wd v);
  dc_btb : bt_facts static_bl_desc (v_blt v) (v_wd v) (v_Sb v) (v_Fb v) (v_ordb v) (v_Rb v)
             (tr_bltree (v_s' v)) (tr_blmax (v_s' v)) (v_wb v);
  dc_lguard : tr_ltree (v_s' v) = set_dl (v_lt0 v) (tr_lmax (v_s' v) + 1) 65535;
  dc_dguard : tr_dtree (v_s' v) = set_dl (v_dt0 v) (tr_dmax (v_s' v) + 1) 65535;
  dc_bldl : dl (v_blt v) = dl (tr_bltree (v_s v));
  dc_blsize : Zlength (fc (v_blt v)) = 2 * BL_CODES + 1;
  dc_blrange : forall n, 0 <= n < 2 * BL_CODES + 1 -> 0 <= Znth n (fc (v_blt v)) < 65536;
  dc_blcnt : forall c, 0 <= c < BL_CODES -> Znth c (fc (v_blt v)) =
               Hd.cnt c (Hd.tree_syms (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v))) +
               Hd.cnt c (Hd.tree_syms (dl (tr_dtree (v_s' v))) (tr_dmax (v_s' v)));
  dc_mbi : v_mbi v = find_max_blindex 20 (tr_bltree (v_s' v)) (BL_CODES - 1);
  dc_opt : w_opt_len (tr_wk (v_s' v)) = u64 (w_opt_len (v_wb v) + (3 * (v_mbi v + 1) + 5 + 5 + 4));
  dc_static : w_static_len (tr_wk (v_s' v)) = w_static_len (v_wb v);
  dc_slb : v_slb v = Z.shiftr (u64 (w_static_len (tr_wk (v_s' v)) + 3 + 7)) 3;
  dc_olb : v_olb v = (if (v_slb v <=? Z.shiftr (u64 (w_opt_len (tr_wk (v_s' v)) + 3 + 7)) 3) ||
                         (tr_strategy (v_s v) =? Z_FIXED)
                      then v_slb v else Z.shiftr (u64 (w_opt_len (tr_wk (v_s' v)) + 3 + 7)) 3);
  dc_keep : tr_out (v_s' v) = tr_out (v_s v) /\ tr_lit_bufsize (v_s' v) = tr_lit_bufsize (v_s v) /\
            tr_sym_next (v_s' v) = tr_sym_next (v_s v) /\ tr_strategy (v_s' v) = tr_strategy (v_s v)
}.

(** The values chosen for [dyn_sum]: the lengths before the guards, the header size, the forced-node overhead. *)
Definition vll (v : dvars) : list Z := dl (v_lt0 v).
Definition vdl0 (v : dvars) : list Z := dl (v_dt0 v).
Definition vHh (v : dvars) : Z :=
  14 + 3 * (v_mbi v + 1) +
  Hd.stream_bits (dl (tr_bltree (v_s' v))) (Hd.tree_syms (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v))) +
  Hd.stream_bits (dl (tr_bltree (v_s' v))) (Hd.tree_syms (dl (tr_dtree (v_s' v))) (tr_dmax (v_s' v))).
Definition vE (v : dvars) : Z := w_opt_len (tr_wk (v_s' v)) - vHh v - dyn_data (v_syms v) (vll v) (vdl0 v).

(** The overhead of the forced nodes of the literal/length and distance trees (as in [ds_E]). *)
Definition forced_extra (syms : list (Z * Z)) (ll dl0 : list Z) : Z :=
  zsum L_CODES (fun c => if (0 <? Znth c ll) && (lfreq syms c =? 0) then Znth c ll - 1 else 0) +
  zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then Znth d dl0 - 1 else 0).

(** *** The context exists *)

Lemma dctx_exists : FlushDyn.dyn_prep_statement -> forall s syms stored_len, flush_pre s syms -> 0 < tr_level s ->
  exists v, dctx v /\ v_s v = s /\ v_syms v = syms /\ v_stored v = stored_len.
Proof.
  intros Hprep s syms stored_len Hpre Hlev.
  specialize (Hprep s syms stored_len Hpre Hlev).
  destruct (flush_prep s stored_len) as [[[s' olb] slb] mbi] eqn:Ep.
  destruct Hprep as (Sl & Fl & ordl & Rl & lt0 & wl & Sd & Fd & ordd & Rd & dt0 & wd & blt & Sb & Fb & ordb & Rb & wb &
    H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
  exists (mkDV s syms stored_len s' olb slb mbi Sl Fl ordl Rl lt0 wl Sd Fd ordd Rd dt0 wd blt Sb Fb ordb Rb wb).
  split; [|simpl; auto].
  constructor; simpl; auto.
Qed.

(** The frequency sums: one literal/length code per symbol plus END_BLOCK, at most one distance code per symbol. *)
Lemma freq_sums : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  zsum L_CODES (lfreq syms) = Zlength syms + 1 /\ zsum D_CODES (dfreq syms) <= Zlength syms /\
  (forall c, 0 <= lfreq syms c) /\ (forall d, 0 <= dfreq syms d).
Proof.
  intros syms Hv.
  assert (Hlk : forall x, In x syms -> 0 <= lcode_of x < 286)
    by (intros x Hx; destruct (FS.lcode_range x (Hv x Hx)); unfold L_CODES in *; lia).
  assert (Hdk : forall x, In x syms -> 0 <= CT.dkey x < 31)
    by (intros x Hx; destruct (Hv x Hx) as [_ Hd]; unfold CT.dkey; destruct (Z.eqb_spec (fst x) 0); [lia|];
        destruct (dist_code_facts (fst x - 1) ltac:(lia)) as [A _]; lia).
  split; [|split; [|split]].
  - assert (Hk := CT.sum_by_key lcode_of (fun _ => 1) 286 syms Hlk). rewrite CT.hsum_ones in Hk.
    unfold L_CODES. rewrite CT.zsum_rs in Hk |- *. change (Z.to_nat 286) with 286%nat in *.
    rewrite (CT.rs_ext _ 0 (lfreq syms)
               (fun j => 1 * Zlength (filter (fun x => lcode_of x =? j) syms) + (if j =? 256 then 1 else 0)))
      by (intros j Hj; unfold lfreq, END_BLOCK; lia).
    rewrite CT.rs_add, CT.rs_ind by (simpl; lia). lia.
  - assert (Hk := CT.sum_by_key CT.dkey (fun j => if j =? 30 then 0 else 1) 31 syms Hdk).
    assert (Hle : HuffAbs.sumZ (map (fun x => (fun j => if j =? 30 then 0 else 1) (CT.dkey x)) syms) <= Zlength syms).
    { rewrite <- CT.hsum_ones. apply CT.hsum_map_le. intros x _. destruct (CT.dkey x =? 30); lia. }
    cbv beta in Hk, Hle. rewrite Hk in Hle. unfold D_CODES. rewrite CT.zsum_rs in Hle |- *.
    change (Z.to_nat 31) with (S 30) in Hle. rewrite CT.rs_snoc in Hle. simpl (0 + Z.of_nat 30) in Hle.
    rewrite Z.eqb_refl in Hle. change (Z.to_nat 30) with 30%nat.
    rewrite (CT.rs_ext _ 0 (dfreq syms)
               (fun j => (if j =? 30 then 0 else 1) * Zlength (filter (fun x => CT.dkey x =? j) syms))).
    + lia.
    + intros j Hj. replace (j =? 30) with false by (symmetry; apply Z.eqb_neq; lia).
      unfold dfreq. rewrite Z.mul_1_l. f_equal. apply filter_ext. intros x. unfold CT.dkey.
      destruct (Z.eqb_spec (fst x) 0); cbn [negb andb]; [symmetry; apply Z.eqb_neq; lia|reflexivity].
  - intros c. unfold lfreq. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? c) syms)).
    destruct (c =? END_BLOCK); lia.
  - intros d. unfold dfreq. apply Zlength_nonneg.
Qed.

Lemma sumZ_indicator_filter : forall (p : Z -> bool) l,
  HuffAbs.sumZ (map (fun i => if p i then 1 else 0) l) = Zlength (filter p l).
Proof.
  intros p l. induction l as [|a l IH]; [reflexivity|]. cbn [map HuffAbs.sumZ filter].
  destruct (p a); rewrite ?Zlength_cons, IH; lia.
Qed.

Lemma lfreq_code_pos : forall syms x, In x syms -> 1 <= lfreq syms (lcode_of x).
Proof.
  intros syms x Hx. unfold lfreq.
  assert (In x (filter (fun s => lcode_of s =? lcode_of x) syms)) by (apply filter_In; rewrite Z.eqb_refl; auto).
  destruct (filter _ syms) as [|y r]; [contradiction|]. rewrite Zlength_cons.
  pose proof (Zlength_nonneg r). destruct (lcode_of x =? END_BLOCK); lia.
Qed.

Lemma lfreq_end : forall syms, 1 <= lfreq syms END_BLOCK.
Proof. intros syms. unfold lfreq. rewrite Z.eqb_refl. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? END_BLOCK) syms)). lia. Qed.

(** *** The symbol sets of the literal/length and distance trees *)

Lemma dsum_sets : forall v, dctx v ->
  (forall c, In c (v_Sl v) <-> 0 <= c < L_CODES /\ (0 < lfreq (v_syms v) c \/ In c (v_Fl v))) /\
  (forall c, In c (v_Fl v) -> 0 <= c < L_CODES /\ lfreq (v_syms v) c = 0) /\
  (v_syms v <> [] -> v_Fl v = []) /\
  (forall d, In d (v_Sd v) <-> 0 <= d < D_CODES /\ (0 < dfreq (v_syms v) d \/ In d (v_Fd v))) /\
  (forall d, In d (v_Fd v) -> 0 <= d < D_CODES /\ dfreq (v_syms v) d = 0) /\
  (v_Fd v <> [] -> zsum D_CODES (fun d => if 0 <? dfreq (v_syms v) d then 1 else 0) <= 1).
Proof.
  intros v Hv.
  pose proof (dc_pre v Hv) as Hpre.
  destruct (fp_syms _ _ Hpre) as [_ [_ [Hval _]]].
  destruct (freq_sums _ Hval) as [_ [_ [Hlpos Hdpos]]].
  destruct (fp_ltree _ _ Hpre) as [_ [_ [_ Hfl]]]. destruct (fp_dtree _ _ Hpre) as [_ [_ [_ Hfd]]].
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ (dc_btl v Hv)) as [ESl [_ [Rgl [Fl0 [_ [Flnil _]]]]]].
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ (dc_btd v Hv)) as [ESd [_ [Rgd [Fd0 [_ [Fdnil _]]]]]].
  cbn [sd_elems static_l_desc static_d_desc] in *.
  assert (HFl : forall c, In c (v_Fl v) -> 0 <= c < L_CODES /\ lfreq (v_syms v) c = 0).
  { intros c Hc. assert (Hr := Rgl c ltac:(rewrite ESl; apply in_or_app; auto)).
    split; [exact Hr|]. rewrite <- Hfl by exact Hr. apply Fl0; auto. }
  assert (HFd : forall c, In c (v_Fd v) -> 0 <= c < D_CODES /\ dfreq (v_syms v) c = 0).
  { intros c Hc. assert (Hr := Rgd c ltac:(rewrite ESd; apply in_or_app; auto)).
    split; [exact Hr|]. rewrite <- Hfd by exact Hr. apply Fd0; auto. }
  split; [|split; [exact HFl|split; [|split; [|split; [exact HFd|]]]]].
  - intros c. rewrite ESl, in_app_iff, BuildPre.in_nzl. split.
    + intros [[Hr Hnz]|HF]; [|destruct (HFl c HF); auto].
      rewrite Hfl in Hnz by exact Hr. specialize (Hlpos c). split; [exact Hr|left; lia].
    + intros [Hr [Hp|HF]]; [left|right; exact HF]. rewrite Hfl by exact Hr. split; [exact Hr|lia].
  - intros Hne. apply Flnil. destruct (v_syms v) as [|x r] eqn:Ey; [congruence|].
    set (a := lcode_of x).
    assert (Ha : 0 <= a < L_CODES /\ a <> END_BLOCK) by (apply FS.lcode_range, Hval; left; reflexivity).
    assert (Hin : incl [a; END_BLOCK] (BuildPre.nzl (fc (tr_ltree (v_s v))) L_CODES)).
    { intros y [<-|[<-|[]]]; apply BuildPre.in_nzl.
      - rewrite Hfl by lia. pose proof (lfreq_code_pos (x :: r) x (or_introl eq_refl)). fold a in H. lia.
      - unfold END_BLOCK, L_CODES. rewrite Hfl by (unfold L_CODES; lia). pose proof (lfreq_end (x :: r)).
        unfold END_BLOCK in H. lia. }
    assert (Hnd : NoDup [a; END_BLOCK]) by (constructor; [intros [E|[]]; lia|constructor; [intros []|constructor]]).
    pose proof (NoDup_incl_length Hnd Hin). rewrite Zlength_correct. simpl in H. lia.
  - intros d. rewrite ESd, in_app_iff, BuildPre.in_nzl. split.
    + intros [[Hr Hnz]|HF]; [|destruct (HFd d HF); auto].
      rewrite Hfd in Hnz by exact Hr. specialize (Hdpos d). split; [exact Hr|left; lia].
    + intros [Hr [Hp|HF]]; [left|right; exact HF]. rewrite Hfd by exact Hr. split; [exact Hr|lia].
  - intros Hne. assert (Hlt : Zlength (BuildPre.nzl (fc (tr_dtree (v_s v))) D_CODES) < 2).
    { destruct (Z_lt_ge_dec (Zlength (BuildPre.nzl (fc (tr_dtree (v_s v))) D_CODES)) 2); [auto|].
      exfalso. apply Hne, Fdnil. lia. }
    unfold zsum. rewrite (map_ext_in _ (fun i => if negb (Znth i (fc (tr_dtree (v_s v))) =? 0) then 1 else 0)).
    + rewrite sumZ_indicator_filter. unfold BuildPre.nzl in Hlt. lia.
    + intros d Hd. apply in_zseq in Hd. rewrite Hfd by (unfold D_CODES in *; lia). specialize (Hdpos d).
      destruct (Z.ltb_spec 0 (dfreq (v_syms v) d)), (Z.eqb_spec (dfreq (v_syms v) d) 0); simpl; lia.
Qed.

(** *** Groups of fields *)

(** Helpers of [dsum_basic]: the basic facts of one tree built by build_tree (max length 15). *)
Lemma dsb_sum_ones : forall l : list Z, sumZ (map (fun _ => 1) l) = Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|]. cbn [map sumZ]. rewrite IH, Zlength_cons. lia.
Qed.

Lemma dsb_tree : forall sd t w S F order R t' mc w' n (f : Z -> Z),
  bt_facts sd t w S F order R t' mc w' -> sd_elems sd = n -> sd_maxlen sd = 15 ->
  (forall x, 0 <= x < n -> Znth x (fc t) = f x) -> (forall x, 0 <= x < n -> 0 <= f x) ->
  (0 <= mc < n /\ Znth mc (dl t') <> 0) /\
  (forall c, 0 <= c < n ->
     0 <= Znth c (dl t') <= 15 /\ (mc < c -> Znth c (dl t') = 0) /\ (f c <> 0 -> Znth c (dl t') <> 0) /\
     (Znth c (dl t') <> 0 -> In c S /\ (f c <> 0 \/ In c F))) /\
  zsum n (fun c => if Znth c (dl t') =? 0 then 0 else 2 ^ (15 - Znth c (dl t'))) = 2 ^ 15 /\
  zsum n (fun c => if (0 <? Znth c (dl t')) && (f c =? 0) then 1 else 0) = Zlength F /\
  zsum n (fun c => if 0 <? f c then 1 else 0) = Zlength (BuildPre.nzl (fc t) n) /\
  Zlength F <= 2 /\ (2 <= Zlength (BuildPre.nzl (fc t) n) -> F = []) /\
  (forall c, 0 <= c < n -> Znth c (dl t') <> 0 -> code_ok (fc t') (dl t') c).
Proof.
  intros sd t w S F order R t' mc w' n f Hbt Hn Hm Hf Hfp.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbt) as [ES [ND [Hr [HF0 [HF2 [HF3 _]]]]]].
  rewrite Hn in Hr.
  pose proof (bt_len_out _ _ _ _ _ _ _ _ _ _ Hbt) as Hout. rewrite Hn in Hout.
  pose proof (bt_len_in _ _ _ _ _ _ _ _ _ _ Hbt) as Hin. rewrite Hm in Hin.
  destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Hbt) as [Hmc Hmc2].
  assert (HS : forall c, In c S <-> (0 <= c < n /\ f c <> 0) \/ In c F).
  { intros c. rewrite ES, in_app_iff, BuildPre.in_nzl, Hn. split.
    - intros [[A B]|B]; [left; rewrite <- Hf by lia; auto|auto].
    - intros [[A B]|B]; [left; rewrite Hf by lia; auto|auto]. }
  assert (Hnz : forall c, 0 <= c < n -> Znth c (dl t') <> 0 -> In c S).
  { intros c Hc Hz. destruct (in_dec Z.eq_dec c S) as [i|i]; auto. specialize (Hout c Hc i). contradiction. }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - specialize (Hr mc Hmc). specialize (Hin mc Hmc). split; lia.
  - intros c Hc. split; [|split; [|split]].
    + destruct (in_dec Z.eq_dec c S) as [i|i]; [specialize (Hin c i); lia|rewrite (Hout c Hc i); lia].
    + intros Hlt. apply Hout; auto. intros i. specialize (Hmc2 c i). lia.
    + intros Hne. assert (i : In c S) by (apply HS; auto). specialize (Hin c i). lia.
    + intros Hz. pose proof (Hnz c Hc Hz) as i. split; auto. apply HS in i. tauto.
  - unfold zsum. rewrite (FT.zseq_sum_support S); auto.
    + rewrite <- Hm, <- (bt_kraft _ _ _ _ _ _ _ _ _ _ Hbt), Hm. apply FT.sumZ_map_ext'.
      intros x i. specialize (Hin x i). destruct (Z.eqb_spec (Znth x (dl t')) 0); lia.
    + intros x Hx i. rewrite (Hout x Hx i). reflexivity.
  - unfold zsum. rewrite (FT.zseq_sum_support F).
    + rewrite <- dsb_sum_ones. apply FT.sumZ_map_ext'. intros x i.
      assert (iS : In x S) by (apply HS; auto). specialize (Hin x iS).
      assert (Hx := Hr x iS). rewrite <- Hf, HF0 by auto.
      destruct (Z.ltb_spec 0 (Znth x (dl t'))); [reflexivity|lia].
    + rewrite ES in ND. eapply NoDup_app_remove_l; eauto.
    + intros x i. apply Hr, HS; auto.
    + intros x Hx i. destruct (in_dec Z.eq_dec x S) as [iS|iS].
      * apply HS in iS. destruct iS as [[_ A]|A]; [|contradiction].
        apply Z.eqb_neq in A. rewrite A, andb_false_r. reflexivity.
      * rewrite (Hout x Hx iS). reflexivity.
  - unfold zsum. rewrite (FT.zseq_sum_support (BuildPre.nzl (fc t) n)).
    + rewrite <- dsb_sum_ones. apply FT.sumZ_map_ext'. intros x i.
      apply BuildPre.in_nzl in i. destruct i as [A B]. rewrite Hf in B by auto. specialize (Hfp x A).
      destruct (Z.ltb_spec 0 (f x)); [reflexivity|lia].
    + apply BuildPre.nzl_nodup.
    + intros x i. apply BuildPre.in_nzl in i. lia.
    + intros x Hx i. rewrite BuildPre.in_nzl in i. rewrite Hf in i by auto.
      destruct (Z.ltb_spec 0 (f x)); [|reflexivity]. exfalso. apply i. split; auto. lia.
  - exact HF2.
  - rewrite <- Hn. exact HF3.
  - intros c Hc Hz. apply (bt_codes _ _ _ _ _ _ _ _ _ _ Hbt), Hnz; auto.
Qed.

(** Lengths, max codes, used and forced codes, Kraft, proper codes. *)
Lemma dsum_basic : forall v, dctx v ->
  let s' := v_s' v in let syms := v_syms v in let ll := vll v in let dl0 := vdl0 v in
  (Zlength ll = HEAP_SIZE /\ Zlength dl0 = 2 * D_CODES + 1) /\
  (dl (tr_ltree s') = upd_Znth (tr_lmax s' + 1) ll 65535 /\
   dl (tr_dtree s') = upd_Znth (tr_dmax s' + 1) dl0 65535) /\
  (END_BLOCK <= tr_lmax s' < L_CODES /\ Znth (tr_lmax s') ll <> 0) /\
  (0 <= tr_dmax s' < D_CODES /\ Znth (tr_dmax s') dl0 <> 0) /\
  (forall c, 0 <= c < L_CODES ->
     0 <= Znth c ll <= 15 /\ (tr_lmax s' < c -> Znth c ll = 0) /\
     (0 < lfreq syms c -> Znth c ll <> 0) /\ (syms <> [] -> Znth c ll <> 0 -> 0 < lfreq syms c)) /\
  (forall d, 0 <= d < D_CODES ->
     0 <= Znth d dl0 <= 15 /\ (tr_dmax s' < d -> Znth d dl0 = 0) /\ (0 < dfreq syms d -> Znth d dl0 <> 0)) /\
  (let used := zsum D_CODES (fun d => if 0 <? dfreq syms d then 1 else 0) in
   let forced := zsum D_CODES (fun d => if (0 <? Znth d dl0) && (dfreq syms d =? 0) then 1 else 0) in
   forced <= 2 /\ (0 < forced -> used <= 1)) /\
  (zsum L_CODES (fun c => if Znth c ll =? 0 then 0 else 2 ^ (15 - Znth c ll)) = 2 ^ 15 /\
   zsum D_CODES (fun d => if Znth d dl0 =? 0 then 0 else 2 ^ (15 - Znth d dl0)) <= 2 ^ 15) /\
  ((forall c, 0 <= c < L_CODES -> Znth c ll <> 0 -> code_ok (fc (tr_ltree s')) (dl (tr_ltree s')) c) /\
   (forall d, 0 <= d < D_CODES -> Znth d dl0 <> 0 -> code_ok (fc (tr_dtree s')) (dl (tr_dtree s')) d)).
Proof.
  intros v Hv s' syms ll dl0.
  destruct Hv as [Hpre _ _ Hbtl Hbtd _ Hlg Hdg _ _ _ _ _ _ _ _ _ _].
  destruct (fp_ltree _ _ Hpre) as [_ [LL _]]. destruct (fp_ltree _ _ Hpre) as [_ [_ [_ Hfl]]].
  destruct (fp_dtree _ _ Hpre) as [_ [LD _]]. destruct (fp_dtree _ _ Hpre) as [_ [_ [_ Hfd]]].
  destruct (fp_syms _ _ Hpre) as [_ [_ [Hval _]]].
  assert (Hlp : forall c, 0 <= lfreq (v_syms v) c).
  { intros c. unfold lfreq. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? c) (v_syms v))).
    destruct (c =? END_BLOCK); lia. }
  assert (Hdp : forall c, 0 <= dfreq (v_syms v) c) by (intros c; unfold dfreq; apply Zlength_nonneg).
  destruct (dsb_tree _ _ _ _ _ _ _ _ _ _ L_CODES (lfreq (v_syms v)) Hbtl eq_refl eq_refl Hfl (fun c _ => Hlp c))
    as [[Lm1 Lm2] [Lc [Lk [_ [_ [_ [LF2 Lcode]]]]]]].
  destruct (dsb_tree _ _ _ _ _ _ _ _ _ _ D_CODES (dfreq (v_syms v)) Hbtd eq_refl eq_refl Hfd (fun c _ => Hdp c))
    as [[Dm1 Dm2] [Dc [Dk [Dforced [Dused [DF1 [DF2 Dcode]]]]]]].
  pose proof (bt_sizes _ _ _ _ _ _ _ _ _ _ Hbtl) as [_ [Sl _]].
  pose proof (bt_sizes _ _ _ _ _ _ _ _ _ _ Hbtd) as [_ [Sd _]].
  subst s' syms ll dl0. unfold vll, vdl0.
  assert (HE : 0 < lfreq (v_syms v) END_BLOCK).
  { unfold lfreq. rewrite Z.eqb_refl. pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? END_BLOCK) (v_syms v))). lia. }
  assert (HEl : END_BLOCK <= tr_lmax (v_s' v)).
  { destruct (Lc END_BLOCK ltac:(unfold END_BLOCK, L_CODES; lia)) as [_ [A [B _]]].
    destruct (Z.le_gt_cases END_BLOCK (tr_lmax (v_s' v))) as [|G]; auto. specialize (A G). specialize (B ltac:(lia)). lia. }
  (* with a symbol, two used literal/length codes: no forced literal node *)
  assert (HFl : v_syms v <> [] -> v_Fl v = []).
  { intros Hne. apply LF2. destruct (v_syms v) as [|x r] eqn:Ey; [contradiction|].
    destruct (FS.lcode_range x (Hval x ltac:(left; reflexivity))) as [R1 R2].
    assert (Hx : 0 < lfreq (x :: r) (lcode_of x)).
    { unfold lfreq. cbn [filter]. rewrite Z.eqb_refl. rewrite Zlength_cons.
      pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? lcode_of x) r)).
      destruct (lcode_of x =? END_BLOCK); lia. }
    assert (Hin : forall c, 0 <= c < L_CODES -> 0 < lfreq (x :: r) c -> In c (BuildPre.nzl (fc (tr_ltree (v_s v))) L_CODES)).
    { intros c Hc Hp. apply BuildPre.in_nzl. split; auto. rewrite Hfl, ?Ey by auto. lia. }
    change 2%Z with (Z.of_nat (length [lcode_of x; END_BLOCK])). rewrite Zlength_correct.
    apply Nat2Z.inj_le, NoDup_incl_length.
    - constructor; [simpl; intuition|constructor; [simpl; auto|constructor]].
    - intros c [<-|[<-|[]]].
      + apply Hin; auto.
      + apply Hin; [unfold END_BLOCK, L_CODES; lia|]. rewrite ?Ey in HE. exact HE. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - rewrite Sl, Sd. auto.
  - rewrite Hlg, Hdg. split; reflexivity.
  - split; [split; [exact HEl|lia]|exact Lm2].
  - split; [lia|exact Dm2].
  - intros c Hc. destruct (Lc c Hc) as [A [B [C D]]]. split; [|split; [|split]]; auto.
    + intros Hp. apply C. lia.
    + intros Hne Hz. destruct (D Hz) as [_ [E|E]]; [specialize (Hlp c); lia|].
      rewrite (HFl Hne) in E. destruct E.
  - intros d Hd. destruct (Dc d Hd) as [A [B [C D]]]. split; [|split]; auto.
    intros Hp. apply C. lia.
  - cbv zeta. rewrite Dforced, Dused. split; [exact DF1|].
    intros Hp. destruct (Z.le_gt_cases 2 (Zlength (BuildPre.nzl (fc (tr_dtree (v_s v))) D_CODES))) as [G|G]; [|lia].
    rewrite (DF2 G), Zlength_nil in Hp. lia.
  - rewrite Lk, Dk. split; lia.
  - split.
    + intros c Hc Hz. rewrite Hlg. unfold set_dl; cbn [fc dl].
      destruct (Lcode c Hc Hz) as [A B]. destruct (Lc c Hc) as [_ [C _]].
      assert (c <= tr_lmax (v_s' v)) by (destruct (Z.le_gt_cases c (tr_lmax (v_s' v))); auto; specialize (C H); contradiction).
      unfold code_ok. rewrite upd_Znth_diff' by (rewrite ?Sl, ?LL; unfold HEAP_SIZE, L_CODES in *; lia). auto.
    + intros c Hc Hz. rewrite Hdg. unfold set_dl; cbn [fc dl].
      destruct (Dcode c Hc Hz) as [A B]. destruct (Dc c Hc) as [_ [C _]].
      assert (c <= tr_dmax (v_s' v)) by (destruct (Z.le_gt_cases c (tr_dmax (v_s' v))); auto; specialize (C H); contradiction).
      unfold code_ok. rewrite upd_Znth_diff' by (rewrite ?Sd, ?LD; unfold D_CODES in *; lia). auto.
Qed.

(** Helpers of [dsum_hdr]. *)

Lemma hdr_tree : forall sd t w S F order R t' mc w',
  bt_facts sd t w S F order R t' mc w' -> sd_maxlen sd = 15 -> mc + 1 < Zlength (dl t') ->
  0 <= mc < sd_elems sd /\
  (forall i, 0 <= i <= mc -> 0 <= Znth i (dl (set_dl t' (mc + 1) 65535)) <= 15) /\
  Znth mc (dl (set_dl t' (mc + 1) 65535)) <> 0 /\ Znth (mc + 1) (dl (set_dl t' (mc + 1) 65535)) = 65535.
Proof.
  intros sd t w S F order R t' mc w' Hb Hml Hlen.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hb) as [_ [_ [HSr _]]].
  destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Hb) as [Hmc Hmx].
  assert (Hmr := HSr mc Hmc).
  unfold set_dl; cbn [dl].
  split; [lia|]. split; [|split].
  - intros i Hi. rewrite upd_Znth_diff' by lia.
    destruct (in_dec Z.eq_dec i S) as [HiS|HiS].
    + assert (X := bt_len_in _ _ _ _ _ _ _ _ _ _ Hb i HiS). lia.
    + rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ Hb i ltac:(lia) HiS). lia.
  - rewrite upd_Znth_diff' by lia. assert (X := bt_len_in _ _ _ _ _ _ _ _ _ _ Hb mc Hmc). lia.
  - rewrite upd_Znth_same by lia. reflexivity.
Qed.

Lemma hdr_cnt_in : forall q l, In q l -> 1 <= Hd.cnt (fst q) l.
Proof.
  intros q l Hq. unfold Hd.cnt.
  assert (Hf : In q (filter (fun q' => fst q' =? fst q) l)) by (apply filter_In; split; [auto|apply Z.eqb_refl]).
  destruct (filter _ l); [contradiction|]. cbn [length]. lia.
Qed.

Lemma hdr_stream_nonneg : forall bll l, (forall q, In q l -> 0 <= Znth (fst q) bll /\ 0 <= snd q) ->
  0 <= Hd.stream_bits bll l.
Proof.
  intros bll l. unfold Hd.stream_bits, Hd.cost_tau. induction l as [|q r IH]; intros Hq; cbn [map Hd.sumZ]; [lia|].
  assert (A := Hq q (or_introl eq_refl)). assert (B := IH (fun q' H' => Hq q' (or_intror H'))). lia.
Qed.

Lemma hdr_extra_blbits : forall s, 0 <= s < 19 -> 0 <= Znth s extra_blbits.
Proof.
  intros s Hs.
  assert (G : forallb (fun s => 0 <=? Znth s extra_blbits) (zseq 0 19) = true) by (vm_compute; reflexivity).
  assert (H1 := proj1 (forallb_forall _ _) G s ltac:(apply in_zseq; simpl; lia)). apply Z.leb_le in H1. exact H1.
Qed.

(** The tree header: bits, writes, crude size. *)
Lemma dsum_hdr : forall v, dctx v ->
  let s' := v_s' v in
  (forall o, bits_ok o ->
     let o' := send_all_trees o (tr_ltree s') (tr_dtree s') (tr_bltree s')
                 (tr_lmax s' + 1) (tr_dmax s' + 1) (v_mbi v + 1) in
     bits_ok o' /\ bitpos o' = bitpos o + vHh v /\ writes o o') /\
  26 <= vHh v <= 2283.
Proof.
  intros v Hv. cbv zeta.
  pose proof (dc_btl v Hv) as Bl. pose proof (dc_btd v Hv) as Bd. pose proof (dc_btb v Hv) as Bb.
  pose proof (dc_pre v Hv) as Hpre.
  destruct (fp_ltree _ _ Hpre) as [_ [Hld [_ Hlq]]].
  destruct (fp_dtree _ _ Hpre) as [_ [Hdd _]].
  destruct (fp_bltree _ _ Hpre) as [_ [Hbd _]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ Bl) as [_ [Lsz _]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ Bd) as [_ [Dsz _]].
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ Bb) as [_ [Bsz _]].
  rewrite (dc_bldl v Hv) in Bsz.
  destruct (hdr_tree _ _ _ _ _ _ _ _ _ _ Bl eq_refl ltac:(rewrite Lsz, Hld; unfold HEAP_SIZE; cbn [sd_elems static_l_desc] in *; destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Bl) as [Hm _]; destruct (bt_S _ _ _ _ _ _ _ _ _ _ Bl) as [_ [_ [HSr _]]]; specialize (HSr _ Hm); cbn [sd_elems static_l_desc] in HSr; unfold L_CODES in HSr; lia))
    as [Lr [Ll [Lnz Lg]]].
  destruct (hdr_tree _ _ _ _ _ _ _ _ _ _ Bd eq_refl ltac:(rewrite Dsz, Hdd; unfold D_CODES; destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Bd) as [Hm _]; destruct (bt_S _ _ _ _ _ _ _ _ _ _ Bd) as [_ [_ [HSr _]]]; specialize (HSr _ Hm); cbn [sd_elems static_d_desc] in HSr; unfold D_CODES in HSr; lia))
    as [Dr [Dl [Dnz Dg]]].
  rewrite <- (dc_lguard v Hv) in Ll, Lnz, Lg. rewrite <- (dc_dguard v Hv) in Dl, Dnz, Dg.
  cbn [sd_elems static_l_desc static_d_desc] in Lr, Dr. unfold L_CODES in Lr. unfold D_CODES in Dr.
  assert (H256 : 256 <= tr_lmax (v_s' v)).
  { destruct (bt_S _ _ _ _ _ _ _ _ _ _ Bl) as [HS _]. destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Bl) as [_ Hmx].
    apply Hmx. rewrite HS. apply in_or_app; left. apply BuildPre.in_nzl. split; [cbn; unfold L_CODES; lia|].
    rewrite Hlq by (unfold L_CODES; lia). unfold lfreq.
    replace (256 =? END_BLOCK) with true by reflexivity.
    pose proof (Zlength_nonneg (filter (fun s => lcode_of s =? 256) (v_syms v))). lia. }
  assert (Hbl : forall x, 0 <= x < 19 -> 0 <= Znth x (dl (tr_bltree (v_s' v))) <= 7).
  { intros x Hx. destruct (in_dec Z.eq_dec x (v_Sb v)) as [Hi|Hi].
    - assert (X := bt_len_in _ _ _ _ _ _ _ _ _ _ Bb x Hi). cbn [sd_maxlen static_bl_desc] in X.
      unfold MAX_BL_BITS in X. lia.
    - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ Bb x ltac:(cbn; unfold BL_CODES; lia) Hi). lia. }
  set (Ls := Hd.tree_syms (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v))) in *.
  set (Ds := Hd.tree_syms (dl (tr_dtree (v_s' v))) (tr_dmax (v_s' v))) in *.
  assert (Okl : Hd.syms_ok Ls) by (apply Hd.tree_syms_ok; [lia|exact Ll]).
  assert (Okd : Hd.syms_ok Ds) by (apply Hd.tree_syms_ok; [lia|exact Dl]).
  assert (HinSb : forall q, In q Ls \/ In q Ds -> In (fst q) (v_Sb v)).
  { intros q Hq. assert (Hr : 0 <= fst q < 19) by (destruct Hq as [Hq|Hq]; [apply (Okl q Hq)|apply (Okd q Hq)]).
    destruct (bt_S _ _ _ _ _ _ _ _ _ _ Bb) as [HS _]. rewrite HS. apply in_or_app; left.
    apply BuildPre.in_nzl. split; [cbn; unfold BL_CODES; lia|].
    rewrite (dc_blcnt v Hv) by (unfold BL_CODES; lia). fold Ls Ds.
    pose proof (Hd.cnt_nonneg (fst q) Ls). pose proof (Hd.cnt_nonneg (fst q) Ds).
    destruct Hq as [Hq|Hq]; pose proof (hdr_cnt_in q _ Hq); lia. }
  destruct (FS.tree_syms_has_length (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v)) ltac:(lia) Ll Lnz Lg) as [vv [Hvv Hin]]. fold Ls in Hin.
  destruct (FS.bl_order_small vv ltac:(lia)) as [r [Hr Hro]].
  assert (Hm : 3 <= v_mbi v <= 18).
  { rewrite (dc_mbi v Hv). unfold BL_CODES.
    apply FS.fmb_spec with (i := 19 - 1); [lia|cbn; lia|].
    exists r. split; [lia|]. rewrite Hro.
    assert (X := bt_len_in _ _ _ _ _ _ _ _ _ _ Bb vv (HinSb (vv, 0) (or_introl Hin))). lia. }
  assert (Hbll : 19 <= Zlength (dl (tr_bltree (v_s' v)))) by (rewrite Bsz, Hbd; unfold BL_CODES; lia).
  split.
  - intros o Ho. split; [|split].
    + apply FH.send_all_trees_ok; [exact Ho|lia|lia|lia|..].
      * intros r' Hr'. assert (X := Hbl (Znth r' bl_order) ltac:(apply FS.bl_order_range; lia)). lia.
      * intros i Hi. apply Ll; lia.
      * intros i Hi. apply Dl; lia.
      * intros q Hq. replace (tr_lmax (v_s' v) + 1 - 1) with (tr_lmax (v_s' v)) in Hq by lia.
        apply (bt_codes _ _ _ _ _ _ _ _ _ _ Bb). apply HinSb; auto.
      * intros q Hq. replace (tr_dmax (v_s' v) + 1 - 1) with (tr_dmax (v_s' v)) in Hq by lia.
        apply (bt_codes _ _ _ _ _ _ _ _ _ _ Bb). apply HinSb; auto.
    + rewrite Hd.send_all_trees_bits by lia.
      replace (tr_lmax (v_s' v) + 1 - 1) with (tr_lmax (v_s' v)) by lia.
      replace (tr_dmax (v_s' v) + 1 - 1) with (tr_dmax (v_s' v)) by lia.
      unfold vHh. fold Ls Ds. lia.
    + apply FH.send_all_trees_writes.
  - unfold vHh. fold Ls Ds.
    assert (Cl : Hd.stream_bits (dl (tr_bltree (v_s' v))) Ls <= 7 * (tr_lmax (v_s' v) + 1))
      by (apply FH.stream_crude; auto; [lia|intros x Hx; apply Hbl; lia]).
    assert (Cd : Hd.stream_bits (dl (tr_bltree (v_s' v))) Ds <= 7 * (tr_dmax (v_s' v) + 1))
      by (apply FH.stream_crude; auto; [lia|intros x Hx; apply Hbl; lia]).
    assert (Nl : 0 <= Hd.stream_bits (dl (tr_bltree (v_s' v))) Ls).
    { apply hdr_stream_nonneg. intros q Hq. destruct (Okl q Hq) as [A B]. rewrite B.
      split; [apply Hbl; auto|apply hdr_extra_blbits; auto]. }
    assert (Nd : 0 <= Hd.stream_bits (dl (tr_bltree (v_s' v))) Ds).
    { apply hdr_stream_nonneg. intros q Hq. destruct (Okd q Hq) as [A B]. rewrite B.
      split; [apply Hbl; auto|apply hdr_extra_blbits; auto]. }
    lia.
Qed.

(** Helpers of [dsum_tau]. *)

(** The bit-length tree against any bit-length code [tau]: the actual lengths cost at most 75 bits more. *)
(** A sum over a duplicate-free subset of [0 .. n-1] of a nonnegative function is at most the full sum. *)
Lemma dtau_sub_le : forall (S : list Z) (g : Z -> Z) n, NoDup S -> (forall x, In x S -> 0 <= x < n) ->
  (forall x, 0 <= x < n -> 0 <= g x) -> HuffAbs.sumZ (map g S) <= zsum n g.
Proof.
  intros S g n Hnd Hr Hg.
  transitivity (HuffAbs.sumZ (map (fun x => if in_dec Z.eq_dec x S then g x else 0) S)).
  { apply Z.eq_le_incl, FT.sumZ_map_ext'. intros x Hx. destruct (in_dec Z.eq_dec x S); [reflexivity|contradiction]. }
  rewrite <- (FT.zseq_sum_support S _ n); [| auto | auto | intros x _ Hx; destruct (in_dec Z.eq_dec x S); [contradiction|reflexivity]].
  unfold zsum.
  assert (Hz : forall x, In x (zseq 0 (Z.to_nat n)) -> 0 <= x < n) by (intros x Hx; apply in_zseq in Hx; lia).
  revert Hz. generalize (zseq 0 (Z.to_nat n)). intros l. induction l as [|a l IH]; intros Hl; simpl; [lia|].
  assert (Ha : 0 <= a < n) by (apply Hl; left; auto).
  specialize (IH (fun x Hx => Hl x (or_intror Hx))). specialize (Hg a Ha).
  destruct (in_dec Z.eq_dec a S); lia.
Qed.

Lemma dtau_bl : forall blt w Sb Fb ordb Rb t' mcb w' (tau : Z -> Z),
  bt_facts static_bl_desc blt w Sb Fb ordb Rb t' mcb w' ->
  (forall x, 0 <= x < 19 -> 0 <= Znth x (fc blt)) ->
  zsum 19 (fun x => Znth x (fc blt)) <= 316 ->
  (forall x, 12 <= x <= 15 -> Znth x (fc blt) = 0) ->
  tau_ok tau ->
  zsum 19 (fun s => Znth s (fc blt) * Znth s (dl t')) <= zsum 19 (fun s => Znth s (fc blt) * tau s) + 75.
Proof.
  intros blt w Sb Fb ordb Rb t' mcb w' tau HB Hpos Hsum H1215 [Htau HK].
  assert (Hpos' : forall x, 0 <= x < sd_elems static_bl_desc -> 0 <= Znth x (fc blt)) by exact Hpos.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 [HFl [HF2 HS2]]]]]].
  change (sd_elems static_bl_desc) with 19 in ES, Hr, HF2.
  assert (Hoff : forall x, 0 <= x < 19 -> ~ In x Sb -> Znth x (fc blt) = 0).
  { intros x Hx Hn. destruct (Z.eq_dec (Znth x (fc blt)) 0) as [|Hne]; auto. exfalso. apply Hn.
    rewrite ES. apply in_or_app. left. apply BuildPre.in_nzl. auto. }
  unfold zsum.
  rewrite !(FT.zseq_sum_support Sb); try exact Hnd; try exact Hr; try (intros x Hx Hn; rewrite Hoff by auto; lia).
  destruct Fb as [|f1 Fr].
  - (* no forced node: the bound of FlushTree.bl_cost *)
    rewrite app_nil_r in ES.
    assert (Efq : forall x, FT.fqt blt [] x = Znth x (fc blt))
      by (intros x; unfold FT.fqt, fq; destruct (in_dec Z.eq_dec x []) as [Hi|]; [destruct Hi|reflexivity]).
    assert (Hincl : incl Sb [0;1;2;3;4;5;6;7;8;9;10;11;16;17;18]).
    { intros x Hx. assert (Hx' := Hx). rewrite ES in Hx'. apply BuildPre.in_nzl in Hx'. destruct Hx' as [Hxr Hne].
      assert (~ (12 <= x <= 15)) by (intros C; apply Hne; apply H1215; auto).
      simpl. lia. }
    assert (HlenS : Zlength Sb <= 15)
      by (rewrite Zlength_correct; apply NoDup_incl_length in Hincl; auto; simpl in Hincl; lia).
    assert (HW : weight Rb <= 316).
    { rewrite (FT.weight_R _ _ _ _ _ _ _ _ _ _ HB).
      rewrite (FT.sumZ_map_ext' _ (fun x => Znth x (fc blt))) by (intros; apply Efq).
      rewrite <- (FT.zseq_sum_support Sb _ 19); [exact Hsum|exact Hnd|exact Hr|intros x Hx Hn; apply Hoff; auto]. }
    assert (Hc := FT.bl_cost _ _ _ _ _ _ _ _ _ _ HB Hpos' eq_refl HlenS HW).
    assert (Ho := FT.R_opt _ _ _ _ _ _ _ _ _ _ HB Hpos' 15 tau).
    lapply Ho; [clear Ho; intros Ho|]. 2: { intros x Hx. specialize (Hr x Hx). specialize (Htau x ltac:(unfold BL_CODES; lia)). lia. }
    lapply Ho; [clear Ho; intros Ho|]. 2: { eapply Z.le_trans; [|exact HK]. apply dtau_sub_le; [exact Hnd|exact Hr|intros x _; apply Z.pow_nonneg; lia]. }
    unfold FT.lenx in Hc.
    assert (Eg : forall g : Z -> Z, HuffAbs.sumZ (map (fun x => FT.fqt blt [] x * g x) Sb) =
                                   HuffAbs.sumZ (map (fun x => Znth x (fc blt) * g x) Sb))
      by (intros g; apply FT.sumZ_map_ext'; intros; rewrite Efq; reflexivity).
    rewrite (Eg (fun x => Znth x (dl t'))), (Eg (depth_of Rb)) in Hc. rewrite (Eg (depth_of Rb)), (Eg tau) in Ho.
    lia.
  - (* a forced node: at most one used symbol *)
    assert (HN : Zlength (BuildPre.nzl (fc blt) 19) < 2) by (destruct (Z_lt_le_dec (Zlength (BuildPre.nzl (fc blt) 19)) 2) as [|Hle]; [auto|discriminate (HF2 Hle)]).
    destruct (BuildPre.nzl (fc blt) 19) as [|s0 [|s1 nz]] eqn:EN.
    + (* nothing used: the cost is 0 *)
      simpl in ES. subst Sb.
      rewrite (FT.sumZ_map_ext' _ (fun x => 0 * Znth x (dl t'))) by (intros x Hx; rewrite HF0 by auto; reflexivity).
      rewrite FT.sumZ_map_scal'.
      assert (0 <= HuffAbs.sumZ (map (fun s => Znth s (fc blt) * tau s) (f1 :: Fr))).
      { apply sumZ_nonneg. intros x Hx. specialize (Hr x Hx). specialize (Hpos x Hr). specialize (Htau x ltac:(unfold BL_CODES; lia)). nia. }
      lia.
    + (* one used symbol s0 and one or two forced nodes *)
      simpl in ES.
      assert (Hs0 : In s0 (BuildPre.nzl (fc blt) 19)) by (rewrite EN; left; auto).
      apply BuildPre.in_nzl in Hs0. destruct Hs0 as [Hs0r Hs0ne].
      assert (Hc0 := Hpos s0 Hs0r). assert (Ht0 := Htau s0 ltac:(unfold BL_CODES; lia)).
      assert (Hdep : forall l, In l Rb -> ld l <= 2).
      { intros l Hl. assert (H := FS.huff_depth_count _ _ (FT.huffR _ _ _ _ _ _ _ _ _ _ HB) 0).
        lapply H; [clear H; intros H|]. 2: { intros I HI x Hx. unfold FT.Pt in HI. apply in_map_iff in HI. destruct HI as [y [<- _]].
                  destruct Hx as [<-|[]]. simpl. lia. }
        specialize (H l Hl). unfold FT.Pt in H. rewrite length_map in H. rewrite ES in H.
        rewrite Zlength_cons, Zlength_correct in HFl. simpl length in H. lia. }
      assert (Hlen : forall x, In x Sb -> Znth x (dl t') = depth_of Rb x).
      { apply (bt_noovf _ _ _ _ _ _ _ _ _ _ HB). intros l Hl. specialize (Hdep l Hl). cbn. unfold MAX_BL_BITS. lia. }
      assert (Hdp := FT.R_depth_pos _ _ _ _ _ _ _ _ _ _ HB Hpos').
      assert (Ho := FT.R_opt _ _ _ _ _ _ _ _ _ _ HB Hpos' 2 (fun x => if x =? s0 then 1 else 2)).
      assert (Hf1 : FT.fqt blt (f1 :: Fr) f1 = 1) by (unfold FT.fqt, fq; destruct (in_dec Z.eq_dec f1 (f1 :: Fr)) as [|C]; [reflexivity|exfalso; apply C; left; auto]).
      subst Sb. inversion Hnd as [|? ? Hn0 Hnd1]; subst.
      assert (Hq0 : FT.fqt blt (f1 :: Fr) s0 = Znth s0 (fc blt))
        by (unfold FT.fqt, fq; destruct (in_dec Z.eq_dec s0 (f1 :: Fr)) as [C|]; [contradiction|reflexivity]).
      destruct Fr as [|f2 [|f3 Fr']].
      * assert (s0 <> f1) by (intros E; apply Hn0; left; auto).
        cbn [map] in Ho |- *. cbn [HuffAbs.sumZ] in Ho |- *.
        rewrite (HF0 f1) by (left; auto). rewrite !Hlen by (simpl; auto).
        assert (D0 := Hdp s0 ltac:(simpl; auto)). assert (D1 := Hdp f1 ltac:(simpl; auto)).
        rewrite Z.eqb_refl, (proj2 (Z.eqb_neq f1 s0)) in Ho by auto. rewrite Hq0, Hf1 in Ho.
        lapply Ho; [clear Ho; intros Ho|]. 2: { intros x [<-|[<-|[]]]; [rewrite Z.eqb_refl|rewrite (proj2 (Z.eqb_neq f1 s0)) by auto]; lia. }
        lapply Ho; [clear Ho; intros Ho|]. 2: { lia. }
        nia.
      * assert (s0 <> f1) by (intros E; apply Hn0; left; auto).
        assert (s0 <> f2) by (intros E; apply Hn0; right; left; auto).
        inversion Hnd1 as [|? ? Hn1 _]; subst.
        assert (f1 <> f2) by (intros E; apply Hn1; left; auto).
        assert (Hf2 : FT.fqt blt [f1; f2] f2 = 1) by (unfold FT.fqt, fq; destruct (in_dec Z.eq_dec f2 [f1; f2]) as [|C]; [reflexivity|exfalso; apply C; right; left; auto]).
        cbn [map] in Ho |- *. cbn [HuffAbs.sumZ] in Ho |- *.
        rewrite (HF0 f1), (HF0 f2) by (simpl; auto). rewrite !Hlen by (simpl; auto).
        assert (D0 := Hdp s0 ltac:(simpl; auto)). assert (D1 := Hdp f1 ltac:(simpl; auto)). assert (D2 := Hdp f2 ltac:(simpl; auto)).
        rewrite Z.eqb_refl, (proj2 (Z.eqb_neq f1 s0)), (proj2 (Z.eqb_neq f2 s0)) in Ho by auto. rewrite Hq0, Hf1, Hf2 in Ho.
        lapply Ho; [clear Ho; intros Ho|]. 2: { intros x [<-|[<-|[<-|[]]]];
                   [rewrite Z.eqb_refl|rewrite (proj2 (Z.eqb_neq f1 s0)) by auto|rewrite (proj2 (Z.eqb_neq f2 s0)) by auto]; lia. }
        lapply Ho; [clear Ho; intros Ho|]. 2: { lia. }
        nia.
      * rewrite !Zlength_cons in HFl. pose proof (Zlength_nonneg Fr'). lia.
    + rewrite !Zlength_cons in HN. pose proof (Zlength_nonneg nz). lia.
Qed.

Lemma dtau_sum1 : forall {A} (l : list A), HuffAbs.sumZ (map (fun _ => 1) l) = Zlength l.
Proof.
  intros A l. induction l as [|a l IH]; cbn [map HuffAbs.sumZ]; [reflexivity|]. rewrite Zlength_cons. lia.
Qed.

Lemma dtau_sum01 : forall {A} (P : A -> bool) (l : list A),
  HuffAbs.sumZ (map (fun s => if P s then 1 else 0) l) <= Zlength l.
Proof.
  intros A P l. induction l as [|a l IH]; cbn [map HuffAbs.sumZ]; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons. destruct (P a); lia.
Qed.

Lemma dtau_wgen : forall sd t w S F order R t' mc w', bt_facts sd t w S F order R t' mc w' ->
  HuffAbs.sumZ (map (fq t F) S) <= zsum (sd_elems sd) (fun x => Znth x (fc t)) + 2.
Proof.
  intros sd t w S F order R t' mc w' HB.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 [HF2 _]]]]].
  rewrite ES, map_app, HuffAbs.sumZ_app.
  rewrite (FT.sumZ_map_ext' (fq t F) (fun x => Znth x (fc t)) (BuildPre.nzl (fc t) (sd_elems sd))).
  2:{ intros x Hx. unfold fq. destruct (in_dec Z.eq_dec x F) as [HxF|HxF]; [|reflexivity].
      apply BuildPre.in_nzl in Hx. specialize (HF0 x HxF). lia. }
  rewrite (FT.sumZ_map_ext' (fq t F) (fun _ => 1) F).
  2:{ intros x Hx. unfold fq. destruct (in_dec Z.eq_dec x F); [reflexivity|contradiction]. }
  rewrite dtau_sum1. unfold zsum.
  rewrite (FT.zseq_sum_support (BuildPre.nzl (fc t) (sd_elems sd))); [lia| | |].
  - unfold BuildPre.nzl. apply NoDup_filter, zseq_nodup.
  - intros x Hx. apply BuildPre.in_nzl in Hx. lia.
  - intros x Hx Hn. destruct (Z.eq_dec (Znth x (fc t)) 0) as [E|E]; [exact E|].
    exfalso. apply Hn. apply BuildPre.in_nzl. auto.
Qed.

Lemma dtau_lsum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  zsum L_CODES (lfreq syms) = Zlength syms + 1.
Proof.
  intros syms Hv. unfold zsum, lfreq. rewrite FT.sumZ_map_add'.
  assert (E1 : HuffAbs.sumZ (map (fun c => Zlength (filter (fun s => lcode_of s =? c) syms))
                                 (zseq 0 (Z.to_nat L_CODES))) = Zlength syms).
  { transitivity (HuffAbs.sumZ (map (fun s => if (fun _ : Z * Z => true) s then (fun _ : Z => 1) (lcode_of s) else 0) syms));
      [|exact (dtau_sum1 syms)].
    rewrite (FS.sum_by_code lcode_of (fun _ => true) (fun _ => 1) L_CODES syms).
    - apply FT.sumZ_map_ext'. intros c _. rewrite Z.mul_1_r. reflexivity.
    - intros x Hx _. apply FS.lcode_range, Hv, Hx. }
  assert (E2 : HuffAbs.sumZ (map (fun c => if c =? END_BLOCK then 1 else 0) (zseq 0 (Z.to_nat L_CODES))) = 1).
  { rewrite (FT.sumZ_map_ext' _ (fun c => if END_BLOCK =? c then 1 else 0))
      by (intros c _; rewrite Z.eqb_sym; reflexivity).
    apply FS.sumZ_indicator_zseq. rewrite Z2Nat.id by (unfold L_CODES; lia). unfold END_BLOCK, L_CODES. lia. }
  rewrite E1, E2. reflexivity.
Qed.

Lemma dtau_dsum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  zsum D_CODES (dfreq syms) <= Zlength syms.
Proof.
  intros syms Hv. eapply Z.le_trans; [|apply (dtau_sum01 (fun s : Z * Z => negb (fst s =? 0)) syms)].
  apply Z.eq_le_incl. unfold zsum, dfreq.
  transitivity (HuffAbs.sumZ (map (fun s => if (fun s : Z * Z => negb (fst s =? 0)) s then (fun _ : Z => 1) (FS.dcode_of s) else 0) syms));
    [|reflexivity].
  rewrite (FS.sum_by_code FS.dcode_of (fun s => negb (fst s =? 0)) (fun _ => 1) D_CODES syms).
  - apply FT.sumZ_map_ext'. intros c _. rewrite Z.mul_1_r. reflexivity.
  - intros x Hx HP. apply FS.dcode_range; [apply Hv, Hx|]. cbv beta in HP.
    destruct (Z.eqb_spec (fst x) 0); [discriminate|auto].
Qed.

(** The weights of the literal/length and distance trees for lit_bufsize <= 256. *)
Lemma dtau_weights : forall v, dctx v -> tr_lit_bufsize (v_s v) <= 256 ->
  HuffAbs.sumZ (map (fq (tr_ltree (v_s v)) (v_Fl v)) (v_Sl v)) <= 258 /\
  HuffAbs.sumZ (map (fq (tr_dtree (v_s v)) (v_Fd v)) (v_Sd v)) <= 258.
Proof.
  intros v Hv HL.
  destruct Hv as [Hpre _ _ Hbtl Hbtd _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct (fp_syms _ _ Hpre) as [_ [Hn [Hval _]]].
  destruct (fp_ltree _ _ Hpre) as [_ [_ [_ Hfl]]].
  destruct (fp_dtree _ _ Hpre) as [_ [_ [_ Hfd]]].
  pose proof (dtau_wgen _ _ _ _ _ _ _ _ _ _ Hbtl) as Wl.
  pose proof (dtau_wgen _ _ _ _ _ _ _ _ _ _ Hbtd) as Wd.
  change (sd_elems static_l_desc) with L_CODES in Wl.
  change (sd_elems static_d_desc) with D_CODES in Wd.
  assert (El : zsum L_CODES (fun x => Znth x (fc (tr_ltree (v_s v)))) = zsum L_CODES (lfreq (v_syms v))).
  { unfold zsum. apply FT.sumZ_map_ext'. intros x Hx. apply in_zseq in Hx.
    rewrite Z2Nat.id in Hx by (unfold L_CODES; lia). apply Hfl. lia. }
  assert (Ed : zsum D_CODES (fun x => Znth x (fc (tr_dtree (v_s v)))) = zsum D_CODES (dfreq (v_syms v))).
  { unfold zsum. apply FT.sumZ_map_ext'. intros x Hx. apply in_zseq in Hx.
    rewrite Z2Nat.id in Hx by (unfold D_CODES; lia). apply Hfd. lia. }
  pose proof (dtau_lsum _ Hval). pose proof (dtau_dsum _ Hval). lia.
Qed.

(** Lengths of a tree of weight <= 316 (max length 15) are at most 11. *)
Lemma dtau_le11 : forall sd t w S F order R t' mc w', bt_facts sd t w S F order R t' mc w' ->
  sd_maxlen sd = 15 -> (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t)) ->
  HuffAbs.sumZ (map (fq t F) S) <= 316 -> forall i, 0 <= i < sd_elems sd -> 0 <= Znth i (dl t') <= 11.
Proof.
  intros sd t w S F order R t' mc w' HB HM Hf HW i Hi.
  destruct (in_dec Z.eq_dec i S) as [HiS|HiS].
  - assert (EW := FT.weight_R _ _ _ _ _ _ _ _ _ _ HB). unfold FT.fqt in EW.
    assert (E := FT.lens_noovf _ _ _ _ _ _ _ _ _ _ HB Hf
                   ltac:(rewrite EW, HM; change (fib (15 + 3)) with 2584; lia) i HiS).
    assert (D := FT.depth_le11 _ _ _ _ _ _ _ _ _ _ HB Hf ltac:(lia) i HiS).
    unfold FT.lenx in E. lia.
  - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ HB i Hi HiS). lia.
Qed.

Lemma dtau_fmb : forall fuel bl i, find_max_blindex fuel bl i <= i.
Proof.
  induction fuel as [|fuel IH]; intros bl i; cbn [find_max_blindex]; [lia|].
  destruct (i >=? 3); [|lia]. destruct (negb _); [lia|]. specialize (IH bl (i - 1)). lia.
Qed.

Lemma dtau_cost_mono : forall (g h : Z -> Z) l, (forall s, g s <= h s) -> Hd.cost_tau g l <= Hd.cost_tau h l.
Proof.
  intros g h l Hgh. induction l as [|[x e] l IH]; unfold Hd.cost_tau in *; cbn [map Hd.sumZ fst snd]; [lia|].
  specialize (Hgh x). lia.
Qed.

Lemma dtau_streams : forall (g f : Z -> Z) T1 T2, Hd.syms_ok T1 -> Hd.syms_ok T2 ->
  (forall s, 0 <= s < 19 -> f s = Hd.cnt s T1 + Hd.cnt s T2) ->
  Hd.cost_tau g T1 + Hd.cost_tau g T2 =
  zsum 19 (fun s => f s * g s) + zsum 19 (fun s => f s * Znth s extra_blbits).
Proof.
  intros g f T1 T2 H1 H2 Hf.
  transitivity (HuffAbs.sumZ (map (fun s => Hd.cnt s T1 * (g s + Znth s extra_blbits) +
                                            Hd.cnt s T2 * (g s + Znth s extra_blbits)) (zseq 0 19))).
  { rewrite FT.sumZ_map_add', !Hd.cost_by_counts, !FS.sum_syms_zseq by auto. reflexivity. }
  unfold zsum. change (Z.to_nat 19) with 19%nat. rewrite <- FT.sumZ_map_add'.
  apply FT.sumZ_map_ext'. intros s Hs. apply in_zseq in Hs. simpl in Hs. rewrite (Hf s ltac:(lia)). ring.
Qed.

(** The tree header against every bit-length code, for lit_bufsize <= 256. *)
Lemma dsum_tau : forall v, dctx v ->
  tr_lit_bufsize (v_s v) <= 256 -> forall tau, tau_ok tau ->
  vHh v <= 71 + charge tau (vll v) (tr_lmax (v_s' v) + 1) + charge tau (vdl0 v) (tr_dmax (v_s' v) + 1) + 75.
Proof.
  intros v Hv HL tau Htau.
  pose proof Hv as Hv'. destruct Hv' as [Hpre _ _ Hbtl Hbtd Hbtb Hlg Hdg _ _ Hblr Hblcnt Hmbi _ _ _ _ _].
  destruct (dtau_weights v Hv HL) as [Wl Wd].
  destruct (fp_ltree _ _ Hpre) as [Lfc [Ldl [Hfl _]]].
  destruct (fp_dtree _ _ Hpre) as [Dfc [Ddl [Hfd _]]].
  assert (Hfl' : forall x, 0 <= x < sd_elems static_l_desc -> 0 <= Znth x (fc (tr_ltree (v_s v))))
    by (intros x Hx; cbn in Hx; unfold L_CODES in Hx; apply Hfl; unfold HEAP_SIZE; lia).
  assert (Hfd' : forall x, 0 <= x < sd_elems static_d_desc -> 0 <= Znth x (fc (tr_dtree (v_s v))))
    by (intros x Hx; cbn in Hx; unfold D_CODES in *; apply Hfd; lia).
  assert (Wl' : HuffAbs.sumZ (map (fq (tr_ltree (v_s v)) (v_Fl v)) (v_Sl v)) <= 316) by lia.
  assert (Wd' : HuffAbs.sumZ (map (fq (tr_dtree (v_s v)) (v_Fd v)) (v_Sd v)) <= 316) by lia.
  assert (Ll := dtau_le11 _ _ _ _ _ _ _ _ _ _ Hbtl eq_refl Hfl' Wl').
  assert (Dl := dtau_le11 _ _ _ _ _ _ _ _ _ _ Hbtd eq_refl Hfd' Wd').
  fold (vll v) in Ll. fold (vdl0 v) in Dl.
  set (s' := v_s' v) in *. set (lmax := tr_lmax s') in *. set (dmax := tr_dmax s') in *.
  destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtl) as [Hlm _].
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtl) as [_ [_ [Hlr _]]].
  destruct (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtd) as [Hdm _].
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtd) as [_ [_ [Hdr _]]].
  assert (Hlmax : 0 <= lmax < 286) by (specialize (Hlr _ Hlm); cbn in Hlr; unfold L_CODES in Hlr; lia).
  assert (Hdmax : 0 <= dmax < 30) by (specialize (Hdr _ Hdm); cbn in Hdr; unfold D_CODES in Hdr; lia).
  assert (Hlnz := bt_len_in _ _ _ _ _ _ _ _ _ _ Hbtl lmax Hlm). fold (vll v) in Hlnz.
  assert (Hdnz := bt_len_in _ _ _ _ _ _ _ _ _ _ Hbtd dmax Hdm). fold (vdl0 v) in Hdnz.
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ Hbtl) as [_ [Lll _]]. fold (vll v) in Lll.
  destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ Hbtd) as [_ [Ldd _]]. fold (vdl0 v) in Ldd.
  assert (Hll : forall i, 0 <= i <= lmax -> 0 <= Znth i (vll v) <= 11)
    by (intros i Hi; apply Ll; cbn; unfold L_CODES; lia).
  assert (Hdl : forall i, 0 <= i <= dmax -> 0 <= Znth i (vdl0 v) <= 11)
    by (intros i Hi; apply Dl; cbn; unfold D_CODES; lia).
  assert (ELT : dl (tr_ltree s') = upd_Znth (lmax + 1) (vll v) 65535) by (rewrite Hlg; reflexivity).
  assert (EDT : dl (tr_dtree s') = upd_Znth (dmax + 1) (vdl0 v) 65535) by (rewrite Hdg; reflexivity).
  assert (HLT : forall i, 0 <= i <= lmax -> Znth i (dl (tr_ltree s')) = Znth i (vll v))
    by (intros i Hi; rewrite ELT, Hd.Znth_upd_other by lia; reflexivity).
  assert (HDT : forall i, 0 <= i <= dmax -> Znth i (dl (tr_dtree s')) = Znth i (vdl0 v))
    by (intros i Hi; rewrite EDT, Hd.Znth_upd_other by lia; reflexivity).
  assert (HLg : Znth (lmax + 1) (dl (tr_ltree s')) = 65535)
    by (rewrite ELT, upd_Znth_same; [reflexivity|rewrite Lll, Ldl; unfold HEAP_SIZE; lia]).
  assert (HDg : Znth (dmax + 1) (dl (tr_dtree s')) = 65535)
    by (rewrite EDT, upd_Znth_same; [reflexivity|rewrite Ldd, Ddl; unfold D_CODES; lia]).
  assert (HLb : forall i, 0 <= i <= lmax -> 0 <= Znth i (dl (tr_ltree s')) <= 11)
    by (intros i Hi; rewrite HLT by lia; auto).
  assert (HDb : forall i, 0 <= i <= dmax -> 0 <= Znth i (dl (tr_dtree s')) <= 11)
    by (intros i Hi; rewrite HDT by lia; auto).
  set (Tl := Hd.tree_syms (dl (tr_ltree s')) lmax) in *.
  set (Td := Hd.tree_syms (dl (tr_dtree s')) dmax) in *.
  assert (HokL : Hd.syms_ok Tl) by (apply Hd.tree_syms_ok; [lia|intros i Hi; specialize (HLb i Hi); lia]).
  assert (HokD : Hd.syms_ok Td) by (apply Hd.tree_syms_ok; [lia|intros i Hi; specialize (HDb i Hi); lia]).
  assert (HrL := FS.tree_syms_range (dl (tr_ltree s')) lmax 11 ltac:(lia) HLb). fold Tl in HrL.
  assert (HrD := FS.tree_syms_range (dl (tr_dtree s')) dmax 11 ltac:(lia) HDb). fold Td in HrD.
  assert (HnL := FH.tree_syms_length (dl (tr_ltree s')) lmax ltac:(lia)). fold Tl in HnL.
  assert (HnD := FH.tree_syms_length (dl (tr_dtree s')) dmax ltac:(lia)). fold Td in HnD.
  assert (Hcnt : forall s, 0 <= s < 19 -> Znth s (fc (v_blt v)) = Hd.cnt s Tl + Hd.cnt s Td)
    by (intros s Hs; apply Hblcnt; unfold BL_CODES; lia).
  assert (Hb1 : forall x, 0 <= x < 19 -> 0 <= Znth x (fc (v_blt v)))
    by (intros x Hx; apply Hblr; unfold BL_CODES; lia).
  assert (Hb2 : zsum 19 (fun x => Znth x (fc (v_blt v))) <= 316).
  { unfold zsum. change (Z.to_nat 19) with 19%nat.
    rewrite (FT.sumZ_map_ext' _ (fun s => Hd.cnt s Tl + Hd.cnt s Td))
      by (intros s Hs; apply in_zseq in Hs; simpl in Hs; apply Hcnt; lia).
    rewrite FT.sumZ_map_add', !FS.sum_cnt_length
      by (intros q Hq; first [destruct (HokL q Hq) | destruct (HokD q Hq)]; lia).
    lia. }
  assert (Hb3 : forall x, 12 <= x <= 15 -> Znth x (fc (v_blt v)) = 0).
  { intros x Hx. rewrite Hcnt by lia.
    assert (Z1 : Hd.cnt x Tl = 0).
    { destruct (Z_le_gt_dec 1 (Hd.cnt x Tl)) as [Hc|Hc]; [|pose proof (Hd.cnt_nonneg x Tl); lia].
      destruct (FS.cnt_in _ _ Hc) as [e He]. specialize (HrL _ He). simpl in HrL. lia. }
    assert (Z2 : Hd.cnt x Td = 0).
    { destruct (Z_le_gt_dec 1 (Hd.cnt x Td)) as [Hc|Hc]; [|pose proof (Hd.cnt_nonneg x Td); lia].
      destruct (FS.cnt_in _ _ Hc) as [e He]. specialize (HrD _ He). simpl in HrD. lia. }
    lia. }
  assert (B := dtau_bl _ _ _ _ _ _ _ _ _ tau Hbtb Hb1 Hb2 Hb3 Htau).
  assert (E1 := dtau_streams (fun s => Znth s (dl (tr_bltree s'))) _ Tl Td HokL HokD Hcnt).
  assert (E2 := dtau_streams tau _ Tl Td HokL HokD Hcnt).
  destruct Htau as [Htau1 _].
  set (tau' := fun s => Z.max 0 (tau s)).
  assert (Htt : forall s, tau s <= tau' s) by (intros; unfold tau'; lia).
  assert (Htt' : forall s, 0 <= s < 19 -> tau' s = tau s)
    by (intros s Hs; unfold tau'; specialize (Htau1 s ltac:(unfold BL_CODES; lia)); lia).
  assert (C1 := dtau_cost_mono _ _ Tl Htt). assert (C1' := dtau_cost_mono _ _ Td Htt).
  assert (C2 : Hd.cost_tau tau' Tl <= charge tau (vll v) (lmax + 1)).
  { replace (charge tau (vll v) (lmax + 1)) with (charge tau' (dl (tr_ltree s')) (lmax + 1)).
    - apply Hd.tree_syms_cost; auto; [intros; unfold tau'; lia|lia| |].
      + intros i Hi. specialize (HLb i Hi). lia.
      + rewrite HLT by lia. lia.
    - rewrite (FH.charge_ext _ _ (vll v)) by (try lia; intros i Hi; apply HLT; lia).
      apply FS.charge_tau_ext; [lia|auto|]. intros i Hi. specialize (Hll i ltac:(lia)). lia. }
  assert (C2' : Hd.cost_tau tau' Td <= charge tau (vdl0 v) (dmax + 1)).
  { replace (charge tau (vdl0 v) (dmax + 1)) with (charge tau' (dl (tr_dtree s')) (dmax + 1)).
    - apply Hd.tree_syms_cost; auto; [intros; unfold tau'; lia|lia| |].
      + intros i Hi. specialize (HDb i Hi). lia.
      + rewrite HDT by lia. lia.
    - rewrite (FH.charge_ext _ _ (vdl0 v)) by (try lia; intros i Hi; apply HDT; lia).
      apply FS.charge_tau_ext; [lia|auto|]. intros i Hi. specialize (Hdl i ltac:(lia)). lia. }
  assert (Hm : v_mbi v <= 18) by (rewrite Hmbi; apply dtau_fmb).
  unfold vHh, Hd.stream_bits. fold s' lmax dmax Tl Td. cbv beta in E1, E2. lia.
Qed.

(** *** Helpers of [dsum_lenb]: opt_len / static_len of one build_tree call as sums over the alphabet *)

Lemma lb_sumZ_bound : forall {A} (g : A -> Z) (l : list A) K,
  (forall x, In x l -> 0 <= g x <= K) -> 0 <= HuffAbs.sumZ (map g l) <= Zlength l * K.
Proof.
  intros A g l K H. induction l as [|a l IH]; cbn [map HuffAbs.sumZ]; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons. specialize (IH (fun x Hx => H x (or_intror Hx))).
  specialize (H a (or_introl eq_refl)). lia.
Qed.

Lemma lb_zsum_bound : forall n g K, 0 <= n -> (forall i, 0 <= i < n -> 0 <= g i <= K) -> 0 <= zsum n g <= n * K.
Proof.
  intros n g K Hn H. unfold zsum.
  assert (E : Zlength (zseq 0 (Z.to_nat n)) = n) by (rewrite Zlength_correct, BuildPre.zseq_length; lia).
  assert (B := lb_sumZ_bound g (zseq 0 (Z.to_nat n)) K). rewrite E in B.
  apply B. intros x Hx. apply in_zseq in Hx. apply H. lia.
Qed.

Lemma lb_zsum_ext : forall n g h, (forall i, 0 <= i < n -> g i = h i) -> zsum n g = zsum n h.
Proof.
  intros n g h H. unfold zsum. apply FT.sumZ_map_ext'. intros x Hx. apply in_zseq in Hx. apply H. lia.
Qed.

Lemma lb_zsum_add : forall n g h, zsum n (fun i => g i + h i) = zsum n g + zsum n h.
Proof. intros. unfold zsum. apply FT.sumZ_map_add'. Qed.

Lemma lb_sumZ_minus1 : forall {A} (g : A -> Z) l,
  HuffAbs.sumZ (map (fun x => g x - 1) l) = HuffAbs.sumZ (map g l) - Zlength l.
Proof.
  intros A g l. induction l as [|a l IH]; cbn [map HuffAbs.sumZ]; [rewrite Zlength_nil; lia|].
  rewrite Zlength_cons, IH. lia.
Qed.

Lemma lb_nodup_app : forall (l1 l2 : list Z) x, NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x Hnd Hx; [destruct Hx|].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha Hnd].
  destruct Hx as [<-|Hx]; [intros H; apply Ha, in_or_app; auto|eauto].
Qed.

Lemma lb_sum_syms : forall f m, Hd.sum_syms f m = zsum (Z.of_nat m) f.
Proof.
  intros f m. rewrite CT.zsum_rs, Nat2Z.id. induction m as [|m IH]; [reflexivity|].
  cbn [Hd.sum_syms]. rewrite CT.rs_snoc, IH. reflexivity.
Qed.

(** A sum over the symbols [S] of a tree, weighted by [fq], = the sum over the alphabet weighted by the
    frequencies + the sum over the forced nodes. *)
Lemma lb_split : forall sd t w S F order R t' mc w' (h : Z -> Z),
  bt_facts sd t w S F order R t' mc w' ->
  HuffAbs.sumZ (map (fun x => fq t F x * h x) S) =
  zsum (sd_elems sd) (fun c => Znth c (fc t) * h c) + HuffAbs.sumZ (map h F).
Proof.
  intros sd t w S F order R t' mc w' h HB.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 _]]]].
  rewrite ES in Hnd |- *. rewrite map_app, HuffAbs.sumZ_app. f_equal.
  - unfold zsum.
    rewrite (FT.zseq_sum_support (BuildPre.nzl (fc t) (sd_elems sd))).
    + apply FT.sumZ_map_ext'. intros x Hx. unfold fq.
      destruct (in_dec Z.eq_dec x F) as [HxF|]; [|reflexivity].
      exfalso. exact (lb_nodup_app _ _ _ Hnd Hx HxF).
    + apply BuildPre.nzl_nodup.
    + intros x Hx. apply BuildPre.in_nzl in Hx. lia.
    + intros x Hx Hn. destruct (Z.eq_dec (Znth x (fc t)) 0) as [E|E]; [rewrite E; lia|].
      exfalso. apply Hn, BuildPre.in_nzl. auto.
  - apply FT.sumZ_map_ext'. intros x Hx. unfold fq.
    destruct (in_dec Z.eq_dec x F); [lia|contradiction].
Qed.

(** opt_len after build_tree. *)
Lemma lb_opt : forall sd t w S F order R t' mc w',
  bt_facts sd t w S F order R t' mc w' ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t) < 65536) ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= xbits sd x <= 16) ->
  sd_maxlen sd <= 15 -> 0 <= sd_elems sd <= 286 ->
  0 <= w_opt_len w <= 2 ^ 40 ->
  w_opt_len w' = w_opt_len w + zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c (dl t') + xbits sd c)) +
                 HuffAbs.sumZ (map (fun x => Znth x (dl t') + xbits sd x - 1) F) /\
  0 <= zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c (dl t') + xbits sd c)) <= 2 ^ 30 /\
  0 <= HuffAbs.sumZ (map (fun x => Znth x (dl t') + xbits sd x - 1) F) <= 62.
Proof.
  intros sd t w S F order R t' mc w' HB Hfc Hxb Hml Hel Hw.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 [HF2 _]]]]].
  assert (HinF : forall x, In x F -> In x S) by (intros x Hx; rewrite ES; apply in_or_app; auto).
  assert (HZ : 0 <= zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c (dl t') + xbits sd c)) <= 2 ^ 30).
  { assert (B := lb_zsum_bound (sd_elems sd) (fun c => Znth c (fc t) * (Znth c (dl t') + xbits sd c)) (65536 * 31)
                  ltac:(lia)).
    destruct B as [B1 B2]; [|split; [exact B1|]; lia].
    intros i Hi. specialize (Hfc i Hi). specialize (Hxb i Hi).
    assert (Hl : 0 <= Znth i (dl t') <= 15).
    { destruct (in_dec Z.eq_dec i S) as [HiS|HiS].
      - specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB i HiS). lia.
      - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ HB i Hi HiS). lia. }
    nia. }
  assert (HFb : 0 <= HuffAbs.sumZ (map (fun x => Znth x (dl t') + xbits sd x - 1) F) <= 62).
  { assert (B := lb_sumZ_bound (fun x => Znth x (dl t') + xbits sd x - 1) F 31).
    destruct B as [B1 B2]; [|lia].
    intros x Hx. assert (HxS := HinF x Hx). specialize (Hr x HxS).
    specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB x HxS). specialize (Hxb x Hr). lia. }
  split; [|auto].
  rewrite (bt_opt _ _ _ _ _ _ _ _ _ _ HB), (lb_split _ _ _ _ _ _ _ _ _ _ _ HB), lb_sumZ_minus1.
  rewrite lb_sumZ_minus1 in HFb. unfold u64. rewrite Z.mod_small; lia.
Qed.

(** static_len after build_tree (literal/length and distance trees). *)
Lemma lb_static : forall sd t w S F order R t' mc w' st,
  bt_facts sd t w S F order R t' mc w' -> sd_stree sd = Some st ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x (fc t) < 65536) ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= xbits sd x <= 16) ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= Znth x st <= 16) ->
  0 <= sd_elems sd <= 286 ->
  0 <= w_static_len w <= 2 ^ 40 ->
  w_static_len w' = w_static_len w + zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c st + xbits sd c)) +
                    HuffAbs.sumZ (map (xbits sd) F) /\
  0 <= zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c st + xbits sd c)) <= 2 ^ 30 /\
  0 <= HuffAbs.sumZ (map (xbits sd) F) <= 32.
Proof.
  intros sd t w S F order R t' mc w' st HB Est Hfc Hxb Hst Hel Hw.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 [HF2 _]]]]].
  assert (HinF : forall x, In x F -> In x S) by (intros x Hx; rewrite ES; apply in_or_app; auto).
  assert (HZ : 0 <= zsum (sd_elems sd) (fun c => Znth c (fc t) * (Znth c st + xbits sd c)) <= 2 ^ 30).
  { assert (B := lb_zsum_bound (sd_elems sd) (fun c => Znth c (fc t) * (Znth c st + xbits sd c)) (65536 * 32)
                  ltac:(lia)).
    destruct B as [B1 B2]; [|split; [exact B1|]; lia].
    intros i Hi. specialize (Hfc i Hi). specialize (Hxb i Hi). specialize (Hst i Hi). nia. }
  assert (HFb : 0 <= HuffAbs.sumZ (map (xbits sd) F) <= 32).
  { assert (B := lb_sumZ_bound (xbits sd) F 16).
    destruct B as [B1 B2]; [|lia].
    intros x Hx. apply Hxb, Hr, HinF, Hx. }
  split; [|auto].
  rewrite (bt_static _ _ _ _ _ _ _ _ _ _ HB), Est, (lb_split _ _ _ _ _ _ _ _ _ _ _ HB).
  rewrite FT.sumZ_map_add'.
  unfold u64. rewrite Z.mod_small; [lia|]. split; [lia|].
  assert (B := lb_sumZ_bound (fun x => Znth x st) F 16).
  destruct B as [B1 B2]; [|lia].
  intros x Hx. apply Hst, Hr, HinF, Hx.
Qed.


Lemma lb_nodup_r : forall (l1 l2 : list Z), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 H; [exact H|].
  simpl in H. apply NoDup_cons_iff in H. apply IH, H.
Qed.

(** The sum over the alphabet of the forced-node indicator = the sum over the forced nodes. *)
Lemma lb_forced_sum : forall sd t w S F order R t' mc w' (f : Z -> Z),
  bt_facts sd t w S F order R t' mc w' ->
  (forall c, 0 <= c < sd_elems sd -> Znth c (fc t) = f c) ->
  zsum (sd_elems sd) (fun c => if (0 <? Znth c (dl t')) && (f c =? 0) then Znth c (dl t') - 1 else 0) =
  HuffAbs.sumZ (map (fun x => Znth x (dl t') - 1) F).
Proof.
  intros sd t w S F order R t' mc w' f HB Hf.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 _]]]].
  assert (HinF : forall x, In x F -> In x S) by (intros x Hx; rewrite ES; apply in_or_app; auto).
  unfold zsum. rewrite (FT.zseq_sum_support F).
  - apply FT.sumZ_map_ext'. intros x Hx. assert (HxS := HinF x Hx).
    specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB x HxS). intros Hl.
    rewrite <- (Hf x (Hr x HxS)), (HF0 x Hx).
    replace (0 <? Znth x (dl t')) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite ES in Hnd. exact (lb_nodup_r _ _ Hnd).
  - intros x Hx. apply Hr, HinF, Hx.
  - intros x Hx HnF. destruct (in_dec Z.eq_dec x S) as [HxS|HxS].
    + rewrite ES in HxS. apply in_app_or in HxS. destruct HxS as [Hn|Hn]; [|contradiction].
      apply BuildPre.in_nzl in Hn. rewrite (Hf x Hx) in Hn.
      replace (f x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      rewrite andb_false_r. reflexivity.
    + rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ HB x Hx HxS). reflexivity.
Qed.

Lemma lb_pow_cases : forall M l, 3 <= M -> 1 <= l <= M ->
  (l = 1 /\ 2 ^ (M - l) = 4 * 2 ^ (M - 3)) \/ (l = 2 /\ 2 ^ (M - l) = 2 * 2 ^ (M - 3)) \/
  (3 <= l /\ 1 <= 2 ^ (M - l) <= 2 ^ (M - 3)).
Proof.
  intros M l HM Hl.
  destruct (Z.eq_dec l 1) as [->|H1]; [left; split; [reflexivity|]|].
  { replace (M - 1) with (2 + (M - 3)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  destruct (Z.eq_dec l 2) as [->|H2]; [right; left; split; [reflexivity|]|].
  { replace (M - 2) with (1 + (M - 3)) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  right; right. split; [lia|]. split.
  - assert (0 < 2 ^ (M - l)) by (apply Z.pow_pos_nonneg; lia). lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

(** Kraft equality over two or three symbols: all lengths are at most 2. *)
Lemma lb_kraft_small : forall (S : list Z) (g : Z -> Z) M, 3 <= M -> 2 <= Zlength S <= 3 ->
  (forall x, In x S -> 1 <= g x <= M) ->
  HuffAbs.sumZ (map (fun x => 2 ^ (M - g x)) S) = 2 ^ M -> forall x, In x S -> g x <= 2.
Proof.
  intros S g M HM HS Hg HK.
  assert (EM : 2 ^ M = 8 * 2 ^ (M - 3)).
  { replace M with (3 + (M - 3)) at 1 by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  destruct S as [|a [|b [|c [|d r]]]]; rewrite ?Zlength_cons, ?Zlength_nil in HS;
    [lia|lia| | |pose proof (Zlength_nonneg r); lia].
  - cbn [map HuffAbs.sumZ] in HK.
    pose proof (lb_pow_cases M (g a) HM (Hg a ltac:(simpl; auto))).
    pose proof (lb_pow_cases M (g b) HM (Hg b ltac:(simpl; auto))).
    intros x [<-|[<-|[]]]; lia.
  - cbn [map HuffAbs.sumZ] in HK.
    pose proof (lb_pow_cases M (g a) HM (Hg a ltac:(simpl; auto))).
    pose proof (lb_pow_cases M (g b) HM (Hg b ltac:(simpl; auto))).
    pose proof (lb_pow_cases M (g c) HM (Hg c ltac:(simpl; auto))).
    intros x [<-|[<-|[<-|[]]]]; lia.
Qed.

(** The forced-node overhead of one tree. *)
Lemma lb_forced_bound : forall sd t w S F order R t' mc w' B,
  bt_facts sd t w S F order R t' mc w' -> 3 <= sd_maxlen sd -> 0 <= B ->
  (forall x, 0 <= x < sd_elems sd -> 0 <= xbits sd x <= B) ->
  HuffAbs.sumZ (map (fun x => Znth x (dl t') - 1) F) <=
  HuffAbs.sumZ (map (fun x => Znth x (dl t') + xbits sd x - 1) F) <= 2 * (1 + B).
Proof.
  intros sd t w S F order R t' mc w' B HB HM HB0 Hxb.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr [HF0 [HF2 [HF3 HS2]]]]]].
  assert (HinF : forall x, In x F -> In x S) by (intros x Hx; rewrite ES; apply in_or_app; auto).
  split.
  { apply CT.hsum_map_le. intros x Hx. specialize (Hxb x (Hr x (HinF x Hx))). lia. }
  assert (Hc : F = [] \/ F <> []) by (destruct F; [left; reflexivity|right; discriminate]).
  destruct Hc as [EF|HnF]; [rewrite EF; cbn [map HuffAbs.sumZ]; lia|].
  assert (HS3 : Zlength S <= 3).
  { rewrite ES, Zlength_app.
    destruct (Z_lt_ge_dec (Zlength (BuildPre.nzl (fc t) (sd_elems sd))) 2) as [Hl|Hl]; [lia|].
    exfalso. exact (HnF (HF3 ltac:(lia))). }
  assert (Hsm := lb_kraft_small S (fun x => Znth x (dl t')) (sd_maxlen sd) HM ltac:(lia)
                   (bt_len_in _ _ _ _ _ _ _ _ _ _ HB) (bt_kraft _ _ _ _ _ _ _ _ _ _ HB)).
  cbn beta in Hsm.
  assert (Bd := lb_sumZ_bound (fun x => Znth x (dl t') + xbits sd x - 1) F (1 + B)).
  destruct Bd as [_ Bd].
  - intros x Hx. assert (HxS := HinF x Hx). specialize (Hsm x HxS).
    specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB x HxS). specialize (Hxb x (Hr x HxS)). lia.
  - nia.
Qed.

(** Table facts. *)
Lemma lb_tab_l : forall c, 0 <= c < 286 ->
  0 <= xbits static_l_desc c <= 5 /\ xbits static_l_desc c = xl c /\ 0 <= Znth c static_ltree_len <= 16.
Proof.
  intros c Hc.
  assert (H := CT.forallb_zseq (fun c => (0 <=? xbits static_l_desc c) && (xbits static_l_desc c <=? 5) &&
                                      (xbits static_l_desc c =? xl c) &&
                                      (0 <=? Znth c static_ltree_len) && (Znth c static_ltree_len <=? 16))
             0 286 ltac:(vm_compute; reflexivity) c ltac:(simpl; lia)).
  cbn beta in H. rewrite !andb_true_iff, !Z.leb_le, Z.eqb_eq in H. lia.
Qed.

Lemma lb_tab_d : forall c, 0 <= c < 30 ->
  0 <= xbits static_d_desc c <= 13 /\ xbits static_d_desc c = xd c /\ Znth c static_dtree_len = 5.
Proof.
  intros c Hc.
  assert (H := CT.forallb_zseq (fun c => (0 <=? xbits static_d_desc c) && (xbits static_d_desc c <=? 13) &&
                                      (xbits static_d_desc c =? xd c) && (Znth c static_dtree_len =? 5))
             0 30 ltac:(vm_compute; reflexivity) c ltac:(simpl; lia)).
  cbn beta in H. rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq in H. lia.
Qed.

Lemma lb_tab_b : forall c, 0 <= c < 19 ->
  0 <= xbits static_bl_desc c <= 7 /\ xbits static_bl_desc c = Znth c extra_blbits.
Proof.
  intros c Hc.
  assert (H := CT.forallb_zseq (fun c => (0 <=? xbits static_bl_desc c) && (xbits static_bl_desc c <=? 7) &&
                                      (xbits static_bl_desc c =? Znth c extra_blbits))
             0 19 ltac:(vm_compute; reflexivity) c ltac:(simpl; lia)).
  cbn beta in H. rewrite !andb_true_iff, !Z.leb_le, !Z.eqb_eq in H. lia.
Qed.

Lemma lb_fmb : forall fuel bl i, 0 <= i -> 0 <= find_max_blindex fuel bl i <= i.
Proof.
  induction fuel as [|fuel IH]; intros bl i Hi; cbn [find_max_blindex]; [lia|].
  destruct (i >=? 3) eqn:E; [|lia]. apply Z.geb_le in E.
  destruct (negb _); [lia|]. specialize (IH bl (i - 1) ltac:(lia)). lia.
Qed.


Lemma lb_len_range : forall sd t w S F order R t' mc w',
  bt_facts sd t w S F order R t' mc w' ->
  forall c, 0 <= c < sd_elems sd -> 0 <= Znth c (dl t') <= sd_maxlen sd.
Proof.
  intros sd t w S F order R t' mc w' HB c Hc.
  destruct (in_dec Z.eq_dec c S) as [HcS|HcS].
  - specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB c HcS). lia.
  - rewrite (bt_len_out _ _ _ _ _ _ _ _ _ _ HB c Hc HcS).
    specialize (bt_len_in _ _ _ _ _ _ _ _ _ _ HB mc (proj1 (bt_mc _ _ _ _ _ _ _ _ _ _ HB))). lia.
Qed.

Lemma lb_xbits_F : forall sd t w S F order R t' mc w' (g : Z -> Z),
  bt_facts sd t w S F order R t' mc w' ->
  (forall c, 0 <= c < sd_elems sd -> xbits sd c = g c) ->
  HuffAbs.sumZ (map (xbits sd) F) = HuffAbs.sumZ (map g F).
Proof.
  intros sd t w S F order R t' mc w' g HB Hg.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ HB) as [ES [Hnd [Hr _]]].
  apply FT.sumZ_map_ext'. intros x Hx. apply Hg, Hr. rewrite ES. apply in_or_app. auto.
Qed.

(** [dsum_lenb] up to the extra bits of the forced nodes in static_len. *)
Lemma dsum_lenb_gen : forall v, dctx v ->
  let syms := v_syms v in let ll := vll v in let dl0 := vdl0 v in
  w_static_len (tr_wk (v_s' v)) =
    stat_data syms + HuffAbs.sumZ (map xl (v_Fl v)) + HuffAbs.sumZ (map xd (v_Fd v)) /\
  v_slb v = (stat_data syms + HuffAbs.sumZ (map xl (v_Fl v)) + HuffAbs.sumZ (map xd (v_Fd v)) + 10) / 8 /\
  v_olb v = (if (v_slb v <=? (vHh v + dyn_data syms ll dl0 + vE v + 10) / 8) || (tr_strategy (v_s v) =? Z_FIXED)
             then v_slb v else (vHh v + dyn_data syms ll dl0 + vE v + 10) / 8) /\
  (0 <= vE v <= 64 /\ forced_extra syms ll dl0 <= vE v).
Proof.
  intros v Hv. cbv zeta.
  destruct Hv as [Hpre Hlev Hprep Hbtl Hbtd Hbtb Hlg Hdg Hbldl Hblsz Hblr Hblc Hmbi Hopt Hstat Hslb Holb Hkeep].
  destruct (fp_ltree _ _ Hpre) as [_ [_ [Hlr Hlf]]].
  destruct (fp_dtree _ _ Hpre) as [_ [_ [Hdr Hdf]]].
  destruct (fp_work _ _ Hpre) as [_ [_ [_ [Hw0o Hw0s]]]].
  assert (El : sd_elems static_l_desc = 286) by reflexivity.
  assert (Ed : sd_elems static_d_desc = 30) by reflexivity.
  assert (Eb : sd_elems static_bl_desc = 19) by reflexivity.
  assert (Ml : sd_maxlen static_l_desc = 15) by reflexivity.
  assert (Md : sd_maxlen static_d_desc = 15) by reflexivity.
  assert (Mb : sd_maxlen static_bl_desc = 7) by reflexivity.
  (* premises *)
  assert (Pl1 : forall x, 0 <= x < sd_elems static_l_desc -> 0 <= Znth x (fc (tr_ltree (v_s v))) < 65536)
    by (rewrite El; intros x Hx; apply Hlr; unfold HEAP_SIZE; lia).
  assert (Pl2 : forall x, 0 <= x < sd_elems static_l_desc -> 0 <= xbits static_l_desc x <= 16)
    by (rewrite El; intros x Hx; destruct (lb_tab_l x Hx); lia).
  assert (Pl3 : forall x, 0 <= x < sd_elems static_l_desc -> 0 <= Znth x static_ltree_len <= 16)
    by (rewrite El; intros x Hx; destruct (lb_tab_l x Hx); lia).
  assert (Pd1 : forall x, 0 <= x < sd_elems static_d_desc -> 0 <= Znth x (fc (tr_dtree (v_s v))) < 65536)
    by (rewrite Ed; intros x Hx; apply Hdr; unfold D_CODES; lia).
  assert (Pd2 : forall x, 0 <= x < sd_elems static_d_desc -> 0 <= xbits static_d_desc x <= 16)
    by (rewrite Ed; intros x Hx; destruct (lb_tab_d x Hx); lia).
  assert (Pd3 : forall x, 0 <= x < sd_elems static_d_desc -> 0 <= Znth x static_dtree_len <= 16)
    by (rewrite Ed; intros x Hx; destruct (lb_tab_d x Hx) as [_ [_ ->]]; lia).
  assert (Pb1 : forall x, 0 <= x < sd_elems static_bl_desc -> 0 <= Znth x (fc (v_blt v)) < 65536)
    by (rewrite Eb; intros x Hx; apply Hblr; unfold BL_CODES; lia).
  assert (Pb2 : forall x, 0 <= x < sd_elems static_bl_desc -> 0 <= xbits static_bl_desc x <= 16)
    by (rewrite Eb; intros x Hx; destruct (lb_tab_b x Hx); lia).
  (* opt_len and static_len of the three trees *)
  destruct (lb_opt _ _ _ _ _ _ _ _ _ _ Hbtl Pl1 Pl2 ltac:(rewrite Ml; lia) ltac:(rewrite El; lia)
              ltac:(rewrite Hw0o; lia)) as [Ol [OlZ OlF]].
  destruct (lb_opt _ _ _ _ _ _ _ _ _ _ Hbtd Pd1 Pd2 ltac:(rewrite Md; lia) ltac:(rewrite Ed; lia)
              ltac:(rewrite Ol, Hw0o; lia)) as [Od [OdZ OdF]].
  destruct (lb_opt _ _ _ _ _ _ _ _ _ _ Hbtb Pb1 Pb2 ltac:(rewrite Mb; lia) ltac:(rewrite Eb; lia)
              ltac:(rewrite Od, Ol, Hw0o; lia)) as [Ob [ObZ ObF]].
  destruct (lb_static _ _ _ _ _ _ _ _ _ _ static_ltree_len Hbtl eq_refl Pl1 Pl2 Pl3 ltac:(rewrite El; lia)
              ltac:(rewrite Hw0s; lia)) as [Sl [SlZ SlF]].
  destruct (lb_static _ _ _ _ _ _ _ _ _ _ static_dtree_len Hbtd eq_refl Pd1 Pd2 Pd3 ltac:(rewrite Ed; lia)
              ltac:(rewrite Sl, Hw0s; lia)) as [Sd [SdZ SdF]].
  assert (Sb : w_static_len (v_wb v) = w_static_len (v_wd v))
    by (rewrite (bt_static _ _ _ _ _ _ _ _ _ _ Hbtb); reflexivity).
  (* the sums in the terms of dyn_sum *)
  assert (ZL : zsum (sd_elems static_l_desc)
                 (fun c => Znth c (fc (tr_ltree (v_s v))) * (Znth c (dl (v_lt0 v)) + xbits static_l_desc c)) =
               zsum L_CODES (fun c => lfreq (v_syms v) c * (Znth c (vll v) + xl c))).
  { rewrite El. apply lb_zsum_ext. intros c Hc. cbv [L_CODES D_CODES] in Hc. unfold vll.
    rewrite Hlf by (unfold L_CODES; lia). rewrite (proj1 (proj2 (lb_tab_l c Hc))). reflexivity. }
  assert (ZD : zsum (sd_elems static_d_desc)
                 (fun c => Znth c (fc (tr_dtree (v_s v))) * (Znth c (dl (v_dt0 v)) + xbits static_d_desc c)) =
               zsum D_CODES (fun d => dfreq (v_syms v) d * (Znth d (vdl0 v) + xd d))).
  { rewrite Ed. apply lb_zsum_ext. intros c Hc. cbv [L_CODES D_CODES] in Hc. unfold vdl0.
    rewrite Hdf by (unfold D_CODES; lia). rewrite (proj1 (proj2 (lb_tab_d c Hc))). reflexivity. }
  assert (SL : zsum (sd_elems static_l_desc)
                 (fun c => Znth c (fc (tr_ltree (v_s v))) * (Znth c static_ltree_len + xbits static_l_desc c)) =
               zsum L_CODES (fun c => lfreq (v_syms v) c * (Znth c static_ltree_len + xl c))).
  { rewrite El. apply lb_zsum_ext. intros c Hc. cbv [L_CODES D_CODES] in Hc.
    rewrite Hlf by (unfold L_CODES; lia). rewrite (proj1 (proj2 (lb_tab_l c Hc))). reflexivity. }
  assert (SD : zsum (sd_elems static_d_desc)
                 (fun c => Znth c (fc (tr_dtree (v_s v))) * (Znth c static_dtree_len + xbits static_d_desc c)) =
               zsum D_CODES (fun d => dfreq (v_syms v) d * (5 + xd d))).
  { rewrite Ed. apply lb_zsum_ext. intros c Hc. cbv [L_CODES D_CODES] in Hc.
    rewrite Hdf by (unfold D_CODES; lia). destruct (lb_tab_d c Hc) as [_ [-> ->]]. reflexivity. }
  assert (XL : HuffAbs.sumZ (map (xbits static_l_desc) (v_Fl v)) = HuffAbs.sumZ (map xl (v_Fl v))).
  { apply (lb_xbits_F _ _ _ _ _ _ _ _ _ _ _ Hbtl). rewrite El. intros c Hc. apply (lb_tab_l c Hc). }
  assert (XD : HuffAbs.sumZ (map (xbits static_d_desc) (v_Fd v)) = HuffAbs.sumZ (map xd (v_Fd v))).
  { apply (lb_xbits_F _ _ _ _ _ _ _ _ _ _ _ Hbtd). rewrite Ed. intros c Hc. apply (lb_tab_d c Hc). }
  (* the bit-length tree part = the two streams *)
  assert (Hlmax : 0 <= tr_lmax (v_s' v) < 286).
  { destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtl) as [_ [_ [Hr _]]].
    specialize (Hr _ (proj1 (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtl))). rewrite El in Hr. lia. }
  assert (Hdmax : 0 <= tr_dmax (v_s' v) < 30).
  { destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtd) as [_ [_ [Hr _]]].
    specialize (Hr _ (proj1 (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtd))). rewrite Ed in Hr. lia. }
  assert (OkL : Hd.syms_ok (Hd.tree_syms (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v)))).
  { apply Hd.tree_syms_ok; [lia|]. intros i Hi. rewrite Hlg. unfold set_dl; cbn [dl].
    rewrite Hd.Znth_upd_other by lia.
    pose proof (lb_len_range _ _ _ _ _ _ _ _ _ _ Hbtl i ltac:(rewrite El; lia)). rewrite Ml in *. lia. }
  assert (OkD : Hd.syms_ok (Hd.tree_syms (dl (tr_dtree (v_s' v))) (tr_dmax (v_s' v)))).
  { apply Hd.tree_syms_ok; [lia|]. intros i Hi. rewrite Hdg. unfold set_dl; cbn [dl].
    rewrite Hd.Znth_upd_other by lia.
    pose proof (lb_len_range _ _ _ _ _ _ _ _ _ _ Hbtd i ltac:(rewrite Ed; lia)). rewrite Md in *. lia. }
  assert (ZB : zsum (sd_elems static_bl_desc)
                 (fun c => Znth c (fc (v_blt v)) * (Znth c (dl (tr_bltree (v_s' v))) + xbits static_bl_desc c)) =
               Hd.stream_bits (dl (tr_bltree (v_s' v))) (Hd.tree_syms (dl (tr_ltree (v_s' v))) (tr_lmax (v_s' v))) +
               Hd.stream_bits (dl (tr_bltree (v_s' v))) (Hd.tree_syms (dl (tr_dtree (v_s' v))) (tr_dmax (v_s' v)))).
  { unfold Hd.stream_bits. rewrite !Hd.cost_by_counts by assumption. rewrite !lb_sum_syms.
    change (Z.of_nat 19) with 19. rewrite <- lb_zsum_add, Eb. apply lb_zsum_ext. intros c Hc. cbv [L_CODES D_CODES] in Hc.
    rewrite Hblc by (unfold BL_CODES; lia). rewrite (proj2 (lb_tab_b c Hc)). ring. }
  rewrite ZL in Ol, OlZ. rewrite ZD in Od, OdZ. rewrite ZB in Ob, ObZ. rewrite SL in Sl, SlZ. rewrite SD in Sd, SdZ.
  rewrite XL in Sl, SlF. rewrite XD in Sd, SdF.
  assert (Hmb : 0 <= v_mbi v <= 18) by (rewrite Hmbi; apply lb_fmb; unfold BL_CODES; lia).
  (* opt_len, static_len of the block *)
  assert (EO : w_opt_len (tr_wk (v_s' v)) = vHh v + dyn_data (v_syms v) (vll v) (vdl0 v) +
                 (HuffAbs.sumZ (map (fun x => Znth x (dl (v_lt0 v)) + xbits static_l_desc x - 1) (v_Fl v)) +
                  HuffAbs.sumZ (map (fun x => Znth x (dl (v_dt0 v)) + xbits static_d_desc x - 1) (v_Fd v)) +
                  HuffAbs.sumZ (map (fun x => Znth x (dl (tr_bltree (v_s' v))) + xbits static_bl_desc x - 1)
                                 (v_Fb v)))).
  { rewrite Hopt, Ob, Od, Ol, Hw0o. unfold vHh, dyn_data.
    unfold u64. rewrite Z.mod_small by lia. ring. }
  assert (EvE : vE v =
                 HuffAbs.sumZ (map (fun x => Znth x (dl (v_lt0 v)) + xbits static_l_desc x - 1) (v_Fl v)) +
                 HuffAbs.sumZ (map (fun x => Znth x (dl (v_dt0 v)) + xbits static_d_desc x - 1) (v_Fd v)) +
                 HuffAbs.sumZ (map (fun x => Znth x (dl (tr_bltree (v_s' v))) + xbits static_bl_desc x - 1)
                                (v_Fb v))).
  { unfold vE. rewrite EO. ring. }
  assert (ES : w_static_len (tr_wk (v_s' v)) =
                 stat_data (v_syms v) + HuffAbs.sumZ (map xl (v_Fl v)) + HuffAbs.sumZ (map xd (v_Fd v))).
  { rewrite Hstat, Sb, Sd, Sl, Hw0s. unfold stat_data. ring. }
  assert (HsN : 0 <= w_static_len (tr_wk (v_s' v)) <= 2 ^ 32) by (rewrite ES; unfold stat_data; lia).
  assert (HoN : 0 <= w_opt_len (tr_wk (v_s' v)) <= 2 ^ 34)
    by (rewrite Hopt, Ob, Od, Ol, Hw0o; unfold u64; rewrite Z.mod_small by lia; lia).
  split; [exact ES|]. split.
  { rewrite Hslb, Z.shiftr_div_pow2 by lia. unfold u64. rewrite Z.mod_small by lia. rewrite ES.
    change (2 ^ 3) with 8. f_equal. ring. }
  split.
  { assert (Esh : Z.shiftr (u64 (w_opt_len (tr_wk (v_s' v)) + 3 + 7)) 3 =
                  (vHh v + dyn_data (v_syms v) (vll v) (vdl0 v) + vE v + 10) / 8).
    { rewrite Z.shiftr_div_pow2 by lia. unfold u64. rewrite Z.mod_small by lia.
      change (2 ^ 3) with 8. f_equal. unfold vE. ring. }
    rewrite Holb, Esh. reflexivity. }
  (* E: bounds, the forced overhead *)
  destruct (lb_forced_bound _ _ _ _ _ _ _ _ _ _ 5 Hbtl ltac:(rewrite Ml; lia) ltac:(lia)
              ltac:(rewrite El; intros x Hx; destruct (lb_tab_l x Hx); lia)) as [Fl1 Fl2].
  destruct (lb_forced_bound _ _ _ _ _ _ _ _ _ _ 13 Hbtd ltac:(rewrite Md; lia) ltac:(lia)
              ltac:(rewrite Ed; intros x Hx; destruct (lb_tab_d x Hx); lia)) as [Fd1 Fd2].
  destruct (lb_forced_bound _ _ _ _ _ _ _ _ _ _ 7 Hbtb ltac:(rewrite Mb; lia) ltac:(lia)
              ltac:(rewrite Eb; intros x Hx; destruct (lb_tab_b x Hx); lia)) as [Fb1 Fb2].
  assert (FEl : zsum L_CODES (fun c => if (0 <? Znth c (vll v)) && (lfreq (v_syms v) c =? 0)
                                       then Znth c (vll v) - 1 else 0) =
                HuffAbs.sumZ (map (fun x => Znth x (dl (v_lt0 v)) - 1) (v_Fl v))).
  { apply (lb_forced_sum _ _ _ _ _ _ _ _ _ _ _ Hbtl). rewrite El. intros c Hc. apply Hlf. unfold L_CODES; lia. }
  assert (FEd : zsum D_CODES (fun d => if (0 <? Znth d (vdl0 v)) && (dfreq (v_syms v) d =? 0)
                                       then Znth d (vdl0 v) - 1 else 0) =
                HuffAbs.sumZ (map (fun x => Znth x (dl (v_dt0 v)) - 1) (v_Fd v))).
  { apply (lb_forced_sum _ _ _ _ _ _ _ _ _ _ _ Hbtd). rewrite Ed. intros c Hc. apply Hdf. unfold D_CODES; lia. }
  unfold forced_extra. rewrite FEl, FEd, EvE. lia.
Qed.


(** *** The forced nodes of an actual build_tree call are 0, 1 or 2 *)

Lemma fs_force_frame : forall f sd t w mc x, 3 <= x ->
  Znth x (fc (fst (fst (bt_force f sd t w mc)))) = Znth x (fc t).
Proof.
  induction f as [|f IH]; intros sd t w mc x Hx; [reflexivity|].
  rewrite BuildPre.bt_force_step. destruct (w_heap_len w <? 2); [|reflexivity].
  rewrite IH by lia. unfold set_fc; cbn [fc].
  apply Hd.Znth_upd_other. unfold BuildPre.force_node.
  destruct (mc <? 2) eqn:E; cbn [fst]; [apply Z.ltb_lt in E|]; lia.
Qed.

Lemma fs_merge_frame : forall f t w node x, x < node ->
  Znth x (fc (fst (fst (bt_merge f t w node)))) = Znth x (fc t).
Proof.
  induction f as [|f IH]; intros t w node x Hx; [reflexivity|].
  rewrite BuildTree.bt_merge_unfold. destruct (BuildThm.merge_body_fc t w node) as [v [_ Ev]].
  destruct (merge_body t w node) as [t1 w1]. cbn [fst] in Ev.
  destruct (w_heap_len w1 >=? 2); [rewrite IH by lia|]; cbn [fst]; rewrite Ev; apply Hd.Znth_upd_other; lia.
Qed.

Lemma fs_pre_frame : forall sd t w x, 3 <= x < sd_elems sd ->
  Znth x (fc (fst (fst (BuildPre.bt_pre sd t w)))) = Znth x (fc t).
Proof.
  intros sd t w x Hx. unfold BuildPre.bt_pre.
  assert (E1 := BuildThm.bt_init_fc (Z.to_nat (sd_elems sd)) (sd_elems sd) t
                  (w_set_heap_max (w_set_heap_len w 0) HEAP_SIZE) (-1) 0).
  destruct (bt_init _ _ _ _ _ _) as [[t1 w1] m1]. cbn [fst] in E1.
  assert (E2 := fs_force_frame 2 sd t1 w1 m1 x ltac:(lia)).
  destruct (bt_force 2 sd t1 w1 m1) as [[t2 w2] m2]. cbn [fst] in E2.
  assert (E3 := fs_merge_frame (Z.to_nat (w_heap_len (bt_heapify (Z.to_nat (w_heap_len w2 / 2)) t2 w2 (w_heap_len w2 / 2))))
                  t2 (bt_heapify (Z.to_nat (w_heap_len w2 / 2)) t2 w2 (w_heap_len w2 / 2)) (sd_elems sd) x ltac:(lia)).
  destruct (bt_merge _ _ _ _) as [[t3 w3] m3]. cbn [fst] in E3 |- *. rewrite E3, E2, E1. reflexivity.
Qed.

(** A symbol of frequency 0 with a nonzero length after build_tree (a forced node) is 0, 1 or 2. *)
Lemma fs_actual : forall sd t w, bt_req sd t w ->
  forall x, 0 <= x < sd_elems sd -> Znth x (fc t) = 0 ->
  Znth x (dl (fst (fst (build_tree sd t w)))) <> 0 -> x <= 2.
Proof.
  intros sd t w HR x Hx Hf0 Hdl.
  destruct HR as [[Hel [HM Hpow]] [HTS HTS2] [Hh [Hd [Hol Hsl]]] Hfr [Hfc0 Hsum] [Hxb Hst]].
  rewrite BuildPre.build_tree_eq in Hdl.
  assert (BP := BuildPre.bt_pre_spec sd t w Hel HTS HTS2 Hh Hd Hol Hsl Hfc0 Hsum).
  assert (FR := BuildThm.bt_pre_fc sd t w Hfr).
  assert (FX := fs_pre_frame sd t w x).
  destruct (BuildPre.bt_pre sd t w) as [[t1 w1] mc] eqn:Ebp. cbn [fst] in FX.
  destruct BP as [S [F [R Hpo]]]. destruct FR as [Hfr1 Hfl1].
  destruct (BuildPre.po_len _ _ _ _ _ _ _ _ _ Hpo) as [PL1 [PL2 PL3]].
  assert (Hdlen : sd_elems sd <= Zlength (dl t1)) by lia.
  assert (Hxb1 : forall n, 0 <= n < Zlength (dl t1) -> 0 <= Bitlen.xb sd n <= 16) by (intros n Hn; apply Hxb; lia).
  assert (Hst1 : forall st, sd_stree sd = Some st -> forall n, 0 <= n < Zlength (dl t1) -> 0 <= Znth n st <= 16)
    by (intros st Hs n Hn; apply (Hst st Hs); lia).
  assert (Hfc1 : forall n, 0 <= n < Zlength (dl t1) -> 0 <= Znth n (fc t1) < 65536) by (intros n Hn; apply Hfr1; lia).
  assert (Hopt1 : 0 <= w_opt_len w1 < 18446744073709551616)
    by (rewrite (BuildPre.po_opt _ _ _ _ _ _ _ _ _ Hpo); unfold u64; apply Z.mod_pos_bound; lia).
  assert (Hstl1 : 0 <= w_static_len w1 < 18446744073709551616).
  { rewrite (BuildPre.po_static _ _ _ _ _ _ _ _ _ Hpo). destruct (sd_stree sd); [unfold u64; apply Z.mod_pos_bound; lia|lia]. }
  assert (G := BuildThm.g_genbitlen sd t w S F R t1 w1 mc Hpo HM Hel Hdlen Hxb1 Hst1 Hfc1 Hopt1 Hstl1 Hpow).
  destruct (gen_bitlen sd mc t1 w1) as [t3 w3] eqn:Egb.
  destruct G as [G1 [G2 [G3 [G4 [G5 [G6 [G7 [G8 _]]]]]]]].
  assert (HSr := BuildThm.g_S sd t w S F R t1 w1 mc Hpo). destruct HSr as [HSe [HSnd HSr]].
  assert (Hmc := BuildThm.g_mc sd t w S F R t1 w1 mc Hpo).
  assert (Hmclt := BuildThm.g_mc_lt sd t w S F R t1 w1 mc Hpo).
  assert (Hlens : forall i, 0 <= i <= mc -> Znth i (dl t3) <> 0 -> 1 <= Znth i (dl t3) <= 15).
  { intros i Hi Hnz. destruct (in_dec Z.eq_dec i S) as [HiS|HiS]; [specialize (G8 i HiS); lia|].
    exfalso. apply Hnz. apply G7; [lia|exact HiS]. }
  assert (Hmc0 : 0 <= mc) by (apply (HSr mc); apply Hmc).
  destruct (GenCodes.gen_codes_spec t3 mc (w_bl_count w3) ltac:(unfold HEAP_SIZE; lia) Hlens) as [C1 _].
  cbn [fst] in Hdl. rewrite C1 in Hdl.
  destruct (in_dec Z.eq_dec x S) as [HxS|HxS]; [|exfalso; apply Hdl, G7; auto].
  assert (HxS' := HxS). rewrite HSe in HxS'. apply in_app_or in HxS'. destruct HxS' as [Hn|HxF].
  - apply BuildPre.in_nzl in Hn. lia.
  - assert (P := BuildPre.po_fc _ _ _ _ _ _ _ _ _ Hpo x HxS).
    destruct (in_dec Z.eq_dec x F) as [_|]; [|contradiction].
    destruct (Z_le_gt_dec x 2) as [|Hgt]; [lia|]. rewrite FX in P by lia. lia.
Qed.


(** The fields of flush_prep's state that come from the two build_tree calls. *)
Lemma fs_blt : forall s,
  tr_ltree (fst (build_bl_tree s)) = set_dl (tr_ltree s) (tr_lmax s + 1) 65535 /\
  tr_lmax (fst (build_bl_tree s)) = tr_lmax s /\
  tr_dtree (fst (build_bl_tree s)) = set_dl (tr_dtree s) (tr_dmax s + 1) 65535 /\
  tr_dmax (fst (build_bl_tree s)) = tr_dmax s.
Proof.
  intros s. unfold build_bl_tree, scan_tree.
  destruct (Znth 0 (dl (tr_ltree s)) =? 0); destruct (Znth 0 (dl (tr_dtree s)) =? 0);
    match goal with |- context [build_tree static_bl_desc ?b ?c] =>
      destruct (build_tree static_bl_desc b c) as [[? ?] ?] end; cbn; auto.
Qed.

Lemma fs_prep : forall s stored, 0 < tr_level s ->
  forall lt lmax w1 dt dmax w2,
  build_tree static_l_desc (tr_ltree s) (tr_wk s) = (lt, lmax, w1) ->
  build_tree static_d_desc (tr_dtree s) w1 = (dt, dmax, w2) ->
  let s' := fst (fst (fst (flush_prep s stored))) in
  tr_ltree s' = set_dl lt (lmax + 1) 65535 /\ tr_lmax s' = lmax /\
  tr_dtree s' = set_dl dt (dmax + 1) 65535 /\ tr_dmax s' = dmax.
Proof.
  intros s stored Hl lt lmax w1 dt dmax w2 EL ED. unfold flush_prep.
  replace (tr_level s >? 0) with true by (symmetry; apply Z.gtb_lt; lia).
  set (s0 := if tr_data_type s =? Z_UNKNOWN then set_data_type s (detect_data_type (fc (tr_ltree s))) else s).
  assert (E0 : tr_ltree s0 = tr_ltree s /\ tr_dtree s0 = tr_dtree s /\ tr_wk s0 = tr_wk s)
    by (unfold s0; destruct (tr_data_type s =? Z_UNKNOWN); repeat split).
  clearbody s0. destruct E0 as [E1 [E2 E3]]. rewrite E1, E3, EL.
  cbn [tr_dtree tr_wk set_wk set_lmax set_ltree]. rewrite E2, ED.
  match goal with |- context [build_bl_tree ?x] => assert (B := fs_blt x); destruct (build_bl_tree x) as [s1 m] end.
  cbn in B |- *. exact B.
Qed.

(** bt_req of the two build_tree calls of flush_prep (as in FlushDyn's proof). *)
Lemma fs_lfreq_sum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  HuffAbs.sumZ (map (fun x => lfreq syms x) (zseq 0 (Z.to_nat L_CODES))) = Zlength syms + 1.
Proof.
  intros syms Hv.
  assert (Hb : forall x, In x syms -> 0 <= lcode_of x < 286).
  { intros x Hx. destruct (FS.lcode_range x (Hv x Hx)) as [A _]. unfold L_CODES in A. lia. }
  assert (Hk := CT.sum_by_key lcode_of (fun _ => 1) 286 syms Hb). rewrite CT.hsum_ones in Hk.
  rewrite CT.zsum_rs in Hk. change (Z.to_nat 286) with 286%nat in Hk.
  change (HuffAbs.sumZ (map (fun x => lfreq syms x) (zseq 0 (Z.to_nat L_CODES)))) with (CT.rs 0 286 (lfreq syms)).
  rewrite (CT.rs_ext _ 0 (lfreq syms)
             (fun j => 1 * Zlength (filter (fun x => lcode_of x =? j) syms) + (if j =? 256 then 1 else 0)))
    by (intros j Hj; unfold lfreq, END_BLOCK; lia).
  rewrite CT.rs_add, CT.rs_ind by (simpl; lia). lia.
Qed.

Definition fs_dkey (x : Z * Z) : Z := if fst x =? 0 then 30 else d_code (fst x - 1).

Lemma fs_dfreq_sum : forall syms, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  HuffAbs.sumZ (map (fun x => dfreq syms x) (zseq 0 (Z.to_nat D_CODES))) <= Zlength syms.
Proof.
  intros syms Hv.
  assert (Hb : forall x, In x syms -> 0 <= fs_dkey x < 31).
  { intros [d lc] Hx. specialize (Hv _ Hx). destruct Hv as [Hl Hd]. unfold fs_dkey; simpl in *.
    destruct (Z.eqb_spec d 0); [lia|]. destruct (dist_code_facts (d - 1) ltac:(lia)) as [A _]. lia. }
  assert (Hk := CT.sum_by_key fs_dkey (fun _ => 1) 31 syms Hb). rewrite CT.hsum_ones in Hk.
  rewrite CT.zsum_rs in Hk. change (Z.to_nat 31) with (S 30) in Hk. rewrite CT.rs_snoc in Hk.
  change (HuffAbs.sumZ (map (fun x => dfreq syms x) (zseq 0 (Z.to_nat D_CODES)))) with (CT.rs 0 30 (dfreq syms)).
  rewrite (CT.rs_ext _ 0 (dfreq syms) (fun j => 1 * Zlength (filter (fun x => fs_dkey x =? j) syms))).
  - assert (H0 := Zlength_nonneg (filter (fun x => fs_dkey x =? 0 + Z.of_nat 30) syms)). lia.
  - intros d Hd. rewrite Z.mul_1_l. unfold dfreq. f_equal. apply filter_ext_in. intros x Hx. unfold fs_dkey.
    destruct (fst x =? 0); cbn [negb andb]; [|reflexivity].
    symmetry. apply Z.eqb_neq. lia.
Qed.

Definition fs_tabs_ok (sd : stat_desc) (n : Z) : bool :=
  (0 <=? xbits sd n) && (xbits sd n <=? 16) &&
  match sd_stree sd with Some st => (0 <=? Znth n st) && (Znth n st <=? 16) | None => true end.

Lemma fs_tabs_ok_spec : forall sd N, forallb (fs_tabs_ok sd) (zseq 0 (Z.to_nat N)) = true ->
  (forall n, 0 <= n < N -> 0 <= xbits sd n <= 16) /\
  (forall st, sd_stree sd = Some st -> forall n, 0 <= n < N -> 0 <= Znth n st <= 16).
Proof.
  intros sd N H. split; [intros n Hn|intros st Est n Hn];
    assert (E := proj1 (forallb_forall _ _) H n ltac:(apply in_zseq; lia)); unfold fs_tabs_ok in E;
    [|rewrite Est in E]; repeat rewrite andb_true_iff in E; rewrite ?Z.leb_le in E; lia.
Qed.

Lemma fs_tabs_l : forallb (fs_tabs_ok static_l_desc) (zseq 0 (Z.to_nat HEAP_SIZE)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fs_tabs_d : forallb (fs_tabs_ok static_d_desc) (zseq 0 (Z.to_nat (2 * D_CODES + 1))) = true.
Proof. vm_compute. reflexivity. Qed.

(** The forced nodes of the literal/length and distance trees of [dctx] are 0, 1 or 2. *)
Lemma dyn_forced_small : forall v, dctx v ->
  (forall x, In x (v_Fl v) -> x <= 2) /\ (forall x, In x (v_Fd v) -> x <= 2).
Proof.
  intros v Hv.
  destruct Hv as [Hpre Hlev Hprep Hbtl Hbtd _ Hlg Hdg _ _ _ _ _ _ _ _ _ _].
  set (s := v_s v) in *. set (syms := v_syms v) in *.
  destruct Hpre as [HL [Hok [Hp0 [Hbv Hob]]] [Hsn [Hsl [Hval Hsy]]] [Hl1 [Hl2 [Hl3 Hl4]]] [Hd1 [Hd2 [Hd3 Hd4]]]
                  [Hb1 [Hb2 [Hb3 Hb4]]] [Hw1 [Hw2 [Hw3 [Hw4 Hw5]]]]].
  assert (HLB : tr_lit_bufsize s <= 32768).
  { destruct HL as [ml [Hml E]]. rewrite E. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  pose proof (Zlength_nonneg syms) as Hn0.
  (* the literal/length tree *)
  assert (RL : bt_req static_l_desc (tr_ltree s) (tr_wk s)).
  { constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE in *. lia.
    - rewrite Hw1, Hw2, Hw4, Hw5. unfold HEAP_SIZE. lia.
    - rewrite Hl1. exact Hl3.
    - split.
      + intros x Hx. cbn in Hx. apply Hl3. unfold HEAP_SIZE, L_CODES in *. lia.
      + cbn [sd_elems static_l_desc].
        rewrite (map_ext_in _ (fun x => lfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hl4; lia).
        rewrite fs_lfreq_sum by exact Hval. lia.
    - rewrite Hl2. exact (fs_tabs_ok_spec _ _ fs_tabs_l). }
  assert (AL := fs_actual _ _ _ RL).
  assert (BL := BuildThm.build_tree_correct _ _ _ RL).
  destruct (build_tree static_l_desc (tr_ltree s) (tr_wk s)) as [[lt lmax] w1] eqn:EL.
  destruct BL as [Sl' [Fl' [ordl' [Rl' BL]]]].
  (* the distance tree *)
  assert (RD : bt_req static_d_desc (tr_dtree s) w1).
  { destruct (bt_sizes _ _ _ _ _ _ _ _ _ _ BL) as [_ [_ [W1 [W2 _]]]].
    assert (O1 := bt_opt _ _ _ _ _ _ _ _ _ _ BL). assert (O2 := bt_static _ _ _ _ _ _ _ _ _ _ BL).
    cbn [sd_stree static_l_desc] in O2.
    constructor.
    - cbn; unfold L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; cbn; lia.
    - cbn. unfold HEAP_SIZE, D_CODES in *. lia.
    - rewrite W1, W2, O1, O2. unfold u64. repeat split; try lia; apply Z.mod_pos_bound; lia.
    - rewrite Hd1. exact Hd3.
    - split.
      + intros x Hx. cbn in Hx. apply Hd3. unfold D_CODES in *. lia.
      + cbn [sd_elems static_d_desc].
        rewrite (map_ext_in _ (fun x => dfreq syms x)) by (intros x Hx; apply in_zseq in Hx; apply Hd4; lia).
        assert (H := fs_dfreq_sum syms Hval). lia.
    - rewrite Hd2. exact (fs_tabs_ok_spec _ _ fs_tabs_d). }
  assert (AD := fs_actual _ _ _ RD).
  destruct (build_tree static_d_desc (tr_dtree s) w1) as [[dt dmax] w2] eqn:ED.
  destruct (fs_prep s (v_stored v) Hlev lt lmax w1 dt dmax w2 EL ED) as [P1 [P2 [P3 P4]]].
  rewrite Hprep in P1, P2, P3, P4. cbn [fst] in P1, P2, P3, P4, AL, AD.
  split.
  - intros x Hx.
    destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtl) as [ES [_ [Hr [HF0 _]]]].
    assert (HxS : In x (v_Sl v)) by (rewrite ES; apply in_or_app; auto).
    assert (Hxr := Hr x HxS).
    assert (Hlen := bt_len_in _ _ _ _ _ _ _ _ _ _ Hbtl x HxS).
    assert (Hxm := proj2 (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtl) x HxS).
    apply (AL x Hxr (HF0 x Hx)).
    assert (E : Znth x (dl (v_lt0 v)) = Znth x (dl lt)).
    { transitivity (Znth x (dl (tr_ltree (v_s' v)))).
      - rewrite Hlg. unfold set_dl; cbn [dl]. rewrite Hd.Znth_upd_other by lia. reflexivity.
      - rewrite P1. unfold set_dl; cbn [dl]. rewrite Hd.Znth_upd_other by lia. reflexivity. }
    lia.
  - intros x Hx.
    destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbtd) as [ES [_ [Hr [HF0 _]]]].
    assert (HxS : In x (v_Sd v)) by (rewrite ES; apply in_or_app; auto).
    assert (Hxr := Hr x HxS).
    assert (Hlen := bt_len_in _ _ _ _ _ _ _ _ _ _ Hbtd x HxS).
    assert (Hxm := proj2 (bt_mc _ _ _ _ _ _ _ _ _ _ Hbtd) x HxS).
    apply (AD x Hxr (HF0 x Hx)).
    assert (E : Znth x (dl (v_dt0 v)) = Znth x (dl dt)).
    { transitivity (Znth x (dl (tr_dtree (v_s' v)))).
      - rewrite Hdg. unfold set_dl; cbn [dl]. rewrite Hd.Znth_upd_other by lia. reflexivity.
      - rewrite P3. unfold set_dl; cbn [dl]. rewrite Hd.Znth_upd_other by lia. reflexivity. }
    lia.
Qed.


(** opt_lenb, static_lenb and the forced-node overhead E. *)
Lemma dsum_lenb : forall v, dctx v ->
  let syms := v_syms v in let ll := vll v in let dl0 := vdl0 v in
  (v_slb v = (stat_data syms + 10) / 8 /\
   v_olb v = (if (v_slb v <=? (vHh v + dyn_data syms ll dl0 + vE v + 10) / 8) || (tr_strategy (v_s v) =? Z_FIXED)
              then v_slb v else (vHh v + dyn_data syms ll dl0 + vE v + 10) / 8)) /\
  (0 <= vE v <= 64 /\ forced_extra syms ll dl0 <= vE v).
Proof.
  intros v Hv. cbv zeta.
  pose proof (dsum_lenb_gen v Hv) as G. cbv zeta in G. destruct G as [_ [G1 [G2 G3]]].
  destruct (dyn_forced_small v Hv) as [HFl HFd].
  assert (Hz : forall (g : Z -> Z) (F : list Z), (forall x, In x F -> g x = 0) -> HuffAbs.sumZ (map g F) = 0).
  { intros g F H. assert (B := lb_sumZ_bound g F 0). destruct B as [B1 B2]; [|lia].
    intros x Hx. rewrite H by exact Hx. lia. }
  assert (Z1 : HuffAbs.sumZ (map xl (v_Fl v)) = 0).
  { apply Hz. intros x Hx. specialize (HFl x Hx). unfold xl.
    replace (257 <=? x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  assert (Z2 : HuffAbs.sumZ (map xd (v_Fd v)) = 0).
  { apply Hz. intros x Hx. specialize (HFd x Hx). unfold xd.
    destruct (Z_lt_ge_dec x 0) as [Hn|Hp]; [apply Znth_underflow; lia|].
    assert (Hc : x = 0 \/ x = 1 \/ x = 2) by lia. destruct Hc as [E|[E|E]]; subst x; reflexivity. }
  rewrite Z1, Z2 in G1. rewrite !Z.add_0_r in G1.
  split; [split; [exact G1|exact G2]|exact G3].
Qed.

(** Helpers of [dsum_cost]. *)

Lemma dc_znth_upd_other : forall (l : list Z) i j u, i <> j -> Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros l i j u Hij. destruct (Z_le_gt_dec 0 j); [destruct (Z_lt_dec j (Zlength l))|].
  - apply upd_Znth_diff'; lia.
  - unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _) as [[? ?]|?]; [lia|reflexivity].
  - unfold upd_Znth. destruct (Sumbool.sumbool_and _ _ _ _ _ _) as [[? ?]|?]; [lia|reflexivity].
Qed.

Lemma dc_cost_sum_ext : forall a b c d (l : list (Z * Z)),
  (forall x, In x l -> sym_cost a b (fst x) (snd x) = sym_cost c d (fst x) (snd x)) ->
  cost_sum a b l = cost_sum c d l.
Proof.
  intros a b c d l. induction l as [|[x y] l IH]; intros H; simpl; [reflexivity|].
  rewrite (H (x, y) (or_introl eq_refl) : sym_cost a b x y = sym_cost c d x y), IH; [reflexivity|]. intros; apply H; right; auto.
Qed.

Lemma dc_filter_pos : forall {A} (f : A -> bool) l x, In x l -> f x = true -> 0 < Zlength (filter f l).
Proof.
  intros A f l x Hx Hf. destruct (filter f l) as [|y r] eqn:E.
  - assert (Hin : In x (filter f l)) by (apply filter_In; auto). rewrite E in Hin. destruct Hin.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg r). lia.
Qed.

Lemma dc_lfreq_pos : forall syms x, In x syms -> 0 < lfreq syms (lcode_of x).
Proof.
  intros syms x Hx. unfold lfreq.
  assert (H := dc_filter_pos (fun s => lcode_of s =? lcode_of x) syms x Hx (Z.eqb_refl _)).
  destruct (lcode_of x =? END_BLOCK); lia.
Qed.

Lemma dc_dfreq_pos : forall syms x, In x syms -> fst x <> 0 -> 0 < dfreq syms (d_code (fst x - 1)).
Proof.
  intros syms x Hx Hne. unfold dfreq. apply (dc_filter_pos _ syms x Hx).
  rewrite (proj2 (Z.eqb_neq _ _) Hne), Z.eqb_refl. reflexivity.
Qed.

(** A code of positive Freq is at most the max code of build_tree. *)
Lemma dc_le_mc : forall sd t w S F order R t' mc w' x,
  bt_facts sd t w S F order R t' mc w' -> 0 <= x < sd_elems sd -> Znth x (fc t) <> 0 -> x <= mc.
Proof.
  intros sd t w S F order R t' mc w' x Hbt Hx Hfx.
  destruct (bt_S _ _ _ _ _ _ _ _ _ _ Hbt) as [ES _]. apply (proj2 (bt_mc _ _ _ _ _ _ _ _ _ _ Hbt)).
  rewrite ES. apply in_or_app. left. apply BuildPre.in_nzl. auto.
Qed.

Definition dc_dkey (x : Z * Z) : Z := if fst x =? 0 then 30 else d_code (fst x - 1).

Definition dc_hl (ll : list Z) (c : Z) : Z := Znth c ll + xl c.
Definition dc_hd (dl : list Z) (d : Z) : Z := if d =? 30 then 0 else Znth d dl + xd d.

Lemma dc_sym_split : forall ll dl x, valid_sym (fst x) (snd x) ->
  sym_cost ll dl (fst x) (snd x) = dc_hl ll (lcode_of x) + dc_hd dl (dc_dkey x).
Proof.
  intros ll dl [d lc] [Hl Hd]. simpl in *. unfold sym_cost, lcode_of, dc_dkey, dc_hl, dc_hd, xl, xd; simpl.
  destruct (Z.eqb_spec d 0) as [E|E].
  - destruct (Z.leb_spec 257 lc); [lia|]. simpl. lia.
  - destruct (length_code_facts lc Hl) as [A _]. destruct (dist_code_facts (d - 1) ltac:(lia)) as [B _].
    unfold LITERALS. destruct (Z.leb_spec 257 (Znth lc length_code_tab + 256 + 1)); [|lia].
    destruct (Z.eqb_spec (d_code (d - 1)) 30); [lia|].
    replace (Znth lc length_code_tab + 256 + 1 - 257) with (Znth lc length_code_tab) by lia.
    replace (Znth lc length_code_tab + 256 + 1) with (Znth lc length_code_tab + 257) by lia. lia.
Qed.

Lemma dc_cost_sum_hsum : forall ll dl (l : list (Z * Z)),
  cost_sum ll dl l = HuffAbs.sumZ (map (fun x => sym_cost ll dl (fst x) (snd x)) l).
Proof. intros ll dl l. induction l as [|[x y] l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

(** The block's cost regrouped by codes. *)
Lemma dc_cost_regroup : forall syms ll dl, (forall x, In x syms -> valid_sym (fst x) (snd x)) ->
  cost_sum ll dl syms + Znth END_BLOCK ll =
  zsum L_CODES (fun c => lfreq syms c * (Znth c ll + xl c)) + zsum D_CODES (fun d => dfreq syms d * (Znth d dl + xd d)).
Proof.
  intros syms ll dl Hv. rewrite dc_cost_sum_hsum.
  rewrite (map_ext_in _ (fun x => dc_hl ll (lcode_of x) + dc_hd dl (dc_dkey x)) syms
             (fun x Hx => dc_sym_split ll dl x (Hv x Hx))).
  rewrite (CT.hsum_map_add (fun x => dc_hl ll (lcode_of x)) (fun x => dc_hd dl (dc_dkey x))).
  rewrite (CT.sum_by_key lcode_of (dc_hl ll) 286 syms).
  2:{ intros x Hx. destruct (FS.lcode_range x (Hv x Hx)). unfold L_CODES in *. lia. }
  rewrite (CT.sum_by_key dc_dkey (dc_hd dl) 31 syms).
  2:{ intros x Hx. destruct (Hv x Hx) as [Hl Hd]. unfold dc_dkey. destruct (Z.eqb_spec (fst x) 0); [lia|].
      destruct (dist_code_facts (fst x - 1) ltac:(lia)) as [B _]. lia. }
  unfold L_CODES, D_CODES. rewrite !CT.zsum_rs.
  change (Z.to_nat 31) with (S 30). rewrite CT.rs_snoc. simpl (0 + Z.of_nat 30).
  replace (dc_hd dl 30) with 0 by reflexivity.
  change (Z.to_nat 30) with 30%nat. change (Z.to_nat 286) with 286%nat.
  rewrite (CT.rs_ext 286 0 (fun c => lfreq syms c * (Znth c ll + xl c))
             (fun c => dc_hl ll c * Zlength (filter (fun x => lcode_of x =? c) syms) +
                       (if c =? 256 then Znth END_BLOCK ll else 0))).
  2:{ intros c Hc. unfold lfreq, END_BLOCK, dc_hl, xl. destruct (Z.eqb_spec c 256); [subst; simpl; lia|lia]. }
  rewrite CT.rs_add, CT.rs_ind by (simpl; lia).
  rewrite (CT.rs_ext 30 0 (fun d => dfreq syms d * (Znth d dl + xd d))
             (fun d => dc_hd dl d * Zlength (filter (fun x => dc_dkey x =? d) syms))).
  2:{ intros d Hd. simpl in Hd. unfold dc_hd. destruct (Z.eqb_spec d 30); [lia|]. unfold dfreq.
      rewrite (filter_ext (fun x => dc_dkey x =? d) (fun s => negb (fst s =? 0) && (d_code (fst s - 1) =? d))).
      - lia.
      - intros x. unfold dc_dkey. destruct (Z.eqb_spec (fst x) 0); [|reflexivity]. cbn [negb andb]. apply Z.eqb_neq; lia. }
  lia.
Qed.

(** The costs of the block's symbols. *)
Lemma dsum_cost : forall v, dctx v ->
  let s' := v_s' v in let syms := v_syms v in let ll := vll v in let dl0 := vdl0 v in
  (forall k, cost_sum (dl (tr_ltree s')) (dl (tr_dtree s')) (firstn k syms) = cost_sum ll dl0 (firstn k syms)) /\
  cost_sum ll dl0 syms + Znth END_BLOCK ll = dyn_data syms ll dl0 /\
  cost_sum static_ltree_len static_dtree_len syms + Znth END_BLOCK static_ltree_len = stat_data syms.
Proof.
  intros v Hv s' syms ll dl0. subst s' syms ll dl0.
  assert (Hval : forall x, In x (v_syms v) -> valid_sym (fst x) (snd x))
    by exact (proj1 (proj2 (proj2 (fp_syms _ _ (dc_pre v Hv))))).
  split; [|split].
  - intros k. rewrite (dc_lguard v Hv), (dc_dguard v Hv). cbn [dl set_dl].
    apply dc_cost_sum_ext. intros [d lc] Hx. apply firstn_In in Hx.
    destruct (Hval _ Hx) as [Hl Hd]. cbn [fst snd] in Hl, Hd.
    destruct (fp_ltree _ _ (dc_pre v Hv)) as [_ [_ [_ Hfl]]].
    destruct (fp_dtree _ _ (dc_pre v Hv)) as [_ [_ [_ Hfd]]].
    assert (HL : lcode_of (d, lc) <= tr_lmax (v_s' v)).
    { destruct (FS.lcode_range (d, lc) (conj Hl Hd)) as [R _].
      apply (dc_le_mc _ _ _ _ _ _ _ _ _ _ _ (dc_btl v Hv)); [exact R|].
      rewrite Hfl by exact R. pose proof (dc_lfreq_pos _ _ Hx). lia. }
    destruct (FS.lcode_range (d, lc) (conj Hl Hd)) as [R _].
    unfold sym_cost, lcode_of in *; cbn [fst snd] in *.
    destruct (Z.eqb_spec d 0) as [E|E].
    + rewrite dc_znth_upd_other by lia. reflexivity.
    + assert (HD : d_code (d - 1) <= tr_dmax (v_s' v)).
      { destruct (dist_code_facts (d - 1) ltac:(lia)) as [B _].
        apply (dc_le_mc _ _ _ _ _ _ _ _ _ _ _ (dc_btd v Hv)); [simpl; unfold D_CODES; lia|].
        rewrite Hfd by (unfold D_CODES; lia). pose proof (dc_dfreq_pos _ _ Hx E). simpl in H. lia. }
      unfold LITERALS in *.
      rewrite !dc_znth_upd_other by lia. reflexivity.
  - apply dc_cost_regroup. exact Hval.
  - rewrite dc_cost_regroup by exact Hval. unfold stat_data. f_equal.
Qed.

Lemma dd_Znth_zseq : forall k a i, 0 <= i < Z.of_nat k -> Znth i (zseq a k) = a + i.
Proof.
  induction k as [|k IH]; intros a i Hi; [lia|]. simpl.
  destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Znth_0_cons; lia|].
  rewrite Znth_pos_cons by lia. rewrite IH by lia. lia.
Qed.

Lemma dd_sumZ_const1 : forall (l : list Z) (g : Z -> Z), (forall x, In x l -> g x = 1) ->
  HuffAbs.sumZ (map g l) = Zlength l.
Proof.
  induction l as [|a l IH]; intros g Hg; simpl; [reflexivity|].
  rewrite Zlength_cons, IH by (intros; apply Hg; right; auto). rewrite Hg by (left; auto). lia.
Qed.

Lemma dd_len_le : forall (S : list Z) n, NoDup S -> (forall x, In x S -> 0 <= x < n) -> Zlength S <= Z.max 0 n.
Proof.
  intros S n Hnd Hr. rewrite Zlength_correct.
  assert (length S <= length (zseq 0 (Z.to_nat n)))%nat.
  { apply NoDup_incl_length; auto. intros x Hx. apply in_zseq. specialize (Hr x Hx). lia. }
  rewrite BuildPre.zseq_length in H. lia.
Qed.

(** A Kraft sum at 2^30 over at most three lengths >= 1: every length is at most 2. *)
Lemma dd_pow_cases : forall d, 1 <= d <= 30 ->
  0 < 2 ^ (30 - d) /\ (2 ^ (30 - d) = 2 ^ 29 \/ 2 ^ (30 - d) <= 2 ^ 28) /\ (3 <= d -> 2 ^ (30 - d) <= 2 ^ 27).
Proof.
  intros d Hd. split; [apply Z.pow_pos_nonneg; lia|]. split.
  - destruct (Z.eq_dec d 1) as [->|Hne]; [left; reflexivity|right; apply Z.pow_le_mono_r; lia].
  - intros. apply Z.pow_le_mono_r; lia.
Qed.

Lemma dd_kraft3 : forall (S : list Z) (g : Z -> Z), 2 <= Zlength S <= 3 -> (forall x, In x S -> 1 <= g x <= 30) ->
  HuffAbs.sumZ (map (fun x => 2 ^ (30 - g x)) S) = 2 ^ 30 -> forall x, In x S -> g x <= 2.
Proof.
  intros S g HS Hg HK x Hx.
  destruct (Z_le_gt_dec (g x) 2) as [|Hgt]; [auto|exfalso].
  destruct S as [|a [|b [|c [|d r]]]];
    try (rewrite ?Zlength_cons, ?Zlength_nil in HS; lia);
    try (rewrite !Zlength_cons in HS; pose proof (Zlength_nonneg r); lia).
  - cbn [map HuffAbs.sumZ] in HK.
    pose proof (dd_pow_cases (g a) (Hg a ltac:(simpl; auto))) as [A1 [A2 A3]].
    pose proof (dd_pow_cases (g b) (Hg b ltac:(simpl; auto))) as [B1 [B2 B3]].
    destruct Hx as [<-|[<-|[]]]; [specialize (A3 ltac:(lia))|specialize (B3 ltac:(lia))];
      change (2 ^ 30) with (2 * 2 ^ 29) in HK; change (2 ^ 29) with (2 * 2 ^ 28) in *;
      change (2 ^ 28) with (2 * 2 ^ 27) in *; lia.
  - cbn [map HuffAbs.sumZ] in HK.
    pose proof (dd_pow_cases (g a) (Hg a ltac:(simpl; auto))) as [A1 [A2 A3]].
    pose proof (dd_pow_cases (g b) (Hg b ltac:(simpl; auto))) as [B1 [B2 B3]].
    pose proof (dd_pow_cases (g c) (Hg c ltac:(simpl; auto))) as [C1 [C2 C3]].
    destruct Hx as [<-|[<-|[<-|[]]]];
      [specialize (A3 ltac:(lia))|specialize (B3 ltac:(lia))|specialize (C3 ltac:(lia))];
      change (2 ^ 30) with (2 * 2 ^ 29) in HK; change (2 ^ 29) with (2 * 2 ^ 28) in *;
      change (2 ^ 28) with (2 * 2 ^ 27) in *; lia.
Qed.

(** One tree of max length 15 (generic): the Huffman depths of [TreeDD.tree_dd] as a list over the alphabet
    [0 .. n-1], in terms of the symbol frequencies [f] (the Freq fields; the forced nodes have frequency 0 here). *)
Lemma dd_tree : TreeDD.tree_dd_statement ->
  forall sd t w S F order R t' mc w' (f : Z -> Z) n,
  bt_facts sd t w S F order R t' mc w' -> sd_maxlen sd = 15 -> sd_elems sd = n -> n <= 286 ->
  (forall x, 0 <= x < n -> Znth x (fc t) = f x) -> (forall x, 0 <= x < n -> 0 <= f x) ->
  zsum n f + Zlength F < 75025 ->
  exists dd : list Z, Zlength dd = n /\
    (forall c, 0 <= c < n -> 0 <= Znth c dd <= 30 /\ (In c S <-> Znth c dd <> 0)) /\
    zsum n (fun c => if Znth c dd =? 0 then 0 else 2 ^ (30 - Znth c dd)) = 2 ^ 30 /\
    (forall c, 0 <= c < n -> 0 < f c -> f c * fib (Znth c dd + 1) <= zsum n f + Zlength F) /\
    (F = [] -> forall e : Z -> Z, (forall c, 0 <= c < n -> 0 <= e c <= 30) ->
       zsum n (fun c => if Znth c dd =? 0 then 0 else 2 ^ (30 - e c)) <= 2 ^ 30 ->
       zsum n (fun c => f c * Znth c dd) <= zsum n (fun c => f c * e c)) /\
    (F <> [] -> forall c, 0 <= c < n -> Znth c dd <= 2) /\
    zsum n (fun c => f c * Znth c dd) <=
      zsum n (fun c => f c * Znth c (dl t')) +
      zsum n (fun c => if (0 <? Znth c (dl t')) && (f c =? 0) then Znth c (dl t') - 1 else 0) /\
    540 * zsum n (fun c => f c * Z.max 0 (Znth c (dl t') - Znth c dd)) <= 2 * n * (zsum n f + Zlength F) /\
    (zsum n f + Zlength F < fib 18 -> forall c, 0 <= c < n -> Znth c dd = Znth c (dl t')).
Proof.
  intros Htdd sd t w S F order R t' mc w' f n Hbt Hml Hel Hn Hf Hfnn HW.
  pose proof (bt_S _ _ _ _ _ _ _ _ _ _ Hbt) as [ES [Hnd [HSr [HF0 [HF2 [HF1 HS2]]]]]].
  pose proof (bt_len_out _ _ _ _ _ _ _ _ _ _ Hbt) as Hlout.
  pose proof (bt_len_in _ _ _ _ _ _ _ _ _ _ Hbt) as Hlin.
  rewrite Hel in ES, HSr, Hlout, HF1. rewrite Hml in Hlin.
  set (N := BuildPre.nzl (fc t) n) in *.
  assert (HN : forall x, In x N <-> 0 <= x < n /\ Znth x (fc t) <> 0) by (intros; apply BuildPre.in_nzl).
  assert (HinS : forall x, In x S <-> In x N \/ In x F) by (intros; rewrite ES, in_app_iff; tauto).
  assert (HfqN : forall x, In x N -> fq t F x = f x).
  { intros x Hx. apply HN in Hx. unfold fq. destruct (in_dec Z.eq_dec x F) as [HxF|]; [exfalso; apply Hx, HF0; auto|].
    apply Hf; lia. }
  assert (HfqF : forall x, In x F -> fq t F x = 1).
  { intros x Hx. unfold fq. destruct (in_dec Z.eq_dec x F); [reflexivity|contradiction]. }
  assert (HfF : forall x, In x F -> f x = 0).
  { intros x Hx. rewrite <- Hf by (apply HSr, HinS; auto). apply HF0; auto. }
  assert (Hfout : forall x, 0 <= x < n -> ~ In x N -> f x = 0).
  { intros x Hx Hn'. rewrite <- Hf by auto. destruct (Z.eq_dec (Znth x (fc t)) 0); [auto|].
    exfalso; apply Hn', HN; auto. }
  assert (Hsupp : forall g, (forall x, 0 <= x < n -> ~ In x S -> g x = 0) -> zsum n g = HuffAbs.sumZ (map g S)).
  { intros g Hg. unfold zsum. apply FT.zseq_sum_support; auto. }
  assert (HWeq : HuffAbs.sumZ (map (fq t F) S) = zsum n f + Zlength F).
  { rewrite ES at 1. rewrite map_app, HuffAbs.sumZ_app, (dd_sumZ_const1 F) by auto. f_equal.
    unfold zsum. rewrite (FT.zseq_sum_support N f n);
      [|apply BuildPre.nzl_nodup|intros x Hx; apply HN; auto|exact Hfout].
    apply FT.sumZ_map_ext'. auto. }
  assert (HSn : Zlength S <= Z.max 0 n) by (apply dd_len_le; auto).
  assert (Hfq0 : forall x, In x S -> 0 <= fq t F x).
  { intros x Hx. apply HinS in Hx as [Hx|Hx]; [rewrite HfqN by auto; apply Hfnn, HN; auto|rewrite HfqF by auto; lia]. }
  assert (HW0 : 0 <= HuffAbs.sumZ (map (fq t F) S)) by (apply HuffAbs.sumZ_nonneg; auto).
  destruct (Htdd sd t w S F order R t' mc w' Hbt ltac:(intros x Hx; rewrite Hf by lia; apply Hfnn; lia)
              Hml ltac:(lia) ltac:(lia))
    as [ddf [Hd1 [Hd2 [Hd3 [Hd4 [Hd5 [Hd6 Hd7]]]]]]].
  set (dd := map (fun c => if in_dec Z.eq_dec c S then ddf c else 0) (zseq 0 (Z.to_nat n))).
  assert (HZ : forall c, 0 <= c < n -> Znth c dd = if in_dec Z.eq_dec c S then ddf c else 0).
  { intros c Hc. unfold dd. rewrite Znth_map by (rewrite Zlength_correct, BuildPre.zseq_length; lia).
    rewrite dd_Znth_zseq by lia. reflexivity. }
  assert (HZin : forall c, In c S -> Znth c dd = ddf c).
  { intros c Hc. rewrite HZ by auto. destruct (in_dec Z.eq_dec c S); [reflexivity|contradiction]. }
  assert (HZout : forall c, 0 <= c < n -> ~ In c S -> Znth c dd = 0).
  { intros c Hc Hc'. rewrite HZ by auto. destruct (in_dec Z.eq_dec c S); [contradiction|reflexivity]. }
  exists dd. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - unfold dd. rewrite Zlength_map, Zlength_correct, BuildPre.zseq_length. lia.
  - intros c Hc. rewrite HZ by auto. destruct (in_dec Z.eq_dec c S) as [Hin|Hin].
    + specialize (Hd1 c Hin). split; [lia|]. split; [lia|auto].
    + split; [lia|]. split; [contradiction|]. intros []; reflexivity.
  - rewrite Hsupp by (intros x Hx Hx'; rewrite HZout by auto; reflexivity).
    rewrite <- Hd2. apply FT.sumZ_map_ext'. intros x Hx. rewrite HZin by auto.
    specialize (Hd1 x Hx). destruct (Z.eqb_spec (ddf x) 0); [lia|reflexivity].
  - intros c Hc Hfc. assert (HcN : In c N) by (apply HN; rewrite Hf by auto; lia).
    rewrite HZin by (apply HinS; auto). rewrite <- HWeq, <- (HfqN c) by auto. apply Hd3, HinS; auto.
  - intros HFn e He HK. subst F.
    assert (HSN : forall x, In x S <-> In x N) by (intros; rewrite HinS; simpl; tauto).
    rewrite (Hsupp (fun c => f c * Znth c dd)) by (intros x Hx Hx'; rewrite HZout by auto; lia).
    rewrite (Hsupp (fun c => f c * e c)) by (intros x Hx Hx'; rewrite Hfout by (auto; rewrite <- HSN; auto); lia).
    rewrite Hsupp in HK by (intros x Hx Hx'; rewrite HZout by auto; reflexivity).
    rewrite (FT.sumZ_map_ext' (fun c => f c * Znth c dd) (fun x => fq t [] x * ddf x))
      by (intros x Hx; rewrite HZin, HfqN by (auto; apply HSN; auto); reflexivity).
    rewrite (FT.sumZ_map_ext' (fun c => f c * e c) (fun x => fq t [] x * e x))
      by (intros x Hx; rewrite HfqN by (apply HSN; auto); reflexivity).
    apply Hd4.
    + intros x Hx. apply He, HSr; auto.
    + rewrite <- HK. apply Z.eq_le_incl, FT.sumZ_map_ext'. intros x Hx. rewrite HZin by auto.
      specialize (Hd1 x Hx). destruct (Z.eqb_spec (ddf x) 0); [lia|reflexivity].
  - intros HFn c Hc. rewrite HZ by auto. destruct (in_dec Z.eq_dec c S) as [Hin|]; [|lia].
    assert (HN2 : Zlength N < 2).
    { destruct (Z_lt_le_dec (Zlength N) 2); [auto|exfalso; apply HFn, HF1; auto]. }
    assert (HS3 : Zlength S <= 3) by (rewrite ES, Zlength_app; lia).
    apply (dd_kraft3 S ddf); auto. intros x Hx; specialize (Hd1 x Hx); lia.
  - set (ind := fun c => if (0 <? Znth c (dl t')) && (f c =? 0) then Znth c (dl t') - 1 else 0).
    rewrite (Hsupp (fun c => f c * Znth c dd)) by (intros x Hx Hx'; rewrite HZout by auto; lia).
    rewrite (Hsupp (fun c => f c * Znth c (dl t'))) by (intros x Hx Hx'; rewrite Hlout by auto; lia).
    rewrite (Hsupp ind) by (intros x Hx Hx'; unfold ind; rewrite Hlout by auto; reflexivity).
    assert (Hpt : forall x, In x S -> f x * Znth x dd + fq t F x * Znth x (dl t') <=
                                     (f x * Znth x (dl t') + ind x) + fq t F x * ddf x).
    { intros x Hx. rewrite HZin by auto. specialize (Hd1 x Hx). specialize (Hlin x Hx). unfold ind.
      destruct (in_dec Z.eq_dec x F) as [HxF|HxF].
      - rewrite HfqF, HfF by auto.
        replace ((0 <? Znth x (dl t')) && (0 =? 0)) with true
          by (symmetry; apply andb_true_iff; split; [apply Z.ltb_lt; lia|reflexivity]). lia.
      - assert (HxN : In x N) by (apply HinS in Hx; tauto). rewrite HfqN by auto.
        destruct ((0 <? Znth x (dl t')) && (f x =? 0)); lia. }
    pose proof (HuffAbs.sumZ_le _ _ S Hpt) as Hsum.
    rewrite !FT.sumZ_map_add' in Hsum. lia.
  - rewrite Hsupp by (intros x Hx Hx'; rewrite HZout, Hlout by auto; lia).
    assert (Hle : HuffAbs.sumZ (map (fun c => f c * Z.max 0 (Znth c (dl t') - Znth c dd)) S) <=
                  HuffAbs.sumZ (map (fun x => fq t F x * Z.max 0 (Znth x (dl t') - ddf x)) S)).
    { apply HuffAbs.sumZ_le. intros x Hx. rewrite HZin by auto.
      destruct (in_dec Z.eq_dec x F) as [HxF|HxF].
      - rewrite HfqF, HfF by auto. lia.
      - assert (HxN : In x N) by (apply HinS in Hx; tauto). rewrite HfqN by auto. lia. }
    rewrite HWeq in Hd6, HW0. assert (Zlength S <= n) by lia. nia.
  - intros HWs c Hc. rewrite HZ by auto. destruct (in_dec Z.eq_dec c S) as [Hin|Hin].
    + apply Hd7; [rewrite HWeq; auto|auto].
    + rewrite Hlout; auto.
Qed.


(** From the raw facts of [FlushDyn.dyn_prep] and the per-tree facts of [TreeDD.tree_dd]. *)
Theorem dyn_sum_holds : FlushDyn.dyn_prep_statement -> TreeDD.tree_dd_statement -> dyn_sum_statement.
Proof.
  intros Hprep Htdd s syms stored_len Hpre Hlev.
  destruct (dctx_exists Hprep s syms stored_len Hpre Hlev) as [v [Hv [Es [Esy Est]]]]. subst.
  pose proof Hv as Hv'. destruct Hv' as [Hpre' Hlev' Hprep' Hbtl Hbtd Hbtb _ _ _ _ _ _ _ _ _ _ _ Hkeep].
  destruct (dsum_sets v Hv) as [HSl [HFl [HFl0 [HSd [HFd HFd1]]]]].
  destruct (freq_sums (v_syms v) (proj1 (proj2 (proj2 (fp_syms _ _ Hpre))))) as [Hsl [Hsd [Hlpos Hdpos]]].
  destruct (fp_ltree _ _ Hpre) as [_ [_ [_ Hfl]]]. destruct (fp_dtree _ _ Hpre) as [_ [_ [_ Hfd]]].
  destruct (fp_syms _ _ Hpre) as [_ [Hn _]].
  destruct (fp_L _ _ Hpre) as [ml [Hml HL]].
  assert (HL128 : 128 <= tr_lit_bufsize (v_s v)).
  { rewrite HL. change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia. }
  assert (HL32 : tr_lit_bufsize (v_s v) <= 32768).
  { rewrite HL. change 32768 with (2 ^ 15). apply Z.pow_le_mono_r; lia. }
  pose proof (bt_S _ _ _ _ _ _ _ _ _ _ Hbtl) as [_ [_ [_ [_ [HFl2 _]]]]].
  pose proof (bt_S _ _ _ _ _ _ _ _ _ _ Hbtd) as [_ [_ [_ [_ [HFd2 _]]]]].
  pose proof (Zlength_nonneg (v_syms v)).
  destruct (dd_tree Htdd _ _ _ _ _ _ _ _ _ _ (lfreq (v_syms v)) L_CODES Hbtl eq_refl eq_refl ltac:(unfold L_CODES; lia)
              Hfl (fun c _ => Hlpos c) ltac:(rewrite Hsl; lia))
    as [dd [Ldd [Hdd1 [Hdd2 [Hdd3 [Hdd4 [_ [Hdd6 [Hdd7 Hdd8]]]]]]]]].
  destruct (dd_tree Htdd _ _ _ _ _ _ _ _ _ _ (dfreq (v_syms v)) D_CODES Hbtd eq_refl eq_refl ltac:(unfold D_CODES; lia)
              Hfd (fun c _ => Hdpos c) ltac:(lia))
    as [dd0 [Ldd0 [Hee1 [Hee2 [Hee3 [Hee4 [Hee5 [Hee6 [Hee7 Hee8]]]]]]]]].
  fold (vll v) in Hdd6, Hdd7, Hdd8. fold (vdl0 v) in Hee6, Hee7, Hee8.
  destruct (dsum_basic v Hv) as [Hb1 [Hb2 [Hb3 [Hb4 [Hb5 [Hb6 [Hb7 [Hb8 Hb9]]]]]]]].
  destruct (dsum_hdr v Hv) as [Hh1 Hh2].
  destruct (dsum_lenb v Hv) as [Hl1 Hl2].
  destruct (dsum_cost v Hv) as [Hc1 [Hc2 Hc3]].
  assert (HWl : zsum L_CODES (lfreq (v_syms v)) + Zlength (v_Fl v) <= tr_lit_bufsize (v_s v) + 1).
  { destruct (v_syms v) as [|x r] eqn:Ey.
    - rewrite Hsl. rewrite Zlength_nil. lia.
    - rewrite (HFl0 ltac:(discriminate)), Zlength_nil. rewrite <- Ey in *. lia. }
  assert (HSlnil : v_syms v <> [] -> forall c, In c (v_Sl v) <-> 0 <= c < L_CODES /\ 0 < lfreq (v_syms v) c).
  { intros Hne c. rewrite HSl, (HFl0 Hne). simpl. tauto. }
  exists (v_s' v), (v_olb v), (v_slb v), (v_mbi v), (vll v), (vdl0 v), dd, dd0, (vHh v), (vE v).
  constructor.
  - exact Hprep'.
  - exact Hkeep.
  - exact (conj (proj1 Hb1) (conj (proj2 Hb1) (conj Ldd Ldd0))).
  - exact Hb2.
  - exact Hb3.
  - exact Hb4.
  - exact Hb5.
  - exact Hb6.
  - exact Hb7.
  - exact Hb8.
  - exact Hb9.
  - exact Hh1.
  - exact Hh2.
  - exact (dsum_tau v Hv).
  - exact Hl1.
  - exact Hl2.
  - exact Hc1.
  - exact Hc2.
  - exact Hc3.
  - split.
    + intros c Hc. destruct (Hdd1 c Hc) as [A B]. split; [lia|].
      intros Hne. rewrite <- B, HSlnil by auto. tauto.
    + intros d Hd. destruct (Hee1 d Hd) as [A B]. split; [lia|].
      intros Hp. apply B. apply HSd. auto.
  - split; [intros _; exact Hdd2|rewrite Hee2; lia].
  - split.
    + intros c Hc Hp. eapply Z.le_trans; [apply Hdd3; auto|]. lia.
    + intros d Hd Hp. eapply Z.le_trans; [apply Hee3; auto|]. lia.
  - intros el ed Hel Hed Hkl Hkd Hne. split.
    + apply (Hdd4 (HFl0 Hne)); [intros c Hc; specialize (Hel c Hc); lia|].
      eapply Z.le_trans; [|exact Hkl]. rewrite !CT.zsum_rs. apply CT.rs_le. intros i Hi.
      destruct (Znth i dd =? 0); [|lia]. apply Z.lt_le_incl, Z.pow_pos_nonneg; [lia|].
      specialize (Hel i ltac:(change (Z.of_nat (Z.to_nat L_CODES)) with L_CODES in Hi; lia)). lia.
    + destruct (v_Fd v) as [|x r] eqn:EF.
      * apply (Hee4 eq_refl); [intros c Hc; specialize (Hed c Hc); lia|].
        eapply Z.le_trans; [|exact Hkd]. rewrite !CT.zsum_rs. apply CT.rs_le. intros i Hi.
        destruct (Znth i dd0 =? 0); [|lia]. apply Z.lt_le_incl, Z.pow_pos_nonneg; [lia|].
        specialize (Hed i ltac:(change (Z.of_nat (Z.to_nat D_CODES)) with D_CODES in Hi; lia)). lia.
      * rewrite !CT.zsum_rs. apply CT.rs_le. intros i Hi.
        change (Z.of_nat (Z.to_nat D_CODES)) with D_CODES in Hi.
        assert (A := Hee5 ltac:(discriminate) i ltac:(lia)). specialize (Hed i ltac:(lia)).
        specialize (Hdpos i). nia.
  - unfold forced_extra in Hl2. lia.
  - unfold L_CODES, D_CODES in *. lia.
  - intros HL2 Hne. assert (Hf18 : fib 18 = 2584) by reflexivity.
    rewrite (HFl0 Hne), Zlength_nil in Hdd8.
    split; [apply Hdd8; lia|apply Hee8; lia].
Qed.
