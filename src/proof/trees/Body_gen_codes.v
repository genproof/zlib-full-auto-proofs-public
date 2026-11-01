(** * The body of trees.c's gen_codes against its shared specification (TSpec.v) *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.Arith.
Require Import Zlib.proof.trees.TSpec.
Require Import Zlib.proof.trees.TLemmas.
Require Import Zlib.proof.trees.CtMode.
Require Import Zlib.trees.code.

#[export] Existing Instance DCS.CS.

Open Scope cmodel_scope.

(** ** The local [next_code]: entries [1 .. b) written (the model's list), the others uninitialised *)

Definition nc_vals (l : list Z) (b : Z) : list val :=
  map (fun i => if andb (0 <? i) (i <? b) then vi (Znth i l) else Vundef) (map Z.of_nat (seq 0 (Z.to_nat 16))).

Lemma Zlength_nc_vals l b : Zlength (nc_vals l b) = 16.
Proof. reflexivity. Qed.

Lemma Znth_nc_vals l b i : 0 <= i < 16 ->
  Znth i (nc_vals l b) = if andb (0 <? i) (i <? b) then vi (Znth i l) else Vundef.
Proof.
  intros. unfold nc_vals. rewrite Znth_map by (rewrite Zlength_map; cbn; lia).
  rewrite (Znth_seq_Z 16 i) by lia. reflexivity.
Qed.

Lemma nc_vals_1 l : nc_vals l 1 = Zrepeat Vundef 16.
Proof. reflexivity. Qed.

Lemma nc_vals_upd_next l b v : 1 <= b < 16 -> Zlength l = 16 ->
  upd_Znth b (nc_vals l b) (vi v) = nc_vals (upd_Znth b l v) (b + 1).
Proof.
  intros Hb Hl. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_nc_vals. reflexivity.
  - intros i Hi. rewrite Zlength_upd_Znth, Zlength_nc_vals in Hi.
    rewrite Znth_nc_vals by lia.
    destruct (Z.eq_dec i b) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_nc_vals; lia).
      rewrite upd_Znth_same by lia.
      replace (andb (0 <? b) (b <? b + 1)) with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
      reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_nc_vals; lia).
      rewrite Znth_nc_vals by lia. rewrite upd_Znth_diff by lia.
      destruct (0 <? i); cbn; [|reflexivity].
      destruct (Z.ltb_spec i b), (Z.ltb_spec i (b + 1)); try reflexivity; lia.
Qed.

Lemma nc_vals_upd l i v : 0 <= i < 16 -> Zlength l = 16 -> 0 < i ->
  upd_Znth i (nc_vals l 16) (vi v) = nc_vals (upd_Znth i l v) 16.
Proof.
  intros Hb Hl Hi0. apply Znth_eq_ext.
  - rewrite Zlength_upd_Znth, !Zlength_nc_vals. reflexivity.
  - intros j Hj. rewrite Zlength_upd_Znth, Zlength_nc_vals in Hj.
    rewrite Znth_nc_vals by lia.
    destruct (Z.eq_dec j i) as [->|ne].
    + rewrite upd_Znth_same by (rewrite Zlength_nc_vals; lia).
      rewrite upd_Znth_same by lia.
      replace (andb (0 <? i) (i <? 16)) with true by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; lia).
      reflexivity.
    + rewrite upd_Znth_diff by (rewrite ?Zlength_nc_vals; lia).
      rewrite Znth_nc_vals by lia. rewrite upd_Znth_diff by lia. reflexivity.
Qed.

Lemma Forall_upd_Znth_range (l : list Z) i v :
  0 <= i < Zlength l ->
  Forall (fun x => 0 <= x < 65536) l -> 0 <= v < 65536 -> Forall (fun x => 0 <= x < 65536) (upd_Znth i l v).
Proof.
  intros Hi Hl Hv. apply Forall_Znth. intros j Hj. rewrite Zlength_upd_Znth in Hj.
  destruct (Z.eq_dec j i) as [->|ne].
  - rewrite upd_Znth_same by lia. auto.
  - rewrite upd_Znth_diff by lia. apply Forall_Znth; auto.
Qed.

Lemma u16_range x : 0 <= u16 x < 65536.
Proof. unfold u16. apply Z.mod_pos_bound. lia. Qed.

Lemma u32_range x : 0 <= u32 x <= Int.max_unsigned.
Proof. unfold u32. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)). rep_lia. Qed.

Lemma code_step_repr code b :
  Int.shl (Int.add (Int.repr code) (Int.repr b)) (Int.repr 1) = Int.repr (u32 (Z.shiftl (code + b) 1)).
Proof.
  rewrite add_repr32, shl1_repr. unfold u32. apply Int.eqm_samerepr. apply Zbits.eqmod_mod. reflexivity.
Qed.

Lemma c_gen_next_code_S f blc ncl code bits :
  c_gen_next_code (S f) blc ncl code bits =
  if bits <=? MAX_BITS then
    let* b := rd blc (bits - 1) in
    let code := u32 (Z.shiftl (code + b) 1) in
    let* ncl := wr ncl bits (u16 code) in
    c_gen_next_code f blc ncl code (bits + 1)
  else Some ncl.
Proof. reflexivity. Qed.

Lemma c_gen_codes_loop_S f max_code t ncl k :
  c_gen_codes_loop (S f) max_code t ncl k =
  if k <=? max_code then
    let* len := rd (dl t) k in
    if len =? 0 then c_gen_codes_loop f max_code t ncl (k + 1)
    else
      let* c := rd ncl len in
      let* ncl := wr ncl len (u16 (c + 1)) in
      let* r := c_bi_reverse c len in
      let* t := c_set_fc t k (u16 r) in
      c_gen_codes_loop f max_code t ncl (k + 1)
  else Some t.
Proof. reflexivity. Qed.

Lemma rd_inv l i x : rd l i = Some x -> 0 <= i < Zlength l /\ x = Znth i l.
Proof.
  unfold rd, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

Lemma wr_inv l i v x : wr l i v = Some x -> 0 <= i < Zlength l /\ x = upd_Znth i l v.
Proof.
  unfold wr, in_range. destruct (andb (0 <=? i) (i <? Zlength l)) eqn:E; [|discriminate].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros H; inversion H; auto.
Qed.

(** The store [tree[k].Code = v] into the array presented in (Code, Len). *)
Lemma ct_arr_store_code (t : tree) k v :
  0 <= k < Zlength (fc t) -> Zlength (dl t) = Zlength (fc t) ->
  upd_Znth k (ct_arr ftrue ftrue t) (inr (Vint (Int.repr v)), snd (Znth k (ct_arr ftrue ftrue t))) =
  ct_arr ftrue ftrue (mkTree (upd_Znth k (fc t) v) (dl t)).
Proof.
  intros Hk Hl. rewrite Znth_ct_arr by lia.
  change (inr (Vint (Int.repr v)), snd (ctv_of (ftrue k) (ftrue k) (Znth k (fc t)) (Znth k (dl t))))
    with (ctv_of true (ftrue k) v (Znth k (dl t))).
  rewrite ct_arr_set_fc by auto.
  apply ct_arr_ext; auto. intros j. unfold fupd. destruct (Z.eq_dec j k); reflexivity.
Qed.

Lemma tree_ok_set_fc (t : tree) n k v :
  tree_ok t n -> 0 <= k < n -> 0 <= v < 65536 -> tree_ok (mkTree (upd_Znth k (fc t) v) (dl t)) n.
Proof.
  intros (Hf & Hd & Hr) Hk Hv. unfold tree_ok; cbn. split; [rewrite Zlength_upd_Znth; auto|]. split; [auto|].
  intros i Hi. destruct (Hr i Hi) as [H1 H2]. split; [|auto].
  destruct (Z.eq_dec i k) as [->|ne].
  - rewrite upd_Znth_same by lia. auto.
  - rewrite upd_Znth_diff by lia. auto.
Qed.

Lemma body_gen_codes : semax_body Vprog Gprog_gen_codes f_gen_codes gen_codes_spec.
Proof.
  start_function.
  unfold c_gen_codes in H2. inv_bind H2. rename x into nc0, Ha into Hnc, H2 into Hloop.
  unfold tree_arr. Intros.
  forward.
  forward_loop
    (EX f : nat, EX code : Z, EX bits : Z, EX ncl : list Z,
      PROP (c_gen_next_code f blc ncl code bits = Some nc0; 1 <= bits <= 16; 0 <= code <= Int.max_unsigned;
            Zlength ncl = 16; Forall (fun x => 0 <= x < 65536) ncl)
      LOCAL (temp _code (Vint (Int.repr code)); temp _bits (Vint (Int.repr bits));
             lvar _next_code (tarray tushort 16) v_next_code;
             temp _tree tp; temp _max_code (vi max_code); temp _bl_count bcp)
      SEP (data_at Tsh (tarray tushort 16) (nc_vals ncl bits) v_next_code;
           @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
           @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp))
    continue:
    (EX f : nat, EX code : Z, EX bits : Z, EX ncl : list Z,
      PROP (c_gen_next_code f blc ncl code (bits + 1) = Some nc0; 1 <= bits <= 15; 0 <= code <= Int.max_unsigned;
            Zlength ncl = 16; Forall (fun x => 0 <= x < 65536) ncl)
      LOCAL (temp _code (Vint (Int.repr code)); temp _bits (Vint (Int.repr bits));
             lvar _next_code (tarray tushort 16) v_next_code;
             temp _tree tp; temp _max_code (vi max_code); temp _bl_count bcp)
      SEP (data_at Tsh (tarray tushort 16) (nc_vals ncl (bits + 1)) v_next_code;
           @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
           @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp))
    break:
    (PROP (Zlength nc0 = 16; Forall (fun x => 0 <= x < 65536) nc0)
      LOCAL (lvar _next_code (tarray tushort 16) v_next_code;
             temp _tree tp; temp _max_code (vi max_code); temp _bl_count bcp)
      SEP (data_at Tsh (tarray tushort 16) (nc_vals nc0 16) v_next_code;
           @data_at DCS.CS Ews (tarray t_ct n) (ct_canon t) tp;
           @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp)).
  - forward.
    Exists 16%nat 0 1 (repeat 0 (Z.to_nat (MAX_BITS + 1))).
    rewrite nc_vals_1. entailer!.
    repeat constructor; lia.
  - Intros f code bits ncl.
    forward_if.
    + destruct f as [|f];
        [simpl in H3; rewrite (proj2 (Z.leb_le bits MAX_BITS)) in H3 by (unfold MAX_BITS; lia); discriminate|].
      rewrite c_gen_next_code_S, (proj2 (Z.leb_le bits MAX_BITS)) in H3 by (unfold MAX_BITS; lia).
      inv_bind H3. rename x into b, Ha into Hb. apply rd_inv in Hb as [Hb ->].
      inv_bind H3. rename x into ncl', Ha into Hw. apply wr_inv in Hw as [_ ->].
      assert (0 <= Znth (bits - 1) blc < 65536) by (apply Forall_Znth; auto; lia).
      fwd. fwd. unfold vi at 1. rewrite code_step_repr.
      pose proof (u32_range (Z.shiftl (code + Znth (bits - 1) blc) 1)).
      set (c' := u32 (Z.shiftl (code + Znth (bits - 1) blc) 1)) in *. clearbody c'.
      fwd.
      rewrite !zext16_repr, Zmod_mod. change (Vint (Int.repr (c' mod 65536))) with (vi (u16 c')).
      rewrite nc_vals_upd_next by lia.
      Exists f c' bits (upd_Znth bits ncl (u16 c')).
      entailer!.
      split; [rewrite Zlength_upd_Znth; auto|].
      apply Forall_upd_Znth_range; [lia|auto|apply u16_range].
    + assert (bits = 16) by lia. subst bits.
      assert (ncl = nc0) as <- by (destruct f; simpl in H3; inversion H3; auto).
      forward. entailer!.
  - Intros f code bits ncl.
    forward.
    Exists f code (bits + 1) ncl.
    entailer!.
  - Intros. unfold ct_canon. rewrite (ct_canon_mode Ews n ftrue ftrue t tp).
    forward_loop
      (EX f : nat, EX k : Z, EX tc : tree, EX ncl : list Z,
        PROP (c_gen_codes_loop f max_code tc ncl k = Some r; 0 <= k; (k + Z.of_nat f = HEAP_SIZE)%Z; tree_ok tc n;
              Zlength ncl = 16; Forall (fun x => 0 <= x < 65536) ncl)
        LOCAL (temp _n (Vint (Int.repr k)); lvar _next_code (tarray tushort 16) v_next_code;
               temp _tree tp; temp _max_code (vi max_code))
        SEP (data_at Tsh (tarray tushort 16) (nc_vals ncl 16) v_next_code;
             @data_at DCS.CS Ews (tarray t_ct n) (ct_arr ftrue ftrue tc) tp;
             @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp))
      continue:
      (EX f : nat, EX k : Z, EX tc : tree, EX ncl : list Z,
        PROP (c_gen_codes_loop f max_code tc ncl (k + 1) = Some r; 0 <= k; (k + 1 + Z.of_nat f = HEAP_SIZE)%Z;
              tree_ok tc n; Zlength ncl = 16; Forall (fun x => 0 <= x < 65536) ncl)
        LOCAL (temp _n (Vint (Int.repr k)); lvar _next_code (tarray tushort 16) v_next_code;
               temp _tree tp; temp _max_code (vi max_code))
        SEP (data_at Tsh (tarray tushort 16) (nc_vals ncl 16) v_next_code;
             @data_at DCS.CS Ews (tarray t_ct n) (ct_arr ftrue ftrue tc) tp;
             @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp))
      break:
      (PROP (tree_ok r n)
        LOCAL (lvar _next_code (tarray tushort 16) v_next_code)
        SEP (data_at_ Tsh (tarray tushort 16) v_next_code;
             @data_at DCS.CS Ews (tarray t_ct n) (ct_arr ffalse ffalse r) tp;
             @data_at DCS.CS Ews (tarray tushort 16) (map vi blc) bcp)).
    + forward.
      Exists (Z.to_nat HEAP_SIZE) 0 t nc0. entailer!.
    + Intros f k tc ncl.
      assert (k <= HEAP_SIZE) by lia. unfold HEAP_SIZE in *.
      forward_if.
      2:{ assert (tc = r) as <-.
          { destruct f; simpl in H5; rewrite (proj2 (Z.leb_gt k max_code)) in H5 by lia; inversion H5; auto. }
          forward. rewrite (ct_arr_mode Ews n ftrue ftrue ffalse ffalse tc tp). entailer!. }
      destruct f as [|f]; [simpl in H5; rewrite (proj2 (Z.leb_le k max_code)) in H5 by lia; discriminate|].
      rewrite c_gen_codes_loop_S, (proj2 (Z.leb_le k max_code)) in H5 by lia.
      inv_bind H5. rename x into len, Ha into Hlen. apply rd_inv in Hlen as [Hk ->].
      pose proof H8 as (Hfc & Hdl & Hrange).
      assert (0 <= Znth k (dl tc) < 65536) by (apply Hrange; lia).
      forward.
      1: rewrite Znth_ct_arr by lia; cbn [ctv_of ftrue]; tc_side.
      rewrite Znth_ct_arr by lia; cbn [ctv_of ftrue].
      forward_if.
      * forward.
        match goal with Hz : Znth k (dl tc) = 0 |- _ => rewrite Hz, Z.eqb_refl in H5 end.
        Exists f k tc ncl. entailer!.
      * match goal with Hz : Znth k (dl tc) <> 0 |- _ => rewrite (proj2 (Z.eqb_neq _ _) Hz) in H5 end.
        set (d := Znth k (dl tc)) in *.
        inv_bind H5. rename x into c, Ha into Hc. apply rd_inv in Hc as [Hd ->].
        inv_bind H5. rename x into ncl', Ha into Hw. apply wr_inv in Hw as [_ ->].
        inv_bind H5. rename x into rv, Ha into Hrv.
        inv_bind H5. rename x into tc', Ha into Hset.
        unfold c_set_fc in Hset. inv_bind Hset. rename x into fc', Ha into Hw. apply wr_inv in Hw as [_ ->].
        injection Hset as <-.
        assert (0 <= Znth d ncl < 65536) by (apply Forall_Znth; auto; lia).
        assert (Hdt : andb (0 <? d) (d <? 16) = true)
          by (apply andb_true_intro; split; apply Z.ltb_lt; lia).
        forward.
        1: rewrite Znth_nc_vals, Hdt by lia; tc_side.
        rewrite Znth_nc_vals, Hdt by lia.
        forward.
        rewrite add_repr32, zext16_repr.
        change (Vint (Int.repr ((Znth d ncl + 1) mod 65536))) with (vi (u16 (Znth d ncl + 1))).
        rewrite nc_vals_upd by lia.
        forward_call (Znth d ncl, d, rv).
        forward.
        rewrite !zext16_repr, Zmod_mod. change (rv mod 65536) with (u16 rv).
        rewrite ct_arr_store_code by lia.
        assert (tree_ok (mkTree (upd_Znth k (fc tc) (u16 rv)) (dl tc)) n)
          by (apply tree_ok_set_fc; [auto|lia|apply u16_range]).
        assert (Zlength (upd_Znth d ncl (u16 (Znth d ncl + 1))) = 16) by (rewrite Zlength_upd_Znth; auto).
        assert (Forall (fun x => 0 <= x < 65536) (upd_Znth d ncl (u16 (Znth d ncl + 1))))
          by (apply Forall_upd_Znth_range; [lia|auto|apply u16_range]).
        Exists f k (mkTree (upd_Znth k (fc tc) (u16 rv)) (dl tc)) (upd_Znth d ncl (u16 (Znth d ncl + 1))).
        entailer!.
    + Intros f k tc ncl.
      assert (k + 1 <= HEAP_SIZE) by lia. unfold HEAP_SIZE in *.
      forward.
      Exists f (k + 1) tc ncl. entailer!.
    + Intros. unfold POSTCONDITION, abbreviate. simpl_ret_assert. unfold tree_arr. entailer!.
Qed.
