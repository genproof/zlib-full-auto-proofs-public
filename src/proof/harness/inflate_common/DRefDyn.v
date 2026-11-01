(* Body proofs of harness/deflate_ref.h helpers: see DRefSpec.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_common.DRefDynFacts.

#[local] Existing Instance Zlib.contracts.x_inflate_decode.Harness.CS.

Lemma byte_Znth (l: list Z) (i: Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) l -> 0 <= Znth i l <= 255.
Proof.
  intros F. destruct (zlt i 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia |].
  destruct (zlt i (Zlength l)); [| rewrite Znth_overflow by lia; unfold Inhabitant_Z; lia].
  rewrite Forall_Znth in F. specialize (F i ltac:(lia)). rep_lia.
Qed.

Ltac bytes_tac :=
  repeat match goal with H: Forall (fun b => 0 <= b <= Byte.max_unsigned) ?l |- context [@Znth Z ?d ?i ?l] =>
    assert_fails (assert (0 <= @Znth Z d i l <= 255) by assumption); pose proof (byte_Znth l i H) end.

Lemma Forall_sublist_snoc {P: Z -> Prop} (l: list Z) (i: Z) :
  0 <= i < Zlength l -> Forall P (sublist 0 i l) -> P (Znth i l) -> Forall P (sublist 0 (i + 1) l).
Proof.
  intros R F X. rewrite (sublist_split 0 i (i + 1)) by lia. apply Forall_app. split; auto.
  rewrite sublist_len_1 by lia. constructor; auto.
Qed.

Lemma cbuf_sub (buf p: val) (sh: share) (l: list Z) (lo n: Z) :
  buf = offset_val lo p -> readable_share sh -> Forall (fun b => 0 <= b <= 15) l ->
  0 <= lo -> 0 <= n -> lo + n <= Zlength l ->
  Bytes.cbuf_ok false buf sh p lo (Zlength l) n (map (fun b => Vint (Int.repr b)) l) (sublist lo (lo + n) l) /\
  Forall (fun x => 0 <= x <= 15) (sublist lo (lo + n) l).
Proof.
  intros -> R F L N H. unfold Bytes.cbuf_ok.
  assert (FS: Forall (fun x => 0 <= x <= 15) (sublist lo (lo + n) l)) by (apply Forall_sublist; auto).
  split; auto. split3; auto. split3; [lia | lia |]. split3.
  - rewrite Zlength_sublist by lia. lia.
  - unfold Bytes.is_bytes. eapply Forall_impl; [| exact FS]. intros; simpl in *; rep_lia.
  - unfold Bytes.bytes_rep. rewrite sublist_map. reflexivity.
Qed.

Lemma bw_room_of (B B': list bool) (cap m d k: Z) :
  Zlength B / 8 + 15 + 2 * m <= cap -> cap <= Int.max_unsigned -> 0 <= k ->
  Zlength B <= Zlength B' <= Zlength B + d -> d + k <= 85 + 14 * m -> bw_room B' cap k.
Proof.
  intros C U K L D. unfold bw_room. split; [lia | split; [| lia]].
  pose proof (Z.div_mod (Zlength B) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Zlength B) 8 ltac:(lia)).
  pose proof (Zlength_nonneg B).
  apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma clorder_range (i: Z) : 0 <= Znth i clorder <= 18.
Proof.
  assert (F: Forall (fun x => 0 <= x <= 18) clorder) by (repeat constructor; lia).
  destruct (zlt i 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia |].
  destruct (zlt i (Zlength clorder)); [| rewrite Znth_overflow by lia; unfold Inhabitant_Z; lia].
  rewrite Forall_Znth in F. apply F. lia.
Qed.

Lemma Zlength_bits_le (v n: Z) : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma Zlength_bits_msb (v n: Z) : 0 <= n -> Zlength (bits_msb v n) = n.
Proof. intros. unfold bits_msb. rewrite Zlength_rev. apply Zlength_bits_le; auto. Qed.

Ltac room B0 D :=
  eapply (bw_room_of B0 _ _ _ D); [eassumption | lia | lia | rewrite ?Zlength_app, ?Zlength_bits_le by lia; lia | lia].

Lemma sublist_const (l: list Z) (i r v: Z) :
  0 <= i -> 0 <= r -> i + r <= Zlength l -> (forall k, 0 <= k < r -> Znth (i + k) l = v) ->
  sublist i (i + r) l = repeat v (Z.to_nat r).
Proof.
  intros I R L F. apply Znth_eq_ext.
  - rewrite Zlength_sublist, Zlength_repeat by lia. lia.
  - intros k K. rewrite Zlength_sublist in K by lia. rewrite Znth_sublist by lia.
    rewrite Znth_repeat_inrange by lia. rewrite <- (F k) by lia. f_equal; lia.
Qed.

Lemma Znth_canon_vals (l: list Z) (k: Z) : 0 <= k < Zlength l -> Znth k (canon_vals l) = canon_val l k.
Proof.
  intros K. unfold canon_vals. rewrite Znth_map by (rewrite Zlength_correct, seq_length; rewrite Zlength_correct in K; lia).
  f_equal. unfold Znth. rewrite if_false by lia. rewrite seq_nth by (rewrite Zlength_correct in K; lia). simpl. lia.
Qed.

Lemma canon_val_range (l: list Z) (k: Z) : 0 <= canon_val l k < 65536.
Proof. unfold canon_val. destruct (Znth k l =? 0); [lia |]. apply Z.mod_pos_bound; lia. Qed.

Lemma Znth_zvals_canon (d: Inhabitant val) (l: list Z) (k: Z) :
  0 <= k < Zlength l -> @Znth val d k (zvals (canon_vals l)) = Vint (Int.repr (canon_val l k)).
Proof.
  intros K. unfold zvals. rewrite Znth_map by (unfold canon_vals; rewrite Zlength_map, Zlength_correct, seq_length;
    rewrite Zlength_correct in K; lia).
  rewrite Znth_canon_vals by auto. reflexivity.
Qed.

Lemma Znth_bound7 (cl: list Z) (k: Z) : Forall (fun l => 0 <= l <= 7) cl -> 0 <= Znth k cl <= 7.
Proof.
  intros F. destruct (zlt k 0); [rewrite Znth_underflow by lia; unfold Inhabitant_Z; lia |].
  destruct (zlt k (Zlength cl)); [| rewrite Znth_overflow by lia; unfold Inhabitant_Z; lia].
  rewrite Forall_Znth in F. apply F. lia.
Qed.

Lemma last_sublist (l: list Z) (i: Z) : 0 < i <= Zlength l -> last (sublist 0 i l) 0 = Znth (i - 1) l.
Proof.
  intros I. rewrite (sublist_split 0 (i - 1) i) by lia.
  replace (sublist (i - 1) i l) with [Znth (i - 1) l]
    by (rewrite <- (sublist_len_1 (i - 1) l) by lia; f_equal; lia).
  rewrite last_app; [reflexivity | discriminate].
Qed.

Ltac bfacts :=
  repeat match goal with
  | H: (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  | H: (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H: (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H: (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Lemma step_zeros (cl lls: list Z) (toks: list cltok) (i r s: Z) :
  tok_expand [] toks = sublist 0 i lls -> toks_ok cl [] toks -> 0 <= i -> i + s <= Zlength lls ->
  (forall k, 0 <= k < s -> Znth (i + k) lls = Znth i lls) -> Znth i lls = 0 -> 3 <= r <= 138 -> r <= s ->
  Znth (if r <=? 10 then 17 else 18) cl <> 0 ->
  tok_expand [] (toks ++ [CZeros r]) = sublist 0 (i + r) lls /\ toks_ok cl [] (toks ++ [CZeros r]).
Proof.
  intros E T I L S Z R RS C. split.
  - rewrite tok_expand_app1, E. simpl. rewrite (sublist_split 0 i (i + r)) by lia. f_equal.
    symmetry. apply sublist_const; try lia. intros k K. rewrite S by lia. auto.
  - apply toks_ok_app1; auto. simpl. auto.
Qed.

Lemma step_rep (cl lls: list Z) (toks: list cltok) (i r s: Z) :
  tok_expand [] toks = sublist 0 i lls -> toks_ok cl [] toks -> 0 < i -> i + s <= Zlength lls ->
  (forall k, 0 <= k < s -> Znth (i + k) lls = Znth i lls) -> Znth (i - 1) lls = Znth i lls -> 3 <= r <= 6 -> r <= s ->
  Znth 16 cl <> 0 ->
  tok_expand [] (toks ++ [CRep r]) = sublist 0 (i + r) lls /\ toks_ok cl [] (toks ++ [CRep r]).
Proof.
  intros E T I L S P R RS C. split.
  - rewrite tok_expand_app1, E. simpl. rewrite last_sublist by lia. rewrite P.
    rewrite (sublist_split 0 i (i + r)) by lia. f_equal.
    symmetry. apply sublist_const; try lia. intros k K. rewrite S by lia. auto.
  - apply toks_ok_app1; auto. rewrite E. simpl. split; [| split; [lia | auto]].
    intros X. apply (f_equal (@Zlength Z)) in X. rewrite Zlength_sublist, Zlength_nil in X by lia. lia.
Qed.

Lemma step_len (cl lls: list Z) (toks: list cltok) (i: Z) :
  tok_expand [] toks = sublist 0 i lls -> toks_ok cl [] toks -> 0 <= i < Zlength lls ->
  0 <= Znth i lls <= 15 -> Znth (Znth i lls) cl <> 0 ->
  tok_expand [] (toks ++ [CLen (Znth i lls)]) = sublist 0 (i + 1) lls /\ toks_ok cl [] (toks ++ [CLen (Znth i lls)]).
Proof.
  intros E T I R C. split.
  - rewrite tok_expand_app1, E. simpl. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite sublist_len_1 by lia.
    reflexivity.
  - apply toks_ok_app1; auto. simpl. auto.
Qed.

Lemma bits_snoc (cl: list Z) (B2: list bool) (toks: list cltok) (t: cltok) (X Y: list bool) :
  X ++ Y = send_tok cl t ->
  ((B2 ++ flat_map (send_tok cl) toks) ++ X) ++ Y = B2 ++ flat_map (send_tok cl) (toks ++ [t]).
Proof. intros E. rewrite List.flat_map_app. cbn [flat_map]. rewrite app_nil_r, <- E, !app_assoc. reflexivity. Qed.

Lemma bits_snoc1 (cl: list Z) (B2: list bool) (toks: list cltok) (t: cltok) (X: list bool) :
  X = send_tok cl t ->
  (B2 ++ flat_map (send_tok cl) toks) ++ X = B2 ++ flat_map (send_tok cl) (toks ++ [t]).
Proof. intros E. rewrite List.flat_map_app. cbn [flat_map]. rewrite app_nil_r, <- E, !app_assoc. reflexivity. Qed.

Lemma send_tok_zeros (cl: list Z) (r: Z) :
  Znth (if r <=? 10 then 17 else 18) cl <= 16 -> 0 < Znth (if r <=? 10 then 17 else 18) cl ->
  bits_msb (canon_val cl (if r <=? 10 then 17 else 18)) (Znth (if r <=? 10 then 17 else 18) cl) ++
    (if r <=? 10 then bits_le (r - 3) 3 else bits_le (r - 11) 7) = send_tok cl (CZeros r).
Proof. intros A B. simpl. rewrite send_sym_canon by lia. destruct (r <=? 10); reflexivity. Qed.

Lemma send_tok_rep (cl: list Z) (r: Z) :
  0 < Znth 16 cl <= 16 -> bits_msb (canon_val cl 16) (Znth 16 cl) ++ bits_le (r - 3) 2 = send_tok cl (CRep r).
Proof. intros A. simpl. rewrite send_sym_canon by lia. reflexivity. Qed.

Lemma send_tok_len (cl: list Z) (l: Z) :
  0 < Znth l cl <= 16 -> bits_msb (canon_val cl l) (Znth l cl) = send_tok cl (CLen l).
Proof. intros A. simpl. rewrite send_sym_canon by lia. reflexivity. Qed.

Lemma room_tok (B B2 F X: list bool) (cap m i k: Z) :
  Zlength B / 8 + 15 + 2 * m <= cap -> cap <= Int.max_unsigned -> Zlength B2 = Zlength B + 71 ->
  Zlength F <= 14 * i -> 0 <= i < m -> 0 <= k -> Zlength X + k <= 14 -> bw_room ((B2 ++ F) ++ X) cap k.
Proof.
  intros C U L2 LF I K XK. apply (bw_room_of B _ cap m (71 + 14 * i + Zlength X)); try lia.
  rewrite !Zlength_app. pose proof (Zlength_nonneg F). pose proof (Zlength_nonneg X). lia.
Qed.

Lemma room_tok0 (B B2 F: list bool) (cap m i k: Z) :
  Zlength B / 8 + 15 + 2 * m <= cap -> cap <= Int.max_unsigned -> Zlength B2 = Zlength B + 71 ->
  Zlength F <= 14 * i -> 0 <= i < m -> 0 <= k <= 14 -> bw_room (B2 ++ F) cap k.
Proof.
  intros C U L2 LF I K. rewrite <- (app_nil_r (B2 ++ F)). apply (room_tok B B2 F [] cap m i k); auto; try lia; rewrite Zlength_nil; lia.
Qed.

Lemma post_ok (nlen ndist: Z) (cl lls: list Z) (toks: list cltok) :
  257 <= nlen <= 286 -> 1 <= ndist <= 30 -> Zlength cl = 19 -> Forall (fun l => 0 <= l <= 7) cl ->
  Zlength lls = nlen + ndist -> Forall (fun l => 0 <= l <= 15) lls -> Znth 256 lls <> 0 ->
  code_okb 1 (sublist 0 nlen lls) = true -> code_okb 2 (sublist nlen (nlen + ndist) lls) = true ->
  code_okb 0 cl = true -> tok_expand [] toks = lls -> toks_ok cl [] toks ->
  dyn_hdr_ok nlen ndist (map (fun k => Znth k cl) clorder) toks.
Proof.
  intros N D LC FC LL FL Z256 C1 C2 C0 E T. unfold dyn_hdr_ok, dyn_ll, dyn_dl, dyn_lens.
  rewrite cl_lens_order by auto. rewrite E.
  split; [rewrite Zlength_map; reflexivity |]. split.
  { apply Forall_map. rewrite Forall_forall. intros x _. simpl. apply Znth_bound7; auto. }
  split; [apply code_okb_cl; auto |]. split; [auto |]. split; [lia |]. split.
  - apply code_okb_ll; auto. apply Forall_sublist; auto. rewrite Znth_sublist by lia. auto.
  - apply code_okb_dl; auto. apply Forall_sublist; auto.
Qed.

Lemma hdr_bits_eq (B: list bool) (nlen ndist: Z) (cl: list Z) (toks: list cltok) :
  Zlength cl = 19 ->
  ((((B ++ bits_le (nlen - 257) 5) ++ bits_le (ndist - 1) 5) ++ bits_le 15 4) ++
     flat_map (fun c => bits_le c 3) (map (fun k => Znth k cl) clorder)) ++ flat_map (send_tok cl) toks =
  B ++ dyn_hdr_bits nlen ndist (map (fun k => Znth k cl) clorder) toks.
Proof.
  intros LC. unfold dyn_hdr_bits. rewrite cl_lens_order by auto. rewrite Zlength_map.
  change (Zlength clorder - 4) with 15. rewrite !app_assoc. reflexivity.
Qed.

Ltac bytes_hyps :=
  repeat match goal with H: Forall (fun b => 0 <= b <= Byte.max_unsigned) ?l, H2: context [@Znth Z ?d ?i ?l] |- _ =>
    assert_fails (assert (0 <= @Znth Z d i l <= 255) by assumption); pose proof (byte_Znth l i H) end.

Ltac bool_tac :=
  bytes_tac; bytes_hyps; unfold bool2val, Int.lt, Int.ltu, Int.eq in *;
  rewrite ?Int.signed_repr, ?Int.unsigned_repr in * by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) | |- context [zeq ?a ?b] => destruct (zeq a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
         | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
  simpl; try lia; try reflexivity.

Ltac cmp_tac :=
  entailer!; bytes_tac; simpl; unfold Int.lt, Int.eq;
  rewrite ?Int.signed_repr, ?Int.unsigned_repr by rep_lia;
  repeat match goal with |- context [zlt ?a ?b] => destruct (zlt a b) | |- context [zeq ?a ?b] => destruct (zeq a b)
         | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end;
  try lia; reflexivity.

Lemma dref_dyn_body_proof : dref_dyn_body.
Proof.
  unfold dref_dyn_body.
  start_function.
  assert_PROP (isptr llp) by entailer!.
  forward.
  set (m := nlen + ndist).
  assert (Hm: 258 <= m <= 316) by (subst m; lia).
  replace (Int.add (Int.repr nlen) (Int.repr ndist)) with (Int.repr m) by (subst m; normalize).
  rewrite (split2_data_at_Tarray_tuchar llsh 316 m) by (auto; lia).
  sep_apply (data_at_data_at_ llsh (tarray tuchar m)).
  assert_PROP (isptr v_cl /\ isptr v_choice /\ isptr v_runs /\ isptr v_clcodes) as Hptrs by entailer!.
  destruct Hptrs as (Pcl & Pch & Pru & Pcc).
  forward_call (llp, m, llsh).
  { rewrite if_false by (destruct llp; try contradiction; discriminate). cancel. }
  Intros lls. rewrite if_false by (destruct llp; try contradiction; discriminate).
  forward_call (v_cl, 19, Tsh).
  { rewrite if_false by (destruct v_cl; try contradiction; discriminate). cancel. }
  Intros cl. rewrite if_false by (destruct v_cl; try contradiction; discriminate).
  assert_PROP (field_compatible (tarray tuchar 316) [] v_choice /\ field_compatible (tarray tuchar 316) [] v_runs)
    as Fchru by entailer!. destruct Fchru as [Fch Fru].
  rewrite (split2_data_at__Tarray_tuchar Tsh 316 m v_choice) by (auto; lia).
  rewrite (split2_data_at__Tarray_tuchar Tsh 316 m v_runs) by (auto; lia).
  forward_call (v_choice, m, Tsh).
  { rewrite if_false by (destruct v_choice; try contradiction; discriminate). cancel. }
  Intros choice. rewrite if_false by (destruct v_choice; try contradiction; discriminate).
  forward_call (v_runs, m, Tsh).
  { rewrite if_false by (destruct v_runs; try contradiction; discriminate). cancel. }
  Intros runs. rewrite if_false by (destruct v_runs; try contradiction; discriminate).
  forward_for_simple_bound m
    (EX i: Z, PROP (Forall (fun x => x <= 15) (sublist 0 i lls))
     LOCAL (temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at_ Tsh (tarray tushort 19) v_clcodes;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       bw_at sh bsh B cap buf w;
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc)
         (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp);
       data_at llsh (tarray tushort 286) lcc lcp;
       data_at llsh (tarray tushort 30) dcc dcp)).
  { entailer!. }
  { forward.
    { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
    forward_call (Int.repr (if Znth i lls <=? 15 then 1 else 0)).
    { cmp_tac. }
    entailer!. apply Forall_sublist_snoc; auto; [lia |].
    destruct (Znth i lls <=? 15) eqn:E; [lia | contradiction]. }
  Intros. rename H15 into Hl15. rewrite sublist_same in Hl15 by lia.
  forward_for_simple_bound 19
    (EX i: Z, PROP (Forall (fun x => x <= 7) (sublist 0 i cl))
     LOCAL (temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at_ Tsh (tarray tushort 19) v_clcodes;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       bw_at sh bsh B cap buf w;
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc)
         (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp);
       data_at llsh (tarray tushort 286) lcc lcp;
       data_at llsh (tarray tushort 30) dcc dcp)).
  { entailer!. }
  { forward.
    { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
    forward_call (Int.repr (if Znth i cl <=? 7 then 1 else 0)).
    { cmp_tac. }
    entailer!. apply Forall_sublist_snoc; auto; [lia |].
    destruct (Znth i cl <=? 7) eqn:E; [lia | contradiction]. }
  Intros. rename H15 into Hc7. rewrite sublist_same in Hc7 by lia.
  assert (HL: Forall (fun l => 0 <= l <= 15) lls).
  { rewrite Forall_forall in *. intros x X. specialize (H8 x X). specialize (Hl15 x X). rep_lia. }
  assert (HC: Forall (fun l => 0 <= l <= 7) cl).
  { rewrite Forall_forall in *. intros x X. specialize (H10 x X). specialize (Hc7 x X). rep_lia. }
  clear Hl15 Hc7.
  forward.
  { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
  forward_call (Int.repr (if Znth 256 lls =? 0 then 0 else 1)).
  { cmp_tac. }
  assert (H256: Znth 256 lls <> 0) by (destruct (Znth 256 lls =? 0) eqn:E; [contradiction | lia]).
  clear H15.
  forward_call (llp, llsh, llp, 0, m, map (fun b => Vint (Int.repr b)) lls, nlen, sublist 0 nlen lls, 1).
  { replace m with (Zlength lls) by lia. replace (sublist 0 nlen lls) with (sublist 0 (0 + nlen) lls) by (f_equal; lia).
    apply cbuf_sub; auto; try lia. destruct llp; try contradiction; simpl; rewrite Ptrofs.add_zero; auto. }
  forward_if (temp HD._t'2 (Vint (Int.repr
    (if andb (code_okb 1 (sublist 0 nlen lls)) (code_okb 2 (sublist nlen m lls)) then 1 else 0)))).
  { destruct (code_okb 1 (sublist 0 nlen lls)) eqn:C1; [| contradiction].
    forward_call (offset_val nlen llp, llsh, llp, nlen, m, map (fun b => Vint (Int.repr b)) lls, ndist,
                  sublist nlen m lls, 2).
    { replace m with (Zlength lls) by lia. replace (sublist nlen (Zlength lls) lls) with (sublist nlen (nlen + ndist) lls) by (f_equal; lia).
      apply cbuf_sub; auto; try lia. }
    forward. entailer!. destruct (code_okb 2 _); reflexivity. }
  { forward. destruct (code_okb 1 (sublist 0 nlen lls)) eqn:C1; [discriminate |]. entailer!. }
  assert (HCB: Bytes.cbuf_ok false v_cl Tsh v_cl 0 19 19 (map (fun b => Vint (Int.repr b)) cl) cl /\
               Forall (fun x => 0 <= x <= 15) cl).
  { pose proof (cbuf_sub v_cl v_cl Tsh cl 0 19) as X. rewrite sublist_same in X by lia. rewrite H9 in X.
    apply X; auto; try lia. destruct v_cl; try contradiction; simpl; rewrite Ptrofs.add_zero; auto.
    eapply Forall_impl; [| exact HC]. simpl; intros; lia. }
  forward_if (temp HD._t'4 (Vint (Int.repr
    (if andb (andb (code_okb 1 (sublist 0 nlen lls)) (code_okb 2 (sublist nlen m lls))) (code_okb 0 cl)
     then 1 else 0)))).
  { destruct (andb (code_okb 1 (sublist 0 nlen lls)) (code_okb 2 (sublist nlen m lls))) eqn:C1; [| contradiction].
    forward_call (v_cl, Tsh, v_cl, 0, 19, map (fun b => Vint (Int.repr b)) cl, 19, cl, 0).
    forward. entailer!. destruct (code_okb 0 cl); reflexivity. }
  { forward. destruct (andb (code_okb 1 (sublist 0 nlen lls)) (code_okb 2 (sublist nlen m lls))) eqn:C1;
    [discriminate |]. entailer!. }
  forward_call (Int.repr (if andb (andb (code_okb 1 (sublist 0 nlen lls)) (code_okb 2 (sublist nlen m lls))) (code_okb 0 cl)
     then 1 else 0)).
  destruct (code_okb 1 (sublist 0 nlen lls)) eqn:C1; [| contradiction].
  destruct (code_okb 2 (sublist nlen m lls)) eqn:C2; [| contradiction].
  destruct (code_okb 0 cl) eqn:C0; [| contradiction].
  clear H15.
  forward_call (llp, llsh, llp, 0, m, map (fun b => Vint (Int.repr b)) lls, nlen, sublist 0 nlen lls,
                llsh, lcp, 286, lcc).
  { split. { replace m with (Zlength lls) by lia. replace (sublist 0 nlen lls) with (sublist 0 (0 + nlen) lls) by (f_equal; lia).
      apply cbuf_sub; auto; try lia. destruct llp; try contradiction; simpl; rewrite Ptrofs.add_zero; auto. }
    apply Forall_sublist; auto. }
  forward_call (offset_val nlen llp, llsh, llp, nlen, m, map (fun b => Vint (Int.repr b)) lls, ndist,
                sublist nlen m lls, llsh, dcp, 30, dcc).
  { split. { replace m with (Zlength lls) by lia. replace (sublist nlen (Zlength lls) lls) with (sublist nlen (nlen + ndist) lls) by (f_equal; lia).
      apply cbuf_sub; auto; try lia. }
    apply Forall_sublist; auto. }
  forward_call (v_cl, Tsh, v_cl, 0, 19, map (fun b => Vint (Int.repr b)) cl, 19, cl,
                Tsh, v_clcodes, 19, default_val (tarray tushort 19)).
  clear HCB. rewrite sublist_nil, app_nil_r.
  forward_call (sh, bsh, B, cap, buf, w, nlen - 257, 5).
  { room B 0. }
  forward_call (sh, bsh, B ++ bits_le (nlen - 257) 5, cap, buf, w, ndist - 1, 5).
  { room B 5. }
  forward_call (sh, bsh, (B ++ bits_le (nlen - 257) 5) ++ bits_le (ndist - 1) 5, cap, buf, w, 15, 4).
  { room B 10. }
  set (B1 := ((B ++ bits_le (nlen - 257) 5) ++ bits_le (ndist - 1) 5) ++ bits_le 15 4).
  assert (LB1: Zlength B1 = Zlength B + 14) by (subst B1; rewrite !Zlength_app, !Zlength_bits_le by lia; lia).
  set (clsent := map (fun k => Znth k cl) clorder).
  assert (Lcs: Zlength clsent = 19) by (subst clsent; rewrite Zlength_map; reflexivity).
  assert (FL3: forall l, Zlength (flat_map (fun c => bits_le c 3) l) = 3 * Zlength l).
  { induction l; cbn [flat_map]; [reflexivity |]. rewrite Zlength_app, Zlength_bits_le, IHl, Zlength_cons by lia; lia. }
  forward_for_simple_bound 19
    (EX i: Z, PROP ()
     LOCAL (temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (bw_at sh bsh (B1 ++ flat_map (fun c => bits_le c 3) (sublist 0 i clsent)) cap buf w;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at Tsh (tarray tushort 19) (zvals (canon_vals cl)) v_clcodes;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at llsh (tarray tushort 30) (zvals (canon_vals (sublist nlen m lls)) ++ sublist ndist 30 dcc) dcp;
       data_at llsh (tarray tushort 286) (zvals (canon_vals (sublist 0 nlen lls)) ++ sublist nlen 286 lcc) lcp;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc) (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp))).
  { entailer!. rewrite sublist_nil; simpl; rewrite app_nil_r. cancel. }
  { assert (ZO: forall d: Inhabitant val, @Znth val d i (zvals clorder) = Vint (Int.repr (Znth i clorder))).
    { intros d. unfold zvals. rewrite Znth_map by (change (Zlength clorder) with 19; lia). reflexivity. }
    pose proof (clorder_range i) as RO.
    forward.
    { rewrite ZO. entailer!. simpl. rep_lia. }
    rewrite ZO.
    forward.
    { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
    forward_call (sh, bsh, B1 ++ flat_map (fun c => bits_le c 3) (sublist 0 i clsent), cap, buf, w,
                  Znth (Znth i clorder) cl, 3).
    { pose proof (byte_Znth cl (Znth i clorder) H10). split; [| rep_lia].
      eapply (bw_room_of B _ _ _ (14 + 3 * i)); [eassumption | lia | lia | | lia].
      rewrite Zlength_app, LB1, FL3, Zlength_sublist by lia. lia. }
    entailer!. rewrite (sublist_split 0 i (i + 1)) by lia. rewrite (sublist_len_1 i) by lia.
    rewrite List.flat_map_app. cbn [flat_map]. subst clsent. rewrite Znth_map by (change (Zlength clorder) with 19; lia).
    rewrite app_nil_r, app_assoc. cancel. }
  rewrite sublist_same by lia.
  set (B2 := B1 ++ flat_map (fun c => bits_le c 3) clsent).
  assert (LB2: Zlength B2 = Zlength B + 71) by (subst B2; rewrite Zlength_app, FL3; lia).
  assert (Em: m = nlen + ndist) by reflexivity. clearbody m. rewrite <- Em in H1.
  forward.
  forward_while
    (EX i: Z, EX toks: list cltok,
     PROP (0 <= i <= m; tok_expand [] toks = sublist 0 i lls; toks_ok cl [] toks)
     LOCAL (temp HD._i__3 (Vint (Int.repr i)); temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (bw_at sh bsh (B2 ++ flat_map (send_tok cl) toks) cap buf w;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at Tsh (tarray tushort 19) (zvals (canon_vals cl)) v_clcodes;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at llsh (tarray tushort 30) (zvals (canon_vals (sublist nlen m lls)) ++ sublist ndist 30 dcc) dcp;
       data_at llsh (tarray tushort 286) (zvals (canon_vals (sublist 0 nlen lls)) ++ sublist nlen 286 lcc) lcp;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc) (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp))).
  { Exists 0 (@nil cltok). entailer!. rewrite app_nil_r. cancel. }
  { entailer!. }
  { assert (LF: Zlength (flat_map (send_tok cl) toks) <= 14 * i).
  { pose proof (send_toks_len cl toks HC) as X1. pose proof (toks_count cl [] toks H17) as X2.
    rewrite H16, Zlength_sublist, Zlength_nil in X2 by lia. lia. }
  assert (LR: 0 <= Znth i lls <= 15) by (pose proof HL as X; rewrite Forall_Znth in X; apply X; lia).
  forward.
  { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
  forward.
  forward_loop
    (EX s: Z,
     PROP (0 <= s <= 138; i + s <= m; forall k, 0 <= k < s -> Znth (i + k) lls = Znth i lls)
     LOCAL (temp HD._same (Vint (Int.repr s)); temp HD._r (Vint (Int.repr (Znth i runs))); temp HD._i__3 (Vint (Int.repr i)); temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (bw_at sh bsh (B2 ++ flat_map (send_tok cl) toks) cap buf w;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at Tsh (tarray tushort 19) (zvals (canon_vals cl)) v_clcodes;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at llsh (tarray tushort 30) (zvals (canon_vals (sublist nlen m lls)) ++ sublist ndist 30 dcc) dcp;
       data_at llsh (tarray tushort 286) (zvals (canon_vals (sublist 0 nlen lls)) ++ sublist nlen 286 lcc) lcp;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc) (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp)))
    break:
    (EX s: Z,
     PROP (0 <= s <= 138; i + s <= m; forall k, 0 <= k < s -> Znth (i + k) lls = Znth i lls)
     LOCAL (temp HD._same (Vint (Int.repr s)); temp HD._r (Vint (Int.repr (Znth i runs))); temp HD._i__3 (Vint (Int.repr i)); temp HD._m (Vint (Int.repr m));
       lvar HD._clcodes (tarray tushort 19) v_clcodes; lvar HD._runs (tarray tuchar 316) v_runs;
       lvar HD._choice (tarray tuchar 316) v_choice; lvar HD._cl (tarray tuchar 19) v_cl; gvars gv;
       temp HD._w w; temp HD._nlen (Vint (Int.repr nlen)); temp HD._ndist (Vint (Int.repr ndist));
       temp HD._ll llp; temp HD._lcodes lcp; temp HD._dcodes dcp)
     SEP (bw_at sh bsh (B2 ++ flat_map (send_tok cl) toks) cap buf w;
       data_at Tsh (tarray tuchar 19) (map (fun b : Z => Vint (Int.repr b)) cl) v_cl;
       data_at Tsh (tarray tushort 19) (zvals (canon_vals cl)) v_clcodes;
       data_at llsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) lls) llp;
       data_at llsh (tarray tushort 30) (zvals (canon_vals (sublist nlen m lls)) ++ sublist ndist 30 dcc) dcp;
       data_at llsh (tarray tushort 286) (zvals (canon_vals (sublist 0 nlen lls)) ++ sublist nlen 286 lcc) lcp;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs;
       data_at Tsh (tarray tuchar m) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice;
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_runs);
       data_at_ Tsh (Tarray tuchar (316 - m) noattr) (field_address0 (Tarray tuchar 316 noattr) (SUB m) v_choice);
       data_at Ers (tarray tuchar 19) (zvals clorder) (gv HD._cl_order);
       data_at llsh (Tarray tuchar (316 - m) noattr) (sublist m 316 llc) (field_address0 (Tarray tuchar 316 noattr) (SUB m) llp))).
  { Exists 0. entailer!. }
  { Intros s.
    forward_if (temp HD._t'6 (Vint (Int.repr (if andb (i + s <? m) (Znth (i + s) lls =? Znth i lls) then 1 else 0)))).
    { forward.
      { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
      forward.
      { entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia. }
      forward.
      entailer!. bool_tac. }
    { forward. entailer!. bool_tac. }
    forward_if (temp HD._t'7 (Vint (Int.repr (if andb (andb (i + s <? m) (Znth (i + s) lls =? Znth i lls)) (s <? 138) then 1 else 0)))).
    { destruct (andb (i + s <? m) (Znth (i + s) lls =? Znth i lls)); [| contradiction].
      forward. entailer!. bool_tac. }
    { destruct (andb (i + s <? m) (Znth (i + s) lls =? Znth i lls)); [discriminate |].
      forward. entailer!. }
    forward_if.
    { match goal with H: Int.repr (if ?c then _ else _) <> _ |- _ => destruct c eqn:E; [| contradiction] end.
      rewrite !andb_true_iff in E. destruct E as [[E1 E2] E3].
      apply Z.ltb_lt in E1. apply Z.eqb_eq in E2. apply Z.ltb_lt in E3.
      forward. Exists (s + 1). entailer!. intros k K. destruct (zeq k s); [subst k; auto | apply H20; lia]. }
    { forward. Exists s. entailer!. } }
  Intros s.
  forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
  forward_if (temp HD._t'19 (Vint (Int.repr (if andb (192 <=? Znth i choice) (Znth i lls =? 0) then 1 else 0)))).
  { forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { forward. entailer!. bool_tac. }
  forward_if (temp HD._t'20 (Vint (Int.repr (if andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs) then 1 else 0)))).
  { destruct (andb (192 <=? Znth i choice) (Znth i lls =? 0)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (192 <=? Znth i choice) (Znth i lls =? 0)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'21 (Vint (Int.repr (if andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138) then 1 else 0)))).
  { destruct (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'22 (Vint (Int.repr (if andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) (Znth i runs <=? s) then 1 else 0)))).
  { destruct (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'23 (Vint (Int.repr (if andb (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) (Znth i runs <=? s)) (negb (Znth 18 cl =? 0)) then 1 else 0)))).
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) (Znth i runs <=? s)) eqn:?; [| contradiction]. bfacts. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) (Znth i runs <=? s)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if.
  { destruct (andb (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (11 <=? Znth i runs)) (Znth i runs <=? 138)) (Znth i runs <=? s)) (negb (Znth 18 cl =? 0))) eqn:?; [| contradiction]. bfacts.
    forward. { rewrite Znth_zvals_canon by lia. entailer!. pose proof (canon_val_range cl (18)). try (rewrite Int.unsigned_repr by rep_lia); rep_lia. } rewrite Znth_zvals_canon by lia. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward_call (sh, bsh, B2 ++ flat_map (send_tok cl) toks, cap, buf, w, canon_val cl (18), Znth (18) cl).
    { pose proof (Znth_bound7 cl (18) HC). pose proof (canon_val_range cl (18)).
      assert (RM: bw_room (B2 ++ flat_map (send_tok cl) toks) cap (Znth (18) cl))
        by (apply (room_tok0 B B2 _ cap m i); [exact H1 | auto | auto | auto | lia | lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward_call (sh, bsh, (B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (18)) (Znth (18) cl), cap, buf, w, Znth i runs - 11, 7).
    { pose proof (Znth_bound7 cl (18) HC).
      assert (RM: bw_room ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (18)) (Znth (18) cl)) cap 7)
        by (apply (room_tok B B2 _ _ cap m i); [exact H1 | auto | auto | auto | lia | lia | rewrite Zlength_bits_msb by lia; lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward.
    assert (ST: tok_expand [] (toks ++ [CZeros (Znth i runs)]) = sublist 0 (i + Znth i runs) lls /\ toks_ok cl [] (toks ++ [CZeros (Znth i runs)]))
      by (apply (step_zeros cl lls toks i (Znth i runs) s); auto; try lia; rewrite (proj2 (Z.leb_gt (Znth i runs) 10)) by lia; auto).
    destruct ST as [ST1 ST2].
    assert (BE: ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (18)) (Znth (18) cl)) ++ bits_le (Znth i runs - 11) 7
                = B2 ++ flat_map (send_tok cl) (toks ++ [CZeros (Znth i runs)]))
      by (apply bits_snoc; pose proof (Znth_bound7 cl 18 HC); pose proof (send_tok_zeros cl (Znth i runs)) as Z1; rewrite (proj2 (Z.leb_gt (Znth i runs) 10)) in Z1 by lia; apply Z1; lia).
    rewrite BE. Exists (i + Znth i runs, toks ++ [CZeros (Znth i runs)]). entailer!; lia. }
  { forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
  forward_if (temp HD._t'14 (Vint (Int.repr (if andb (192 <=? Znth i choice) (Znth i lls =? 0) then 1 else 0)))).
  { forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { forward. entailer!. bool_tac. }
  forward_if (temp HD._t'15 (Vint (Int.repr (if andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs) then 1 else 0)))).
  { destruct (andb (192 <=? Znth i choice) (Znth i lls =? 0)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (192 <=? Znth i choice) (Znth i lls =? 0)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'16 (Vint (Int.repr (if andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10) then 1 else 0)))).
  { destruct (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'17 (Vint (Int.repr (if andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) (Znth i runs <=? s) then 1 else 0)))).
  { destruct (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'18 (Vint (Int.repr (if andb (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) (Znth i runs <=? s)) (negb (Znth 17 cl =? 0)) then 1 else 0)))).
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) (Znth i runs <=? s)) eqn:?; [| contradiction]. bfacts. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) (Znth i runs <=? s)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if.
  { destruct (andb (andb (andb (andb (andb (192 <=? Znth i choice) (Znth i lls =? 0)) (3 <=? Znth i runs)) (Znth i runs <=? 10)) (Znth i runs <=? s)) (negb (Znth 17 cl =? 0))) eqn:?; [| contradiction]. bfacts.
    forward. { rewrite Znth_zvals_canon by lia. entailer!. pose proof (canon_val_range cl (17)). try (rewrite Int.unsigned_repr by rep_lia); rep_lia. } rewrite Znth_zvals_canon by lia. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward_call (sh, bsh, B2 ++ flat_map (send_tok cl) toks, cap, buf, w, canon_val cl (17), Znth (17) cl).
    { pose proof (Znth_bound7 cl (17) HC). pose proof (canon_val_range cl (17)).
      assert (RM: bw_room (B2 ++ flat_map (send_tok cl) toks) cap (Znth (17) cl))
        by (apply (room_tok0 B B2 _ cap m i); [exact H1 | auto | auto | auto | lia | lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward_call (sh, bsh, (B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (17)) (Znth (17) cl), cap, buf, w, Znth i runs - 3, 3).
    { pose proof (Znth_bound7 cl (17) HC).
      assert (RM: bw_room ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (17)) (Znth (17) cl)) cap 3)
        by (apply (room_tok B B2 _ _ cap m i); [exact H1 | auto | auto | auto | lia | lia | rewrite Zlength_bits_msb by lia; lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward.
    assert (ST: tok_expand [] (toks ++ [CZeros (Znth i runs)]) = sublist 0 (i + Znth i runs) lls /\ toks_ok cl [] (toks ++ [CZeros (Znth i runs)]))
      by (apply (step_zeros cl lls toks i (Znth i runs) s); auto; try lia; rewrite (proj2 (Z.leb_le (Znth i runs) 10)) by lia; auto).
    destruct ST as [ST1 ST2].
    assert (BE: ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (17)) (Znth (17) cl)) ++ bits_le (Znth i runs - 3) 3
                = B2 ++ flat_map (send_tok cl) (toks ++ [CZeros (Znth i runs)]))
      by (apply bits_snoc; pose proof (Znth_bound7 cl 17 HC); pose proof (send_tok_zeros cl (Znth i runs)) as Z1; rewrite (proj2 (Z.leb_le (Znth i runs) 10)) in Z1 by lia; apply Z1; lia).
    rewrite BE. Exists (i + Znth i runs, toks ++ [CZeros (Znth i runs)]). entailer!; lia. }
  { forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
  forward_if (temp HD._t'8 (Vint (Int.repr (if andb (192 <=? Znth i choice) (0 <? i) then 1 else 0)))).
  { forward. entailer!. bool_tac. }
  { forward. entailer!. bool_tac. }
  forward_if (temp HD._t'9 (Vint (Int.repr (if andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls) then 1 else 0)))).
  { destruct (andb (192 <=? Znth i choice) (0 <? i)) eqn:?; [| contradiction]. bfacts. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { destruct (andb (192 <=? Znth i choice) (0 <? i)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'10 (Vint (Int.repr (if andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs) then 1 else 0)))).
  { destruct (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'11 (Vint (Int.repr (if andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6) then 1 else 0)))).
  { destruct (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'12 (Vint (Int.repr (if andb (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) (Znth i runs <=? s) then 1 else 0)))).
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) eqn:?; [| contradiction]. bfacts. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if (temp HD._t'13 (Vint (Int.repr (if andb (andb (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) (Znth i runs <=? s)) (negb (Znth 16 cl =? 0)) then 1 else 0)))).
  { destruct (andb (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) (Znth i runs <=? s)) eqn:?; [| contradiction]. bfacts. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. forward. entailer!. bool_tac. }
  { destruct (andb (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) (Znth i runs <=? s)) eqn:?; [discriminate |]. forward. entailer!. }
  forward_if.
  { destruct (andb (andb (andb (andb (andb (andb (192 <=? Znth i choice) (0 <? i)) (Znth (i - 1) lls =? Znth i lls)) (3 <=? Znth i runs)) (Znth i runs <=? 6)) (Znth i runs <=? s)) (negb (Znth 16 cl =? 0))) eqn:?; [| contradiction]. bfacts.
    forward. { rewrite Znth_zvals_canon by lia. entailer!. pose proof (canon_val_range cl (16)). try (rewrite Int.unsigned_repr by rep_lia); rep_lia. } rewrite Znth_zvals_canon by lia. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward_call (sh, bsh, B2 ++ flat_map (send_tok cl) toks, cap, buf, w, canon_val cl (16), Znth (16) cl).
    { pose proof (Znth_bound7 cl (16) HC). pose proof (canon_val_range cl (16)).
      assert (RM: bw_room (B2 ++ flat_map (send_tok cl) toks) cap (Znth (16) cl))
        by (apply (room_tok0 B B2 _ cap m i); [exact H1 | auto | auto | auto | lia | lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward_call (sh, bsh, (B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (16)) (Znth (16) cl), cap, buf, w, Znth i runs - 3, 2).
    { pose proof (Znth_bound7 cl (16) HC).
      assert (RM: bw_room ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (16)) (Znth (16) cl)) cap 2)
        by (apply (room_tok B B2 _ _ cap m i); [exact H1 | auto | auto | auto | lia | lia | rewrite Zlength_bits_msb by lia; lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward.
    assert (ST: tok_expand [] (toks ++ [CRep (Znth i runs)]) = sublist 0 (i + Znth i runs) lls /\ toks_ok cl [] (toks ++ [CRep (Znth i runs)]))
      by (apply (step_rep cl lls toks i (Znth i runs) s); auto; lia).
    destruct ST as [ST1 ST2].
    assert (BE: ((B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (16)) (Znth (16) cl)) ++ bits_le (Znth i runs - 3) 2
                = B2 ++ flat_map (send_tok cl) (toks ++ [CRep (Znth i runs)]))
      by (apply bits_snoc; apply send_tok_rep; pose proof (Znth_bound7 cl 16 HC); lia).
    rewrite BE. Exists (i + Znth i runs, toks ++ [CRep (Znth i runs)]). entailer!; lia. }
  { forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward_call (Int.repr (if Znth (Znth i lls) cl =? 0 then 0 else 1)).
    { cmp_tac. }
    assert (CN: Znth (Znth i lls) cl <> 0) by (destruct (Znth (Znth i lls) cl =? 0) eqn:?; [contradiction | lia]).
    forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward. { rewrite Znth_zvals_canon by lia. entailer!. pose proof (canon_val_range cl (Znth i lls)). try (rewrite Int.unsigned_repr by rep_lia); rep_lia. } rewrite Znth_zvals_canon by lia. forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward. all: try solve [entailer!; bytes_tac; try (rewrite Int.unsigned_repr by rep_lia); rep_lia]. 
    forward_call (sh, bsh, B2 ++ flat_map (send_tok cl) toks, cap, buf, w, canon_val cl (Znth i lls), Znth (Znth i lls) cl).
    { pose proof (Znth_bound7 cl (Znth i lls) HC). pose proof (canon_val_range cl (Znth i lls)).
      assert (RM: bw_room (B2 ++ flat_map (send_tok cl) toks) cap (Znth (Znth i lls) cl))
        by (apply (room_tok0 B B2 _ cap m i); [exact H1 | auto | auto | auto | lia | lia]).
      unfold bw_room in *. repeat split; try rep_lia. }
    forward.
    assert (ST: tok_expand [] (toks ++ [CLen (Znth i lls)]) = sublist 0 (i + 1) lls /\ toks_ok cl [] (toks ++ [CLen (Znth i lls)]))
      by (apply (step_len cl lls toks i); auto; lia).
    destruct ST as [ST1 ST2].
    assert (BE: (B2 ++ flat_map (send_tok cl) toks) ++ bits_msb (canon_val cl (Znth i lls)) (Znth (Znth i lls) cl)
                = B2 ++ flat_map (send_tok cl) (toks ++ [CLen (Znth i lls)]))
      by (apply bits_snoc1; apply send_tok_len; pose proof (Znth_bound7 cl (Znth i lls) HC); lia).
    rewrite BE. Exists (i + 1, toks ++ [CLen (Znth i lls)]). entailer!; lia. } } }

  }
  assert (i = m) by lia. subst i. rewrite sublist_same in H16 by lia.
  assert (POK: dyn_hdr_ok nlen ndist clsent toks).
  { unfold clsent. apply (post_ok nlen ndist cl lls); auto; try lia. rewrite <- Em; auto. }
  assert (BB: B2 ++ flat_map (send_tok cl) toks = B ++ dyn_hdr_bits nlen ndist clsent toks)
    by (unfold B2, B1, clsent; apply hdr_bits_eq; auto).
  assert (DL: dyn_lens toks = lls) by exact H16.
  assert (DLL: dyn_ll nlen toks = sublist 0 nlen lls) by (unfold dyn_ll; rewrite DL; auto).
  assert (DDL: dyn_dl nlen ndist toks = sublist nlen m lls) by (unfold dyn_dl; rewrite DL, Em; auto).
  forward. Exists clsent toks. rewrite BB, DL, DLL, DDL, <- Em. entailer!.
  set (L := tok_expand [] toks) in *.
  rewrite (split2_data_at__Tarray_tuchar Tsh 316 (Zlength L) v_runs) by (auto; lia).
  rewrite (split2_data_at__Tarray_tuchar Tsh 316 (Zlength L) v_choice) by (auto; lia).
  rewrite (split2_data_at_Tarray_tuchar llsh 316 (Zlength L) (zvals L ++ sublist (Zlength L) 316 llc))
    by (unfold zvals; rewrite ?Zlength_app, ?Zlength_map, ?Zlength_sublist by lia; lia).
  replace (sublist 0 (Zlength L) (zvals L ++ sublist (Zlength L) 316 llc)) with (zvals L) by (unfold zvals; list_solve).
  replace (sublist (Zlength L) 316 (zvals L ++ sublist (Zlength L) 316 llc)) with (sublist (Zlength L) 316 llc)
    by (unfold zvals; list_solve).
  unfold zvals.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (Zlength L)) (map (fun b : Z => Vint (Int.repr b)) runs) v_runs).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (Zlength L)) (map (fun b : Z => Vint (Int.repr b)) choice) v_choice).
  cancel.
Qed.
