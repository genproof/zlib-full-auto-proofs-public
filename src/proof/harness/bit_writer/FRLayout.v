(* The fixed-block run theory (FRDefs.v): the layout of the input (fr_ok) and the lengths of the fixed codes. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.bit_writer.FRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* lengths of the pieces of the bit string *)
Lemma frl_bits_le_len v n : 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros H. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma frl_send_sym_len lens s : 0 <= Znth s lens -> Zlength (send_sym lens s) = Znth s lens.
Proof. intros H. unfold send_sym, bits_msb. rewrite Zlength_rev. apply frl_bits_le_len; exact H. Qed.

(* the fixed code lengths and the length/distance tables *)
Lemma frl_ll_len : Zlength fixed_ll = 288.
Proof. reflexivity. Qed.

Lemma frl_dl_len : Zlength fixed_dl = 32.
Proof. reflexivity. Qed.

Lemma frl_ll_range sy : 0 <= sy < 288 -> 7 <= Znth sy fixed_ll <= 9.
Proof.
  intros H. assert (HF: Forall (fun x => 7 <= x <= 9) fixed_ll).
  { apply Forall_forall. intros x Hx. unfold fixed_ll in Hx. rewrite !in_app_iff in Hx.
    destruct Hx as [Hx|[Hx|[Hx|Hx]]]; apply repeat_spec in Hx; lia. }
  apply (sublist.Forall_Znth (fun x => 7 <= x <= 9) fixed_ll sy); [rewrite frl_ll_len; lia | exact HF].
Qed.

Lemma frl_dl_val d : 0 <= d < 32 -> Znth d fixed_dl = 5.
Proof.
  intros H. assert (HF: Forall (fun x => x = 5) fixed_dl).
  { unfold fixed_dl. apply Forall_forall. intros x Hx; apply repeat_spec in Hx; lia. }
  apply (sublist.Forall_Znth (fun x => x = 5) fixed_dl d); [rewrite frl_dl_len; lia | exact HF].
Qed.

Lemma frl_len_tables i : 0 <= i <= 28 -> 0 <= Znth i len_extra <= 5 /\ 3 <= Znth i len_base <= 258.
Proof.
  intros H. split.
  - apply (sublist.Forall_Znth (fun x => 0 <= x <= 5)); [replace (Zlength len_extra) with 29 by reflexivity; lia|].
    unfold len_extra; repeat constructor; lia.
  - apply (sublist.Forall_Znth (fun x => 3 <= x <= 258)); [replace (Zlength len_base) with 29 by reflexivity; lia|].
    unfold len_base; repeat constructor; lia.
Qed.

Lemma frl_dist_tables d : 0 <= d <= 29 -> 0 <= Znth d dist_extra <= 13 /\ 1 <= Znth d dist_base <= 24577.
Proof.
  intros H. split.
  - apply (sublist.Forall_Znth (fun x => 0 <= x <= 13)); [replace (Zlength dist_extra) with 30 by reflexivity; lia|].
    unfold dist_extra; repeat constructor; lia.
  - apply (sublist.Forall_Znth (fun x => 1 <= x <= 24577)); [replace (Zlength dist_base) with 30 by reflexivity; lia|].
    unfold dist_base; repeat constructor; lia.
Qed.

(* a piece in the middle of a known sublist *)
Lemma frl_sub_mid (l: list bool) a b X Y R :
  0 <= a <= b -> b <= Zlength l -> sublist a b l = X ++ Y ++ R ->
  sublist (a + Zlength X) (a + Zlength X + Zlength Y) l = Y.
Proof.
  intros Hab Hb Hs.
  assert (HL: Zlength (X ++ Y ++ R) = b - a) by (rewrite <- Hs, Zlength_sublist; lia).
  rewrite !Zlength_app in HL.
  pose proof (Zlength_nonneg X). pose proof (Zlength_nonneg Y). pose proof (Zlength_nonneg R).
  replace (sublist (a + Zlength X) (a + Zlength X + Zlength Y) l)
    with (sublist (Zlength X) (Zlength X + Zlength Y) (sublist a b l))
    by (rewrite sublist_sublist by lia; f_equal; lia).
  rewrite Hs, sublist_app2 by lia.
  replace (Zlength X - Zlength X) with 0 by lia.
  replace (Zlength X + Zlength Y - Zlength X) with (Zlength Y) by lia.
  rewrite sublist_app1 by lia. apply sublist_same; lia.
Qed.

(* the bits of literals *)
Definition frl_P (L: list Z) (j: Z) : list bool := concat (map (send_sym fixed_ll) (sublist 0 j L)).

Lemma frl_P_split L j k : 0 <= j <= k -> k <= Zlength L ->
  frl_P L k = frl_P L j ++ concat (map (send_sym fixed_ll) (sublist j k L)).
Proof.
  intros. unfold frl_P. rewrite (sublist_split 0 j k) by lia. rewrite map_app, concat_app. reflexivity.
Qed.

Lemma frl_P_succ L j : 0 <= j < Zlength L ->
  frl_P L (j + 1) = frl_P L j ++ send_sym fixed_ll (Znth j L).
Proof.
  intros. rewrite (frl_P_split L j (j + 1)) by lia. rewrite sublist_len_1 by lia.
  cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma frl_lpos_eq C j : fr_lpos C j = 3 + Zlength (frl_P (fr_lits C) j).
Proof. unfold fr_lpos, frl_P. rewrite sublist_firstn. reflexivity. Qed.

Lemma frl_lit_eq C j : fr_lit C j = sublist 0 j (fr_lits C).
Proof. unfold fr_lit. rewrite sublist_firstn. reflexivity. Qed.

Lemma frl_bytes_bits_len l : Zlength (bytes_bits l) = 8 * Zlength l.
Proof.
  induction l as [|a l IH]; [reflexivity|].
  unfold bytes_bits in *. cbn [flat_map]. rewrite Zlength_app, frl_bits_le_len, IH, Zlength_cons by lia. lia.
Qed.

Lemma frl_P_full L : frl_P L (Zlength L) = concat (map (send_sym fixed_ll) L).
Proof. unfold frl_P. rewrite sublist_same by lia. reflexivity. Qed.

(* a literal's code has 7 to 9 bits *)
Lemma frl_lit_code_len l : 0 <= l < 256 -> Zlength (send_sym fixed_ll l) = Znth l fixed_ll.
Proof. intros. apply frl_send_sym_len. pose proof (frl_ll_range l). lia. Qed.

Lemma frl_P_mono L j k : 0 <= j <= k -> k <= Zlength L -> Zlength (frl_P L j) <= Zlength (frl_P L k).
Proof.
  intros. rewrite (frl_P_split L j k) by lia. rewrite Zlength_app. pose proof (Zlength_nonneg (concat (map (send_sym fixed_ll) (sublist j k L)))). lia.
Qed.

Lemma fr_layout : fr_layout_stmt.
Proof.
  intros C HC. destruct HC as (Hbytes & Hlits & Hn20 & Htail & Hend & H12 & Hbody).
  pose proof (frl_bytes_bits_len (fr_src C)) as Hsb.
  set (sb := bytes_bits (fr_src C)) in *.
  set (L := fr_lits C) in *.
  assert (Hn: fr_n C = Zlength L) by reflexivity.
  assert (HfeP: fr_end C = 3 + Zlength (frl_P L (Zlength L)) + Zlength (tail_bits (fr_tail C))).
  { unfold fr_end, fr_body. rewrite Zlength_app, frl_P_full. fold L. lia. }
  assert (HB: sublist 3 (fr_end C) sb = frl_P L (Zlength L) ++ tail_bits (fr_tail C)).
  { rewrite Hbody. unfold fr_body. rewrite frl_P_full. reflexivity. }
  assert (Hfe3: 3 <= fr_end C).
  { rewrite HfeP. pose proof (Zlength_nonneg (frl_P L (Zlength L))). pose proof (Zlength_nonneg (tail_bits (fr_tail C))). lia. }
  assert (Hlpos: forall j, fr_lpos C j = 3 + Zlength (frl_P L j)) by (intros; apply frl_lpos_eq).
  assert (Htpos: fr_tpos C = 3 + Zlength (frl_P L (Zlength L))) by (unfold fr_tpos; rewrite Hn; apply Hlpos).
  (* the tail is non-empty and lies at tpos *)
  assert (Htl: 0 < Zlength (tail_bits (fr_tail C))).
  { destruct (fr_tail C) as [w|w|lc lx dc dx]; cbn [tail_bits tail_ok] in Htail |- *.
    - rewrite frl_send_sym_len by (pose proof (frl_ll_range (286 + w)); lia). pose proof (frl_ll_range (286 + w)); lia.
    - rewrite Zlength_app, frl_send_sym_len by (pose proof (frl_ll_range 257); lia).
      pose proof (frl_ll_range 257). pose proof (Zlength_nonneg (send_sym fixed_dl (30 + w))). lia.
    - rewrite Zlength_app, frl_send_sym_len by (pose proof (frl_ll_range lc); lia).
      pose proof (frl_ll_range lc).
      pose proof (Zlength_nonneg (bits_le lx (Znth (lc - 257) len_extra) ++ send_sym fixed_dl dc ++
                                  bits_le dx (Znth dc dist_extra))). lia. }
  assert (Htail_at: sublist (fr_tpos C) (fr_end C) sb = tail_bits (fr_tail C)).
  { assert (Hend8: fr_end C <= Zlength sb) by lia.
    pose proof (frl_sub_mid sb 3 (fr_end C) (frl_P L (Zlength L)) (tail_bits (fr_tail C)) []) as Hm.
    rewrite app_nil_r in Hm. specialize (Hm ltac:(lia) Hend8 HB).
    etransitivity; [|exact Hm]. f_equal; lia. }
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - (* the literals *)
    intros j Hj. rewrite Hn in Hj.
    assert (HLj: 0 <= Znth j L < 256) by (apply (sublist.Forall_Znth (fun l => 0 <= l < 256)); [lia | exact Hlits]).
    assert (HPs := frl_P_succ L j ltac:(lia)).
    assert (Hlen := frl_lit_code_len _ HLj).
    split; [exact HLj|]. split; [|split].
    + rewrite !Hlpos, HPs, Zlength_app, Hlen. lia.
    + rewrite !Hlpos, HPs, Zlength_app.
      rewrite (frl_P_split L (j + 1) (Zlength L)), HPs in HB by lia.
      rewrite <- !app_assoc in HB.
      assert (Hend8: fr_end C <= Zlength sb) by lia.
      pose proof (frl_sub_mid sb 3 (fr_end C) _ _ _ ltac:(lia) Hend8 HB) as Hm.
      etransitivity; [|exact Hm]. f_equal; lia.
    + rewrite !frl_lit_eq. fold L. rewrite (sublist_split 0 j (j + 1)) by lia. rewrite sublist_len_1 by lia. reflexivity.
  - rewrite Hlpos. reflexivity.
  - intros j Hj. rewrite Hn in Hj. rewrite Htpos, Hlpos.
    pose proof (frl_P_mono L 0 j ltac:(lia) ltac:(lia)). pose proof (frl_P_mono L j (Zlength L) ltac:(lia) ltac:(lia)).
    pose proof (Zlength_nonneg (frl_P L 0)). lia.
  - intros j Hj. rewrite Hn in Hj. rewrite frl_lit_eq. fold L. rewrite Zlength_sublist by lia. lia.
  - rewrite frl_lit_eq, Hn. fold L. apply sublist_same; reflexivity.
  - rewrite Htpos, HfeP. lia.
  - (* the tail *)
    assert (Hend8: fr_end C <= Zlength sb) by lia.
    assert (Htp: 3 <= fr_tpos C) by (rewrite Htpos; pose proof (Zlength_nonneg (frl_P L (Zlength L))); lia).
    assert (HT: forall X Y R, tail_bits (fr_tail C) = X ++ Y ++ R ->
              sublist (fr_tpos C + Zlength X) (fr_tpos C + Zlength X + Zlength Y) sb = Y).
    { intros X Y R HXYZ.
      rewrite HXYZ, app_assoc in HB.
      pose proof (frl_sub_mid sb 3 (fr_end C) (frl_P L (Zlength L) ++ X) Y R ltac:(lia) Hend8 HB) as Hm.
      rewrite Zlength_app in Hm. etransitivity; [|exact Hm]. f_equal; rewrite Htpos; lia. }
    assert (HTe: fr_end C = fr_tpos C + Zlength (tail_bits (fr_tail C))) by (rewrite Htpos, HfeP; lia).
    clear HfeP HB Hbody.
    destruct (fr_tail C) as [w|w|lc lx dc dx] eqn:Et; cbn [tail_bits tail_ok] in Htail, HTe, HT |- *.
    + pose proof (frl_ll_range (286 + w) ltac:(lia)). rewrite frl_send_sym_len in HTe by lia.
      split; [exact HTe|exact Htail_at].
    + pose proof (frl_ll_range 257 ltac:(lia)). pose proof (frl_dl_val (30 + w) ltac:(lia)).
      rewrite Zlength_app, !frl_send_sym_len in HTe by lia.
      split; [lia|]. split.
      * specialize (HT [] (send_sym fixed_ll 257) (send_sym fixed_dl (30 + w)) eq_refl).
        rewrite frl_send_sym_len in HT by lia. rewrite Zlength_nil in HT. etransitivity; [|exact HT]. f_equal; lia.
      * specialize (HT (send_sym fixed_ll 257) (send_sym fixed_dl (30 + w)) [] ltac:(rewrite app_nil_r; reflexivity)).
        rewrite !frl_send_sym_len in HT by lia. etransitivity; [|exact HT]. f_equal; lia.
    + destruct Htail as (Hlc & Hlx & Hdc & Hdx & Hfar).
      pose proof (frl_ll_range lc ltac:(lia)). pose proof (frl_dl_val dc ltac:(lia)).
      pose proof (frl_len_tables (lc - 257) ltac:(lia)). pose proof (frl_dist_tables dc ltac:(lia)).
      rewrite !Zlength_app, !frl_send_sym_len, !frl_bits_le_len in HTe by lia.
      set (a := send_sym fixed_ll lc) in *. set (b := bits_le lx (Znth (lc - 257) len_extra)) in *.
      set (c := send_sym fixed_dl dc) in *. set (d := bits_le dx (Znth dc dist_extra)) in *.
      assert (Ha: Zlength a = Znth lc fixed_ll) by (apply frl_send_sym_len; lia).
      assert (Hb: Zlength b = Znth (lc - 257) len_extra) by (apply frl_bits_le_len; lia).
      assert (Hc: Zlength c = Znth dc fixed_dl) by (apply frl_send_sym_len; lia).
      assert (Hd: Zlength d = Znth dc dist_extra) by (apply frl_bits_le_len; lia).
      split; [lia|]. split; [|split; [|split]].
      * specialize (HT [] a (b ++ c ++ d) eq_refl). rewrite Zlength_nil in HT. etransitivity; [|exact HT]. f_equal; lia.
      * specialize (HT a b (c ++ d) eq_refl). etransitivity; [|exact HT]. f_equal; lia.
      * specialize (HT (a ++ b) c d ltac:(rewrite <- !app_assoc; reflexivity)).
        rewrite Zlength_app in HT. etransitivity; [|exact HT]. f_equal; lia.
      * specialize (HT (a ++ b ++ c) d [] ltac:(rewrite app_nil_r, <- !app_assoc; reflexivity)).
        rewrite !Zlength_app in HT. etransitivity; [|exact HT]. f_equal; lia.
  - split; [exact frl_ll_len|]. split; [exact frl_dl_len|]. split; [exact frl_ll_range|].
    split; [intros; apply frl_dl_val; lia|]. split; [exact frl_len_tables|exact frl_dist_tables].
Qed.
