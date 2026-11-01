(* RT-D part DEFLATE, stage lemma kf_hdr_ok: the header bytes deflate() writes (RTDLTDefs.hdr_bytes)
   are Format's headers of RTDK.khdr. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDK.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The zlib header word, as a function of the parameters it reads (copy of RTDDfXHdrSt.hs_zh). *)
Definition hb_zh (wb st lv : Z) (nd : bool) : Z :=
  let header := u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (wb - 8)) 4))) 8) in
  let level_flags :=
    if (st >=? Z_HUFFMAN_ONLY) || (lv <? 2) then 0
    else if lv <? 6 then 1
    else if lv =? 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if nd then header else Z.lor header PRESET_DICT in
  u32 (header + u32 (31 - header mod 31)).

Lemma hb_zh_eq : forall s, zlib_header s = hb_zh (d_w_bits s) (d_strategy s) (d_level s) (d_strstart s =? 0).
Proof. intros s. reflexivity. Qed.

Definition hb_zh_ok (wb st lv : Z) (nd : bool) : bool :=
  let h := hb_zh wb st lv nd in
  let b0 := u8 (Z.shiftr h 8) in let b1 := u8 (Z.land h 255) in
  (b0 =? zcmf wb) && (0 <=? b1) && (b1 <? 256) && ((zcmf wb * 256 + b1) mod 31 =? 0) &&
  Bool.eqb (Z.testbit b1 5) (negb nd).

Definition hb_zr (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).

Lemma hb_zr_in : forall lo n x, lo <= x < lo + n -> In x (hb_zr lo n).
Proof.
  intros lo n x H. unfold hb_zr. apply in_map_iff. exists (Z.to_nat (x - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma hb_zh_all : forallb (fun wb => forallb (fun st => forallb (fun lv =>
    hb_zh_ok wb st lv true && hb_zh_ok wb st lv false) (hb_zr 0 10)) (hb_zr 0 5)) (hb_zr 9 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hb_zh_good : forall wb st lv nd, 9 <= wb <= 15 -> 0 <= st <= 4 -> 0 <= lv <= 9 ->
  hb_zh_ok wb st lv nd = true.
Proof.
  intros wb st lv nd Hw Hs Hl. pose proof hb_zh_all as A.
  rewrite forallb_forall in A. specialize (A wb (hb_zr_in 9 7 wb ltac:(lia))).
  rewrite forallb_forall in A. specialize (A st (hb_zr_in 0 5 st ltac:(lia))).
  rewrite forallb_forall in A. specialize (A lv (hb_zr_in 0 10 lv ltac:(lia))).
  apply andb_prop in A. destruct nd; apply A.
Qed.

Lemma hb_be32 : forall a, 0 <= a < 2 ^ 32 ->
  msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535)) = F.be_bytes a 4.
Proof.
  intros a Ha. unfold msb2, F.be_bytes, F.le_bytes, u32, u8. simpl.
  repeat rewrite Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8). change 65535 with (Z.ones 16).
  repeat rewrite Z.land_ones by lia.
  assert (H16 : 0 <= a / 2 ^ 16 < 4294967296) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small (a / 2 ^ 16)) by exact H16.
  assert (Hlo : 0 <= a mod 2 ^ 16 < 4294967296) by (pose proof (Z.mod_pos_bound a (2 ^ 16)); lia).
  rewrite (Z.mod_small (a mod 2 ^ 16)) by exact Hlo.
  rewrite !Z.div_div by lia. rewrite !Zmod_mod.
  change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216.
  change (2 ^ 8 * 2 ^ 16) with 16777216. change (2 ^ 16 * 2 ^ 8) with 16777216.
  assert (E : a / 256 = (a mod 65536) / 256 + (a / 65536) * 256).
  { rewrite (Z.div_mod a 65536) at 1 by lia.
    replace (65536 * (a / 65536) + a mod 65536) with ((a / 65536) * 256 * 256 + a mod 65536) by lia.
    rewrite Z.div_add_l by lia. lia. }
  rewrite E, Z.mod_add by lia. rewrite Z.div_1_r.
  assert (E2 : a mod 256 = (a mod 65536) mod 256).
  { rewrite (Z.div_mod a 65536) at 1 by lia.
    replace (65536 * (a / 65536) + a mod 65536) with (a mod 65536 + (a / 65536 * 256) * 256) by lia.
    apply Z.mod_add. lia. }
  rewrite <- E2.
  change (65536 * 256) with 16777216. reflexivity.
Qed.

Lemma hb_adler_fold : forall d x y, 0 <= x < 65521 -> 0 <= y < 65521 ->
  0 <= fst (fold_left Zlib.proof.adler32.Model.adler_ref_step d (x, y)) < 65521 /\
  0 <= snd (fold_left Zlib.proof.adler32.Model.adler_ref_step d (x, y)) < 65521.
Proof.
  induction d as [|b d IH]; intros x y Hx Hy; simpl; [lia|].
  unfold Zlib.proof.adler32.Model.adler_ref_step at 2. simpl.
  unfold Zlib.proof.adler32.Model.ADLER_BASE.
  apply IH; apply Z.mod_pos_bound; lia.
Qed.

Lemma hs_radler_range' : forall d, 0 <= radler 1 d < 2 ^ 32.
Proof.
  intros d. unfold Zlib.proof.adler32.Model.ref_adler32, Zlib.proof.adler32.Model.adler_pack.
  change (Zlib.proof.adler32.Model.adler_lo 1) with 1. change (Zlib.proof.adler32.Model.adler_hi 1) with 0.
  destruct (hb_adler_fold d 1 0 ltac:(lia) ltac:(lia)) as [A B].
  destruct (fold_left _ d _) as [u v]; simpl in *. lia.
Qed.

(* the zlib header of a fresh stream, with the dictionary id when a dictionary was set *)
Lemma hb_zlib : forall s dict a,
  prm s -> (d_strstart s = 0 <-> dict = []) -> (dict <> [] -> a = radler 1 dict) ->
  khdr dict 1 s (zlib_hdr_bytes s a).
Proof.
  intros s dict a Hp Hss Ha.
  destruct Hp as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hs & _).
  pose proof (hb_zh_good (d_w_bits s) (d_strategy s) (d_level s) (d_strstart s =? 0)
                ltac:(lia) ltac:(lia) ltac:(lia)) as G.
  unfold hb_zh_ok in G. rewrite <- hb_zh_eq in G.
  repeat rewrite andb_true_iff in G. destruct G as [[[[G1 G2] G3] G4] G5].
  apply Z.eqb_eq in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3. apply Z.eqb_eq in G4.
  apply Bool.eqb_prop in G5.
  unfold khdr. simpl.
  exists (u8 (Z.land (zlib_header s) 255)).
  split.
  { split; [lia|]. split; [exact G4|]. rewrite G5.
    destruct (d_strstart s =? 0) eqn:E.
    - apply Z.eqb_eq in E. assert (dict = []) as -> by (apply Hss; exact E). reflexivity.
    - apply Z.eqb_neq in E. destruct dict; [exfalso; apply E, Hss; reflexivity|reflexivity]. }
  unfold zlib_hdr_bytes. unfold msb2 at 1. rewrite G1. cbn [app]. f_equal. f_equal.
  destruct (d_strstart s =? 0) eqn:E.
  - apply Z.eqb_eq in E. assert (dict = []) as -> by (apply Hss; exact E). reflexivity.
  - apply Z.eqb_neq in E. assert (Hd : dict <> []) by (intros N; apply E, Hss, N).
    rewrite hb_be32 by (rewrite (Ha Hd); apply hs_radler_range'). rewrite (Ha Hd).
    destruct dict; [congruence|reflexivity].
Qed.

Lemma hb_land255 : forall a, Z.land a 255 = a mod 256.
Proof. intros a. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma hb_cstr : forall o, cstr_ok o ->
  cstr_bytes o = match option_map (@removelast Z) o with Some n => n ++ [0] | None => [] end.
Proof.
  intros [l|] Hc; [|reflexivity]. destruct (Hc l eq_refl) as [l0 [-> _]].
  simpl. rewrite removelast_last. reflexivity.
Qed.

Lemma hb_le4 : forall t, F.le_bytes t 4 =
  [t mod 256; Z.shiftr t 8 mod 256; Z.shiftr t 16 mod 256; Z.shiftr t 24 mod 256].
Proof. intros t. reflexivity. Qed.

Lemma hb_le2 : forall t, F.le_bytes t 2 = [t mod 256; Z.shiftr t 8 mod 256].
Proof. intros t. reflexivity. Qed.

Lemma hb_body : forall h xfl, hdr_ok h -> 0 <= xfl < 256 ->
  gz_body h xfl = F.gz_bytes0 (fhdr_of (Some h) xfl).
Proof.
  intros h xfl (Ht & Hh & Hos & Htm & Hel & Hx & Hn & Hc) Hxfl.
  unfold gz_body, gz_pre, gz_extra_bytes, F.gz_bytes0, F.gz_flg, fhdr_of, gz_flags. cbn [F.gz_text F.gz_hcrc F.gz_extra
    F.gz_name F.gz_comment F.gz_mtime F.gz_xfl F.gz_os].
  rewrite (hb_cstr _ Hn), (hb_cstr _ Hc), hb_le4, !hb_land255.
  destruct Ht as [Ht|Ht]; destruct Hh as [Hh|Hh]; rewrite Ht, Hh; cbn [Z.eqb negb];
  destruct (gz_extra h) as [x|] eqn:Ex; cbn [option_map];
  destruct (gz_name h), (gz_comment h); cbn [option_map];
  unfold u8; cbn [map app]; rewrite ?Zmod_mod, (Z.mod_small xfl) by lia;
  try reflexivity;
  (destruct (Hx x eq_refl) as [Lx _];
   change 65535 with (Z.ones 16); rewrite Z.land_ones by lia;
   rewrite (Z.mod_small (gz_extra_len h) (2 ^ 16)) by lia;
   rewrite hb_le2, Zlength_sublist by lia; rewrite Z.sub_0_r; reflexivity).
Qed.

(* the gzip header of deflateSetHeader's header [h] with the XFL byte [xfl] *)
Lemma hb_gz_some : forall h xfl, hdr_ok h -> 0 <= xfl < 256 ->
  gz_hdr_bytes (Some h) xfl = F.gz_bytes (fhdr_of (Some h) xfl).
Proof.
  intros h xfl Hok Hxfl. unfold gz_hdr_bytes, F.gz_bytes.
  rewrite (hb_body h xfl Hok Hxfl).
  replace (F.gz_hcrc (fhdr_of (Some h) xfl)) with (negb (gz_hcrc h =? 0)) by reflexivity.
  destruct (gz_hcrc h =? 0); cbn [negb]; [apply app_nil_r|].
  f_equal. rewrite hb_le2, !hb_land255. reflexivity.
Qed.

(* zlib's default gzip header *)
Lemma hb_gz_none : forall xfl, gz_hdr_bytes None xfl = F.gz_bytes (fhdr_of None xfl).
Proof.
  intros xfl. reflexivity.
Qed.
