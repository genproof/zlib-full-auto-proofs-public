(* Law inflate_header, theory part: the layout of the member (IHTDefs.ih_lay) *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_header.IHTDefs.
Require Import Coq.btauto.Btauto.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Arithmetic of the little-endian fields                                                        *)

Lemma ihl2_le2 a b : ih_le [a; b] = a + 256 * b.
Proof. cbn. ring. Qed.

Lemma ihl2_hb2 a b : 0 <= a <= 255 -> 0 <= b <= 255 -> hbytes2 (a + 256 * b) = [a; b].
Proof.
  intros A B. unfold hbytes2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((a + 256 * b) / 256) with b by (apply Z.div_unique with a; lia).
  rewrite (Z.mul_comm 256 b), Z.mod_add by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma ihl2_split2 x : 0 <= x < 65536 -> x mod 256 + 256 * (x / 256) = x /\ 0 <= x mod 256 <= 255 /\ 0 <= x / 256 <= 255.
Proof.
  intros X. pose proof (Z.div_mod x 256 ltac:(lia)). pose proof (Z.mod_pos_bound x 256 ltac:(lia)).
  split; [lia|]. split; [lia|]. split; [apply Z.div_pos; lia |].
  assert (x / 256 < 256) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma ihl2_mt m : 0 <= m < 2 ^ 32 ->
  ih_le [m mod 256; (m / 256) mod 256; (m / 65536) mod 256; (m / 16777216) mod 256] = m /\
  hbytes4 m = [m mod 256; (m / 256) mod 256; (m / 65536) mod 256; (m / 16777216) mod 256].
Proof.
  intros M. split.
  - cbn [ih_le].
    assert (D1: m / 65536 = m / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
    assert (D2: m / 16777216 = m / 65536 / 256) by (rewrite Z.div_div by lia; reflexivity).
    pose proof (Z.div_mod m 256 ltac:(lia)). pose proof (Z.div_mod (m / 256) 256 ltac:(lia)).
    pose proof (Z.div_mod (m / 65536) 256 ltac:(lia)).
    assert (E3: (m / 16777216) mod 256 = m / 16777216).
    { apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    rewrite E3. rewrite <- D1 in *. rewrite <- D2 in *. lia.
  - unfold hbytes4. rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma ihl2_land_lxor x d M : Z.land (Z.lxor x d) M = Z.lxor (Z.land x M) (Z.land d M).
Proof. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec. btauto. Qed.

(* the stored header CRC compared with the CRC *)
Lemma ihl2_hcrc c d :
  (Z.land (Z.lxor (Z.land c 65535) d) 65535 =? Z.land c 65535) = (Z.land d 65535 =? 0).
Proof.
  rewrite ihl2_land_lxor, <- Z.land_assoc, Z.land_diag.
  destruct (Z.eqb_spec (Z.land d 65535) 0) as [E|E].
  - rewrite E, Z.lxor_0_r. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros H. apply E.
    apply (f_equal (Z.lxor (Z.land c 65535))) in H. rewrite <- Z.lxor_assoc, !Z.lxor_nilpotent, Z.lxor_0_l in H.
    exact H.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The member as a concatenation                                                                 *)

Definition ihA (g: ihg) : list Z :=
  [31; 139; 8; g_flg g; g_mtime g mod 256; (g_mtime g / 256) mod 256; (g_mtime g / 65536) mod 256;
   (g_mtime g / 16777216) mod 256; g_xfl g; g_os g].
Definition ihX (g: ihg) : list Z := if fl g 4 then [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g else [].
Definition ihN (g: ihg) : list Z := if fl g 8 then g_nf g ++ [0] else [].
Definition ihC (g: ihg) : list Z := if fl g 16 then g_cf g ++ [0] else [].
Definition ihH (g: ihg) : list Z := if fl g 2 then [ih_stored g mod 256; ih_stored g / 256] else [].
Definition ihT : list Z := [1; 0; 0; 255; 255] ++ Zrepeat 0 8.

Lemma ihl2_hdr_eq g : ih_hdr g = ihA g ++ ihX g ++ ihN g ++ ihC g.
Proof. reflexivity. Qed.

Lemma ihl2_src_eq g : ih_src g = ihA g ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ ihT.
Proof. unfold ih_src. rewrite ihl2_hdr_eq. unfold ihT. rewrite !app_assoc. reflexivity. Qed.

Lemma ihl2_lens g : Zlength (ihA g) = 10 /\ Zlength (ihX g) = ih_ne g - 10 /\ Zlength (ihN g) = ih_nn g - ih_ne g /\
  Zlength (ihC g) = ih_nc g - ih_nn g /\ Zlength (ihH g) = ih_nh g - ih_nc g /\ Zlength ihT = 13.
Proof.
  unfold ihA, ihX, ihN, ihC, ihH, ihT, ih_nh, ih_nc, ih_nn, ih_ne.
  repeat split; try reflexivity;
  repeat match goal with |- context [fl g ?b] => destruct (fl g b) end;
  rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try lia; reflexivity.
Qed.

Lemma ihl2_mid (L P Q R: list Z) a b : L = P ++ Q ++ R -> a = Zlength P -> b = Zlength P + Zlength Q ->
  sublist a b L = Q.
Proof. intros -> -> ->. list_solve. Qed.

Lemma ihl2_stored g : 0 <= ih_stored g < 65536.
Proof.
  assert (E: forall x, Z.land x 65535 = x mod 65536)
    by (intros x; change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
  unfold ih_stored. rewrite E. apply Z.mod_pos_bound. lia.
Qed.

Lemma ih_lay_proof : forall g, ih_ok g -> ih_lay g.
Proof.
  intros g G. pose proof (ihl2_lens g) as (LA & LX & LN & LC & LH & LT).
  pose proof (ihl2_src_eq g) as SE.
  assert (NE: ih_ne g = 10 + Zlength (ihX g)) by lia.
  assert (Xs: ih_xs g = if fl g 4 then 12 else 10) by reflexivity.
  pose proof (Zlength_nonneg (ihX g)). pose proof (Zlength_nonneg (ihN g)).
  pose proof (Zlength_nonneg (ihC g)). pose proof (Zlength_nonneg (ihH g)).
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  assert (XL: 0 <= Zlength (g_xf g) < 65536) by (pose proof (Zlength_nonneg (g_xf g)); lia).
  destruct (ihl2_split2 _ XL) as (XS1 & XS2 & XS3).
  constructor.
  - (* bytes *)
    rewrite SE. unfold is_bytes. change Byte.max_unsigned with 255.
    repeat rewrite Forall_app. repeat split.
    + unfold ihA. pose proof (Z.mod_pos_bound (g_mtime g) 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound (g_mtime g / 256) 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound (g_mtime g / 65536) 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound (g_mtime g / 16777216) 256 ltac:(lia)).
      repeat constructor; lia.
    + unfold ihX. destruct (fl g 4); [|constructor]. rewrite Forall_app. split; [repeat constructor; lia|].
      exact G6.
    + unfold ihN. destruct (fl g 8); [|constructor]. rewrite Forall_app. split; [|repeat constructor; lia].
      eapply Forall_impl; [|exact G8]. cbn. intros a A; lia.
    + unfold ihC. destruct (fl g 16); [|constructor]. rewrite Forall_app. split; [|repeat constructor; lia].
      eapply Forall_impl; [|exact G10]. cbn. intros a A; lia.
    + unfold ihH. destruct (fl g 2); [|constructor]. pose proof (ihl2_stored g) as ST.
      destruct (ihl2_split2 _ ST) as (_ & S2 & S3). repeat constructor; lia.
    + unfold ihT. repeat constructor; cbn; lia.
  - (* length *)
    rewrite SE, !Zlength_app. lia.
  - (* order *)
    rewrite Xs. unfold ihX in LX. destruct (fl g 4); rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil in LX;
      pose proof (Zlength_nonneg (g_xf g)); lia.
  - (* the header *)
    rewrite ihl2_hdr_eq. apply (ihl2_mid _ [] _ (ihH g ++ ihT)); [rewrite SE, !app_assoc; reflexivity | reflexivity |].
    rewrite Zlength_nil, !Zlength_app. lia.
  - (* 1f 8b *)
    rewrite (ihl2_mid (ih_src g) [] [31; 139] (sublist 2 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ ihT) 0 2);
      [split; reflexivity | rewrite SE; reflexivity | reflexivity | reflexivity].
  - (* CM FLG *)
    rewrite (ihl2_mid (ih_src g) [31; 139] [8; g_flg g] (sublist 4 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ ihT) 2 4);
      [ | rewrite SE; reflexivity | reflexivity | reflexivity].
    rewrite ihl2_le2. split; [reflexivity | apply ihl2_hb2; lia].
  - (* MTIME *)
    rewrite (ihl2_mid (ih_src g) (sublist 0 4 (ihA g)) (sublist 4 8 (ihA g)) (sublist 8 10 (ihA g) ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ ihT) 4 8);
      [ | rewrite SE; reflexivity | reflexivity | reflexivity].
    exact (ihl2_mt _ G2).
  - (* XFL OS *)
    rewrite (ihl2_mid (ih_src g) (sublist 0 8 (ihA g)) [g_xfl g; g_os g] (ihX g ++ ihN g ++ ihC g ++ ihH g ++ ihT) 8 10);
      [ | rewrite SE; reflexivity | reflexivity | reflexivity].
    rewrite ihl2_le2. split; [reflexivity | apply ihl2_hb2; lia].
  - (* XLEN *)
    intros F4. assert (EXq: ihX g = [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g)
      by (unfold ihX; rewrite F4; reflexivity).
    rewrite (ihl2_mid (ih_src g) (ihA g) [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]
               (g_xf g ++ ihN g ++ ihC g ++ ihH g ++ ihT) 10 12);
      [ | rewrite SE, EXq, <- !app_assoc; reflexivity | rewrite LA; reflexivity | rewrite LA; reflexivity].
    rewrite ihl2_le2. split; [exact XS1|].
    rewrite <- XS1 at 1. apply ihl2_hb2; lia.
  - (* the extra field *)
    intros F4. assert (EXq: ihX g = [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256] ++ g_xf g)
      by (unfold ihX; rewrite F4; reflexivity).
    apply (ihl2_mid _ (ihA g ++ [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]) _ (ihN g ++ ihC g ++ ihH g ++ ihT));
      [rewrite SE, EXq, <- !app_assoc; reflexivity | rewrite Zlength_app, LA; reflexivity |].
    rewrite Zlength_app, LA. unfold ih_ne. rewrite F4.
    change (Zlength [Zlength (g_xf g) mod 256; Zlength (g_xf g) / 256]) with 2. lia.
  - (* the name *)
    intros F8. assert (EN: ihN g = g_nf g ++ [0]) by (unfold ihN; rewrite F8; reflexivity).
    apply (ihl2_mid _ (ihA g ++ ihX g) _ (ihC g ++ ihH g ++ ihT));
      [rewrite SE, EN, <- !app_assoc; reflexivity | rewrite Zlength_app; lia | rewrite Zlength_app, <- EN; lia].
  - (* the comment *)
    intros F16. assert (EC: ihC g = g_cf g ++ [0]) by (unfold ihC; rewrite F16; reflexivity).
    apply (ihl2_mid _ (ihA g ++ ihX g ++ ihN g) _ (ihH g ++ ihT));
      [rewrite SE, EC, <- !app_assoc; reflexivity | rewrite !Zlength_app; lia | rewrite <- EC, !Zlength_app; lia].
  - (* the header CRC *)
    intros F2. assert (EH: ihH g = [ih_stored g mod 256; ih_stored g / 256]) by (unfold ihH; rewrite F2; reflexivity).
    rewrite (ihl2_mid (ih_src g) (ihA g ++ ihX g ++ ihN g ++ ihC g) [ih_stored g mod 256; ih_stored g / 256] ihT
               (ih_nc g) (ih_nc g + 2));
      [ | rewrite SE, EH, <- !app_assoc; reflexivity | rewrite !Zlength_app; lia | rewrite !Zlength_app; cbn; lia].
    rewrite ihl2_le2. destruct (ihl2_split2 _ (ihl2_stored g)) as (S1 & _ & _). rewrite S1.
    rewrite (ihl2_mid (ih_src g) [] (ih_hdr g) (ihH g ++ ihT) 0 (ih_nc g));
      [ | rewrite SE, ihl2_hdr_eq, <- !app_assoc; reflexivity | reflexivity | rewrite ihl2_hdr_eq, !Zlength_app; cbn; lia].
    unfold ih_stored. rewrite ihl2_hcrc. unfold ih_badcrc. rewrite F2. cbn [andb]. rewrite negb_involutive. reflexivity.
  - (* the stored block *)
    apply (ihl2_mid _ (ihA g ++ ihX g ++ ihN g ++ ihC g ++ ihH g) _ (Zrepeat 0 8));
      [rewrite SE; unfold ihT; rewrite <- !app_assoc; reflexivity | rewrite !Zlength_app; lia | rewrite !Zlength_app; cbn; lia].
  - (* the trailer *)
    apply (ihl2_mid _ (ihA g ++ ihX g ++ ihN g ++ ihC g ++ ihH g ++ [1; 0; 0; 255; 255]) _ []);
      [rewrite SE; unfold ihT; rewrite <- !app_assoc, app_nil_r; reflexivity | rewrite !Zlength_app; cbn; lia
      | rewrite !Zlength_app; cbn; lia].
Qed.
