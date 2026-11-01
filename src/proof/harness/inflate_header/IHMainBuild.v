(* Law inflate_header, main: positions 24 .. 52 of b0 (IHMainKit.v): the fields xf, nf, cf drawn
   (nondet_bytes, draw_nonzero, the zero bytes), the member built in src (header, the three optional fields by
   bytes_copy, hcrc = ref_crc32(0, src, hlen) & 0xffff, the stored header CRC, the empty stored block, the
   zero trailer), reserved and badcrc; src then holds ih_src g (IHFacts.v) for the ghost g of the drawn
   fields; then seg_53 (given). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_header.IHLawCS Zlib.proof.harness.inflate_header.IHGlobals
               Zlib.proof.harness.inflate_header.IHHelpers Zlib.proof.harness.inflate_header.IHFacts
               Zlib.proof.harness.inflate_header.IHMainStmt.
Require Import Zlib.harness.x_inflate_header.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_header.IHMainKit.
Local Open Scope logic.


(* ---------------------------------------------------------------------------------------------- *)
(* Helpers: src as a prefix of bytes followed by undefined bytes                                  *)

Definition srcv (l: list Z) (T: Z) : list val := bytes_rep l ++ Zrepeat Vundef (T - Zlength l).

Lemma srcv_upd i l T x: i = Zlength l -> i < T ->
  upd_Znth i (srcv l T) (Vint (Int.repr x)) = srcv (l ++ [x]) T.
Proof.
  intros -> H. unfold srcv, bytes_rep. rewrite map_app. simpl map.
  pose proof (Zlength_nonneg l).
  rewrite upd_Znth_app2 by (rewrite Zlength_map; list_solve).
  rewrite Zlength_map, Z.sub_diag.
  replace (T - Zlength l) with (1 + (T - Zlength (l ++ [x]))) by list_solve.
  rewrite <- Zrepeat_app by list_solve.
  rewrite upd_Znth_app1 by list_solve. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma srcv_len l T: Zlength l <= T -> Zlength (srcv l T) = T.
Proof. intros. unfold srcv, bytes_rep. pose proof (Zlength_nonneg l). list_solve. Qed.

Lemma split3_tuchar {cs: compspecs} sh p T (A B C: list val):
  field_compatible (tarray tuchar T) [] p -> Zlength A + Zlength B + Zlength C = T ->
  data_at sh (tarray tuchar T) (A ++ B ++ C) p =
  data_at sh (tarray tuchar (Zlength A)) A p * data_at sh (tarray tuchar (Zlength B)) B (offset_val (Zlength A) p) *
  data_at sh (tarray tuchar (Zlength C)) C (offset_val (Zlength A + Zlength B) p).
Proof.
  intros FC E.
  pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B). pose proof (Zlength_nonneg C).
  rewrite (split3_data_at_Tarray sh tuchar T (Zlength A) (Zlength A + Zlength B) (A ++ B ++ C) (A ++ B ++ C) A B C p).
  2: (unfold naturally_aligned; simpl; auto). 2: lia. 2: list_solve. 2: list_solve. 2: list_solve. 2: list_solve. 2: list_solve.
  rewrite !field_address0_offset by auto with field_compatible.
  simpl. rewrite !Z.mul_1_l, !Z.add_0_l. replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
  replace (T - (Zlength A + Zlength B)) with (Zlength C) by lia. reflexivity.
Qed.

Lemma split2_tuchar {cs: compspecs} sh p T (A B: list val):
  field_compatible (tarray tuchar T) [] p -> Zlength A + Zlength B = T ->
  data_at sh (tarray tuchar T) (A ++ B) p =
  data_at sh (tarray tuchar (Zlength A)) A p * data_at sh (tarray tuchar (Zlength B)) B (offset_val (Zlength A) p).
Proof.
  intros FC E. pose proof (Zlength_nonneg A). pose proof (Zlength_nonneg B).
  rewrite (split2_data_at_Tarray_app (Zlength A) T sh tuchar A B p); [ | reflexivity | change (Zlength B = T - Zlength A); lia ].
  rewrite field_address0_offset by auto with field_compatible.
  simpl. rewrite Z.mul_1_l, Z.add_0_l. replace (T - Zlength A) with (Zlength B) by lia. reflexivity.
Qed.

Lemma data_at__uchar {cs: compspecs} sh n p:
  data_at_ sh (tarray tuchar n) p = data_at sh (tarray tuchar n) (Zrepeat Vundef n) p.
Proof. reflexivity. Qed.

Lemma bytes_rep_len l: Zlength (bytes_rep l) = Zlength l.
Proof. unfold bytes_rep. apply Zlength_map. Qed.

(* src as srcv l T, split around the next len bytes *)
Lemma srcv_split {cs: compspecs} sh p T l len:
  field_compatible (tarray tuchar T) [] p -> 0 <= len -> Zlength l + len <= T ->
  data_at sh (tarray tuchar T) (srcv l T) p =
  data_at sh (tarray tuchar (Zlength l)) (bytes_rep l) p * data_at_ sh (tarray tuchar len) (offset_val (Zlength l) p) *
  data_at sh (tarray tuchar (T - Zlength l - len)) (Zrepeat Vundef (T - Zlength l - len)) (offset_val (Zlength l + len) p).
Proof.
  intros FC H1 H2. pose proof (Zlength_nonneg l). unfold srcv.
  replace (Zrepeat Vundef (T - Zlength l)) with (Zrepeat Vundef len ++ Zrepeat Vundef (T - Zlength l - len))
    by (rewrite Zrepeat_app by lia; f_equal; lia).
  rewrite split3_tuchar by (auto; rewrite bytes_rep_len, !Zlength_Zrepeat by lia; lia).
  rewrite bytes_rep_len, !Zlength_Zrepeat by lia. rewrite data_at__uchar. reflexivity.
Qed.

Lemma srcv_join {cs: compspecs} sh p T l d:
  field_compatible (tarray tuchar T) [] p -> Zlength l + Zlength d <= T ->
  data_at sh (tarray tuchar (Zlength l)) (bytes_rep l) p *
  data_at sh (tarray tuchar (Zlength d)) (bytes_rep d) (offset_val (Zlength l) p) *
  data_at sh (tarray tuchar (T - Zlength l - Zlength d)) (Zrepeat Vundef (T - Zlength l - Zlength d))
    (offset_val (Zlength l + Zlength d) p) =
  data_at sh (tarray tuchar T) (srcv (l ++ d) T) p.
Proof.
  intros FC H2. pose proof (Zlength_nonneg l). pose proof (Zlength_nonneg d). unfold srcv.
  unfold bytes_rep at 3. rewrite map_app, <- app_assoc. fold (bytes_rep l) (bytes_rep d).
  rewrite split3_tuchar by (auto; rewrite Zlength_app, !bytes_rep_len, !Zlength_Zrepeat by lia; lia).
  rewrite Zlength_app, !bytes_rep_len, !Zlength_Zrepeat by lia.
  replace (T - (Zlength l + Zlength d)) with (T - Zlength l - Zlength d) by lia. reflexivity.
Qed.

(* nf / cf: the first n bytes, then the last one *)
Lemma last_split {cs: compspecs} sh p n:
  field_compatible (tarray tuchar (n + 1)) [] p -> 0 <= n ->
  data_at_ sh (tarray tuchar (n + 1)) p = data_at_ sh (tarray tuchar n) p * data_at_ sh (tarray tuchar 1) (offset_val n p).
Proof.
  intros FC H. rewrite !data_at__uchar.
  replace (Zrepeat Vundef (n + 1)) with (Zrepeat Vundef n ++ Zrepeat Vundef 1) by (rewrite Zrepeat_app by lia; reflexivity).
  rewrite split2_tuchar by (auto; rewrite !Zlength_Zrepeat by lia; lia).
  rewrite !Zlength_Zrepeat by lia. reflexivity.
Qed.

Lemma last_join {cs: compspecs} sh p bs:
  field_compatible (tarray tuchar (Zlength bs + 1)) [] p ->
  data_at sh (tarray tuchar (Zlength bs)) (bytes_rep bs) p * data_at_ sh (tarray tuchar 1) (offset_val (Zlength bs) p) =
  data_at sh (tarray tuchar (Zlength bs + 1)) (srcv bs (Zlength bs + 1)) p.
Proof.
  intros FC. unfold srcv. replace (Zlength bs + 1 - Zlength bs) with 1 by lia.
  rewrite split2_tuchar by (auto; rewrite bytes_rep_len, Zlength_Zrepeat by lia; lia).
  rewrite bytes_rep_len, Zlength_Zrepeat by lia. rewrite data_at__uchar. reflexivity.
Qed.

Lemma srcv_full l: srcv l (Zlength l) = bytes_rep l.
Proof. unfold srcv. rewrite Z.sub_diag. simpl. apply app_nil_r. Qed.

Lemma zext8 x: Int.zero_ext 8 (Int.repr x) = Int.repr (x mod 256).
Proof.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 _)), Int.zero_ext_mod by (cbn; lia).
  rewrite Int.unsigned_repr_eq. f_equal. change Int.modulus with (2 ^ 32).
  change (two_p 8) with 256. symmetry. apply Znumtheory.Zmod_div_mod; [ lia | lia | ].
  exists (2 ^ 24). reflexivity.
Qed.

Lemma srcv_last l x: srcv (l ++ [x]) (Zlength l + 1) = bytes_rep (l ++ [x]).
Proof. replace (Zlength l + 1) with (Zlength (l ++ [x])) by list_solve. apply srcv_full. Qed.

Lemma ifl_true flg bit: Int.repr (Z.land flg bit) <> Int.zero -> flb flg bit = true.
Proof. intros H. unfold flb. destruct (Z.land flg bit =? 0) eqn:E; auto. apply Z.eqb_eq in E. rewrite E in H. contradiction. Qed.

Lemma ifl_false flg bit: 0 <= flg <= 255 -> 0 <= bit <= 255 -> Int.repr (Z.land flg bit) = Int.zero -> flb flg bit = false.
Proof.
  intros H1 H2 H. unfold flb. assert (0 <= Z.land flg bit <= 255).
  { assert (E: Z.land flg bit = (Z.land flg bit) mod 2 ^ 8).
    { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm bit), Z.land_assoc.
      rewrite (Z.land_ones flg 8) by lia. rewrite Z.mod_small by (simpl; lia). reflexivity. }
    rewrite E. pose proof (Z.mod_pos_bound (Z.land flg bit) (2 ^ 8)). change (2 ^ 8) with 256 in *. lia. }
  apply repr_inj_unsigned in H; [rewrite H; reflexivity | rep_lia | rep_lia].
Qed.

Lemma shru64_div m k: 0 <= m < 2 ^ 32 -> 0 <= k < 64 ->
  Int64.unsigned (Int64.shru (Int64.repr m) (Int64.repr k)) = m / 2 ^ k.
Proof.
  intros Hm Hk. unfold Int64.shru. rewrite (Int64.unsigned_repr m) by rep_lia.
  rewrite (Int64.unsigned_repr k) by rep_lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (m / 2 ^ k <= m / 1) by (apply Z.div_le_compat_l; lia).
  rewrite Z.div_1_r in *. apply Int64.unsigned_repr. split; [apply Z.div_pos; lia | rep_lia].
Qed.

Definition hfix (flg mtime xfl os: Z) : list Z :=
  [31; 139; 8; flg; mtime mod 256; (mtime / 256) mod 256; (mtime / 65536) mod 256; (mtime / 16777216) mod 256;
   xfl; os].

Definition hx (flg: Z) (bx: list Z) : list Z := if flb flg 4 then [Zlength bx mod 256; Zlength bx / 256] ++ bx else [].
Definition hn (flg: Z) (bn: list Z) : list Z := if flb flg 8 then bn ++ [0] else [].
Definition hc (flg: Z) (bc: list Z) : list Z := if flb flg 16 then bc ++ [0] else [].

Ltac ifsrc l' kv := match goal with
  |- semax _ (PROPx _ (LOCALx (temp _k _ :: ?Q) (SEPx (data_at ?sh (tarray tuchar ?T) _ ?p :: ?R)))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp _k (Vint (Int.repr kv)) :: Q)
    (SEPx (data_at sh (tarray tuchar T) (srcv l' T) p :: R)))) end.

Lemma shru32_div x k: 0 <= x < 2 ^ 32 -> 0 <= k < 32 ->
  Int.shru (Int.repr x) (Int.repr k) = Int.repr (x / 2 ^ k).
Proof.
  intros Hx Hk. unfold Int.shru. rewrite (Int.unsigned_repr x) by rep_lia.
  rewrite (Int.unsigned_repr k) by rep_lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma srcv_join' {cs: compspecs} sh p T l d n:
  field_compatible (tarray tuchar T) [] p -> Zlength l + n <= T -> n = Zlength d ->
  data_at sh (tarray tuchar (Zlength l)) (bytes_rep l) p *
  data_at sh (tarray tuchar n) (bytes_rep d) (offset_val (Zlength l) p) *
  data_at sh (tarray tuchar (T - Zlength l - n)) (Zrepeat Vundef (T - Zlength l - n))
    (offset_val (Zlength l + n) p) =
  data_at sh (tarray tuchar T) (srcv (l ++ d) T) p.
Proof. intros FC H ->. apply srcv_join; auto. Qed.

Lemma cbuf_ok_whole' sh p n data:
  readable_share sh -> is_bytes data -> isptr p -> n = Zlength data ->
  cbuf_ok false p sh p 0 n n (bytes_rep data) data.
Proof. intros ? ? ? ->. apply cbuf_ok_whole; auto. Qed.

Lemma hx_len flg bx: Zlength (hx flg bx) = if flb flg 4 then 2 + Zlength bx else 0.
Proof. unfold hx. destruct (flb flg 4); [list_solve | reflexivity]. Qed.
Lemma hn_len flg bn: Zlength (hn flg bn) = if flb flg 8 then Zlength bn + 1 else 0.
Proof. unfold hn. destruct (flb flg 8); [list_solve | reflexivity]. Qed.
Lemma hc_len flg bc: Zlength (hc flg bc) = if flb flg 16 then Zlength bc + 1 else 0.
Proof. unfold hc. destruct (flb flg 16); [list_solve | reflexivity]. Qed.

Lemma is_bytes_z0 l: Forall (fun b => 0 < b <= Byte.max_unsigned) l -> is_bytes (l ++ [0]).
Proof.
  intros H. apply is_bytes_app; [ | repeat constructor; rep_lia].
  unfold is_bytes. eapply Forall_impl; [ | exact H]. intros a Ha; simpl in Ha; lia.
Qed.

Lemma cbuf_srcv sh p T n l:
  readable_share sh -> isptr p -> Zlength l = n -> n <= T -> is_bytes l ->
  cbuf_ok false p sh p 0 T n (srcv l T) l.
Proof.
  intros Hsh Hp Hn HT Hb. unfold cbuf_ok. pose proof (Zlength_nonneg l).
  split; [rewrite isptr_offset_val_zero; auto | ]. repeat split; auto; try lia.
  unfold srcv. rewrite Z.add_0_l, <- Hn. rewrite sublist_app1 by (rewrite ?bytes_rep_len; lia).
  rewrite sublist_same by (rewrite ?bytes_rep_len; lia). reflexivity.
Qed.

Lemma is_bytes_hdr3 flg mtime xfl os bx bn bc:
  0 <= flg <= 255 -> 0 <= xfl <= 255 -> 0 <= os <= 255 -> 0 <= Zlength bx <= 65535 -> is_bytes bx ->
  Forall (fun b => 0 < b <= Byte.max_unsigned) bn -> Forall (fun b => 0 < b <= Byte.max_unsigned) bc ->
  is_bytes (((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) ++ hc flg bc).
Proof.
  intros. repeat apply is_bytes_app.
  - unfold hfix, is_bytes.
    repeat (apply Forall_cons; [ try (pose proof (Z.mod_pos_bound mtime 256); pose proof (Z.mod_pos_bound (mtime / 256) 256);
      pose proof (Z.mod_pos_bound (mtime / 65536) 256); pose proof (Z.mod_pos_bound (mtime / 16777216) 256)); rep_lia | ]).
    constructor.
  - unfold hx. destruct (flb flg 4); [ | constructor].
    apply is_bytes_app; auto. unfold is_bytes.
    pose proof (Z.mod_pos_bound (Zlength bx) 256).
    assert (0 <= Zlength bx / 256 < 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    repeat constructor; rep_lia.
  - unfold hn. destruct (flb flg 8); [apply is_bytes_z0; auto | constructor].
  - unfold hc. destruct (flb flg 16); [apply is_bytes_z0; auto | constructor].
Qed.

Lemma land64 c: Int64.and (Int64.repr c) (Int64.repr 65535) = Int64.repr (Z.land c 65535).
Proof.
  unfold Int64.and. rewrite (Int64.unsigned_repr 65535) by rep_lia. rewrite Int64.unsigned_repr_eq.
  change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
  change Int64.modulus with (2 ^ 64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity | lia | lia | ].
  exists (2 ^ 48). reflexivity.
Qed.

Lemma xor64 a d: 0 <= a <= Int64.max_unsigned -> 0 <= d <= Int64.max_unsigned ->
  Int64.xor (Int64.repr a) (Int64.repr d) = Int64.repr (Z.lxor a d).
Proof. intros. unfold Int64.xor. rewrite !Int64.unsigned_repr by lia. reflexivity. Qed.

Lemma land16_range c: 0 <= Z.land c 65535 < 65536.
Proof. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Definition hs (flg S: Z) : list Z := if flb flg 2 then [S mod 256; S / 256] else [].

Lemma zrep_snoc (l: list Z) i: 0 <= i -> (l ++ Zrepeat 0 i) ++ [0] = l ++ Zrepeat 0 (i + 1).
Proof. intros. rewrite <- app_assoc. f_equal. rewrite <- Zrepeat_app by lia. reflexivity. Qed.

Lemma hs_len flg S: Zlength (hs flg S) = if flb flg 2 then 2 else 0.
Proof. unfold hs. destruct (flb flg 2); reflexivity. Qed.

Lemma land_byte a b: 0 <= a <= 255 -> 0 <= Z.land a b <= 255.
Proof.
  intros H. assert (E: Z.land a b = (Z.land a b) mod 2 ^ 8).
  { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm b), Z.land_assoc.
    rewrite (Z.land_ones a 8) by lia. rewrite Z.mod_small by (simpl; lia). reflexivity. }
  rewrite E. pose proof (Z.mod_pos_bound (Z.land a b) (2 ^ 8)). change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma res_eq flg: 0 <= flg <= 255 ->
  Z.b2z (negb (Int.eq (Int.and (Int.repr flg) (Int.repr 224)) (Int.repr 0))) = b2z (negb (Z.land flg 224 =? 0)).
Proof.
  intros H. rewrite and_repr. pose proof (land_byte flg 224 H).
  unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia.
  destruct (zeq (Z.land flg 224) 0) as [E|E]; [rewrite E | apply Z.eqb_neq in E; rewrite E]; reflexivity.
Qed.

Lemma bad_eq d: 0 <= d < 2 ^ 32 ->
  bool2val (negb (Int.eq (Int.and (Int.repr d) (Int.repr 65535)) (Int.repr 0))) =
  Vint (Int.repr (b2z (negb (Z.land d 65535 =? 0)))).
Proof.
  intros H. rewrite and_repr. pose proof (land16_range d).
  unfold Int.eq. rewrite !Int.unsigned_repr by rep_lia.
  destruct (zeq (Z.land d 65535) 0) as [E|E]; [rewrite E | apply Z.eqb_neq in E; rewrite E]; reflexivity.
Qed.

Local Opaque Int64.shru Int.shru.
Definition Kgoal {Espec: OracleKind} gv V b P : Prop :=
  forall g, ih_f53 g b P -> semax Delta_m (ih_s53 gv V g b P) seg_53 POST_b.

Lemma hx_true flg bx: flb flg 4 = true -> Zlength bx <= 65535 ->
  hx flg bx = [Zlength bx mod 256; (Zlength bx / 2 ^ 8) mod 256] ++ bx.
Proof.
  intros F H. unfold hx. rewrite F. pose proof (Zlength_nonneg bx).
  rewrite (Z.mod_small (Zlength bx / 2 ^ 8)); [reflexivity | ].
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Ltac st := forward; try (entailer!; lia); rewrite ?Int.zero_ext_idem by lia; rewrite ?shru32_div by rep_lia; rewrite ?zext8; rewrite srcv_upd by (try list_solve; lia).

Lemma build_ok {Espec: OracleKind} gv V n b P:
  ih_f24 n b P ->
  (forall g, ih_f53 g b P -> semax Delta_m (ih_s53 gv V g b P) seg_53 POST_b) ->
  semax Delta_m (ih_s24 gv V n b P) seg_24 POST_b.
Proof.
  intros F K. fold (Kgoal gv V b P) in K.
  destruct n as [flg mtime xfl os xlen nl cl delta]; destruct b as [w xmax nmax cmax xnul nnul cnul];
  destruct P as [src xf nf cf]; destruct V as [vs vh vxs vns vcs vosn]; simpl in *.
  destruct F as (Hflg & Hmt & Hxfl & Hos & Hxlen & Hnl & Hcl & Hdl & Hw & Hxm & Hnm & Hcm & Hxn & Hnn & Hcn & Psrc & Pxf & Pnf & Pcf).
  unfold ih_s24, seg_24, Delta_m, Gmain, POST_b, POST_m.
  cbn [n_flg n_mtime n_xfl n_os n_xlen n_nl n_cl n_delta b_w b_xmax b_nmax b_cmax b_xnul b_nnul b_cnul
       p_src p_xf p_nf p_cf v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_] in *.
  set (T := n_total _). set (HL := n_hlen _).
  simplify_func_tycontext. abbreviate_semax.
  forward_call (xf, xlen, Ews).
  { destruct (eq_dec xf nullval); [subst; contradiction | cancel]. }
  Intros bx. destruct (eq_dec xf nullval); [subst; contradiction | ]. fold (bytes_rep bx). subst xlen.
  assert_PROP (field_compatible (tarray tuchar (nl + 1)) [] nf) as FCn by entailer!.
  assert_PROP (field_compatible (tarray tuchar (cl + 1)) [] cf) as FCc by entailer!.
  assert_PROP (field_compatible (tarray tuchar T) [] src) as FCs by entailer!.
  rewrite (last_split Ews nf nl) by (auto; lia). Intros.
  forward_call (nf, nl, Ews).
  Intros bn. subst nl. fold (bytes_rep bn).
  gather_SEP (data_at _ (tarray tuchar (Zlength bn)) _ nf) (data_at_ _ (tarray tuchar 1) _).
  rewrite (last_join Ews nf bn) by auto.
  forward.
  rewrite zext8, srcv_upd, srcv_last by lia. change (0 mod 256) with 0.
  rewrite (last_split Ews cf cl) by (auto; lia). Intros.
  forward_call (cf, cl, Ews).
  Intros bc. subst cl. fold (bytes_rep bc).
  gather_SEP (data_at _ (tarray tuchar (Zlength bc)) _ cf) (data_at_ _ (tarray tuchar 1) _).
  rewrite (last_join Ews cf bc) by auto.
  forward.
  rewrite zext8, srcv_upd, srcv_last by lia. change (0 mod 256) with 0.
  rewrite data_at__uchar. replace (Zrepeat Vundef T) with (srcv [] T) by (unfold srcv; rewrite Zlength_nil, Z.sub_0_r; reflexivity).
  assert (EHL: HL + 0 = 10 + (if flb flg 4 then 2 + Zlength bx else 0) + (if flb flg 8 then Zlength bn + 1 else 0) +
                    (if flb flg 16 then Zlength bc + 1 else 0)) by (rewrite Z.add_0_r; reflexivity).
  assert (ET: T + 0 = HL + (if flb flg 2 then 2 else 0) + 13) by (rewrite Z.add_0_r; reflexivity).
  clearbody T HL.
  assert (HHL: 10 <= HL <= 10 + 3 * 65537) by (destruct (flb flg 4), (flb flg 8), (flb flg 16); lia).
  assert (HT: HL + 13 <= T <= HL + 15) by (destruct (flb flg 2); lia).
  st. st. st. st. st. st. st. st. st. st.
  match goal with |- context [srcv ?l T] => replace l with (hfix flg mtime xfl os) end.
  2: { rewrite !Int.unsigned_repr by rep_lia. rewrite !shru64_div by lia.
       rewrite Int64.Z_mod_modulus_eq, (Z.mod_small mtime Int64.modulus) by rep_lia. rewrite ?Zmod_mod.
       rewrite (Z.mod_small flg), (Z.mod_small xfl), (Z.mod_small os) by lia. reflexivity. }
  forward.
  gather_SEP (data_at _ (tarray tuchar T) _ src).
  ifsrc (hfix flg mtime xfl os ++ hx flg bx) (10 + Zlength (hx flg bx)).
  - assert (F4: flb flg 4 = true) by (apply ifl_true; rewrite <- and_repr; auto).
    st. st.
    match goal with |- context [srcv ?l T] => set (l1 := l) end.
    assert (Z1: Zlength l1 = 12) by reflexivity.
    assert (Hx: 12 + Zlength bx <= HL) by (rewrite F4 in EHL; destruct (flb flg 8), (flb flg 16); lia).
    rewrite (srcv_split Ews src T l1 (Zlength bx)) by (auto; rewrite ?Z1; lia).
    Intros.
    forward_call (offset_val (Zlength l1) src, Ews, xf, Ews, xf, 0, Zlength bx, bytes_rep bx, Zlength bx, bx).
    { rewrite (@data_at__uchar Zlib.units.Adler32.CS), !ih_bytes_adler_cs, data_at__uchar. cancel. }
    { apply cbuf_ok_whole; auto. }
    rewrite !ih_bytes_adler_cs.
    gather_SEP (data_at _ (tarray tuchar (Zlength l1)) _ src) (data_at _ (tarray tuchar (Zlength bx)) _ (offset_val _ src))
      (data_at _ (tarray tuchar (T - Zlength l1 - Zlength bx)) _ _).
    rewrite (srcv_join Ews src T l1 bx) by (auto; lia).
    forward.
    replace (l1 ++ bx) with (hfix flg mtime xfl os ++ hx flg bx)
      by (subst l1; rewrite hx_true by (auto; lia); rewrite <- !app_assoc; reflexivity).
    entailer!. rewrite hx_true by (auto; lia). rewrite Zlength_app. reflexivity.
  - assert (F4: flb flg 4 = false) by (apply ifl_false; try lia; rewrite <- and_repr; auto).
    forward. unfold hx. rewrite F4. rewrite app_nil_r. entailer!.
  - (* the name *)
  pose proof (hx_len flg bx) as Lx.
  ifsrc ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) (10 + Zlength (hx flg bx) + Zlength (hn flg bn)).
  + assert (F8: flb flg 8 = true) by (apply ifl_true; rewrite <- and_repr; auto).
    assert (Zl: Zlength (hfix flg mtime xfl os ++ hx flg bx) = 10 + Zlength (hx flg bx)) by (rewrite Zlength_app; reflexivity).
    assert (Hn: 10 + Zlength (hx flg bx) + (Zlength bn + 1) <= HL)
      by (rewrite Lx; rewrite F8 in EHL; destruct (flb flg 4), (flb flg 16); lia).
    rewrite (srcv_split Ews src T (hfix flg mtime xfl os ++ hx flg bx) (Zlength bn + 1)) by (auto; rewrite ?Zl; lia).
    rewrite Zl. Intros.
    forward_call (offset_val (10 + Zlength (hx flg bx)) src, Ews, nf, Ews, nf, 0, Zlength bn + 1,
                  bytes_rep (bn ++ [0]), Zlength bn + 1, bn ++ [0]).
    { rewrite (@data_at__uchar Zlib.units.Adler32.CS), !ih_bytes_adler_cs, data_at__uchar. cancel. }
    { apply cbuf_ok_whole'; auto. apply is_bytes_z0; auto. list_solve. }
    rewrite !ih_bytes_adler_cs. rewrite <- Zl.
    gather_SEP (data_at _ (tarray tuchar (Zlength (hfix flg mtime xfl os ++ hx flg bx))) _ src)
      (data_at _ (tarray tuchar (Zlength bn + 1)) _ (offset_val _ src))
      (data_at _ (tarray tuchar (T - _ - (Zlength bn + 1))) _ _).
    rewrite (srcv_join' Ews src T (hfix flg mtime xfl os ++ hx flg bx) (bn ++ [0])) by (auto; try list_solve; lia).
    forward.
    replace (hn flg bn) with (bn ++ [0]) by (unfold hn; rewrite F8; auto).
    entailer!. rewrite Zl. f_equal. f_equal. list_solve.
  + assert (F8: flb flg 8 = false) by (apply ifl_false; try lia; rewrite <- and_repr; auto).
    forward. unfold hn. rewrite F8. rewrite app_nil_r. entailer!.
  + (* the comment *)
  pose proof (hn_len flg bn) as Ln.
  ifsrc (((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) ++ hc flg bc)
        (10 + Zlength (hx flg bx) + Zlength (hn flg bn) + Zlength (hc flg bc)).
  * assert (F16: flb flg 16 = true) by (apply ifl_true; rewrite <- and_repr; auto).
    assert (Zl: Zlength ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) = 10 + Zlength (hx flg bx) + Zlength (hn flg bn))
      by (rewrite !Zlength_app; reflexivity).
    assert (Hc: 10 + Zlength (hx flg bx) + Zlength (hn flg bn) + (Zlength bc + 1) <= HL)
      by (rewrite Lx, Ln; rewrite F16 in EHL; destruct (flb flg 4), (flb flg 8); lia).
    rewrite (srcv_split Ews src T ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) (Zlength bc + 1))
      by (auto; rewrite ?Zl; lia).
    rewrite Zl. Intros.
    forward_call (offset_val (10 + Zlength (hx flg bx) + Zlength (hn flg bn)) src, Ews, cf, Ews, cf, 0, Zlength bc + 1,
                  bytes_rep (bc ++ [0]), Zlength bc + 1, bc ++ [0]).
    { rewrite (@data_at__uchar Zlib.units.Adler32.CS), !ih_bytes_adler_cs, data_at__uchar. cancel. }
    { apply cbuf_ok_whole'; auto. apply is_bytes_z0; auto. list_solve. }
    rewrite !ih_bytes_adler_cs. rewrite <- Zl.
    gather_SEP (data_at _ (tarray tuchar (Zlength ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn))) _ src)
      (data_at _ (tarray tuchar (Zlength bc + 1)) _ (offset_val _ src))
      (data_at _ (tarray tuchar (T - _ - (Zlength bc + 1))) _ _).
    rewrite (srcv_join' Ews src T ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) (bc ++ [0])) by (auto; try list_solve; lia).
    forward.
    replace (hc flg bc) with (bc ++ [0]) by (unfold hc; rewrite F16; auto).
    entailer!. rewrite Zl. f_equal. f_equal. list_solve.
  * assert (F16: flb flg 16 = false) by (apply ifl_false; try lia; rewrite <- and_repr; auto).
    forward. unfold hc. rewrite F16. rewrite app_nil_r. entailer!.
  * pose proof (hc_len flg bc) as Lc.
    assert (EH: 10 + Zlength (hx flg bx) + Zlength (hn flg bn) + Zlength (hc flg bc) = HL) by (rewrite Lx, Ln, Lc; lia).
    rewrite EH.
    set (l3 := ((hfix flg mtime xfl os ++ hx flg bx) ++ hn flg bn) ++ hc flg bc).
    assert (Z3: Zlength l3 = HL) by (subst l3; rewrite !Zlength_app; rewrite <- EH; reflexivity).
    forward_call (0, src, Ews, src, 0, T, srcv l3 T, HL, l3).
    { rewrite ih_bytes_crc_cs. cancel. }
    { apply cbuf_srcv; auto; try lia. apply is_bytes_hdr3; auto. }
    rewrite ih_bytes_crc_cs.
    forward.
    change (Int.signed (Int.repr 65535)) with 65535. rewrite land64.
    set (crc := ref_crc32 0 l3).
    set (S := Z.land (Z.lxor (Z.land crc 65535) delta) 65535).
    assert (HS: 0 <= S < 65536) by apply land16_range.
    pose proof (land16_range crc) as Hc16.
    match goal with |- semax _ (PROPx _ (LOCALx (?h :: ?t :: temp _k _ :: ?Q)
                                   (SEPx (data_at ?sh (tarray tuchar ?TT) _ ?p :: ?R)))) _ _ =>
      forward_if (PROPx [] (LOCALx (h :: t :: temp _k (Vint (Int.repr (HL + Zlength (hs flg S)))) :: Q)
                                   (SEPx (data_at sh (tarray tuchar TT) (srcv (l3 ++ hs flg S) TT) p :: R)))) end.
    { assert (F2: flb flg 2 = true) by (apply ifl_true; rewrite <- and_repr; auto).
      forward.
      change (Int.signed (Int.repr 65535)) with 65535. rewrite (Int.unsigned_repr delta) by rep_lia.
      rewrite xor64, land64 by rep_lia. fold S.
      forward. rewrite Int64.Z_mod_modulus_eq, (Z.mod_small S) by rep_lia. rewrite ?Int.zero_ext_idem by lia. rewrite zext8.
      rewrite srcv_upd by lia.
      forward.
      rewrite (Int.unsigned_repr 8) by rep_lia. rewrite shru64_div by rep_lia.
      rewrite ?Int.zero_ext_idem by lia. rewrite zext8.
      rewrite srcv_upd by list_solve.
      forward.
      assert (ES: (S / 2 ^ 8) mod 256 = S / 256) by (rewrite Z.mod_small; [reflexivity | ];
        split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      rewrite ES.
      replace (hs flg S) with [S mod 256; S / 256] by (unfold hs; rewrite F2; reflexivity).
      rewrite <- app_assoc. entailer!. }
    { assert (F2: flb flg 2 = false) by (apply ifl_false; try lia; rewrite <- and_repr; auto).
      forward. unfold hs. rewrite F2. rewrite app_nil_r, Z.add_0_r. entailer!. }
    pose proof (hs_len flg S) as Ls.
    set (l4 := l3 ++ hs flg S).
    assert (Z4: Zlength l4 = HL + Zlength (hs flg S)) by (subst l4; rewrite Zlength_app, Z3; reflexivity).
    assert (ET': T = Zlength l4 + 13) by (rewrite Z4, Ls; lia).
    st. st. st. st. st.
    set (l5 := l4 ++ [1] ++ [0] ++ [0] ++ [255] ++ [255]).
    match goal with |- context [srcv ?l T] => replace l with l5 by (subst l5; rewrite <- !app_assoc; reflexivity) end.
    assert (Z5: Zlength l5 = Zlength l4 + 5) by (subst l5; list_solve).
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx (data_at ?sh (tarray tuchar ?TT) _ ?p :: ?R)))) _ _ =>
      forward_for_simple_bound 8 (EX i: Z, PROPx [] (LOCALx Q
        (SEPx (data_at sh (tarray tuchar TT) (srcv (l5 ++ Zrepeat 0 i) TT) p :: R)))) end.
    { entailer!. rewrite app_nil_r. auto. }
    { st. rewrite zrep_snoc by lia. entailer!. }
    forward.
    set (g := IHG flg mtime xfl os bx bn bc delta).
    rewrite (res_eq flg) by lia. change (negb (Z.land flg 224 =? 0)) with (ih_reserved g).
    match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx [] (LOCALx (temp _t'32 (Vint (Int.repr (b2z (ih_badcrc g)))) :: Q) (SEPx R))) end.
    { assert (F2: flb flg 2 = true) by (apply ifl_true; rewrite <- and_repr; auto).
      forward. rewrite bad_eq by lia.
      replace (negb (Z.land delta 65535 =? 0)) with (ih_badcrc g)
        by (unfold ih_badcrc, fl; simpl g_flg; fold (flb flg 2); rewrite F2; reflexivity).
      entailer!. }
    { assert (F2: flb flg 2 = false) by (apply ifl_false; try lia; rewrite <- and_repr; auto).
      forward. entailer!. unfold ih_badcrc, fl. simpl g_flg. fold (flb flg 2). rewrite F2. reflexivity. }
    forward.
    unfold Kgoal in K.
    assert (E3: l3 = ih_hdr g) by (subst l3 g; rewrite <- !app_assoc; reflexivity).
    assert (ES: ih_stored g = S) by (unfold ih_stored; rewrite <- E3; reflexivity).
    assert (EG: ih_src g = l5 ++ Zrepeat 0 8).
    { unfold ih_src. rewrite ES, <- E3. subst l5 l4. unfold hs. rewrite <- !app_assoc. reflexivity. }
    assert (ET2: T = Zlength (l5 ++ Zrepeat 0 8)) by (rewrite Zlength_app, Z5, Zlength_Zrepeat by lia; lia).
    assert (F53: ih_f53 g (IHB w xmax nmax cmax xnul nnul cnul) (IHP src xf nf cf)).
    { unfold ih_f53, ih_ok. subst g. cbn [g_flg g_mtime g_xfl g_os g_xf g_nf g_cf g_delta b_w b_xmax b_nmax b_cmax
        b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf].
      repeat split; auto; try lia. }
    unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
    eapply semax_pre; [ | apply (K g F53) ].
    unfold ih_s53. rewrite EG. clear ET'. subst T. rewrite srcv_full.
    subst g. cbn [g_flg g_mtime g_xfl g_os g_xf g_nf g_cf g_delta b_w b_xmax b_nmax b_cmax
        b_xnul b_nnul b_cnul p_src p_xf p_nf p_cf v_s_ v_h_ v_xs_ v_ns_ v_cs_ v_osn_].
    entailer!.
Qed.
