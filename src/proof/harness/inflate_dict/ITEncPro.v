(* Law inflate_dict, main encoder half: the prologue, from main's start to the block loop (statement in ITEncKit.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessRef Zlib.proof.adler32.HarnessBytes
               Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.harness.inflate_dict.ITLawCS Zlib.proof.harness.inflate_dict.ITGlobals
               Zlib.proof.harness.inflate_dict.ITFacts Zlib.proof.harness.inflate_dict.ITMainKit
               Zlib.proof.harness.inflate_dict.ITEncKit.
Require Import Zlib.harness.x_inflate_dict.code.
Require Import Zlib.proof.crc32.Spec.

(* hides an equation from entailer!'s subst *)
Definition itenc_hide (P: Prop) : Prop := P.

Ltac itenc_infeas := exfalso; first [ match goal with H: ?a <> ?b |- _ => solve [apply H; reflexivity] end
                                | match goal with H: _ |- _ => solve [discriminate H] end
                                | contradiction
                                | lia ].

Ltac itenc_nn := match goal with |- context [sem_cmp_pp Ceq ?p _] =>
  destruct p; try contradiction; try reflexivity; simpl in *; subst; contradiction end.

Ltac itenc_drop p R := match R with
  | data_at_ _ _ p :: ?R' => R'
  | ?a :: ?R' => let r := itenc_drop p R' in constr:(a :: r) end.

Lemma itenc_bytes_adler_cs_ sh n q:
  @data_at_ Zlib.units.Adler32.CS sh (tarray tuchar n) q = @data_at_ CS sh (tarray tuchar n) q.
Proof. unfold data_at_. apply bytes_adler_cs. Qed.

Lemma itenc_xor1 b: 0 <= b <= 255 ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.xor (Int.repr b) (Int.repr 1))) = Int.repr (Z.lxor b 1).
Proof.
  intros Hb. unfold Int.xor. rewrite !Int.unsigned_repr by rep_lia. rewrite !zext8.
  pose proof (IntFacts.lxor_lt_pow2 b 1 8 ltac:(lia) ltac:(change (2 ^ 8) with 256; lia) ltac:(change (2 ^ 8) with 256; lia)) as Hx.
  change (2 ^ 8) with 256 in Hx. rewrite Zmod_mod, (Z.mod_small (Z.lxor b 1) 256) by lia. auto.
Qed.

(* the bit writer after `w.buf = src; w.len = 0; w.nb = 0;` *)
Lemma itenc_bw_init N (srcp vw: val): 0 <= N ->
  data_at Tsh (Tstruct _bw noattr) (srcp, (Vint (Int.repr 0), Vint (Int.repr 0))) vw *
  data_at_ Ews (tarray tuchar N) srcp |-- bw_at Tsh Ews [] N srcp vw.
Proof.
  intros HN. rewrite bw_at_law. Exists (default_val (tarray tuchar N)). unfold data_at_. entailer!.
  unfold bw_bytes_ok. unfold default_val. simpl. rewrite Zlength_Zrepeat by lia.
  change (pack []) with (@nil Z). rewrite Zlength_nil. split; [auto | ]. split; [lia | ]. reflexivity.
Qed.

Lemma itenc_shl wb: 8 <= wb <= 15 -> Int.shl (Int.repr 1) (Int.repr wb) = Int.repr (2 ^ wb).
Proof.
  intros Hw. assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; reflexivity.
Qed.

Lemma itenc_len_bits v n: 0 <= n -> Zlength (bits_le v n) = n.
Proof. intros. unfold bits_le. rewrite Zlength_map, Zlength_correct, seq_length. lia. Qed.

Lemma itenc_cmf wb: 8 <= wb <= 15 ->
  Int.or (Int.shl (Int.sub (Int.repr wb) (Int.repr 8)) (Int.repr 4)) (Int.repr 8) = Int.repr ((wb - 8) * 16 + 8).
Proof.
  intros Hw. assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; reflexivity.
Qed.

Lemma itenc_land3_range fl: 0 <= Z.land fl 3 <= 3.
Proof.
  split; [apply Z.land_nonneg; lia | ].
  replace (Z.land fl 3) with (Z.land fl (Z.ones 2)) by reflexivity. rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound fl (2 ^ 2) ltac:(lia)). change (2 ^ 2) with 4 in *. lia.
Qed.

Lemma itenc_and3 fl: 0 <= fl <= 255 -> Int.and (Int.repr fl) (Int.repr 3) = Int.repr (Z.land fl 3).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma itenc_flg0 fl: 0 <= fl <= 3 ->
  Int.or (Int.shl (Int.repr fl) (Int.repr 6)) (Int.repr 32) = Int.repr (fl * 64 + 32).
Proof.
  intros Hf. assert (fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; reflexivity.
Qed.

Lemma itenc_flg wb fl: 8 <= wb <= 15 -> 0 <= fl <= 3 ->
  Int.add (Int.repr (fl * 64 + 32))
    (Int.modu (Int.sub (Int.repr 31)
       (Int.modu (Int.add (Int.shl (Int.repr ((wb - 8) * 16 + 8)) (Int.repr 8)) (Int.repr (fl * 64 + 32)))
          (Int.repr 31))) (Int.repr 31)) =
  Int.repr (fl * 64 + 32 + (31 - (((wb - 8) * 16 + 8) * 256 + (fl * 64 + 32)) mod 31) mod 31).
Proof.
  intros Hw Hf. assert (wb = 8 \/ wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14 \/ wb = 15) by lia.
  assert (fl = 0 \/ fl = 1 \/ fl = 2 \/ fl = 3) by lia.
  repeat match goal with H: _ \/ _ |- _ => destruct H end; subst; reflexivity.
Qed.

Ltac itenc_dropbw w R := match R with
  | bw_at _ _ _ _ _ w :: ?R' => R'
  | ?a :: ?R' => let r := itenc_dropbw w R' in constr:(a :: r) end.

Ltac itenc_room := try unfold bw_room;
  match goal with HN: itenc_hide (_ = 2 ^ 19 /\ _) |- _ => let Hr := fresh "Hr" in destruct HN as [Hr _]; rewrite Hr end;
  rewrite ?Zlength_app, ?itenc_len_bits, ?Zlength_nil by lia; change (2 ^ 19) with 524288;
  change Int.max_unsigned with 4294967295; repeat split;
  first [ lia | apply Z.div_le_upper_bound; lia
        | reflexivity
        | match goal with |- context [?a mod 256] => pose proof (Z.mod_pos_bound a 256 ltac:(lia)); lia end ].
Ltac itenc_mod8 := rewrite ?Zlength_app, ?itenc_len_bits, ?Zlength_nil by lia; reflexivity.

Ltac itenc_bwcall v := match goal with |- context [bw_at Tsh Ews ?B ?N ?sp ?w] =>
  forward_call (Tsh, Ews, B, N, sp, w, v) end.

(* (unsigned char) (dictid >> k) and (unsigned char) dictid *)
Lemma itenc_byte_shr d k: 0 <= d < 2 ^ 32 -> 0 <= k < 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (eval_binop Oshr tulong tint (Vlong (Int64.repr d)) (Vint (Int.repr k))))
  = Vint (Int.repr (Z.shiftr d k mod 256)).
Proof.
  intros Hd Hk. unfold eval_binop, eval_cast. simpl.
  rewrite Int.unsigned_repr by rep_lia. rewrite !Int64.Z_mod_modulus_eq.
  assert (Hm: Int64.modulus = 2 ^ 64) by reflexivity.
  rewrite Hm, (Z.mod_small d) by lia. rewrite (Z.mod_small k) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= d / 2 ^ k <= d).
  { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | ]].
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
  rewrite Z.mod_small by lia. rewrite !zext8, Zmod_mod. auto.
Qed.

Lemma itenc_byte_shr2 d k: 0 <= d < 2 ^ 32 -> 0 <= k < 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (force_val (sem_shift_li
    (fun (sg : signedness) (n1 n2 : int64) => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
    Unsigned (Vlong (Int64.repr d)) (Vint (Int.repr k)))))
  = Vint (Int.repr (Z.shiftr d k mod 256)).
Proof.
  intros Hd Hk. rewrite <- (itenc_byte_shr d k Hd Hk). unfold eval_binop, sem_binary_operation', sem_shr, sem_shift_li.
  simpl. rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma itenc_byte_lo2 d: 0 <= d < 2 ^ 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (Vlong (Int64.repr d))) = Vint (Int.repr (Z.shiftr d 0 mod 256)).
Proof.
  intros Hd. unfold eval_cast. simpl. rewrite !Int64.Z_mod_modulus_eq.
  assert (Hm: Int64.modulus = 2 ^ 64) by reflexivity.
  rewrite Hm, (Z.mod_small d) by lia. rewrite !zext8, Zmod_mod. auto.
Qed.

Lemma itenc_hdr_bits wb fl d cmfv flgv: cmfv = (wb - 8) * 16 + 8 ->
  flgv = fl * 64 + 32 + (31 - (cmfv * 256 + (fl * 64 + 32)) mod 31) mod 31 ->
  ((((([] ++ bits_le cmfv 8) ++ bits_le flgv 8) ++ bits_le (Z.shiftr d 24 mod 256) 8) ++
     bits_le (Z.shiftr d 16 mod 256) 8) ++ bits_le (Z.shiftr d 8 mod 256) 8) ++ bits_le (Z.shiftr d 0 mod 256) 8
  = bytes_bits (zlib_hdr wb fl true ++ be_bytes d 4).
Proof.
  intros -> ->.
  replace (zlib_hdr wb fl true ++ be_bytes d 4) with
    [(wb - 8) * 16 + 8; fl * 64 + 32 + (31 - (((wb - 8) * 16 + 8) * 256 + (fl * 64 + 32)) mod 31) mod 31;
     Z.shiftr d 24 mod 256; Z.shiftr d 16 mod 256; Z.shiftr d 8 mod 256; Z.shiftr d 0 mod 256] by reflexivity.
  unfold bytes_bits. cbn [flat_map]. rewrite app_nil_r, app_nil_l, <- !app_assoc. reflexivity.
Qed.

Lemma itenc_edata_nil E: edata E [] = [].
Proof. unfold edata, data, expand. simpl. apply sublist_nil. Qed.

Lemma itenc_byte_lo d: 0 <= d < 2 ^ 32 ->
  eval_cast tuchar tuchar (eval_cast tulong tuchar (Vlong (Int64.repr d))) = Vint (Int.repr (Z.shiftr d 0 mod 256)).
Proof.
  intros Hd. unfold eval_cast. simpl. rewrite !Int64.Z_mod_modulus_eq.
  assert (Hm: Int64.modulus = 2 ^ 64) by reflexivity.
  rewrite Hm, (Z.mod_small d) by lia. rewrite !zext8, Zmod_mod. auto.
Qed.

Ltac itenc_types := match goal with |- context [eval_cast (typeof ?e1) tuchar (eval_cast (typeof ?e2) tuchar _)] =>
  change (typeof e1) with tuchar; change (typeof e2) with tulong end.

(* the bits so far as an opaque variable (forward_call diverges on the concrete list otherwise) *)
Ltac itenc_absB := match goal with |- context [bw_at Tsh Ews ?B _ _ _] =>
  let Bv := fresh "Bv" in let HB := fresh "HB" in let HBh := fresh "HBh" in
  remember B as Bv eqn:HB; assert (HBh: itenc_hide (Bv = B)) by exact HB; clear HB end.
Ltac itenc_unB := repeat match goal with H: itenc_hide (@eq (list bool) ?x _) |- _ => unfold itenc_hide in H; subst x end.

Ltac show := match goal with |- semax _ ?P _ _ => fail 100 "PRE" P | |- ?G => fail 100 "GOAL" G end.

Lemma seg_pro_ok {Espec: OracleKind} : seg_pro_stmt.
Proof.
  intros gv vw vs vosn vdl K.
  unfold pro_pre, S_main, Delta_m, Gmain_k, POST_m. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros wrap.
  forward_call tt. Intros flevel.
  forward_call tt. Intros isel.
  forward_call tt. Intros wsel.
  forward_call tt. Intros wb.
  forward_call tt. Intros dlen.
  ifpost _t'7 (Int.repr (if andb (8 <=? wb) (wb <=? 15) then 1 else 0)).
  { forward. entailer!. arg_cmp. }
  { forward. entailer!. arg_cmp. }
  forward_call (Int.repr (if andb (8 <=? wb) (wb <=? 15) then 1 else 0)).
  assumed. apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
  forward_call (Int.repr (if dlen <=? 2^16 then 1 else 0)).
  { entailer!. change (Int.shl (Int.repr 1) (Int.repr 16)) with (Int.repr (2 ^ 16)). arg_cmp. }
  assumed. apply Z.leb_le in E.
  forward.
  forward_call (tarray tuchar dlen, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros dictp.
  set (blen := if dlen =? 0 then 1 else dlen).
  assert (Hbl: 1 <= blen <= 2 ^ 16) by (subst blen; destruct (Z.eqb_spec dlen 0); lia).
  ifpost _t'9 (Int.repr blen).
  { forward. entailer!. }
  { forward. entailer!. subst blen. rewrite (proj2 (Z.eqb_neq dlen 0)) by auto. reflexivity. }
  forward_call (tarray tuchar blen, gv).
  { simpl. rewrite Z.max_r by lia. rep_lia. }
  Intros badp. forward.
  remember (2 ^ 19) as N19 eqn:HN19. remember (2 ^ 18) as N18 eqn:HN18.
  assert (HN: itenc_hide (N19 = 2 ^ 19 /\ N18 = 2 ^ 18)) by (split; assumption). clear HN19 HN18.
  forward_call (tarray tuchar N18, gv).
  { entailer!. destruct HN as [_ ->]. reflexivity. }
  { destruct HN as [_ ->]. simpl. rep_lia. }
  Intros datap.
  forward_call (tarray tuchar N19, gv).
  { entailer!. destruct HN as [-> _]. reflexivity. }
  { destruct HN as [-> _]. simpl. rep_lia. }
  Intros srcp.
  destruct (eq_dec dictp nullval) as [ND|ND].
  { subst dictp.
    ifpost _t'13 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    ifpost _t'14 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    ifpost _t'15 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    forward_if. { ret0. } { itenc_infeas. } }
  Intros.
  destruct (eq_dec badp nullval) as [NB|NB].
  { subst badp.
    ifpost _t'13 (Int.repr 1). { itenc_infeas. } { forward. entailer!. }
    ifpost _t'14 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    ifpost _t'15 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    forward_if. { ret0. } { itenc_infeas. } }
  Intros.
  ifpost _t'13 (Int.repr 0). { itenc_infeas. } { forward. entailer!. itenc_nn. }
  destruct (eq_dec datap nullval) as [NA|NA].
  { subst datap.
    ifpost _t'14 (Int.repr 1). { itenc_infeas. } { forward. entailer!. }
    ifpost _t'15 (Int.repr 1). { forward. entailer!. } { itenc_infeas. }
    forward_if. { ret0. } { itenc_infeas. } }
  Intros.
  ifpost _t'14 (Int.repr 0). { itenc_infeas. } { forward. entailer!. itenc_nn. }
  destruct (eq_dec srcp nullval) as [NS|NS].
  { subst srcp.
    ifpost _t'15 (Int.repr 1). { itenc_infeas. } { forward. entailer!. }
    forward_if. { ret0. } { itenc_infeas. } }
  Intros.
  ifpost _t'15 (Int.repr 0). { itenc_infeas. } { forward. entailer!. itenc_nn. }
  forward_if. { itenc_infeas. }
  assert_PROP (isptr dictp /\ isptr badp /\ isptr datap /\ isptr srcp) as Pp by entailer!.
  destruct Pp as (Pdict & Pbad & Pdata & Psrc).
  forward_call (dictp, dlen, Ews).
  { rewrite if_false by exact ND. cancel. }
  Intros dict. rewrite if_false by exact ND.
  match goal with H: Zlength dict = dlen |- _ => rename H into Hdl end.
  match goal with H: Forall _ dict |- _ => rename H into Hdb end.
  fold (bytes_rep dict). subst dlen.
  ifpost _t'16 (Int.repr blen).
  { forward. entailer!. subst blen. destruct (Z.eqb_spec (Zlength dict) 0); first [reflexivity | lia]. }
  { forward. entailer!. subst blen. destruct (Z.eqb_spec (Zlength dict) 0); first [reflexivity | lia]. }
  forward.
  set (badl := match dict with [] => [0] | b :: r => Z.lxor b 1 :: r end).
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := itenc_drop badp R in
    forward_if (PROPx [] (LOCALx Q (SEPx (data_at Ews (tarray tuchar blen) (bytes_rep badl) badp :: R')))) end.
  { assert (dict = []) by (apply Zlength_nil_inv; lia). subst dict.
    assert (Eb: blen = 1) by reflexivity. clearbody blen. subst blen.
    forward. entailer!. }
  { assert (Eb: blen = Zlength dict) by (subst blen; destruct (Z.eqb_spec (Zlength dict) 0); lia).
    rewrite Eb.
    forward_call (badp, Ews, dictp, Ews, dictp, 0, Zlength dict, bytes_rep dict, Zlength dict, dict).
    { rewrite itenc_bytes_adler_cs_, bytes_adler_cs. cancel. }
    { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
      rewrite sublist_same by (rewrite ?Zlength_bytes_rep; lia). repeat split; auto; lia. }
    rewrite ?bytes_adler_cs.
    destruct dict as [|b r]; [rewrite Zlength_nil in H6; contradiction | ].
    forward.
    { entailer!. inversion Hdb; subst. rewrite Int.unsigned_repr by rep_lia. rep_lia. }
    change (Znth 0 (bytes_rep (b :: r))) with (Vint (Int.repr b)).
    forward. entailer!.
    rewrite Eb, itenc_xor1 by (inversion Hdb; subst; rep_lia).
    change (bytes_rep (b :: r)) with (Vint (Int.repr b) :: bytes_rep r). rewrite upd_Znth0. cancel. }
  (* the call alone (with the rest, forward_call does not finish) *)
  eapply semax_seq'.
  { forward_call (1, dictp, Ews, dictp, 0, Zlength dict, bytes_rep dict, Zlength dict, dict).
    { rewrite bytes_adler_cs. cancel. }
    { unfold cbuf_ok. rewrite isptr_offset_val_zero by auto.
      rewrite sublist_same by (rewrite ?Zlength_bytes_rep; lia). repeat split; auto; lia. }
    forward. rewrite bytes_adler_cs. apply ENTAIL_refl. }
  abbreviate_semax.
  forward. forward. forward.
  sep_apply (itenc_bw_init N19 srcp vw ltac:(destruct HN as [-> _]; lia)).
  forward.
  { entailer!. change (Int.unsigned Int.iwordsize) with 32. lia. }
  rewrite itenc_shl by lia.
  set (zl := negb (wrap =? 0)).
  replace (Z.b2z (negb (zeq wrap 0))) with (if zl then 1 else 0)
    by (subst zl; destruct (zeq wrap 0), (Z.eqb_spec wrap 0); try lia; reflexivity).
  set (did := ref_adler32 1 dict).
  assert (Hdid: 0 <= did < 2 ^ 32).
  { apply (Zlib.proof.adler32.Model.ref_adler32_valid 1 dict).
    unfold Zlib.proof.adler32.Model.adler_valid, Zlib.proof.adler32.Model.adler_lo,
      Zlib.proof.adler32.Model.adler_hi, Zlib.proof.adler32.Model.ADLER_BASE. cbn. lia. }
  assert (Edid: did = ref_adler32 1 dict) by reflexivity. clearbody did.
  assert (Ezl: zl = negb (wrap =? 0)) by reflexivity. clearbody zl.
  (* dictid's value opaque: forward_call on `(unsigned char) (dictid >> k)` diverges otherwise *)
  remember (Vlong (Int64.repr did)) as vd eqn:HVD.
  assert (HVDh: itenc_hide (vd = Vlong (Int64.repr did))) by exact HVD. clear HVD.
  assert (ZX: forall v, 0 <= v <= 255 -> Int.zero_ext 8 (Int.repr v) = Int.repr v).
  { intros v Hv. rewrite zext8, Z.mod_small by lia. auto. }
  match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
    let R' := itenc_dropbw vw R in
    forward_if (PROPx [] (LOCALx Q (SEPx (bw_at Tsh Ews (bytes_bits (if zl then zlib_hdr wb (Z.land flevel 3) true
                                              ++ be_bytes did 4 else [])) N19 srcp vw :: R')))) end.
  { destruct zl; [ | contradiction]. 
    forward. forward. forward.
    pose proof (itenc_land3_range flevel) as Hfl.
    rewrite (itenc_and3 flevel), (itenc_cmf wb), (itenc_flg0 (Z.land flevel 3)), (itenc_flg wb (Z.land flevel 3))
      by rep_lia.
    set (cmfv := (wb - 8) * 16 + 8).
    set (flgv := Z.land flevel 3 * 64 + 32 + (31 - (cmfv * 256 + (Z.land flevel 3 * 64 + 32)) mod 31) mod 31).
    assert (Hcmf: 0 <= cmfv <= 255) by (subst cmfv; lia).
    assert (Hflg: 0 <= flgv <= 255).
    { subst flgv. pose proof (Z.mod_pos_bound (31 - (cmfv * 256 + (Z.land flevel 3 * 64 + 32)) mod 31) 31 ltac:(lia)).
      lia. }
    assert (Ecmf: cmfv = (wb - 8) * 16 + 8) by reflexivity.
    assert (Eflg: flgv = Z.land flevel 3 * 64 + 32 + (31 - (cmfv * 256 + (Z.land flevel 3 * 64 + 32)) mod 31) mod 31)
      by reflexivity.
    clearbody cmfv flgv.
    itenc_bwcall cmfv. { entailer!. simpl. rewrite !ZX by lia. reflexivity. } { itenc_room. }
    itenc_bwcall flgv. { entailer!. simpl. rewrite !ZX by lia. reflexivity. } { itenc_room. }
    itenc_absB. itenc_bwcall (Z.shiftr did 24 mod 256).
    { entailer!. unfold itenc_hide in HVDh. subst vd. cbn [firstn length].
      itenc_types.
      rewrite itenc_byte_shr2 by lia. destruct vw; try contradiction; reflexivity. }
    { itenc_unB. itenc_room. }
    itenc_absB. itenc_bwcall (Z.shiftr did 16 mod 256).
    { entailer!. unfold itenc_hide in HVDh. subst vd. cbn [firstn length].
      itenc_types.
      rewrite itenc_byte_shr2 by lia. destruct vw; try contradiction; reflexivity. }
    { itenc_unB. itenc_room. }
    itenc_absB. itenc_bwcall (Z.shiftr did 8 mod 256).
    { entailer!. unfold itenc_hide in HVDh. subst vd. cbn [firstn length].
      itenc_types.
      rewrite itenc_byte_shr2 by lia. destruct vw; try contradiction; reflexivity. }
    { itenc_unB. itenc_room. }
    itenc_absB. itenc_bwcall (Z.shiftr did 0 mod 256).
    { entailer!. unfold itenc_hide in HVDh. subst vd. cbn [firstn length].
      itenc_types.
      rewrite itenc_byte_lo2 by lia. destruct vw; try contradiction; reflexivity. }
    { itenc_unB. itenc_room. }
    itenc_unB.
    rewrite (itenc_hdr_bits wb (Z.land flevel 3) did cmfv flgv Ecmf Eflg).
    entailer!. }
  { destruct zl; [itenc_infeas | ]. forward. entailer!. }
  forward.
  set (Ec := EC gv vw vs vosn vdl dictp badp datap srcp zl wb flevel isel wsel dict).
  unfold abbreviate in MORE_COMMANDS, POSTCONDITION. subst MORE_COMMANDS POSTCONDITION.
  eapply semax_pre; [ | apply (K Ec)].
  assert (Hbl2: Zlength badl = blen).
  { subst badl blen. destruct dict as [|b r]; [reflexivity | ]. rewrite !Zlength_cons. pose proof (Zlength_nonneg r).
    rewrite (proj2 (Z.eqb_neq _ 0)) by lia. reflexivity. }
  unfold itenc_hide in HVDh. subst vd.
  unfold blk_inv. Exists (@nil block) (default_val (tarray tuchar N18)).
  unfold blk_at, enc_fr. rewrite itenc_edata_nil.
  unfold blk_bits. change (enc_nf 0 []) with (@nil bool). rewrite app_nil_r.
  unfold hdr_bytes, edictid, ebad. subst Ec.
  cbn [e_gv e_vw e_vs e_vosn e_vdl e_dictp e_badp e_datap e_srcp e_zlib e_wb e_flevel e_isel e_wsel e_dict].
  rewrite <- Edid. change (match dict with [] => [0] | b :: r => Z.lxor b 1 :: r end) with badl. rewrite Hbl2.
  (* the object sizes as N19 / N18 (entailer! overflows the stack on the literals) *)
  destruct HN as [HN19 HN18]. rewrite <- HN19, <- HN18.
  assert (HNh: itenc_hide (N19 = 2 ^ 19 /\ N18 = 2 ^ 18)) by (split; auto). clear HN19 HN18.
  unfold data_at_.
  entailer!.
  unfold itenc_hide in HNh. destruct HNh as [_ HN18].
  split; [ | split].
  - unfold ectx_ok; cbn [e_wb e_flevel e_isel e_wsel e_dict e_dictp e_badp e_datap e_srcp].
    repeat split; auto; rep_lia.
  - unfold enc_ok. split; [constructor | exact I].
  - unfold data_ok. unfold default_val. simpl. rewrite Zlength_Zrepeat by lia.
    split; [auto | ]. split; [rewrite Zlength_nil; lia | ]. split; [constructor | ]. reflexivity.
Qed.
