(* Law deflate_bound, main: part_bound (MainKit.v): bound = deflateBound(&s, n); the compressBound checks;
   ob = malloc(bound); if (ob == NULL) return 0 (msuf 40 -> msuf 45). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DCS Zlib.proof.deflate.Rep Zlib.proof.deflate.DSpec.
Require Zlib.proof.compress.CSpec.
Require Import Zlib.proof.deflate.LawFacts Zlib.proof.deflate.HarnessLib Zlib.proof.deflate.GlobalsInit.
Require Import Zlib.proof.deflate.Obligations.
Require Import Zlib.proof.harness.deflate_bound.MainKit.
Require Import Zlib.harness.x_deflate_bound.code.
Require Zlib.proof.harness.bound_common.BoundKit.
#[local] Existing Instance DCS.CS.
Local Open Scope logic.

Lemma cb_range (n : Z) : 0 <= c_compressBound n <= Int64.max_unsigned.
Proof.
  unfold c_compressBound, compressBound_z.
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - cbv; split; discriminate.
  - unfold u64. match goal with |- context [?a mod ?m] => pose proof (Z.mod_pos_bound a m) end.
    change Int64.max_unsigned with (2^64-1). lia.
Qed.

Lemma bd_override_normal Delta (P Q : environ -> mpred) (R : ret_assert) :
  ENTAIL Delta, P |-- Q -> ENTAIL Delta, P |-- RA_normal (overridePost Q R).
Proof. intros H. destruct R. exact H. Qed.

(* a branch excluded by the value of its test *)
Ltac nob := exfalso; first [ congruence | exact (Int.one_not_zero ltac:(assumption)) | contradiction ].

(* the values of the tests: the booleans by cases, the hypotheses of the branches as Z facts *)
Ltac vcl :=
  unfold bool2val in *;
  repeat match goal with
  | |- context [Int.eq ?x ?y] => pose proof (Int.eq_spec x y); destruct (Int.eq x y)
  end;
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  | H : context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b)
  end;
  cbn [negb andb orb] in *;
  repeat match goal with
  | H : Int.repr 0 <> Int.zero |- _ => exfalso; exact (H eq_refl)
  | H : Int.repr 1 = Int.zero |- _ => exfalso; exact (Int.one_not_zero H)
  | H : Int.repr ?x = Int.repr ?y |- _ =>
      apply repr_inj_signed in H; [| unfold repable_signed, s32 in *; rep_lia ..]
  | H : Int.repr ?x <> Int.repr ?y |- _ => assert (x <> y) by congruence; clear H
  end;
  first [ reflexivity | lia | exfalso; lia ].

(* the return of main after deflateBound: the stream and h give back main's locals *)
Lemma bnd_ret_close (gv : globals) (vs vh ghp : val) (s : dstate) (hx : share * val * val * val) (Hr : mpred)
    (nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  ob_dstream_to_end -> hclose vh s ghp hx Hr ->
  dstream 2 (Some s) vs ghp gv * hdr_at (Some s) ghp hx * api_fields vs nin ain tin nout aout tout msgv adler *
  data_at_ (Share.comp Ews) t_strm vs * Hr * BoundKit.strm_pad vs
  |-- data_at_ Tsh t_strm vs * data_at_ Tsh t_gzh vh * TT.
Proof.
  intros HOB HC.
  sep_apply (BoundKit.dstream_data_at_ (Some s) vs ghp gv nin ain tin nout aout tout msgv adler HOB).
  sep_apply (HC s eq_refl).
  rewrite (BoundKit.data_at__Tsh_split t_strm vs). unfold BoundKit.Ecomp. cancel.
Qed.

Ltac bnull gv vs vh ghp st hx Hr HOB :=
  forward; Exists (Int.repr 0); unfold st_fields, srest; entailer!;
  sep_apply (bnd_ret_close gv vs vh ghp (st_s st) hx Hr nullval (st_ain st) (st_tin st) nullval (st_aout st)
               (st_tout st) (st_msgv st) (st_adler st) HOB ltac:(assumption));
  cancel.

(* ob = malloc(bound); if (ob == NULL) return 0; then the continuation at msuf45 *)
Ltac btail gv vs vh ghp st hx Hr HOB b HK :=
  forward_call (tarray tuchar b, gv);
  [ simpl; rewrite Z.max_r by lia; rep_lia | ];
  let obp := fresh "obp" in
  Intros obp;
  let Pob := fresh "Pob" in
  destruct (eq_dec obp nullval) as [Pob | Pob];
  [ subst obp; forward_if False; [ bnull gv vs vh ghp st hx Hr HOB | nob ]
  | Intros;
    ifsame; [ nob | forward; apply bd_override_normal; entailer! | ];
    eapply semax_pre; [| apply (HK b obp)];
    unfold A4; entailer! ].

(* v5: deflateBound takes strm->next_in separately: the caller's fields without it *)
Definition af_rest (sp : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) : mpred :=
  !! (u32_ok ain /\ u64_ok tin /\ u32_ok aout /\ u64_ok tout /\ u64_ok adler) &&
  (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_in) (vi ain) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_in) (vl tin) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_out) nout sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._avail_out) (vi aout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._total_out) (vl tout) sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._msg) msgv sp *
   @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._adler) (vl adler) sp).

Lemma af_split (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  api_fields sp nin ain tin nout aout tout msgv adler =
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler.
Proof.
  unfold api_fields, af_rest. apply pred_ext; entailer!.
Qed.

Lemma af_join (sp nin : val) (ain tin : Z) (nout : val) (aout tout : Z) (msgv : val) (adler : Z) :
  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) nin sp * af_rest sp ain tin nout aout tout msgv adler
  |-- api_fields sp nin ain tin nout aout tout msgv adler.
Proof. rewrite af_split. apply derives_refl. Qed.

Lemma part_bound {Espec : OracleKind} (Bpre : bpre_inv) (Brun : brun_inv) (gv : globals) (vs vh : val)
    (bs : bsetup) (st : bstrm) (ghp : val) (hx : share * val * val * val) (Hr : mpred) :
  ob_dstream_to_end ->
  (forall b obp, semax Delta_m (A4 Bpre Brun gv vs vh bs st ghp hx Hr b obp) msuf45 POST_m) ->
  semax Delta_m (A3 Bpre Brun gv vs vh bs st ghp hx Hr) msuf40 POST_m.
Proof.
  intros HOB HK.
  unfold msuf40, A3.
  abbreviate_semax.
  Intros.
  unfold bs_locals; cbn [app].
  pose proof H as BS. pose proof H0 as BF.
  destruct (bf_bound _ _ BF _ _ _ _ _ _ _ _ _ (b_n bs) H1) as (b & Hb & Hbr & Hcb & HBr).
  { destruct BS as (_ & _ & _ & _ & _ & Hn & _). exact Hn. }
  assert (Hn : 0 <= b_n bs <= 1048576) by (destruct BS as (_ & _ & _ & _ & _ & Hn & _); exact Hn).
  unfold st_fields. rewrite af_split.
  forward_call (Some (st_s st), vs, nullval, ghp, hx, b_n bs, b, gv).
  all: try (cancel; fail). all: try (unfold u64_ok; rep_lia; fail).
  sep_apply (af_join vs nullval (st_ain st) (st_tin st) nullval (st_aout st) (st_tout st) (st_msgv st) (st_adler st)).
  fold (st_fields vs st).
  pose proof (bf_cbound _ _ BF (b_n bs) Hn) as Hcn.
  forward_call (b_n bs).
  pose proof (cb_range (b_n bs)) as Hcr.
  forward_call Int.one.
  { entailer!. simpl.
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt _ _); [lia | reflexivity]. }
  destruct BS as (Hl & Hw & Hm & _).
  destruct (ds_of bs) eqn:Eds.
  { ifpost _t'43 Int.zero.
    { exfalso. exact (Int.one_not_zero ltac:(assumption)). }
    { forward. apply bd_override_normal. entailer!. }
    ifpost _t'44 Int.zero.
    { nob. }
    { forward. apply bd_override_normal. entailer!. }
    ifpost _t'45 Int.zero.
    { nob. }
    { forward. apply bd_override_normal. entailer!. }
    ifsame.
    { nob. }
    { forward. apply bd_override_normal. entailer!. }
    btail gv vs vh ghp st hx Hr HOB b HK. }
  set (c43 := ((b_level bs =? 6) || (b_level bs =? -1))%bool).
  ifpost _t'43 (Int.repr (if c43 then 1 else 0)).
  { forward_if.
    - forward. apply bd_override_normal. entailer!. unfold c43. vcl.
    - forward. forward. apply bd_override_normal. entailer!. unfold c43. vcl. }
  { nob. }
  ifpost _t'44 (Int.repr (if (c43 && (b_wbits bs =? 15))%bool then 1 else 0)).
  { forward. apply bd_override_normal. entailer!. unfold c43 in *. vcl. }
  { forward. apply bd_override_normal. entailer!. unfold c43 in *. vcl. }
  ifpost _t'45 (Int.repr (if (c43 && (b_wbits bs =? 15) && (b_mem bs =? 8))%bool then 1 else 0)).
  { forward. apply bd_override_normal. entailer!. unfold c43 in *. vcl. }
  { forward. apply bd_override_normal. entailer!. unfold c43 in *. vcl. }
  ifsame.
  { assert (Hc : b <= c_compressBound (b_n bs)).
    { unfold c43 in *.
      repeat match goal with H : context [?a =? ?b] |- _ => destruct (Z.eqb_spec a b) end;
      cbn [andb orb] in *;
      first [ exfalso; match goal with H : Int.repr 0 <> Int.zero |- _ => exact (H eq_refl) end
            | apply Hcb; auto ]. }
    forward_call (b_n bs).
    forward_call Int.one.
    { entailer!. simpl. unfold Int64.ltu. rewrite !Int64.unsigned_repr by rep_lia.
      destruct (zlt _ _); [lia | reflexivity]. }
    apply bd_override_normal. entailer!. }
  { forward. apply bd_override_normal. entailer!. }
  btail gv vs vh ghp st hx Hr HOB b HK.
Qed.
