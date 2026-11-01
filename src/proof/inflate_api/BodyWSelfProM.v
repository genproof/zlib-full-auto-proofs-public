(* The middle of inflate()'s prologue in the allocator-generic port, after the tests of inflateStateCheck() and
   of next_out == Z_NULL: the test of next_in == Z_NULL && avail_in != 0 with its return (Z_STREAM_ERROR,
   inflate_bad; BodyWSelfProB.v), then BodyWSelfProT.v's pro_tail_za.  It holds for any output object (the
   output's malloc token is not used).  The script is the middle of za/inflate_api/Body5Pro.v's pro_part5_za (the
   prologue is cut in parts so that each file checks quickly). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.za.inflate_api.Body5Parts.
Require Import Zlib.proof.za.inflate_api.Body5Conv.
Require Import Zlib.proof.za.inflate_api.Body5Pro.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.za.inflate.ZAV.
Require Import Zlib.proof.za.inflate.ZEvents.
Require Import Zlib.proof.za.inflate.ZTac.
Require Zlib.proof.inflate.InvW.
Require Import Zlib.proof.inflate_api.BodyWSelfProL.
Require Import Zlib.proof.inflate_api.BodyWSelfProT.
Require Import Zlib.proof.inflate_api.BodyWSelfProB.
Require Import Zlib.proof.crc32.Spec.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.
Local Opaque denote_tc_test_eq.
Section ZAlloc.
Context {ZA : Zlib.proof.zutil.ZAlloc.zallocator} {ZAV : Zlib.proof.za.inflate.ZAV.adler_cell}.

Definition pro_chk_mid_za_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (L: live)
    (ib: inbuf) (inp: list Z) (osh: share) (op: val) (olo on: Z) (oc: list val) (flush: Z) (gsh tsh: share)
    (itok otok: bool) (vh vl vb: val) (tr: list zev) (R: ret_assert),
  in_tok_ok itok ib -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  zf_no z = out_ptr (OutBuf osh op olo on oc) 0 ->
  out_ok (OutBuf osh op olo on oc) (zf_ao z) ->
  strmp <> nullval -> zf_ok z -> writable_share shs -> live_ok L ->
  (inflate_bad strmp z (Some L) ib (Some (OutBuf osh op olo on oc)) ->
   ENTAIL Delta_inflate5_za,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt_za gv shs strmp z (Some L); head_opt (Some L);
              bufs_opt (Some L) ib (Some (OutBuf osh op olo on oc)) [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; za_res gv tr; zfuncs_za gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5_za (pro_chk_za gv shs strmp z L ib osh op olo on oc flush gsh tsh itok otok vh vl vb tr)
    inflate_chk_mid
    (overridePost (pro_post_za gv shs strmp z (Some L) ib inp (Some (OutBuf osh op olo on oc)) flush gsh tsh
       itok otok vh vl vb tr) R).

Lemma pro_chk_mid_za : pro_chk_mid_za_stmt.
Proof.
intros Espec gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr R
  HIT HNI HIB HNO HOO NN ZOK WS LOK HBAD.
destruct R as [Rn Rb Rc Rr]. simpl RA_return in HBAD.
pose proof LOK as (LP & LS & LM & LH & LS3 & LW & LW0 & LHD & LWIN).
assert (ISL: is_live strmp (Some L) = Some L).
{ unfold is_live. destruct (eq_dec strmp nullval); [contradiction | reflexivity]. }
pose proof HOO as (OW & OP & OL & OA & ON & OC & OM).
unfold pro_chk_za.
remember za_alloc as zca eqn:Hzca. remember za_free as zcf eqn:Hzcf.
cbv beta iota zeta delta [inflate_chk_mid f_inflate fn_body].
assert (DEC: (ib = InNull /\ zf_ai z <> 0) \/ ~ (ib = InNull /\ zf_ai z <> 0)).
{ destruct ib; [destruct (Z.eq_dec (zf_ai z) 0); [right; intros [_ ?]; auto | left; auto]
              | right; intros [? _]; discriminate]. }
destruct DEC as [BADI | GOODI].
{ (* next_in = Z_NULL, avail_in > 0: Z_STREAM_ERROR *)
  subst zca zcf.
  apply (@pro_chk_bad_za ZA ZAV _ gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr
           (Build_ret_assert Rn Rb Rc Rr)); auto. }
forward_if (temp _t'3 (Vint (Int.repr 0))).
{ dead_branch. }
{ destruct ib as [|ish ip ilo ilen ic].
  - (* next_in = Z_NULL, avail_in = 0 *)
    assert (AI0: zf_ai z = 0) by (destruct (Z.eq_dec (zf_ai z) 0); auto; contradiction GOODI; auto).
    simpl in HNI. rewrite HNI, AI0.
    forward.
    forward_if.
    { forward. forward. forward. rewrite HNI, AI0. entailer!. }
    { dead_branch. }
  - (* an input object *)
    destruct HIB as [HIO HIA]. pose proof HIO as (IR & IP & IL & ILN & IC & IM & IB & IBO).
    pose proof (Zlength_nonneg inp).
    simpl in HNI. rewrite HNI, Z.add_0_r.
    forward.
    forward_if.
    { simpl in_rep. simpl in_tok. entailer!. apply tc_test_eq_null; [destruct ip; try contradiction; exact I | ].
      sep_apply (bytes_wvp ish ip ilo (Zlength ic) ic itok); [rep_lia | ].
      apply sepcon_weak_valid_pointer1, derives_refl. }
    { exfalso. destruct ip; try contradiction. match goal with H: offset_val _ _ = nullval |- _ => inv H end. }
    { forward. rewrite HNI, Z.add_0_r. entailer!. apply derives_refl. } }
forward_if.
{ dead_branch. }
(* state = strm->state and the rest *)
subst zca zcf.
apply (@pro_tail_za ZA ZAV _ gv shs strmp z L ib inp osh op olo on oc flush gsh tsh itok otok vh vl vb tr
         (Build_ret_assert Rn Rb Rc Rr)); auto.
Qed.

End ZAlloc.
