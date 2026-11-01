(* Law inflate_decode, main: after the decode loop, the final checks, inflateEnd, return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.EnvBodies QuickProof.Assembly QuickProof.Pick.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.HarnessBytes Zlib.proof.adler32.HarnessRef
               Zlib.proof.adler32.MainLib.
Require Zlib.proof.crc32.HarnessRef.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.harness.inflate_common.HarnessLib.
Require Import Zlib.proof.harness.inflate_common.DRefSpec.
Require Import Zlib.proof.rfc1951.Decode.
Require Import Zlib.proof.harness.inflate_decode.IDLawCS Zlib.proof.harness.inflate_decode.IDGlobals.
Require Import Zlib.harness.x_inflate_decode.code.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.proof.harness.inflate_decode.IDMainKit.

Definition idt_strm_tuple : Type :=
  (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * (val * val)))))))))))))%type.

Lemma idt_strm_cs sh (v: idt_strm_tuple) q:
  @data_at Zlib.units.Inflate.CS sh Rep.t_strm v q = @data_at CS sh (Tstruct _z_stream_s noattr) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Definition idt_tup (gv: globals) (z: zfields) (sp: val) : idt_strm_tuple :=
  (zf_ni z, (Vint (Int.repr (zf_ai z)), (Vlong (Int64.repr (zf_tin z)), (zf_no z, (Vint (Int.repr (zf_ao z)),
   (Vlong (Int64.repr (zf_tout z)), (msg_val gv (zf_msg z), (sp, (gv Zlib.inflate.code._zcalloc,
   (gv Zlib.inflate.code._zcfree, (nullval, (Vint (Int.repr (zf_dt z)), (Vlong (Int64.repr (zf_adler z)),
   zf_res z))))))))))))).

Lemma idt_istream_unfold gv shs vs z L:
  istream gv shs vs z (Some L) =
  !! (zf_ok z /\ writable_share shs /\ live_ok L) &&
  (@data_at CS shs (Tstruct _z_stream_s noattr) (idt_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite idt_strm_cs.
  apply pred_ext; entailer!.
Qed.

Lemma idt_istream_fold gv shs vs z L:
  zf_ok z -> writable_share shs -> live_ok L ->
  (@data_at CS shs (Tstruct _z_stream_s noattr) (idt_tup gv z (l_sp L)) vs * state_mem gv vs L)%logic
  |-- istream gv shs vs z (Some L).
Proof. intros. rewrite idt_istream_unfold. entailer!. Qed.

Lemma idt_istream_none gv shs vs z:
  istream gv shs vs z None =
  !! (zf_ok z /\ writable_share shs) &&
  @data_at CS shs (Tstruct _z_stream_s noattr) (idt_tup gv z nullval) vs.
Proof.
  unfold istream, zstrm_at, strm_rep.
  rewrite idt_strm_cs. reflexivity.
Qed.

Lemma idt_istream_opt gv shs (vs: val) z st: isptr vs -> istream_opt gv shs vs z st = istream gv shs vs z st.
Proof. intros P. unfold istream_opt. destruct (eq_dec vs nullval); [subst; contradiction | reflexivity]. Qed.

Lemma id_tail_ok {Espec: OracleKind} gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr
    (Post: ret_assert) :
  RA_return Post = RA_return POST_id ->
  dec_facts G datap srcp isbp dcont scont isbz ls ->
  semax Delta_id (dec_post gv vw vll vlc vdc vs vosn G datap srcp isbp dcont scont isbz ls Fr) seg_tail Post.
Proof.
  intros HR HF.
  destruct Post as [Pn Pb Pc Pr]; simpl in HR; subst Pr.
  apply (semax_post (overridePost FF POST_id)); simpl RA_normal; simpl RA_break; simpl RA_continue;
    simpl RA_return; try (intros; apply andp_left2; intro rho; simpl; normalize; fail);
    try (intros; apply andp_left2, derives_refl).
  unfold seg_tail, dec_post, Delta_id, Gmain_k. simplify_func_tycontext. abbreviate_semax.
  Intros lim z L.
  destruct HF as (GOK & Hh & Pd & Ps & Pi & DOK & _).
  assert (HN: Zlength (full G) <= 262144) by (destruct DOK as (_ & ? & _); lia).
  rewrite idt_istream_unfold. Intros.
  assert_PROP (isptr vs) as Pvs by entailer!.
  (* gp_assert(opos == n) *)
  forward_call (Int.repr 1); [entailer!; simpl; rewrite Int.eq_true; reflexivity | ].
  (* gp_assert(s.total_out == n) *)
  forward.
  forward_call (Int.repr 1); [entailer!; simpl; rewrite H, Int64.eq_true; reflexivity | ].
  (* gp_assert(pos == slen) *)
  forward_call (Int.repr 1); [entailer!; simpl; rewrite Int.eq_true; reflexivity | ].
  (* inflateEnd(&s) *)
  sep_apply (idt_istream_fold gv Tsh vs z L); auto.
  forward_call (gv, Tsh, vs, z, Some L).
  { rewrite idt_istream_opt by auto. cancel. }
  rewrite idt_istream_opt, idt_istream_none by auto. Intros.
  (* return 0 *)
  forward. Exists (Int.repr 0). apply andp_right; [apply prop_right; reflexivity | ].
  sep_apply (data_at_data_at_ Tsh (Tstruct _z_stream_s noattr) (idt_tup gv z nullval) vs).
  cancel.
Qed.
