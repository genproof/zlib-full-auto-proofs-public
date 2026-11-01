(* Law rt_session (harness/rt_session.c), main's final checks with a header (SMKit.segE_9_stmt, statements 74-84):
   the kit of the proof (SMSegE9.v), rt_gzip_header's G2MS7Kit.v on this program.

   [got_view9]: got's memory after the inflate loop (RTH8Spec.head_mem8 read with G2IFacts.g2_hdr_out) as got's
   struct with the values main checks ([gotv]) and, for each field present in main's header (bits 2, 4, 8 of
   choice), got's buffer holding its bytes ([gfield]); [hobjs_view9]: the copies of extra, name and comment made
   before compression, which the checks compare got's buffers with, at the compspecs of same_field.  The
   decompressor's struct is read by the checks of next_in and next_out ([istream8_view]), the compressor is not read
   any more ([cstream_back9]).  [Q9]: main's state between the header checks (the structs got and head, the locals'
   memory, and the buffers and copies the remaining checks read). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.deflate.DSpec.
Require Zlib.proof.deflate.Api_toend.
Require Zlib.proof.harness.bound_common.BoundKit.
Require Import Zlib.proof.inflate_api.Bodies5.
Require Import Zlib.proof.inflate_api.SpecW.
Require Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTH8Spec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.rt_session.SCS.
Require Import Zlib.proof.harness.rt_session.SIFacts.
Require Import Zlib.proof.harness.rt_session.SMainStmt.
Require Import Zlib.proof.harness.rt_session.SMKit.
Require Zlib.proof.harness.rt_stream.USegE.
Require Zlib.proof.roundtrip.RTDIface Zlib.proof.harness.rt_stream.UDFacts.
Require Zlib.proof.harness.rt_gzip_header.G2MS7Kit.
Require Import Zlib.harness.rt_session.code.
#[local] Existing Instance SCS.CS.
Local Open Scope logic.

Module E9S5 := Zlib.proof.inflate_api.Spec5.
Module E9H8 := Zlib.proof.roundtrip.RTH8Spec.
Module E9H6 := Zlib.proof.roundtrip.RTHSpec.
Module E9K7 := Zlib.proof.harness.rt_gzip_header.G2MS7Kit.

(** ** The decompressor and the compressor *)

(* the decompressor's struct z_stream as main reads it *)
Definition istrm9 (gv : globals) (z : zfields) (sp : val) : reptype t_z :=
  (zf_ni z, (vi (zf_ai z), (vl (zf_tin z), (zf_no z, (vi (zf_ao z), (vl (zf_tout z), (msg_val gv (zf_msg z),
   (sp, (gv Zlib.inflate.code._zcalloc, (gv Zlib.inflate.code._zcfree, (nullval, (vi (zf_dt z),
   (vl (zf_adler z), zf_res z))))))))))))).

Lemma strm_cs9 sh (v : reptype t_z) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_strm v q = data_at sh t_z v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

Lemma istream8_view gv vd z L :
  E9H8.istream8 gv Tsh vd z (Some L) |-- data_at Tsh t_z (istrm9 gv z (l_sp L)) vd * TT.
Proof.
  unfold E9H8.istream8, E9S5.zstrm_at, Zlib.proof.inflate.Rep.strm_rep.
  rewrite strm_cs9. Intros. cancel.
Qed.

(* at the return: the compressor, whatever deflate's state, gives back the local's memory *)
Lemma cstream_back9 (gv : globals) (vc ghp : val) (c : cst) : cstream gv vc ghp c |-- data_at_ Tsh t_z vc * TT.
Proof.
  unfold cstream, srest.
  sep_apply (BoundKit.dstream_data_at_ (Some (cs_s c)) vc ghp gv (cs_ni c) (cs_ain c) (cs_tin c) (cs_no c)
               (cs_aout c) (cs_tout c) (cs_msgv c) (cs_adler c) Api_toend.dstream_to_end).
  rewrite (@data_at__change_composite Zlib.proof.deflate.DCS.CS CS CC_dcs Ews Zlib.proof.deflate.Rep.t_strm)
    by reflexivity.
  rewrite (BoundKit.data_at__Tsh_split t_z vc). cancel.
Qed.

(** ** The checks of next_in, next_out and the bytes *)

(* a pointer into or one past a malloc'ed byte object is weakly valid, so comparing it with itself is defined *)
Local Transparent denote_tc_test_eq.
Lemma test_eq_self9 (R : mpred) (p : val) (lo n : Z) (contents : list val) :
  0 <= lo <= n -> isptr p ->
  (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
  |-- denote_tc_test_eq (offset_val lo p) (offset_val lo p).
Proof.
  intros Hlo Pp.
  assert (W : (malloc_token Ews (tarray tuchar n) p * data_at Ews (tarray tuchar n) contents p) * R
              |-- weak_valid_pointer (offset_val lo p)).
  { apply sepcon_weak_valid_pointer1.
    apply (cbuf_weak_valid true Ews Ews p lo n contents); auto. }
  destruct p; try contradiction. unfold denote_tc_test_eq, offset_val, test_eq_ptrs.
  unfold sameblock. destruct (peq b b) as [E | NE]; [ | congruence]. cbn [proj_sumbool].
  apply andp_right; apply W.
Qed.
Local Opaque denote_tc_test_eq.

(* byte objects at the compspecs of bytes_eq's and same_field's specifications (the adler32 unit's) *)
Lemma bytes_a9 sh n (v : list val) q :
  @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q = data_at sh (tarray tuchar n) v q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_adler32); [apply JMeq_refl | reflexivity]. Qed.

(** ** got after the inflate loop *)

(* a pointer field of got: the buffer when bit m of choice is set, else Z_NULL *)
Definition gq (u : setup) (m : Z) (q : val) : val := if Z.land (su_choice u) m =? 0 then nullval else q.

(* got as main reads it: done 1, text and hcrc as 0/1 flags, os & 255, time, the pointers of the present fields;
   xflags anything, extra_len anything (the extra field's length when it is present) *)
Definition gotv (u : setup) (vxf vxl : val) : reptype t_g :=
  (vi (if su_text u =? 0 then 0 else 1), (vl (su_time u), (vxf, (vi (Z.land (su_os u) 255),
   (gq u 2 (su_gxp u), (vxl, (vi (Zlength (su_xf u)), (gq u 4 (su_gnp u), (vi (Zlength (su_nm u) + 1),
   (gq u 8 (su_gcp u), (vi (Zlength (su_cm u) + 1), (vi (if su_hcrc u =? 0 then 0 else 1), vi 1)))))))))))).

(* got's buffer of n bytes for a present field: the bytes l, at the compspecs of same_field *)
Definition gfield (u : setup) (m : Z) (q : val) (n : Z) (l : list Z) : mpred :=
  if Z.land (su_choice u) m =? 0 then emp
  else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q.

(* the gz_header struct at inflate.c's compspecs is got at main's *)
Lemma head_cs9 sh (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head
    (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) q =
  @data_at CS sh t_g (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* what g2_hdr_out says of one field of main's header: absent, it is reported Z_NULL; present, with its bytes *)
Lemma hdr_field9 (u : setup) (m : Z) (l : list Z) (P : list Z -> Prop) (Q : Prop) :
  match selo u m l with None => Q | Some x => P x end ->
  (Z.land (su_choice u) m =? 0 = true -> Q) /\ (Z.land (su_choice u) m =? 0 = false -> P l).
Proof.
  unfold selo, has. destruct (Z.land (su_choice u) m =? 0); cbn; intro H; split; intro E; try discriminate E;
  exact H.
Qed.

Lemma nbtok_tok9 q n : isptr q -> 0 <= n ->
  Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |-- @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q.
Proof.
  intros Hq Hn. unfold Zlib.proof.inflate.CaseHyps5.btok, nbtok.
  rewrite if_false by (intros ->; exact Hq).
  destruct (zeq n 0); [ subst; rewrite sepcon_emp | rewrite emp_sepcon ];
    rewrite ?(E9K7.tok_cs8 Zlib.units.Inflate.CS Zlib.units.Adler32.CS), ?(E9K7.tok_cs8 CS Zlib.units.Adler32.CS);
    apply derives_refl.
Qed.

Lemma bytes_cs9 sh n (v : list val) q :
  @data_at Zlib.units.Inflate.CS sh (tarray tuchar n) v q = @data_at Zlib.units.Adler32.CS sh (tarray tuchar n) v q.
Proof.
  rewrite bytes_a9. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity].
Qed.

(* one of got's buffers after the header modes: present, its first n bytes are l (all of it) *)
Lemma buf_view9 (b : bool) q n l lx c cont :
  isptr q -> 0 <= n -> (b = false -> c = n /\ sublist 0 n cont = l) -> E9H6.bufok6 lx n c cont ->
  E9H6.hbuf6 q n lx * Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |--
  (if b then emp else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
                      @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q) * TT.
Proof.
  intros Hq Hn Hb (Hl & Hc & Hs). rewrite sepcon_assoc. sep_apply (nbtok_tok9 q n Hq Hn).
  unfold E9H6.hbuf6. rewrite if_false by (intros ->; exact Hq).
  destruct b; [ cancel | ].
  destruct (Hb eq_refl) as [-> Hsub]. rewrite sublist_same in Hs by auto. rewrite Hs, Hsub.
  rewrite bytes_cs9. unfold Zlib.proof.zutil.Libc.byte_vals, bytes_rep. cancel.
Qed.

(* the same for a defined header (Spec5's head_rep) *)
Lemma buf_viewd9 (b : bool) q n l cont :
  isptr q -> 0 <= n -> Zlength cont = n -> (b = false -> sublist 0 n cont = l) ->
  Zlib.proof.inflate.Rep.hbuf_rep q n cont * Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |--
  (if b then emp else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
                      @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q) * TT.
Proof.
  intros Hq Hn Hl Hb. rewrite sepcon_assoc. sep_apply (nbtok_tok9 q n Hq Hn).
  unfold Zlib.proof.inflate.Rep.hbuf_rep. rewrite if_false by (intros ->; exact Hq).
  destruct b; [ cancel | ].
  specialize (Hb eq_refl). rewrite sublist_same in Hb by auto. subst l.
  rewrite bytes_cs9. unfold Zlib.proof.zutil.Libc.byte_vals, bytes_rep. cancel.
Qed.

(* the facts of su_ok the checks use *)
Lemma su_ok_e9 (u : setup) : su_ok u ->
  0 <= su_choice u <= 255 /\ Zlength (su_xf u) <= 65535 /\ RTDIface.rbytes (su_xf u) /\
  Zlength (su_nm u) <= 4294967294 /\ nzbytes (su_nm u) /\ Zlength (su_cm u) <= 4294967294 /\ nzbytes (su_cm u) /\
  Zlength (su_data u) <= UDFacts.max_size /\ RTDIface.rbytes (su_data u) /\
  RTDIface.rs32 (su_text u) /\ 0 <= su_time u <= 4294967295 /\ RTDIface.rs32 (su_os u) /\ RTDIface.rs32 (su_hcrc u) /\
  isptr (su_xcp u) /\ isptr (su_ncp u) /\ isptr (su_ccp u) /\ isptr (su_ep u) /\ isptr (su_op u) /\
  isptr (su_gxp u) /\ isptr (su_gnp u) /\ isptr (su_gcp u).
Proof. unfold su_ok, su_dok. intuition. Qed.

(* got's memory after the inflate loop: g2_hdr_out read on head_mem8 (either of its post-header forms) *)
Lemma got_view9 (u : setup) (L : live) (vg : val) :
  su_ok u -> g2_hdr_out (gh_of u) (h0 u) (l_s L) (l_h L) -> IR.i_head (l_s L) = true -> got_at u vg L ->
  E9H8.head_mem8 L * gtoks u |--
  EX vxf : val, EX vxl : val, !! (Z.land (su_choice u) 2 =? 0 = false -> vxl = vi (Zlength (su_xf u))) &&
  (data_at Tsh t_g (gotv u vxf vxl) vg * gfield u 2 (su_gxp u) (Zlength (su_xf u)) (su_xf u) *
   gfield u 4 (su_gnp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0]) *
   gfield u 8 (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0]) * TT).
Proof.
  intros Hg Ho Hi (Hp & Hs & Hx & Hn & Hc).
  set (h := l_h L) in *. set (s := l_s L) in *.
  destruct Ho as (_ & Hm & Hd & Ht & Hhc & Hos & Htm & Hxm & Hnm & Hcm & Fx & Fn & Fc).
  unfold gh_of in *; cbn [RTK7.DS7.gz_extra RTK7.DS7.gz_name RTK7.DS7.gz_comment RTK7.DS7.gz_text RTK7.DS7.gz_time
                          RTK7.DS7.gz_os RTK7.DS7.gz_hcrc] in *.
  cbn [h0 IR.h_extra_max IR.h_name_max IR.h_comm_max] in Hxm, Hnm, Hcm.
  pose proof (hdr_field9 u 2 (su_xf u)
    (fun x => IR.h_xp h = true /\ E9H6.fextra s = true /\ IR.h_extra_len h = Zlength x /\ E9H8.cxa h = Zlength x /\
              sublist 0 (Zlength x) (IR.h_xbuf h) = x) _ Fx) as [Fx0 Fx1].
  pose proof (hdr_field9 u 4 (su_nm u ++ [0])
    (fun l => IR.h_np h = true /\ E9H8.cna h = Zlength l /\ sublist 0 (Zlength l) (IR.h_nbuf h) = l) _ Fn)
    as [Fn0 Fn1].
  pose proof (hdr_field9 u 8 (su_cm u ++ [0])
    (fun l => IR.h_cp h = true /\ E9H8.cca h = Zlength l /\ sublist 0 (Zlength l) (IR.h_cbuf h) = l) _ Fc)
    as [Fc0 Fc1].
  cbv beta in Fx1, Fn1, Fc1. clear Fx Fn Fc.
  assert (Ex : (if IR.h_xp h then su_gxp u else nullval) = gq u 2 (su_gxp u)).
  { unfold gq. destruct (Z.land (su_choice u) 2 =? 0) eqn:E;
      [ rewrite (Fx0 eq_refl) | rewrite (proj1 (Fx1 eq_refl)) ]; reflexivity. }
  assert (En : (if IR.h_np h then su_gnp u else nullval) = gq u 4 (su_gnp u)).
  { unfold gq. destruct (Z.land (su_choice u) 4 =? 0) eqn:E;
      [ rewrite (Fn0 eq_refl) | rewrite (proj1 (Fn1 eq_refl)) ]; reflexivity. }
  assert (Ec : (if IR.h_cp h then su_gcp u else nullval) = gq u 8 (su_gcp u)).
  { unfold gq. destruct (Z.land (su_choice u) 8 =? 0) eqn:E;
      [ rewrite (Fc0 eq_refl) | rewrite (proj1 (Fc1 eq_refl)) ]; reflexivity. }
  pose proof (su_ok_e9 u Hg) as (_ & Lx & _ & Ln & _ & Lc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Px & Pn & Pc).
  assert (Ln1 : Zlength (su_nm u ++ [0]) = Zlength (su_nm u) + 1) by (rewrite Zlength_app; reflexivity).
  assert (Lc1 : Zlength (su_cm u ++ [0]) = Zlength (su_cm u) + 1) by (rewrite Zlength_app; reflexivity).
  pose proof (Zlength_nonneg (su_xf u)) as Z1. pose proof (Zlength_nonneg (su_nm u)) as Z2.
  pose proof (Zlength_nonneg (su_cm u)) as Z3.
  unfold E9H8.head_mem8, gtoks. fold s h. rewrite Hi, Hp, Hs, Hx, Hn, Hc, Hxm, Hnm, Hcm.
  rewrite !distrib_orp_sepcon. apply orp_left; [apply orp_left |].
  - Intros. unfold Zlib.proof.inflate.Rep.head_rep. rewrite Ex, En, Ec, Hxm, Hnm, Hcm, head_cs9.
    match goal with H : Zlib.proof.inflate.Inv.hwf _ |- _ => destruct H as [_ _ _ _ _ _ _ _ [Hxw _] [Hnw _] [Hcw _] _ _] end.
    sep_apply (buf_viewd9 (Z.land (su_choice u) 2 =? 0) (su_gxp u) (Zlength (su_xf u)) (su_xf u) (IR.h_xbuf h) Px
      ltac:(lia) ltac:(lia) (fun E => proj2 (proj2 (proj2 (proj2 (Fx1 E)))))).
    sep_apply (buf_viewd9 (Z.land (su_choice u) 4 =? 0) (su_gnp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0])
      (IR.h_nbuf h) Pn ltac:(lia) ltac:(lia) (fun E => ltac:(rewrite <- Ln1; exact (proj2 (proj2 (Fn1 E)))))).
    sep_apply (buf_viewd9 (Z.land (su_choice u) 8 =? 0) (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0])
      (IR.h_cbuf h) Pc ltac:(lia) ltac:(lia) (fun E => ltac:(rewrite <- Lc1; exact (proj2 (proj2 (Fc1 E)))))).
    Exists (vi (IR.h_xflags h)) (vi (IR.h_extra_len h)).
    unfold gotv, gfield, vi, vl. rewrite Ht, Hhc, Hos, Htm, Hd.
    apply andp_right; [ apply prop_right; intros E; rewrite (proj1 (proj2 (proj2 (Fx1 E)))); reflexivity | ].
    cancel.
  - Intros. congruence.
  - Intros. unfold E9H8.head_rep8a, E9H6.head_rep6p. Intros vt vtm vxf vos vxl vhc lx ln lc.
    rewrite Ex, En, Ec, Hxm, Hnm, Hcm, head_cs9.
    rewrite Hxm in H4. rewrite Hnm in H5. rewrite Hcm in H6.
    sep_apply (buf_view9 (Z.land (su_choice u) 2 =? 0) (su_gxp u) (Zlength (su_xf u)) (su_xf u) lx (E9H8.cxa h)
      (IR.h_xbuf h) Px ltac:(lia) (fun E => ltac:(destruct (Fx1 E) as (_ & _ & _ & -> & Hsx);
                                                  split; [reflexivity | exact Hsx])) H4).
    sep_apply (buf_view9 (Z.land (su_choice u) 4 =? 0) (su_gnp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0]) ln
      (E9H8.cna h) (IR.h_nbuf h) Pn ltac:(lia) (fun E => ltac:(destruct (Fn1 E) as (_ & -> & Hsx); rewrite <- Ln1;
                                                               split; [reflexivity | exact Hsx])) H5).
    sep_apply (buf_view9 (Z.land (su_choice u) 8 =? 0) (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0]) lc
      (E9H8.cca h) (IR.h_cbuf h) Pc ltac:(lia) (fun E => ltac:(destruct (Fc1 E) as (_ & -> & Hsx); rewrite <- Lc1;
                                                               split; [reflexivity | exact Hsx])) H6).
    Exists vxf vxl.
    rewrite (H ltac:(lia)), (H0 ltac:(lia)), (proj2 (H1 ltac:(lia))), (H3 ltac:(lia)).
    unfold gotv, gfield, vi, vl. rewrite Ht, Hhc, Hos, Htm, Hd.
    apply andp_right; [ apply prop_right; intros E; destruct (Fx1 E) as (_ & Hf & Hl & _);
                        rewrite (H2 ltac:(lia) Hf), Hl; reflexivity | ].
    cancel.
Qed.

(** ** The copies of head's fields as same_field reads them *)
Definition hx9 (u : setup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (su_xf u))) (bytes_rep (su_xf u)) (su_xcp u).
Definition hn9 (u : setup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (su_nm u) + 1)) (bytes_rep (su_nm u ++ [0])) (su_ncp u).
Definition hc9 (u : setup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength (su_cm u) + 1)) (bytes_rep (su_cm u ++ [0])) (su_ccp u).

(* head's objects and the tokens of the copies are not needed any more *)
Lemma hobjs_view9 (u : setup) : hobjs u |-- hx9 u * hn9 u * hc9 u * TT.
Proof.
  unfold hobjs, hcopies, bobj, hx9, hn9, hc9. rewrite !Zlength_app. cbn [Zlength Datatypes.length Z.of_nat].
  rewrite !bytes_a9. unfold bytes_rep, vi. cancel.
Qed.

(** ** The comparisons of the checks *)

Lemma gq_pn9 (u : setup) (m : Z) (q : val) : isptr q -> is_pointer_or_null (gq u m q).
Proof. intros Hq. unfold gq. destruct (_ =? 0); [ simpl; auto | destruct q; try contradiction; exact I ]. Qed.

(* same_field's answer for a field of main's header: 1 *)
Lemma sf_one9 (u : setup) (m : Z) (q : val) (l : list Z) : isptr q ->
  (if Z.land (su_choice u) m =? 0 then 1
   else if eq_dec (gq u m q) nullval then 0 else if list_eq_dec Z.eq_dec l l then 1 else 0) = 1.
Proof.
  intros Hq. unfold gq. destruct (Z.land (su_choice u) m =? 0); [ reflexivity | ].
  rewrite if_false by (intros ->; exact Hq).
  destruct (list_eq_dec Z.eq_dec l l); [ reflexivity | congruence ].
Qed.

(* same_field's precondition for a field of main's header: got's buffer when present, and the copy *)
Lemma sf_pre9 (u : setup) (m : Z) (q given : val) (n : Z) (l : list Z) :
  gfield u m q n l * @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) given |--
  (if Z.land (su_choice u) m =? 0 then emp
   else (if eq_dec (gq u m q) nullval then emp
         else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) (gq u m q) *
              @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) (gq u m q)) *
        @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) given) * TT.
Proof.
  unfold gfield, gq. destruct (Z.land (su_choice u) m =? 0); [ cancel | ].
  destruct (eq_dec q nullval); cancel.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead. *)
Ltac e9_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in e9_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := e9_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The statements and the states between them *)

(* statements 74-77 (asked, next_in, next_out and the bytes, !with_head), 78-83 (the header checks), 84 (return) *)
Definition E74_77 : statement :=
  ltac:(let x := eval cbv [take suf segE] in (take 4 segE) in exact x).
Definition E78 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 4 segE)) in exact x).
Definition E79 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 5 segE)) in exact x).
Definition E80 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 6 segE)) in exact x).
Definition E81 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 7 segE)) in exact x).
Definition E82 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 8 segE)) in exact x).
Definition E83 : statement := ltac:(let x := eval cbv [take suf segE] in (take 1 (suf 9 segE)) in exact x).
Definition E84 : statement := ltac:(let x := eval cbv [take suf segE] in (suf 10 segE) in exact x).

Definition segE_parts : statement :=
  Ssequence E74_77 (Ssequence E78 (Ssequence E79 (Ssequence E80 (Ssequence E81 (Ssequence E82
    (Ssequence E83 E84)))))).

Lemma segE_split : unfold_Ssequence segE = unfold_Ssequence segE_parts.
Proof. reflexivity. Qed.

(* statement 78 cut in three: its first test (done, text), its second test (hcrc), its gp_assert *)
Definition E78a : statement :=
  ltac:(let x := eval cbv [E78] in (match E78 with Ssequence (Ssequence a _) _ => a | _ => Sskip end) in exact x).
Definition E78b : statement :=
  ltac:(let x := eval cbv [E78] in (match E78 with Ssequence (Ssequence _ b) _ => b | _ => Sskip end) in exact x).
Definition E78c : statement :=
  ltac:(let x := eval cbv [E78] in (match E78 with Ssequence _ c => c | _ => Sskip end) in exact x).

Lemma E78_split : E78 = Ssequence (Ssequence E78a E78b) E78c.
Proof. reflexivity. Qed.

(* statement 79 cut in two: its test (os, time), its gp_assert *)
Definition E79a : statement :=
  ltac:(let x := eval cbv [E79] in (match E79 with Ssequence a _ => a | _ => Sskip end) in exact x).
Definition E79b : statement :=
  ltac:(let x := eval cbv [E79] in (match E79 with Ssequence _ b => b | _ => Sskip end) in exact x).

Lemma E79_split : E79 = Ssequence E79a E79b.
Proof. reflexivity. Qed.

(* the locals main reads in the header checks *)
Definition locals9 (gv : globals) (vh vg vc va vd : val) (u : setup) : list localdef :=
  c_locals u ++ d_locals u (rts_iw (su_wbits u)) ++ lvs gv vh vg vc va vd.

(* main's state between the header checks: got (vxl its extra_len, defined when the extra field is present), head
   (not read; given back at the return), the memory of the other locals, and [rest]: the buffers and copies of the
   checks still to come; [tl]: the temporaries of a statement in progress *)
Definition Q9 (gv : globals) (vh vg vc va vd : val) (u : setup) (vxf vxl : val) (tl : list localdef)
    (rest : list mpred) : environ -> mpred :=
  PROPx [su_ok u; with_head u = true; Z.land (su_choice u) 2 =? 0 = false -> vxl = vi (Zlength (su_xf u))]
  (LOCALx (tl ++ locals9 gv vh vg vc va vd u)
  (SEPx (data_at Tsh t_g (gotv u vxf vxl) vg :: data_at Tsh t_g (hvals u) vh :: data_at_ Tsh t_z vd ::
         data_at_ Tsh t_z vc :: data_at_ Tsh t_p va :: mem_mgr gv :: TT :: rest))).

(* the rests before statement 78 (and 79, 80), 81 (and 82), 83 *)
Definition rest78 (u : setup) : list mpred :=
  [gfield u 2 (su_gxp u) (Zlength (su_xf u)) (su_xf u); gfield u 4 (su_gnp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0]);
   gfield u 8 (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0]); hx9 u; hn9 u; hc9 u].
Definition rest81 (u : setup) : list mpred :=
  [gfield u 4 (su_gnp u) (Zlength (su_nm u) + 1) (su_nm u ++ [0]);
   gfield u 8 (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0]); hn9 u; hc9 u].
Definition rest83 (u : setup) : list mpred := [gfield u 8 (su_gcp u) (Zlength (su_cm u) + 1) (su_cm u ++ [0]); hc9 u].
