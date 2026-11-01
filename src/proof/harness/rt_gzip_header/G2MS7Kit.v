(* Law rt_gzip_header, main's body, segment 7 (G2MainKit.seg7_stmt), statements 48-54 of main (the six checks and
   the return): the kit of the proof.

   [got_view]: got's memory after the inflate loop (RTH8Spec.head_mem8 read with G2IFacts.g2_hdr_out) as got's
   struct with the values main checks ([gotv]) and, for each field present in main's header, got's buffer holding
   its bytes ([gfield]); [hobjs_view]: the copies of extra, name and comment made before compression, which the
   checks compare got's buffers with, at the compspecs of same_field (head's struct and original objects are not
   read any more).  The flags, os and time are compared with main's locals text, hcrc, os and time.  [Q7]: main's
   state between the checks (the struct got, the struct head, and the buffers and copies the remaining checks
   read).  The statements S40 .. S46 (named after round 2's statement numbers, as the assertions of G2MainKit.v)
   are proved in G2MS7A1.v, G2MS7A.v .. G2MS7F.v (one file per statement or two: a file with all of them takes
   minutes to check), and assembled in G2MainSeg7.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract QuickProof.Env QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.harness.rt_gzip_header.CS.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainDefs.
Require Import Zlib.proof.deflate.Rep.
Require Import Zlib.proof.harness.rt_gzip_header.G2MainKit.
Require Zlib.proof.roundtrip.RTHSpec Zlib.proof.roundtrip.RTH8Spec.
Require Zlib.proof.harness.rt_gzip_header.G2IFacts.
Require Import Zlib.harness.rt_gzip_header.code.
#[local] Existing Instance Zlib.proof.harness.rt_gzip_header.CS.CS.
Local Open Scope logic.

Module S5 := Zlib.proof.inflate_api.Spec5.
Module IR := Zlib.proof.inflate.Records.
Module H8 := Zlib.proof.roundtrip.RTH8Spec.
Module H6 := Zlib.proof.roundtrip.RTHSpec.

(** ** got after the inflate loop *)

(* a pointer field of got: the buffer when bit m of present is set, else Z_NULL *)
Definition gq (g : gsetup) (m : Z) (q : val) : val := if Z.land (g_pr g) m =? 0 then nullval else q.

(* got as main reads it: done 1, text and hcrc as 0/1 flags, os & 255, time, the pointers of the present fields;
   xflags anything, extra_len anything (the extra field's length when it is present) *)
Definition gotv (g : gsetup) (vxf vxl : val) : reptype t_g :=
  (vi (if g_text g =? 0 then 0 else 1), (vl (g_time g), (vxf, (vi (Z.land (g_os g) 255), (gq g 1 (g_gxp g),
   (vxl, (vi (g_xl g), (gq g 2 (g_gnp g), (vi (g_nl g + 1), (gq g 4 (g_gcp g), (vi (g_cl g + 1),
   (vi (if g_hcrc g =? 0 then 0 else 1), vi 1)))))))))))).

(* got's buffer of n bytes for a present field: the bytes l, at the compspecs of same_field *)
Definition gfield (g : gsetup) (m : Z) (q : val) (n : Z) (l : list Z) : mpred :=
  if Z.land (g_pr g) m =? 0 then emp
  else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q.

(* the gz_header struct at inflate.c's compspecs is got at main's *)
Lemma head_cs8 sh (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : val) q :
  @data_at Zlib.units.Inflate.CS sh Zlib.proof.inflate.Rep.t_head
    (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) q =
  @data_at CS sh t_g (a1, (a2, (a3, (a4, (a5, (a6, (a7, (a8, (a9, (a10, (a11, (a12, a13)))))))))))) q.
Proof. apply equal_f; apply (@data_at_change_composite _ _ CC_inflate); [apply JMeq_refl | reflexivity]. Qed.

(* what g2_hdr_out says of one field of main's header: absent, it is reported Z_NULL; present, with its bytes *)
Lemma hdr_field (g : gsetup) (m : Z) (l : list Z) (P : list Z -> Prop) (Q : Prop) :
  match selo g m l with None => Q | Some x => P x end ->
  (Z.land (g_pr g) m =? 0 = true -> Q) /\ (Z.land (g_pr g) m =? 0 = false -> P l).
Proof. unfold selo, has. destruct (Z.land (g_pr g) m =? 0); cbn; intro H; split; intro E; try discriminate E; exact H. Qed.

(* the malloc token of a byte array is the same at every compspecs *)
Lemma tok_cs8 (cs1 cs2 : compspecs) sh n q :
  @malloc_token cs1 sh (tarray tuchar n) q = @malloc_token cs2 sh (tarray tuchar n) q.
Proof. apply equal_f. apply (@malloc_token_change_composite cs1 cs2 (CCE_any cs1 cs2)). reflexivity. Qed.

Lemma nbtok_tok q n : isptr q -> 0 <= n ->
  Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |-- @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q.
Proof.
  intros Hq Hn. unfold Zlib.proof.inflate.CaseHyps5.btok, nbtok.
  rewrite if_false by (intros ->; exact Hq).
  destruct (zeq n 0); [ subst; rewrite sepcon_emp | rewrite emp_sepcon ];
    rewrite ?(tok_cs8 Zlib.units.Inflate.CS Zlib.units.Adler32.CS), ?(tok_cs8 CS Zlib.units.Adler32.CS);
    apply derives_refl.
Qed.

(* one of got's buffers after the header modes: present, its first n bytes are l (all of it) *)
Lemma buf_view6 (b : bool) q n l lx c cont :
  isptr q -> 0 <= n -> (b = false -> c = n /\ sublist 0 n cont = l) -> H6.bufok6 lx n c cont ->
  H6.hbuf6 q n lx * Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |--
  (if b then emp else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
                      @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q) * TT.
Proof.
  intros Hq Hn Hb (Hl & Hc & Hs). rewrite sepcon_assoc. sep_apply (nbtok_tok q n Hq Hn).
  unfold H6.hbuf6. rewrite if_false by (intros ->; exact Hq).
  destruct b; [ cancel | ].
  destruct (Hb eq_refl) as [-> Hsub]. rewrite sublist_same in Hs by auto. rewrite Hs, Hsub.
  rewrite (data_at_tuchar_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS). unfold Zlib.proof.zutil.Libc.byte_vals, bytes_rep. cancel.
Qed.

(* the same for a defined header (Spec5's head_rep) *)
Lemma buf_viewd (b : bool) q n l cont :
  isptr q -> 0 <= n -> Zlength cont = n -> (b = false -> sublist 0 n cont = l) ->
  Zlib.proof.inflate.Rep.hbuf_rep q n cont * Zlib.proof.inflate.CaseHyps5.btok q n * nbtok q n |--
  (if b then emp else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) q *
                      @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) q) * TT.
Proof.
  intros Hq Hn Hl Hb. rewrite sepcon_assoc. sep_apply (nbtok_tok q n Hq Hn).
  unfold Zlib.proof.inflate.Rep.hbuf_rep. rewrite if_false by (intros ->; exact Hq).
  destruct b; [ cancel | ].
  specialize (Hb eq_refl). rewrite sublist_same in Hb by auto. subst l.
  rewrite (data_at_tuchar_cs Zlib.units.Inflate.CS Zlib.units.Adler32.CS). unfold Zlib.proof.zutil.Libc.byte_vals, bytes_rep. cancel.
Qed.

(* got's memory after the inflate loop: g2_hdr_out read on head_mem8 (either of its post-header forms) *)
Lemma got_view (g : gsetup) (L1 : S5.live) (vg : val) :
  gs_ok g -> GI.g2_hdr_out (gh_of g) (h0 g) (S5.l_s L1) (S5.l_h L1) -> IR.i_head (S5.l_s L1) = true ->
  S5.l_headp L1 = vg -> S5.l_hsh L1 = Tsh ->
  S5.l_xb L1 = g_gxp g -> S5.l_nb L1 = g_gnp g -> S5.l_cb L1 = g_gcp g ->
  H8.head_mem8 L1 * gtoks g |--
  EX vxf : val, EX vxl : val, !! (Z.land (g_pr g) 1 =? 0 = false -> vxl = vi (g_xl g)) &&
  (data_at Tsh t_g (gotv g vxf vxl) vg * gfield g 1 (g_gxp g) (g_xl g) (g_xf g) *
   gfield g 2 (g_gnp g) (g_nl g + 1) (g_nm g ++ [0]) * gfield g 4 (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]) * TT).
Proof.
  intros Hg Ho Hi Hp Hs Hx Hn Hc.
  set (h := S5.l_h L1) in *. set (s := S5.l_s L1) in *.
  destruct Ho as (_ & Hm & Hd & Ht & Hhc & Hos & Htm & Hxm & Hnm & Hcm & Fx & Fn & Fc).
  unfold gh_of in *; cbn [DS.gz_extra DS.gz_name DS.gz_comment DS.gz_text DS.gz_time DS.gz_os DS.gz_hcrc] in *.
  cbn [h0 IR.h_extra_max IR.h_name_max IR.h_comm_max] in Hxm, Hnm, Hcm.
  pose proof (hdr_field g 1 (g_xf g)
    (fun x => IR.h_xp h = true /\ H6.fextra s = true /\ IR.h_extra_len h = Zlength x /\ H8.cxa h = Zlength x /\
              sublist 0 (Zlength x) (IR.h_xbuf h) = x) _ Fx) as [Fx0 Fx1].
  pose proof (hdr_field g 2 (g_nm g ++ [0])
    (fun l => IR.h_np h = true /\ H8.cna h = Zlength l /\ sublist 0 (Zlength l) (IR.h_nbuf h) = l) _ Fn)
    as [Fn0 Fn1].
  pose proof (hdr_field g 4 (g_cm g ++ [0])
    (fun l => IR.h_cp h = true /\ H8.cca h = Zlength l /\ sublist 0 (Zlength l) (IR.h_cbuf h) = l) _ Fc)
    as [Fc0 Fc1].
  cbv beta in Fx1, Fn1, Fc1. clear Fx Fn Fc.
  assert (Ex : (if IR.h_xp h then g_gxp g else nullval) = gq g 1 (g_gxp g)).
  { unfold gq. destruct (Z.land (g_pr g) 1 =? 0) eqn:E; [ rewrite (Fx0 eq_refl) | rewrite (proj1 (Fx1 eq_refl)) ];
    reflexivity. }
  assert (En : (if IR.h_np h then g_gnp g else nullval) = gq g 2 (g_gnp g)).
  { unfold gq. destruct (Z.land (g_pr g) 2 =? 0) eqn:E; [ rewrite (Fn0 eq_refl) | rewrite (proj1 (Fn1 eq_refl)) ];
    reflexivity. }
  assert (Ec : (if IR.h_cp h then g_gcp g else nullval) = gq g 4 (g_gcp g)).
  { unfold gq. destruct (Z.land (g_pr g) 4 =? 0) eqn:E; [ rewrite (Fc0 eq_refl) | rewrite (proj1 (Fc1 eq_refl)) ];
    reflexivity. }
  pose proof Hg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lx & _ & Ln & _ & Lc & _ & _ & _ & _ & Px & Pn & Pc & _).
  assert (Ln1 : Zlength (g_nm g ++ [0]) = g_nl g + 1) by (rewrite Zlength_app, Ln; reflexivity).
  assert (Lc1 : Zlength (g_cm g ++ [0]) = g_cl g + 1) by (rewrite Zlength_app, Lc; reflexivity).
  unfold H8.head_mem8, gtoks. fold s h. rewrite Hi, Hp, Hs, Hx, Hn, Hc, Hxm, Hnm, Hcm.
  rewrite !distrib_orp_sepcon. apply orp_left; [apply orp_left |].
  - Intros. unfold Zlib.proof.inflate.Rep.head_rep. rewrite Ex, En, Ec, Hxm, Hnm, Hcm, head_cs8.
    match goal with H : Zlib.proof.inflate.Inv.hwf _ |- _ => destruct H as [_ _ _ _ _ _ _ _ [Hxw _] [Hnw _] [Hcw _] _ _] end.
    sep_apply (buf_viewd (Z.land (g_pr g) 1 =? 0) (g_gxp g) (g_xl g) (g_xf g) (IR.h_xbuf h) Px ltac:(rep_lia)
      ltac:(lia) (fun E => ltac:(rewrite <- Lx; exact (proj2 (proj2 (proj2 (proj2 (Fx1 E)))))))).
    sep_apply (buf_viewd (Z.land (g_pr g) 2 =? 0) (g_gnp g) (g_nl g + 1) (g_nm g ++ [0]) (IR.h_nbuf h) Pn
      ltac:(rep_lia) ltac:(lia) (fun E => ltac:(rewrite <- Ln1; exact (proj2 (proj2 (Fn1 E)))))).
    sep_apply (buf_viewd (Z.land (g_pr g) 4 =? 0) (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]) (IR.h_cbuf h) Pc
      ltac:(rep_lia) ltac:(lia) (fun E => ltac:(rewrite <- Lc1; exact (proj2 (proj2 (Fc1 E)))))).
    Exists (vi (IR.h_xflags h)) (vi (IR.h_extra_len h)).
    unfold gotv, gfield, vi, vl. rewrite Ht, Hhc, Hos, Htm, Hd.
    apply andp_right; [ apply prop_right; intros E; rewrite (proj1 (proj2 (proj2 (Fx1 E)))), Lx; reflexivity | ].
    cancel.
  - Intros. congruence.
  - Intros. unfold H8.head_rep8a, H6.head_rep6p. Intros vt vtm vxf vos vxl vhc lx ln lc.
    rewrite Ex, En, Ec, Hxm, Hnm, Hcm, head_cs8.
    rewrite Hxm in H4. rewrite Hnm in H5. rewrite Hcm in H6.
    sep_apply (buf_view6 (Z.land (g_pr g) 1 =? 0) (g_gxp g) (g_xl g) (g_xf g) lx (H8.cxa h) (IR.h_xbuf h) Px
      ltac:(rep_lia) (fun E => ltac:(destruct (Fx1 E) as (_ & _ & _ & -> & Hsx); rewrite <- Lx;
                                     split; [reflexivity | exact Hsx])) H4).
    sep_apply (buf_view6 (Z.land (g_pr g) 2 =? 0) (g_gnp g) (g_nl g + 1) (g_nm g ++ [0]) ln (H8.cna h) (IR.h_nbuf h)
      Pn ltac:(rep_lia) (fun E => ltac:(destruct (Fn1 E) as (_ & -> & Hsx); rewrite <- Ln1;
                                        split; [reflexivity | exact Hsx])) H5).
    sep_apply (buf_view6 (Z.land (g_pr g) 4 =? 0) (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]) lc (H8.cca h) (IR.h_cbuf h)
      Pc ltac:(rep_lia) (fun E => ltac:(destruct (Fc1 E) as (_ & -> & Hsx); rewrite <- Lc1;
                                        split; [reflexivity | exact Hsx])) H6).
    Exists vxf vxl.
    rewrite (H ltac:(lia)), (H0 ltac:(lia)), (proj2 (H1 ltac:(lia))), (H3 ltac:(lia)).
    unfold gotv, gfield, vi, vl. rewrite Ht, Hhc, Hos, Htm, Hd.
    apply andp_right; [ apply prop_right; intros E; destruct (Fx1 E) as (_ & Hf & Hl & _);
                        rewrite (H2 ltac:(lia) Hf), Hl, Lx; reflexivity | ].
    cancel.
Qed.

(** ** The comparisons of the checks *)

(* got.text == (head.text != 0), got.hcrc == (head.hcrc != 0) *)
Lemma flag_eq (t : Z) : -2147483648 <= t <= 2147483647 ->
  Int.eq (Int.repr (if t =? 0 then 0 else 1)) (Int.repr (Z.b2z (negb (Int.eq (Int.repr t) (Int.repr 0))))) = true.
Proof.
  intros Ht. destruct (Z.eqb_spec t 0) as [-> | Hn]; [ reflexivity | ].
  rewrite (Int.eq_false (Int.repr t)); [ reflexivity | ].
  intros E. apply (f_equal Int.signed) in E. rewrite !Int.signed_repr in E by rep_lia. lia.
Qed.

(* got.os == (head.os & 255) *)
Lemma os_eq (o : Z) : Int.eq (Int.repr (Z.land o 255)) (Int.and (Int.repr o) (Int.repr 255)) = true.
Proof.
  unfold Int.and. rewrite Int.unsigned_repr with (z := 255) by rep_lia.
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia.
  rewrite Int.unsigned_repr_eq. unfold Int.modulus, Int.wordsize, Wordsize_32.wordsize.
  rewrite (Znumtheory.Zmod_div_mod (2 ^ 8) (two_power_nat 32) o); [ apply Int.eq_true | lia | reflexivity | ].
  exists (2 ^ 24)%Z. reflexivity.
Qed.

(* present & m *)
Lemma land_repr (pr m : Z) : 0 <= pr <= 255 -> 0 <= m <= 255 ->
  Int.and (Int.repr pr) (Int.repr m) = Int.repr (Z.land pr m).
Proof. intros. unfold Int.and. rewrite !Int.unsigned_repr by rep_lia. reflexivity. Qed.

Lemma land_range (pr m : Z) : 0 <= pr <= 255 -> 0 <= m -> 0 <= Z.land pr m <= 255.
Proof.
  intros Hp Hm. split; [ apply Z.land_nonneg; lia | ].
  assert (E : Z.land pr (Z.ones 8) = pr) by (rewrite Z.land_ones by lia; apply Z.mod_small; cbn; lia).
  rewrite <- E, <- Z.land_assoc, (Z.land_comm (Z.ones 8) m), Z.land_assoc, Z.land_ones by lia.
  pose proof (Z.mod_pos_bound (Z.land pr m) (2 ^ 8) ltac:(lia)). cbn in *. lia.
Qed.

Lemma gq_pn (g : gsetup) (m : Z) (q : val) : isptr q -> is_pointer_or_null (gq g m q).
Proof. intros Hq. unfold gq. destruct (_ =? 0); [ simpl; auto | destruct q; try contradiction; exact I ]. Qed.

(* same_field's answer for a field of main's header: 1 *)
Lemma sf_one (g : gsetup) (m : Z) (q : val) (l : list Z) : isptr q ->
  (if Z.land (g_pr g) m =? 0 then 1
   else if eq_dec (gq g m q) nullval then 0 else if list_eq_dec Z.eq_dec l l then 1 else 0) = 1.
Proof.
  intros Hq. unfold gq. destruct (Z.land (g_pr g) m =? 0); [ reflexivity | ].
  rewrite if_false by (intros ->; exact Hq).
  destruct (list_eq_dec Z.eq_dec l l); [ reflexivity | congruence ].
Qed.

(* same_field's precondition for a field of main's header: got's buffer when present, and head's object *)
Lemma sf_pre (g : gsetup) (m : Z) (q given : val) (n : Z) (l : list Z) :
  gfield g m q n l * @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) given |--
  (if Z.land (g_pr g) m =? 0 then emp
   else (if eq_dec (gq g m q) nullval then emp
         else @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) (gq g m q) *
              @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar n) (gq g m q)) *
        @data_at Zlib.units.Adler32.CS Ews (tarray tuchar n) (bytes_rep l) given) * TT.
Proof.
  unfold gfield, gq. destruct (Z.land (g_pr g) m =? 0); [ cancel | ].
  destruct (eq_dec q nullval); cancel.
Qed.

(* the copies of head's three objects at the compspecs of same_field (head's objects and the tokens are not needed
   any more) *)
Lemma hobjs_view (g : gsetup) : gs_ok g ->
  hobjs g |--
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_xl g)) (bytes_rep (g_xf g)) (g_xcp g) *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_nl g + 1)) (bytes_rep (g_nm g ++ [0])) (g_ncp g) *
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_cl g + 1)) (bytes_rep (g_cm g ++ [0])) (g_ccp g) * TT.
Proof.
  intros Hg. pose proof Hg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lx & _ & Ln & _ & Lc & _).
  unfold hobjs, hcopies, cobj. rewrite !Zlength_app, Lx, Ln, Lc. cbn [Zlength Datatypes.length Z.of_nat].
  rewrite !(data_at_tuchar_cs CS Zlib.units.Adler32.CS). unfold bytes_rep, vi. cancel.
Qed.

(* the bytes of main's fields are bytes *)
Lemma is_bytes_r (l : list Z) : Zlib.proof.roundtrip.RTDIface.rbytes l -> is_bytes l.
Proof. unfold Zlib.proof.roundtrip.RTDIface.rbytes, is_bytes. intros H. eapply Forall_impl; [ | exact H]. cbn. intros; rep_lia. Qed.

Lemma is_bytes_nz (l : list Z) : nzbytes l -> is_bytes (l ++ [0]).
Proof.
  unfold nzbytes, is_bytes. intros H. apply Forall_app; split; [ | repeat constructor; rep_lia ].
  eapply Forall_impl; [ | exact H]. cbn. intros; rep_lia.
Qed.

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers; each identifier comparison is decided by vm_compute instead (as in round 1's MainSeg3.v). *)
Ltac ms7_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in ms7_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := ms7_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(** ** The statements and the states between them *)

Definition S40 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 0 seg7)) in exact x).
Definition S41 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 1 seg7)) in exact x).
Definition S42 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 2 seg7)) in exact x).
Definition S43 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 3 seg7)) in exact x).
Definition S44 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 4 seg7)) in exact x).
Definition S45 : statement := ltac:(let x := eval cbv [take suf seg7] in (take 1 (suf 5 seg7)) in exact x).
Definition S46 : statement := ltac:(let x := eval cbv [take suf seg7] in (suf 6 seg7) in exact x).

Lemma seg7_split : seg7 = Ssequence S40 (Ssequence S41 (Ssequence S42 (Ssequence S43 (Ssequence S44
                            (Ssequence S45 S46))))).
Proof. reflexivity. Qed.

(* statement 40 cut in three: its first test (done, text), its second test (hcrc), its gp_assert *)
Definition S40a : statement :=
  ltac:(let x := eval cbv [S40] in (match S40 with Ssequence (Ssequence a _) _ => a | _ => Sskip end) in exact x).
Definition S40b : statement :=
  ltac:(let x := eval cbv [S40] in (match S40 with Ssequence (Ssequence _ b) _ => b | _ => Sskip end) in exact x).
Definition S40c : statement :=
  ltac:(let x := eval cbv [S40] in (match S40 with Ssequence _ c => c | _ => Sskip end) in exact x).

Lemma S40_split : S40 = Ssequence (Ssequence S40a S40b) S40c.
Proof. reflexivity. Qed.

(* the copies of head's three objects as same_field reads them *)
Definition hx7 (g : gsetup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_xl g)) (bytes_rep (g_xf g)) (g_xcp g).
Definition hn7 (g : gsetup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_nl g + 1)) (bytes_rep (g_nm g ++ [0])) (g_ncp g).
Definition hc7 (g : gsetup) : mpred :=
  @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (g_cl g + 1)) (bytes_rep (g_cm g ++ [0])) (g_ccp g).

(* main's state between the checks: got (vxl its extra_len, defined when the extra field is present), head (not
   read; given back at the return), the rest of main's memory, and [rest]: the buffers and copies of the checks
   still to come *)
Definition Q7 (gv : globals) (vh vg vc vd vr : val) (g : gsetup) (Fr : mpred) (vxf vxl : val) (rest : list mpred)
    : environ -> mpred :=
  PROPx [gs_ok g; dback vc vd vr Fr; Z.land (g_pr g) 1 =? 0 = false -> vxl = vi (g_xl g)]
  (LOCALx (gp_locals g ++ gs_locals g ++ lv_locals gv vh vg vc vd vr)
  (SEPx (data_at Tsh t_g (gotv g vxf vxl) vg :: data_at Tsh t_g (hvals g) vh :: Fr :: mem_mgr gv :: R gv :: TT ::
         rest))).

(* the same with the temporaries tl of a statement in progress *)
Definition Q7x (gv : globals) (vh vg vc vd vr : val) (g : gsetup) (Fr : mpred) (vxf vxl : val) (tl : list localdef)
    (rest : list mpred) : environ -> mpred :=
  PROPx [gs_ok g; dback vc vd vr Fr; Z.land (g_pr g) 1 =? 0 = false -> vxl = vi (g_xl g)]
  (LOCALx (tl ++ gp_locals g ++ gs_locals g ++ lv_locals gv vh vg vc vd vr)
  (SEPx (data_at Tsh t_g (gotv g vxf vxl) vg :: data_at Tsh t_g (hvals g) vh :: Fr :: mem_mgr gv :: R gv :: TT ::
         rest))).

(* the rests before statement 40 (and 41), 42 (and 43), 44, 45 (round 2's numbers: main's 48 .. 53) *)
Definition rest40 (g : gsetup) : list mpred :=
  [gfield g 1 (g_gxp g) (g_xl g) (g_xf g); gfield g 2 (g_gnp g) (g_nl g + 1) (g_nm g ++ [0]);
   gfield g 4 (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]); hx7 g; hn7 g; hc7 g].
Definition rest42 (g : gsetup) : list mpred :=
  [gfield g 2 (g_gnp g) (g_nl g + 1) (g_nm g ++ [0]); gfield g 4 (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]);
   hn7 g; hc7 g].
Definition rest44 (g : gsetup) : list mpred := [gfield g 4 (g_gcp g) (g_cl g + 1) (g_cm g ++ [0]); hc7 g].
