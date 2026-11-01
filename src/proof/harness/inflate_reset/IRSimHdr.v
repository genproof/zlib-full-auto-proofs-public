(* Law inflate_reset, theory part: one pass of the gzip header cases FLAGS .. HCRC from related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The working relation: ma is mb with its own state's dead fields (sgraft) and its own gz_header   *)

Definition irh_G (m: mst) (s: istate) (h: hstate) : mst := set_m_h (set_m_s m s) h.

(* sb's fields, but sa's check, length and the fields these modes never read *)
Definition irh_sg (sb sa: istate) : istate :=
  IS (i_mode sb) (i_last sb) (i_wrap sb) (i_havedict sb) (i_flags sb) (i_dmax sb) (i_check sa) (i_total sb)
     (i_head sb) (i_wbits sb) (i_wsize sb) (i_whave sb) (i_wnext sb) (i_win sa) (i_wdata sb) (i_hold sb)
     (i_bits sb) (i_length sa) (i_offset sa) (i_extra sa) (i_lencode sb) (i_distcode sb) (i_lenbits sa)
     (i_distbits sa) (i_ncode sa) (i_nlen sa) (i_ndist sa) (i_have sa) (i_next sb) (i_lens sa) (i_codes sa)
     (i_sane sb) (i_back sb) (i_was sa).

Record irh (W0 wrap: Z) (src: list Z) (inp: list Z) (aout: Z) (ma mb: mst) : Prop := {
  irh_loc : ma = irh_G mb (m_s ma) (m_h ma);
  irh_st : m_s ma = irh_sg (m_s mb) (m_s ma);
  irh_check : i_check (m_s ma) = i_check (m_s mb) \/ wrap = 0;
  irh_len : i_mode (m_s mb) = EXTRA -> Z.land (i_flags (m_s mb)) 1024 <> 0 ->
            i_length (m_s ma) = i_length (m_s mb);
  irh_head : i_head (m_s mb) = false;
  irh_inp : m_inp mb = inp;
  irh_aout : m_aout mb = aout;
  irh_wrap : i_wrap (m_s mb) = wrap;
  irh_wb : wcl W0 wrap src (i_wbits (m_s mb)) }.

Definition irh_md (md: Z) : Prop := md_hdr md \/ md = Zlib.proof.inflate.Model.TYPE \/ md = BAD.

Definition irh_P (W0 wrap: Z) (src: list Z) (inp: list Z) (aout: Z) (oa ob: iout) : Prop :=
  match oa, ob with
  | IBrk a, IBrk b => irh W0 wrap src inp aout a b /\ irh_md (i_mode (m_s b))
  | _, _ => False
  end.

Lemma irh_open W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb ->
  exists sa ha, ma = irh_G mb (irh_sg (m_s mb) sa) ha /\
    (i_check sa = i_check (m_s mb) \/ wrap = 0) /\
    (i_mode (m_s mb) = EXTRA -> Z.land (i_flags (m_s mb)) 1024 <> 0 -> i_length sa = i_length (m_s mb)) /\
    i_head (m_s mb) = false /\ m_inp mb = inp /\ m_aout mb = aout /\ i_wrap (m_s mb) = wrap /\
    wcl W0 wrap src (i_wbits (m_s mb)).
Proof.
  intros [L S C Ln Hd Hi Ha Hw Wb].
  exists (m_s ma), (m_h ma). split; [|tauto].
  rewrite S in L. exact L.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* NEEDBITS and the NAME / COMMENT loop do not look at the state                                 *)

Lemma irh_nbf_G k n m s h : needbits_f k n (irh_G m s h) = irh_G (needbits_f k n m) s h.
Proof.
  revert m. induction k as [|k IH]; intros m; [reflexivity|].
  cbn [needbits_f].
  replace (m_bits (irh_G m s h)) with (m_bits m) by reflexivity.
  replace (m_have (irh_G m s h)) with (m_have m) by reflexivity.
  destruct (m_bits m <? n); [|reflexivity].
  destruct (m_have m =? 0); [reflexivity|].
  rewrite <- IH. reflexivity.
Qed.

Lemma irh_nb_G n m s h : needbits n (irh_G m s h) = irh_G (needbits n m) s h.
Proof. apply irh_nbf_G. Qed.

Lemma irh_nbf_ex k n m : exists nx hd b lv,
  needbits_f k n m = MS (m_s m) (m_h m) (m_inp m) (m_aout m) nx (m_ow m) hd b (m_in m) (m_out m) (m_ret m) lv
                        (m_adler m) (m_msg m) (m_tin m) (m_tout m) (m_snx m) (m_sow m).
Proof.
  revert m. induction k as [|k IH]; intros m.
  - exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). destruct m; reflexivity.
  - cbn [needbits_f].
    destruct (m_bits m <? n).
    + destruct (m_have m =? 0).
      * exists (m_nx m), (m_hold m), (m_bits m), 1. destruct m; reflexivity.
      * destruct (IH (pull m)) as (nx & hd & b & lv & ->).
        exists nx, hd, b, lv. destruct m; reflexivity.
    + exists (m_nx m), (m_hold m), (m_bits m), (m_leave m). destruct m; reflexivity.
Qed.

Lemma irh_nb_ex n m : exists nx hd b lv,
  needbits n m = MS (m_s m) (m_h m) (m_inp m) (m_aout m) nx (m_ow m) hd b (m_in m) (m_out m) (m_ret m) lv
                    (m_adler m) (m_msg m) (m_tin m) (m_tout m) (m_snx m) (m_sow m).
Proof. apply irh_nbf_ex. Qed.

(* the copy loop without writing (length 0, no buffer) *)
Definition irh_zc (k: nat) (bytes: list Z) (have copy: Z) : Z * Z * Z * list Z :=
  zstr_f k bytes have 0 0 false [] copy.

Lemma irh_zstr k bytes have : forall len max buf copy,
  zstr_f k bytes have len max false buf copy =
  (fst (fst (fst (irh_zc k bytes have copy))), snd (fst (fst (irh_zc k bytes have copy))), len, buf).
Proof.
  unfold irh_zc.
  induction k as [|k IH]; intros len max buf copy; [reflexivity|].
  cbn [zstr_f andb].
  destruct ((negb (Znth copy bytes =? 0) && (copy + 1 <? have))%bool); [apply IH|reflexivity].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* Tactics                                                                                        *)

Ltac irh_red :=
  cbv beta iota zeta delta [irh_G irh_sg upd_s upd_h set_mode set_leave set_bad initbits crc_if inbytes m_have
    m_mode set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
    set_i_mode set_i_check set_i_length set_i_flags
    m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
    m_snx m_sow
    i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
    i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits
    i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was andb negb].

Ltac irh_nb :=
  repeat match goal with |- context [needbits ?n (irh_G ?m ?s ?h)] => rewrite (irh_nb_G n m s h) end;
  repeat match goal with |- context [needbits ?n ?m] =>
    let E := fresh "E" in destruct (irh_nb_ex n m) as (? & ? & ? & ? & E); rewrite E; clear E end.

Ltac irh_open H :=
  let sa := fresh "sa" in let ha := fresh "ha" in let C := fresh "C" in let Ln := fresh "Ln" in
  let Hd := fresh "Hd" in let Hi := fresh "Hi" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
  let Wb := fresh "Wb" in
  destruct (irh_open _ _ _ _ _ _ _ H) as (sa & ha & -> & C & Ln & Hd & Hi & Ha & Hw & Wb); clear H;
  match goal with |- context [irh_G ?mb _ _] =>
    destruct mb as [[b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34] l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17] end;
  destruct sa as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34];
  cbn [m_s m_inp m_aout i_mode i_check i_flags i_head i_wrap i_wbits i_length] in *; subst.

Ltac irh_md_tac :=
  unfold irh_md, md_hdr, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, Zlib.proof.inflate.Model.TYPE,
    BAD in *; lia.

Ltac irh_rel :=
  constructor; irh_red;
  first [ reflexivity | assumption | (left; reflexivity) | (right; reflexivity)
        | (intros; reflexivity) | (intros; irh_md_tac)
        | (intros ? N; exfalso; apply N; apply Z.eqb_eq; assumption) | idtac ].

(* close irh_P (IBrk a) (IBrk b) *)
Ltac irh_leaf := cbn [irh_P]; irh_red; split; [irh_rel | irh_md_tac].

Ltac irh_cases :=
  match goal with C: _ = _ \/ _ = 0 |- _ =>
    destruct C as [C|C]; subst; [|try change (Z.land 0 4 =? 0) with true; cbv beta iota] end;
  repeat match goal with |- context [if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E end;
  try irh_leaf.

(* the value of a guard (a small term): setters, projections and andb reduced *)
Ltac irh_n t :=
  eval cbv beta iota zeta delta [irh_G irh_sg upd_s upd_h set_mode set_leave set_bad initbits inbytes m_have
    m_mode set_m_s set_m_h set_m_nx set_m_hold set_m_bits set_m_leave set_m_msg set_m_adler
    set_i_mode set_i_check set_i_length set_i_flags
    m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
    m_snx m_sow
    i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize i_whave i_wnext
    i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits i_distbits
    i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was andb negb] in t.

Lemma irh_crc_t m d :
  (negb (Z.land (i_flags (m_s m)) 512 =? 0) && negb (Z.land (i_wrap (m_s m)) 4 =? 0))%bool = true ->
  crc_if m d = upd_s m (fun s => set_i_check s (ref_crc32 (i_check s) d)).
Proof. intros G. unfold crc_if. rewrite G. reflexivity. Qed.

Lemma irh_crc_f m d :
  (negb (Z.land (i_flags (m_s m)) 512 =? 0) && negb (Z.land (i_wrap (m_s m)) 4 =? 0))%bool = false ->
  crc_if m d = m.
Proof. intros G. unfold crc_if. rewrite G. reflexivity. Qed.

(* decide every CRC update by its (common) guard *)
Ltac irh_crc :=
  repeat match goal with |- context [crc_if ?X ?d] =>
    let g := irh_n ((negb (Z.land (i_flags (m_s X)) 512 =? 0) && negb (Z.land (i_wrap (m_s X)) 4 =? 0))%bool) in
    first [ match goal with G: g = true |- _ => rewrite (irh_crc_t X d G) end
          | match goal with G: g = false |- _ => rewrite (irh_crc_f X d G) end
          | let G := fresh "G" in destruct g eqn:G ]
  end.

(* decide every if, innermost first, by its normalized guard (the same on both machines) *)
Ltac irh_split :=
  repeat (match goal with |- context [if ?c then _ else _] =>
    lazymatch c with context [if _ then _ else _] => fail | _ => idtac end;
    lazymatch c with true => fail | false => fail | _ => idtac end;
    let c' := irh_n c in
    change c with c';
    lazymatch c' with
    | true => idtac
    | false => idtac
    | context [if _ then _ else _] => idtac
    | _ => first [ match goal with E: c' = _ |- _ => rewrite E end
                 | let E := fresh "E" in destruct c' eqn:E ]
    end
  end; cbv beta iota).

Ltac irh_pre := irh_crc; irh_split; irh_red.

Ltac irh_next L := apply L; [irh_rel | irh_red; reflexivity].

(* NAME / COMMENT: the copy loop with wr = false *)
Ltac irh_zs := rewrite ?irh_zstr; irh_red.

(* EXTRA: with FEXTRA, length is live *)
Ltac irh_lenfix :=
  match goal with Ln: _ = _ -> Z.land ?f 1024 <> 0 -> ?a = ?b |- _ =>
    let F := fresh "F" in
    destruct (Z.land f 1024 =? 0) eqn:F;
    [clear Ln | let F' := fresh in pose proof F as F'; apply Z.eqb_neq in F'; specialize (Ln eq_refl F'); subst]
  end.

Lemma irh_hcrc W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = HCRC ->
  irh_P W0 wrap src inp aout (c_HCRC ma) (c_HCRC mb).
Proof.
  intros H Md. irh_open H.
  unfold c_HCRC; cbv beta zeta. irh_nb. irh_red. irh_cases.
Qed.

Lemma irh_comment W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = COMMENT ->
  irh_P W0 wrap src inp aout (c_COMMENT2 ma) (c_COMMENT2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_COMMENT2; cbv beta zeta. irh_red. irh_zs. irh_cases.
  all: irh_next irh_hcrc.
Qed.

Lemma irh_name W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = NAME ->
  irh_P W0 wrap src inp aout (c_NAME2 ma) (c_NAME2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_NAME2; cbv beta zeta. irh_red. irh_zs. irh_cases.
  all: irh_next irh_comment.
Qed.

Lemma irh_extra W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = EXTRA ->
  irh_P W0 wrap src inp aout (c_EXTRA2 ma) (c_EXTRA2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_EXTRA2; cbv beta zeta. irh_lenfix; irh_pre; irh_cases.
  all: irh_next irh_name.
Qed.

Lemma irh_exlen W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = EXLEN ->
  irh_P W0 wrap src inp aout (c_EXLEN2 ma) (c_EXLEN2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_EXLEN2; cbv beta zeta. irh_nb; irh_pre; irh_cases.
  all: irh_next irh_extra.
Qed.

Lemma irh_os W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = OS ->
  irh_P W0 wrap src inp aout (c_OS2 ma) (c_OS2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_OS2; cbv beta zeta. irh_nb; irh_pre; irh_cases.
  all: irh_next irh_exlen.
Qed.

Lemma irh_time W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = TIME ->
  irh_P W0 wrap src inp aout (c_TIME2 ma) (c_TIME2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_TIME2; cbv beta zeta. irh_nb; irh_pre; irh_cases.
  all: irh_next irh_os.
Qed.

Lemma irh_flags W0 wrap src inp aout ma mb :
  irh W0 wrap src inp aout ma mb -> i_mode (m_s mb) = FLAGS ->
  irh_P W0 wrap src inp aout (c_FLAGS2 ma) (c_FLAGS2 mb).
Proof.
  intros H Md. irh_open H.
  unfold c_FLAGS2; cbv beta zeta. irh_nb; irh_pre; irh_cases.
  all: irh_next irh_time.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* From Kr and back                                                                               *)

Ltac irh_mds :=
  unfold irh_md, md_hdr, lenlive, decode_mode, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC,
    Zlib.proof.inflate.Model.TYPE, BAD, HEAD, COPY_, COPY, LENEXT, DIST, DISTEXT, MATCH, LIT, LEN_, LEN,
    LENLENS, CODELENS in *; lia.

Lemma irh_of_Kr W0 wrap src pos inp aout ma mb :
  Kr W0 wrap src pos inp aout ma mb -> md_hdr (i_mode (m_s mb)) -> irh W0 wrap src inp aout ma mb.
Proof.
  intros [R Hi Ha Hw Hd Wa Wb Hh] Md.
  destruct R as [S R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17].
  destruct ma as [[a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34] ha la3 la4 la5 la6 la7 la8 la9 la10 la11 la12 la13 la14 la15 la16 la17 la18], mb as [[b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34] hb lb3 lb4 lb5 lb6 lb7 lb8 lb9 lb10 lb11 lb12 lb13 lb14 lb15 lb16 lb17 lb18].
  destruct S as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 S18 S19 S20 S21 S22 S23 S24 S25 S26 S27 S28 S29 S30 S31 S32 S33].
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize
       i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
       i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was] in *.
  assert (W : a10 = b10) by (destruct S20 as [E|[E|E]]; [exact E | exfalso; irh_mds | exfalso; irh_mds]).
  subst.
  constructor; irh_red; try reflexivity; try assumption.
  - destruct S21 as [E|[E|[[E|E] _]]]; [left; exact E | right; exact E | exfalso; irh_mds | exfalso; irh_mds].
  - intros E F. apply S22. unfold lenlive. cbn [i_mode i_flags]. do 7 right. split; assumption.
Qed.

Lemma irh_Kr W0 wrap src pos inp aout a b :
  irh W0 wrap src inp aout a b -> irh_md (i_mode (m_s b)) -> Kr W0 wrap src pos inp aout a b.
Proof.
  intros [L S C Ln Hd Hi Ha Hw Wb] Md.
  destruct a as [[a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34] ha la3 la4 la5 la6 la7 la8 la9 la10 la11 la12 la13 la14 la15 la16 la17 la18], b as [[b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34] hb lb3 lb4 lb5 lb6 lb7 lb8 lb9 lb10 lb11 lb12 lb13 lb14 lb15 lb16 lb17 lb18].
  cbv [irh_G irh_sg set_m_h set_m_s m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave
       m_adler m_msg m_tin m_tout m_snx m_sow i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total
       i_head i_wbits i_wsize i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra
       i_lencode i_distcode i_lenbits i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane
       i_back i_was] in *.
  injection L; intros; subst. injection S; intros; subst. clear L S.
  constructor; [constructor; [constructor|..]|..]; unfold m_mode;
  cbn [m_s m_h m_inp m_aout m_nx m_ow m_hold m_bits m_in m_out m_ret m_leave m_adler m_msg m_tin m_tout
       m_snx m_sow i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize
       i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
       i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was];
  try reflexivity; try assumption.
  all: first
    [ (left; reflexivity)
    | (destruct C as [E|E]; [left; exact E | right; left; exact E])
    | (intros HL; unfold lenlive in HL; cbn [i_mode i_flags] in HL; apply Ln;
       [ irh_mds
       | destruct HL as [E|[E|[E|[E|[E|[E|[E|[_ E]]]]]]]]; try exact E; exfalso; irh_mds ])
    | (intros; exfalso; irh_mds) ].
Qed.

Lemma irh_post W0 wrap src pos inp aout oa ob :
  irh_P W0 wrap src inp aout oa ob -> sim_post W0 wrap src pos inp aout oa ob.
Proof.
  destruct oa, ob; cbn [irh_P sim_post]; try tauto.
  intros [I M]. apply irh_Kr; assumption.
Qed.

Lemma hdr_sim : hdr_sim_stmt.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  pose proof (irh_of_Kr _ _ _ _ _ _ _ _ K Hmd) as I.
  assert (Em : m_mode ma = m_mode mb) by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))).
  apply irh_post. unfold m_mode in Em.
  unfold md_hdr, m_mode in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_FLAGS2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_FLAGS2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_flags; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_TIME2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_TIME2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_time; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_OS2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_OS2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_os; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_EXLEN2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_EXLEN2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_exlen; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_EXTRA2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_EXTRA2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_extra; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_NAME2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_NAME2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_name; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_COMMENT2 ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_COMMENT2 mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_comment; assumption.
  - replace (stepf2 flush lenfix_list distfix_list ma) with (c_HCRC ma)
      by (unfold stepf2, step2, m_mode; rewrite Em, Hmd; reflexivity).
    replace (stepf2 flush lenfix_list distfix_list mb) with (c_HCRC mb)
      by (unfold stepf2, step2, m_mode; rewrite Hmd; reflexivity).
    apply irh_hcrc; assumption.
Qed.
