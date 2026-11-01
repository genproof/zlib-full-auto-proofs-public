(* Law inflate_reset, theory part: one pass of STORED, COPY_, COPY, CHECK, LENGTH, DONE, BAD, MEM, SYNC from related machines. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.inflate_reset.IRDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* a machine with its state and gz_header replaced: the two related machines are irb_xf m0 sa ha and
   irb_xf m0 sb hb (mrel: every other field equal) *)
Definition irb_xf (m: mst) (s: istate) (h: hstate) : mst := set_m_h (set_m_s m s) h.

Lemma irb_mrel_xf ma mb : mrel ma mb -> ma = irb_xf mb (m_s ma) (m_h ma).
Proof.
  intros R. destruct R. destruct ma, mb; cbn in *; subst; reflexivity.
Qed.

Lemma irb_eta m : m = irb_xf m (m_s m) (m_h m).
Proof. destruct m; reflexivity. Qed.

Lemma irb_nb k n m s h : needbits_f k n (irb_xf m s h) = irb_xf (needbits_f k n m) s h.
Proof.
  revert m. induction k as [|k IH]; intros m; [reflexivity|].
  cbn [needbits_f].
  change (m_bits (irb_xf m s h)) with (m_bits m). change (m_have (irb_xf m s h)) with (m_have m).
  destruct (m_bits m <? n); [|reflexivity].
  destruct (m_have m =? 0); [reflexivity|].
  change (pull (irb_xf m s h)) with (irb_xf (pull m) s h). apply IH.
Qed.

Lemma irb_nb_fields k n m :
  m_inp (needbits_f k n m) = m_inp m /\ m_aout (needbits_f k n m) = m_aout m /\
  m_ow (needbits_f k n m) = m_ow m.
Proof.
  revert m. induction k as [|k IH]; intros m; [auto|].
  cbn [needbits_f]. destruct (m_bits m <? n); [|auto].
  destruct (m_have m =? 0); [auto|]. destruct (IH (pull m)) as (A & B & C). rewrite A, B, C. auto.
Qed.

Section XfRewrites.
Variables (m: mst) (s: istate) (h: hstate).
Lemma irb_x_needbits n : needbits n (irb_xf m s h) = irb_xf (needbits n m) s h.
Proof. apply irb_nb. Qed.
Lemma irb_x_bytebits : bytebits (irb_xf m s h) = irb_xf (bytebits m) s h.
Proof. reflexivity. Qed.
Lemma irb_x_initbits : initbits (irb_xf m s h) = irb_xf (initbits m) s h.
Proof. reflexivity. Qed.
Lemma irb_x_leave : set_leave (irb_xf m s h) = irb_xf (set_leave m) s h.
Proof. reflexivity. Qed.
Lemma irb_x_ret v : set_m_ret (irb_xf m s h) v = irb_xf (set_m_ret m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_tout v : set_m_tout (irb_xf m s h) v = irb_xf (set_m_tout m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_out v : set_m_out (irb_xf m s h) v = irb_xf (set_m_out m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_adler v : set_m_adler (irb_xf m s h) v = irb_xf (set_m_adler m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_nx v : set_m_nx (irb_xf m s h) v = irb_xf (set_m_nx m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_ow v : set_m_ow (irb_xf m s h) v = irb_xf (set_m_ow m v) s h.
Proof. reflexivity. Qed.
Lemma irb_x_upd_s f : upd_s (irb_xf m s h) f = irb_xf m (f s) h.
Proof. reflexivity. Qed.
Lemma irb_x_mode v : set_mode (irb_xf m s h) v = irb_xf m (set_i_mode s v) h.
Proof. reflexivity. Qed.
Lemma irb_x_bad e : set_bad (irb_xf m s h) e = irb_xf (set_m_msg m (Some e)) (set_i_mode s BAD) h.
Proof. reflexivity. Qed.
Lemma irb_x_s : m_s (irb_xf m s h) = s. Proof. reflexivity. Qed.
Lemma irb_x_inp : m_inp (irb_xf m s h) = m_inp m. Proof. reflexivity. Qed.
Lemma irb_x_aout : m_aout (irb_xf m s h) = m_aout m. Proof. reflexivity. Qed.
Lemma irb_x_nx' : m_nx (irb_xf m s h) = m_nx m. Proof. reflexivity. Qed.
Lemma irb_x_ow' : m_ow (irb_xf m s h) = m_ow m. Proof. reflexivity. Qed.
Lemma irb_x_hold : m_hold (irb_xf m s h) = m_hold m. Proof. reflexivity. Qed.
Lemma irb_x_bits : m_bits (irb_xf m s h) = m_bits m. Proof. reflexivity. Qed.
Lemma irb_x_out' : m_out (irb_xf m s h) = m_out m. Proof. reflexivity. Qed.
Lemma irb_x_leave' : m_leave (irb_xf m s h) = m_leave m. Proof. reflexivity. Qed.
Lemma irb_x_tout' : m_tout (irb_xf m s h) = m_tout m. Proof. reflexivity. Qed.
Lemma irb_x_have : m_have (irb_xf m s h) = m_have m. Proof. reflexivity. Qed.
Lemma irb_x_left : m_left (irb_xf m s h) = m_left m. Proof. reflexivity. Qed.
Lemma irb_x_mmode : m_mode (irb_xf m s h) = i_mode s. Proof. reflexivity. Qed.
Lemma irb_x_inbytes n : inbytes (irb_xf m s h) n = inbytes m n. Proof. reflexivity. Qed.
End XfRewrites.

Lemma irb_nb_inp n m : m_inp (needbits n m) = m_inp m.
Proof. apply irb_nb_fields. Qed.
Lemma irb_nb_aout n m : m_aout (needbits n m) = m_aout m.
Proof. apply irb_nb_fields. Qed.
Lemma irb_nb_ow n m : m_ow (needbits n m) = m_ow m.
Proof. apply irb_nb_fields. Qed.

Ltac irb_push :=
  repeat first
    [ rewrite irb_x_needbits | rewrite irb_x_bytebits | rewrite irb_x_initbits | rewrite irb_x_leave
    | rewrite irb_x_ret | rewrite irb_x_tout | rewrite irb_x_out | rewrite irb_x_adler | rewrite irb_x_nx
    | rewrite irb_x_ow | rewrite irb_x_upd_s | rewrite irb_x_mode | rewrite irb_x_bad | rewrite irb_x_s
    | rewrite irb_x_inp | rewrite irb_x_aout | rewrite irb_x_nx' | rewrite irb_x_ow' | rewrite irb_x_hold
    | rewrite irb_x_bits | rewrite irb_x_out' | rewrite irb_x_leave' | rewrite irb_x_tout'
    | rewrite irb_x_have | rewrite irb_x_left | rewrite irb_x_mmode | rewrite irb_x_inbytes ].

(* the reset stream's state with the fields srel says are always equal taken from the fresh one's *)
Definition irb_gr (sa sb: istate) : istate :=
  IS (i_mode sb) (i_last sb) (i_wrap sb) (i_havedict sb) (i_flags sb) (i_dmax sb) (i_check sa) (i_total sb)
     (i_head sb) (i_wbits sb) (i_wsize sb) (i_whave sb) (i_wnext sb) (i_win sa) (i_wdata sb) (i_hold sb)
     (i_bits sb) (i_length sa) (i_offset sa) (i_extra sa) (i_lencode sb) (i_distcode sb) (i_lenbits sa)
     (i_distbits sa) (i_ncode sa) (i_nlen sa) (i_ndist sa) (i_have sa) (i_next sb) (i_lens sa) (i_codes sa)
     (i_sane sb) (i_back sb) (i_was sa).

Lemma irb_gr_eq n sa sb : srel n sa sb -> i_wbits sa = i_wbits sb -> sa = irb_gr sa sb.
Proof.
  intros R W. destruct R as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 _ _ _ _ _ _ _ _ _ _ _ _ _].
  unfold irb_gr. rewrite <- E1, <- E2, <- E3, <- E4, <- E5, <- E6, <- E7, <- E8, <- W, <- E9, <- E10, <- E11,
    <- E12, <- E13, <- E14, <- E15, <- E16, <- E17, <- E18, <- E19.
  destruct sa; reflexivity.
Qed.

(* the leaves: two results that share every machine field but the state and the gz_header *)
Lemma irb_leaf W0 wrap src pos inp aout M sa ha sb hb :
  m_inp M = inp -> m_aout M = aout -> i_wrap sb = wrap -> i_head sb = false ->
  wcl W0 wrap src (i_wbits sa) -> wcl W0 wrap src (i_wbits sb) -> i_mode sb <> HEAD ->
  srel (m_ow M = []) sa sb ->
  Kr W0 wrap src pos inp aout (irb_xf M sa ha) (irb_xf M sb hb).
Proof.
  intros Hi Ha Hw Hh Wa Wb Hm R.
  constructor; try assumption.
  - constructor; try reflexivity. exact R.
  - intros _ E. contradiction.
Qed.

Ltac irb_open :=
  intros K Hmd;
  pose proof (kr_rel _ _ _ _ _ _ _ _ K).(mr_s _ _) as S0;
  cbn [m_s m_ow irb_xf set_m_h set_m_s] in S0;
  destruct K as [[S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] Ki Ka Kw Kh Wa Wb _];
  cbn [m_s m_ow m_inp m_aout m_mode irb_xf set_m_h set_m_s] in S, Ki, Ka, Kw, Kh, Wa, Wb;
  destruct S as [Qmode Qlast Qwrap Qhavedict Qflags Qdmax Qtotal Qhead Qwsize Qwhave Qwnext Qwdata Qhold Qbits
    Qlencode Qdistcode Qnext Qsane Qback Qwbits Qcheck Qlength Qoffset Qextra Qlenbits Qdistbits Qncode Qnlen
    Qlenlens Qcodelens Qcltab Qdectab].

(* projections of states (and of setters on them) *)
Ltac irb_st := cbn [irb_gr i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize
    i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
    i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
    set_i_mode set_i_length set_i_check set_i_total].

(* contradictory mode facts *)
Ltac irb_mc :=
  unfold lenlive, decode_mode in *; cbn [i_mode i_last i_wrap i_havedict i_flags i_dmax i_check i_total i_head i_wbits i_wsize
    i_whave i_wnext i_win i_wdata i_hold i_bits i_length i_offset i_extra i_lencode i_distcode i_lenbits
    i_distbits i_ncode i_nlen i_ndist i_have i_next i_lens i_codes i_sane i_back i_was
    set_i_mode set_i_length set_i_check set_i_total] in *;
  repeat match goal with H: _ \/ _ |- _ => destruct H | H: _ /\ _ |- _ => destruct H end;
  unfold HEAD, FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, DICTID, DICT,
    Zlib.proof.inflate.Model.TYPE, TYPEDO, STORED, COPY_, COPY, TABLE, LENLENS, CODELENS, LEN_, LEN, LENEXT,
    DIST, DISTEXT, MATCH, LIT, CHECK, LENGTH, DONE, BAD, MEM, SYNC in *;
  lia.

(* a goal P -> False-ish about modes, from the mode hypothesis (i_mode _ = <a mode constant>) alone *)
Ltac irb_mcx :=
  let Hx := fresh "Hx" in intros Hx; exfalso;
  match goal with Hm: i_mode ?s = ?c |- _ => is_const c; clear - Hm Hx; irb_mc end.

(* after irb_open, for a mode other than HEAD and BAD: wbits equal; check equal or wrap = 0; length when live *)
Ltac irb_prep W C L :=
  destruct W as [?|?]; [ | exfalso; irb_mc];
  match goal with S0: srel _ ?a ?b, Ew: i_wbits ?a = i_wbits ?b |- _ => rewrite (irb_gr_eq _ a b S0 Ew) end;
  destruct C as [?|[?|?]]; [ | | exfalso; irb_mc];
  try specialize (L ltac:(unfold lenlive; first [left; assumption | right; left; assumption])).

(* rewrite the reset stream's fields to the fresh one's where they are known equal; wrap 0 *)
Ltac irb_rw :=
  repeat match goal with
  | H: i_check ?a = i_check ?b |- context [i_check ?a] => rewrite H
  | H: i_length ?a = i_length ?b |- context [i_length ?a] => rewrite H
  | H: i_wrap ?s = 0 |- context [i_wrap ?s] => rewrite H
  end.

Ltac irb_red :=
  irb_push; irb_st; irb_rw; cbn [Z.eqb Z.land negb andb]; irb_push; irb_st.

Ltac irb_split :=
  repeat (irb_red; match goal with |- context [if ?c then _ else _] => destruct c end); irb_red.

Ltac irb_srel :=
  constructor; irb_st; irb_rw; unfold lenlive, decode_mode; irb_st;
  first [ reflexivity | (left; reflexivity) | (right; left; assumption) | (right; left; reflexivity)
        | (intros; irb_rw; reflexivity)
        | irb_mcx ].

Ltac irb_mfield :=
  rewrite ?irb_nb_inp, ?irb_nb_aout;
  cbn [m_inp m_aout set_m_ret set_leave set_m_leave set_m_nx set_m_ow set_m_out set_m_tout
      set_m_adler set_m_msg set_m_bits set_m_hold bytebits initbits];
  rewrite ?irb_nb_inp, ?irb_nb_aout; first [assumption | reflexivity].

Ltac irb_kr :=
  apply irb_leaf;
  [ irb_mfield | irb_mfield | irb_st; assumption | irb_st; assumption | irb_st; assumption | irb_st; assumption
  | irb_st; irb_mcx | irb_srel ].

Ltac irb_leaf_tac := cbn [sim_post]; irb_kr.

Lemma irb_done W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = DONE ->
  sim_post W0 wrap src pos inp aout (c_DONE (irb_xf m0 sa ha)) (c_DONE (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold c_DONE; cbv beta zeta; irb_split.
  all: irb_leaf_tac.
Qed.

Lemma irb_length W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = LENGTH ->
  sim_post W0 wrap src pos inp aout (c_LENGTH (irb_xf m0 sa ha)) (c_LENGTH (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold c_LENGTH; cbv beta zeta; irb_split.
  all: first [irb_leaf_tac | apply irb_done; [irb_kr | irb_st; reflexivity]].
Qed.

(* CHECK, cut in two: the counters and check value update (irb_cku), then the comparison (irb_ckt) *)
Definition irb_cku (m: mst) : mst :=
  let out := u32 (m_out m - m_left m) in
  let m := set_m_tout m (u64 (m_tout m + out)) in
  let m := upd_s m (fun s => set_i_total s (u64 (i_total s + out))) in
  let m := if (negb (Z.land (i_wrap (m_s m)) 4 =? 0) && negb (out =? 0))%bool then
             let c := update_check (i_flags (m_s m)) (i_check (m_s m))
                        (sublist (Zlength (m_ow m) - out) (Zlength (m_ow m)) (m_ow m)) in
             set_m_adler (upd_s m (fun s => set_i_check s c)) c
           else m in
  set_m_out m (m_left m).

Definition irb_ckt (m: mst) : iout :=
  let s := m_s m in
  if (negb (Z.land (i_wrap s) 4 =? 0) &&
      negb ((if i_flags s =? 0 then swap32 (m_hold m) else m_hold m) =? i_check s))%bool
  then IBrk (set_bad m M_dcheck)
  else c_LENGTH (set_mode (initbits m) LENGTH).

Lemma irb_check_eq m :
  c_CHECK m = if negb (i_wrap (m_s m) =? 0) then
                if m_leave (needbits 32 m) =? 1 then IBrk (needbits 32 m)
                else irb_ckt (irb_cku (needbits 32 m))
              else c_LENGTH (set_mode m LENGTH).
Proof. cbv delta [c_CHECK irb_ckt irb_cku] beta zeta. reflexivity. Qed.

(* the lemmas over related machines in general (mrel: they are irb_xf of one machine) *)
Lemma irb_gen (P: mst -> mst -> Prop) :
  (forall m0 sa ha sb hb, P (irb_xf m0 sa ha) (irb_xf m0 sb hb)) -> forall ma mb, mrel ma mb -> P ma mb.
Proof.
  intros H ma mb R. specialize (H mb (m_s ma) (m_h ma) (m_s mb) (m_h mb)).
  rewrite <- (irb_eta mb) in H. rewrite <- (irb_mrel_xf _ _ R) in H. exact H.
Qed.

Lemma irb_ckt_ok W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = CHECK ->
  sim_post W0 wrap src pos inp aout (irb_ckt (irb_xf m0 sa ha)) (irb_ckt (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold irb_ckt; cbv beta zeta; irb_split.
  all: first [irb_leaf_tac | apply irb_length; [irb_kr | irb_st; reflexivity]].
Qed.

Lemma irb_cku_ok W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = CHECK ->
  Kr W0 wrap src pos inp aout (irb_cku (irb_xf m0 sa ha)) (irb_cku (irb_xf m0 sb hb)) /\
  m_mode (irb_cku (irb_xf m0 sb hb)) = CHECK.
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold irb_cku; cbv beta zeta; irb_split.
  all: split; [irb_kr | irb_st; assumption].
Qed.

Lemma irb_ck2 W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = CHECK ->
  sim_post W0 wrap src pos inp aout (irb_ckt (irb_cku (irb_xf m0 sa ha))) (irb_ckt (irb_cku (irb_xf m0 sb hb))).
Proof.
  intros K H. destruct (irb_cku_ok _ _ _ _ _ _ _ _ _ _ _ K H) as [K2 M2]. revert K2 M2.
  generalize (irb_cku (irb_xf m0 sa ha)) (irb_cku (irb_xf m0 sb hb)). intros ma mb K2 M2.
  refine (irb_gen (fun ma mb => Kr W0 wrap src pos inp aout ma mb -> m_mode mb = CHECK ->
    sim_post W0 wrap src pos inp aout (irb_ckt ma) (irb_ckt mb)) _ ma mb (kr_rel _ _ _ _ _ _ _ _ K2) K2 M2).
  intros m1 sa1 ha1 sb1 hb1 K3 M3. apply irb_ckt_ok; assumption.
Qed.

Lemma irb_check W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = CHECK ->
  sim_post W0 wrap src pos inp aout (c_CHECK (irb_xf m0 sa ha)) (c_CHECK (irb_xf m0 sb hb)).
Proof.
  intros K Hmd. rewrite !irb_check_eq. revert K Hmd.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: irb_split.
  all: first [irb_leaf_tac | apply irb_length; [irb_kr | irb_st; reflexivity]
             | apply irb_ck2; [irb_kr | irb_st; assumption]].
Qed.

Lemma irb_copy W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = COPY ->
  sim_post W0 wrap src pos inp aout (c_COPY (irb_xf m0 sa ha)) (c_COPY (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold c_COPY; cbv beta zeta; irb_split.
  all: irb_leaf_tac.
Qed.

Lemma irb_copy_ W0 wrap src pos inp aout m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = COPY_ ->
  sim_post W0 wrap src pos inp aout (c_COPY_ (irb_xf m0 sa ha)) (c_COPY_ (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold c_COPY_; cbv beta zeta; irb_split.
  all: first [irb_leaf_tac | apply irb_copy; [irb_kr | irb_st; reflexivity]].
Qed.

Lemma irb_stored W0 wrap src pos inp aout (flush: Z) m0 sa ha sb hb :
  Kr W0 wrap src pos inp aout (irb_xf m0 sa ha) (irb_xf m0 sb hb) -> i_mode sb = STORED ->
  sim_post W0 wrap src pos inp aout (c_STORED flush (irb_xf m0 sa ha)) (c_STORED flush (irb_xf m0 sb hb)).
Proof.
  irb_open. irb_prep Qwbits Qcheck Qlength.
  all: unfold c_STORED; cbv beta zeta; irb_split.
  all: first [irb_leaf_tac | apply irb_copy_; [irb_kr | irb_st; reflexivity]].
Qed.

Lemma irb_bad_kr W0 wrap src pos inp aout ma mb r :
  Kr W0 wrap src pos inp aout ma mb ->
  Kr W0 wrap src pos inp aout (set_leave (set_m_ret ma r)) (set_leave (set_m_ret mb r)).
Proof.
  intros [[A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17] B1 B2 B3 B4 B5 B6 B7].
  constructor; [constructor| | | | | | | ]; cbn; first [assumption | reflexivity | exact B7].
Qed.

Ltac irb_case lem X :=
  match goal with
  | K: Kr ?W0 ?wrap ?src ?pos ?inp ?aout ?ma ?mb, Mm: m_mode ?ma = m_mode ?mb, Hmd: m_mode ?mb = ?md |- _ =>
    replace (stepf2 _ _ _ ma) with (X ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity);
    replace (stepf2 _ _ _ mb) with (X mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity);
    refine (irb_gen (fun ma mb => Kr W0 wrap src pos inp aout ma mb -> m_mode mb = md ->
      sim_post W0 wrap src pos inp aout (X ma) (X mb)) _ ma mb (kr_rel _ _ _ _ _ _ _ _ K) K Hmd);
    let K' := fresh "K'" in let H' := fresh "H'" in
    intros ? ? ? ? ? K' H'; apply lem; [exact K' | exact H']
  end.

Lemma block_sim : block_sim_stmt.
Proof.
  intros W0 wrap src pos inp aout flush ma mb Hc K Wa Wb Hl Hmd.
  assert (Mm : m_mode ma = m_mode mb) by exact (sr_mode _ _ _ (mr_s _ _ (kr_rel _ _ _ _ _ _ _ _ K))).
  unfold md_block in Hmd.
  repeat match type of Hmd with _ \/ _ => destruct Hmd as [Hmd|Hmd] end.
  - irb_case irb_stored (c_STORED flush).
  - irb_case irb_copy_ c_COPY_.
  - irb_case irb_copy c_COPY.
  - irb_case irb_check c_CHECK.
  - irb_case irb_length c_LENGTH.
  - irb_case irb_done c_DONE.
  - replace (stepf2 _ _ _ ma) with (c_BAD ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (c_BAD mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    unfold c_BAD. cbn [sim_post]. apply irb_bad_kr. exact K.
  - replace (stepf2 _ _ _ ma) with (IRet Z_MEM_ERROR ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (IRet Z_MEM_ERROR mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    cbn [sim_post]. split; [reflexivity | exact K].
  - replace (stepf2 _ _ _ ma) with (IRet Z_STREAM_ERROR ma) by (unfold stepf2, step2; rewrite Mm, Hmd; reflexivity).
    replace (stepf2 _ _ _ mb) with (IRet Z_STREAM_ERROR mb) by (unfold stepf2, step2; rewrite Hmd; reflexivity).
    cbn [sim_post]. split; [reflexivity | exact K].
Qed.
