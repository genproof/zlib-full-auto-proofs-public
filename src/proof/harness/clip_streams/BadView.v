(* Law rj_bad_checksum: the passes of the switch in the modes of the blocks (TYPE .. LIT, inflate_fast
   included) never read the fields that BadKit.bview replaces (state->wrap, check, total, flags, the saved
   bit buffer state->hold / state->bits, strm->next_in, the count of input bytes `in`), and they read the input
   only at next and after it: the pass on the raw view of a machine is the raw view of the pass on the
   machine.  RESTORE() writes the saved bit buffer and strm->next_in, hence the new hh', bb', x'. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.harness.clip_streams.BadKit.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Model.fast_iter cut into pieces (each one definitionally the corresponding part of it)          *)

(* the refill of the bit buffer before a table walk *)
Definition fi_refill (m: mst) : mst := if m_bits m <? 15 then fpull (fpull m) else m.

(* the extra bits of a length *)
Definition fi_lenx (here: entry) (m: mst) : Z * mst :=
  let len := e_val here in
  let opx := Z.land (e_op here) 15 in
  if negb (opx =? 0) then
    let m := if m_bits m <? opx then fpull m else m in
    (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
  else (len, m).

(* the refill for the extra bits of a distance *)
Definition fi_dpull (opx: Z) (m: mst) : mst :=
  if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m.

(* the copy of a match of length len at distance dist *)
Definition fi_copy (s: istate) (len dist: Z) (m: mst) : bool * mst :=
  let op := Zlength (m_ow m) in
  if op <? dist then
    let op := dist - op in
    if (i_whave s <? op) && negb (i_sane s =? 0) then (false, set_bad m F_far) else
    let w := i_wdata s in
    let wsz := i_wsize s in let wnx := i_wnext s in
    let '(ow, sr, len) :=
      if wnx =? 0 then
        if op <? len then
          let '(ow, _) := copy_bytes w (SWin (wsz - op)) op (m_ow m) in
          (ow, SOut (Zlength ow - dist), len - op)
        else (m_ow m, SWin (wsz - op), len)
      else if wnx <? op then
        let op2 := op - wnx in
        if op2 <? len then
          let '(ow, _) := copy_bytes w (SWin (wsz + wnx - op)) op2 (m_ow m) in
          let len := len - op2 in
          if wnx <? len then
            let '(ow, _) := copy_bytes w (SWin 0) wnx ow in
            (ow, SOut (Zlength ow - dist), len - wnx)
          else (ow, SWin 0, len)
        else (m_ow m, SWin (wsz + wnx - op), len)
      else
        if op <? len then
          let '(ow, _) := copy_bytes w (SWin (wnx - op)) op (m_ow m) in
          (ow, SOut (Zlength ow - dist), len - op)
        else (m_ow m, SWin (wnx - op), len) in
    let '(ow, _) := copy_bytes w sr len ow in
    (true, set_m_ow m ow)
  else
    let '(ow, _) := copy_bytes (i_wdata s) (SOut (Zlength (m_ow m) - dist)) len (m_ow m) in
    (true, set_m_ow m ow).

(* the distance code, its extra bits and the copy *)
Definition fi_dist (fx dx: list entry) (s: istate) (len: Z) (m: mst) : bool * mst :=
  let m := fi_refill m in
  let '(here, m) := fwalk_f fx dx 2 dist_link (i_distcode s)
                      (tab_entry fx dx s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m in
  let op := e_op here in
  if negb (Z.land op 16 =? 0) then
    let opx := Z.land op 15 in
    let m := fi_dpull opx m in
    let dist := u32 (e_val here + m_hold m mod 2 ^ opx) in
    let m := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)) in
    fi_copy s len dist m
  else (false, set_bad m F_d_code).

Definition fi_iter (fx dx: list entry) (m: mst) : bool * mst :=
  let s := m_s m in
  let m := fi_refill m in
  let '(here, m) := fwalk_f fx dx 2 len_link (i_lencode s)
                      (tab_entry fx dx s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m in
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ [e_val here mod 256]))
  else if negb (Z.land op 16 =? 0) then
    let '(len, m) := fi_lenx here m in fi_dist fx dx s len m
  else if negb (Z.land op 32 =? 0) then (false, set_mode m TYPE)
  else (false, set_bad m F_ll_code).

Lemma fi_iter_eq fx dx m : fast_iter fx dx m = fi_iter fx dx m.
Proof. reflexivity. Qed.


(* Model.codelens_iter cut into pieces: the repeat codes 16, 17, 18 (their extra bits) *)
Definition cl_rep (here: entry) (m: mst) : mst * Z * Z * bool :=
  if e_val here =? 16 then
    let m := needbits (e_bits here + 2) m in
    if m_leave m =? 1 then (m, 0, 0, false) else
    let m := dropbits (e_bits here) m in
    if i_have (m_s m) =? 0 then (set_bad m M_repeat, 0, 0, true) else
    let len := Znth (i_have (m_s m) - 1) (i_lens (m_s m)) in
    let copy := 3 + bitsn m 2 in
    (dropbits 2 m, len, copy, true)
  else if e_val here =? 17 then
    let m := needbits (e_bits here + 3) m in
    if m_leave m =? 1 then (m, 0, 0, false) else
    let m := dropbits (e_bits here) m in
    let copy := 3 + bitsn m 3 in
    (dropbits 3 m, 0, copy, true)
  else
    let m := needbits (e_bits here + 7) m in
    if m_leave m =? 1 then (m, 0, 0, false) else
    let m := dropbits (e_bits here) m in
    let copy := 11 + bitsn m 7 in
    (dropbits 7 m, 0, copy, true).

Definition cl_iter (fx dx: list entry) (m: mst) : clout :=
  let s := m_s m in
  let '(here, m, ok) := lookup1 fx dx (i_lencode s) (i_lenbits s) m in
  if negb ok then CLleave m else
  if e_val here <? 16 then
    let m := dropbits (e_bits here) m in
    CLnext (upd_s m (fun s => set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) (e_val here)))
                                         (i_have s + 1)))
  else
    let '(m, len, copy, ok) := cl_rep here m in
    if negb ok then CLleave m else
    if m_mode m =? BAD then CLbad m else
    let s := m_s m in
    if i_nlen s + i_ndist s <? i_have s + copy then CLbad (set_bad m M_repeat) else
    CLnext (upd_s m (lens_fill (Z.to_nat copy) len)).

Lemma cl_iter_eq fx dx m : codelens_iter fx dx m = cl_iter fx dx m.
Proof. reflexivity. Qed.

(* case split on the pair a `let '(_, _) :=` matches *)
Ltac dpair := match goal with |- context [match ?X with pair _ _ => _ end] =>
  lazymatch X with context [bview] => fail | _ => destruct X end end.

(* ---------------------------------------------------------------------------------------------- *)
(* The view on the fields, the setters and the input primitives                                   *)

Section View.
Variables (d x hh bb w c t f: Z).
Local Notation V := (bview d x hh bb w c t f).

(* the state as the view has it *)
Definition bv_rep (s: istate) : istate :=
  set_i_flags (set_i_total (set_i_check (set_i_wrap (set_i_bits (set_i_hold s hh) bb) w) c) t) f.

(* the conditions under which the view reads the same input bytes: the shift d is at most the bytes read
   (next) and the bytes offered *)
Definition bv_good (m: mst) : Prop := 0 <= d <= m_nx m /\ d <= Zlength (m_inp m).

Lemma bv_s m : m_s (V m) = bv_rep (m_s m).            Proof. reflexivity. Qed.
Lemma bv_mode m : m_mode (V m) = m_mode m.            Proof. reflexivity. Qed.
Lemma bv_hold m : m_hold (V m) = m_hold m.            Proof. reflexivity. Qed.
Lemma bv_bits m : m_bits (V m) = m_bits m.            Proof. reflexivity. Qed.
Lemma bv_ow m : m_ow (V m) = m_ow m.                  Proof. reflexivity. Qed.
Lemma bv_aout m : m_aout (V m) = m_aout m.            Proof. reflexivity. Qed.
Lemma bv_out m : m_out (V m) = m_out m.               Proof. reflexivity. Qed.
Lemma bv_leave m : m_leave (V m) = m_leave m.         Proof. reflexivity. Qed.
Lemma bv_ret m : m_ret (V m) = m_ret m.               Proof. reflexivity. Qed.
Lemma bv_nx m : m_nx (V m) = m_nx m - d.              Proof. reflexivity. Qed.
Lemma bv_left m : m_left (V m) = m_left m.            Proof. reflexivity. Qed.
Lemma bv_bitsn m n : bitsn (V m) n = bitsn m n.       Proof. reflexivity. Qed.

Lemma bv_inplen m : 0 <= d <= Zlength (m_inp m) -> Zlength (m_inp (V m)) = Zlength (m_inp m) - d.
Proof. intros. cbn [bview m_inp]. rewrite Zlength_sublist; lia. Qed.

Lemma bv_have m : 0 <= d <= Zlength (m_inp m) -> m_have (V m) = m_have m.
Proof. intros. unfold m_have. rewrite bv_inplen by lia. rewrite bv_nx. lia. Qed.

(* the byte at next *)
Lemma bv_byte m : bv_good m -> Znth (m_nx (V m)) (m_inp (V m)) = Znth (m_nx m) (m_inp m).
Proof.
  intros [H1 H2]. rewrite bv_nx. cbn [bview m_inp].
  destruct (Z_lt_le_dec (m_nx m) (Zlength (m_inp m))).
  - rewrite Znth_sublist by lia. f_equal. lia.
  - rewrite !Znth_overflow; auto; try lia. rewrite Zlength_sublist; lia.
Qed.

(* the fields of the state the view keeps *)
Lemma bvr_mode s : i_mode (bv_rep s) = i_mode s.         Proof. reflexivity. Qed.
Lemma bvr_last s : i_last (bv_rep s) = i_last s.         Proof. reflexivity. Qed.
Lemma bvr_length s : i_length (bv_rep s) = i_length s.   Proof. reflexivity. Qed.
Lemma bvr_offset s : i_offset (bv_rep s) = i_offset s.   Proof. reflexivity. Qed.
Lemma bvr_extra s : i_extra (bv_rep s) = i_extra s.      Proof. reflexivity. Qed.
Lemma bvr_lencode s : i_lencode (bv_rep s) = i_lencode s.     Proof. reflexivity. Qed.
Lemma bvr_distcode s : i_distcode (bv_rep s) = i_distcode s.  Proof. reflexivity. Qed.
Lemma bvr_lenbits s : i_lenbits (bv_rep s) = i_lenbits s.     Proof. reflexivity. Qed.
Lemma bvr_distbits s : i_distbits (bv_rep s) = i_distbits s.  Proof. reflexivity. Qed.
Lemma bvr_ncode s : i_ncode (bv_rep s) = i_ncode s.      Proof. reflexivity. Qed.
Lemma bvr_nlen s : i_nlen (bv_rep s) = i_nlen s.         Proof. reflexivity. Qed.
Lemma bvr_ndist s : i_ndist (bv_rep s) = i_ndist s.      Proof. reflexivity. Qed.
Lemma bvr_have s : i_have (bv_rep s) = i_have s.         Proof. reflexivity. Qed.
Lemma bvr_next s : i_next (bv_rep s) = i_next s.         Proof. reflexivity. Qed.
Lemma bvr_lens s : i_lens (bv_rep s) = i_lens s.         Proof. reflexivity. Qed.
Lemma bvr_codes s : i_codes (bv_rep s) = i_codes s.      Proof. reflexivity. Qed.
Lemma bvr_wdata s : i_wdata (bv_rep s) = i_wdata s.      Proof. reflexivity. Qed.
Lemma bvr_wsize s : i_wsize (bv_rep s) = i_wsize s.      Proof. reflexivity. Qed.
Lemma bvr_whave s : i_whave (bv_rep s) = i_whave s.      Proof. reflexivity. Qed.
Lemma bvr_wnext s : i_wnext (bv_rep s) = i_wnext s.      Proof. reflexivity. Qed.
Lemma bvr_sane s : i_sane (bv_rep s) = i_sane s.         Proof. reflexivity. Qed.
Lemma bvr_back s : i_back (bv_rep s) = i_back s.         Proof. reflexivity. Qed.
Lemma bvr_was s : i_was (bv_rep s) = i_was s.            Proof. reflexivity. Qed.

Lemma bv_tab fx dx s tr i : tab_entry fx dx (bv_rep s) tr i = tab_entry fx dx s tr i.
Proof. destruct tr; reflexivity. Qed.

(* the setters of the machine *)
Lemma bv_set_bits m v : set_m_bits (V m) v = V (set_m_bits m v).    Proof. reflexivity. Qed.
Lemma bv_set_hold m v : set_m_hold (V m) v = V (set_m_hold m v).    Proof. reflexivity. Qed.
Lemma bv_set_ow m v : set_m_ow (V m) v = V (set_m_ow m v).          Proof. reflexivity. Qed.
Lemma bv_set_leave m v : set_m_leave (V m) v = V (set_m_leave m v). Proof. reflexivity. Qed.
Lemma bv_set_ret m v : set_m_ret (V m) v = V (set_m_ret m v).       Proof. reflexivity. Qed.
Lemma bv_set_msg m v : set_m_msg (V m) v = V (set_m_msg m v).       Proof. reflexivity. Qed.
Lemma bv_set_nx m v : set_m_nx (V m) v = V (set_m_nx m (v + d)).
Proof. unfold bview, set_m_nx; cbn. f_equal. lia. Qed.
Lemma bv_set_s m s : set_m_s (V m) (bv_rep s) = V (set_m_s m s).    Proof. reflexivity. Qed.

(* a state update that commutes with the replaced fields *)
Lemma bv_upd m g g' : g (bv_rep (m_s m)) = bv_rep (g' (m_s m)) -> upd_s (V m) g = V (upd_s m g').
Proof. intros E. unfold upd_s. rewrite bv_s, E. reflexivity. Qed.

Lemma bv_set_mode m v : set_mode (V m) v = V (set_mode m v).
Proof. apply bv_upd. destruct (m_s m); reflexivity. Qed.
Lemma bv_set_leave' m : set_leave (V m) = V (set_leave m).          Proof. reflexivity. Qed.
Lemma bv_set_bad m e : set_bad (V m) e = V (set_bad m e).
Proof. unfold set_bad. rewrite bv_set_msg. apply bv_set_mode. Qed.
Lemma bv_dropbits n m : dropbits n (V m) = V (dropbits n m).        Proof. reflexivity. Qed.
Lemma bv_initbits m : initbits (V m) = V (initbits m).              Proof. reflexivity. Qed.
Lemma bv_bytebits m : bytebits (V m) = V (bytebits m).              Proof. reflexivity. Qed.

Lemma bv_pull m : bv_good m -> pull (V m) = V (pull m).
Proof.
  intros G. unfold pull. rewrite (bv_byte m G), bv_nx, bv_hold, bv_bits, bv_set_nx, bv_set_hold, bv_set_bits.
  replace (m_nx m - d + 1 + d) with (m_nx m + 1) by lia. reflexivity.
Qed.

(* bv_good along the steps *)
Lemma bvg_nx m v : bv_good m -> m_nx m <= v -> bv_good (set_m_nx m v).
Proof. unfold bv_good; cbn; lia. Qed.
Lemma bvg_pull m : bv_good m -> bv_good (pull m).
Proof. unfold bv_good, pull; cbn; lia. Qed.

Lemma bvg_set_bits m v : bv_good m -> bv_good (set_m_bits m v).    Proof. auto. Qed.
Lemma bvg_set_hold m v : bv_good m -> bv_good (set_m_hold m v).    Proof. auto. Qed.
Lemma bvg_set_ow m v : bv_good m -> bv_good (set_m_ow m v).        Proof. auto. Qed.
Lemma bvg_set_leave m : bv_good m -> bv_good (set_leave m).        Proof. auto. Qed.
Lemma bvg_set_ret m v : bv_good m -> bv_good (set_m_ret m v).      Proof. auto. Qed.
Lemma bvg_set_s m v : bv_good m -> bv_good (set_m_s m v).          Proof. auto. Qed.
Lemma bvg_upd m g : bv_good m -> bv_good (upd_s m g).              Proof. auto. Qed.
Lemma bvg_set_mode m v : bv_good m -> bv_good (set_mode m v).      Proof. auto. Qed.
Lemma bvg_set_bad m e : bv_good m -> bv_good (set_bad m e).        Proof. auto. Qed.
Lemma bvg_dropbits n m : bv_good m -> bv_good (dropbits n m).      Proof. auto. Qed.
Lemma bvg_initbits m : bv_good m -> bv_good (initbits m).          Proof. auto. Qed.
Lemma bvg_bytebits m : bv_good m -> bv_good (bytebits m).          Proof. auto. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* inflate_fast                                                                                   *)

Lemma bv_fwalk fx dx k il tr here m :
  fwalk_f fx dx k il tr here (V m) = (fst (fwalk_f fx dx k il tr here m), V (snd (fwalk_f fx dx k il tr here m))).
Proof.
  revert here m. induction k as [|k IH]; intros here m; cbn [fwalk_f].
  - reflexivity.
  - rewrite bv_hold, bv_bits, bv_set_hold, bv_set_bits.
    destruct (il (e_op here)); [|reflexivity].
    rewrite bv_s, bv_tab, bv_hold. apply IH.
Qed.

Lemma bv_good_fwalk fx dx k il tr here m : bv_good m -> bv_good (snd (fwalk_f fx dx k il tr here m)).
Proof.
  revert here m. induction k as [|k IH]; intros here m G; cbn [fwalk_f].
  - auto.
  - destruct (il (e_op here)); [apply IH|]; auto.
Qed.



Lemma bv_refill m : bv_good m -> fi_refill (V m) = V (fi_refill m) /\ bv_good (fi_refill m).
Proof.
  intros G. unfold fi_refill. rewrite bv_bits. unfold fpull. destruct (m_bits m <? 15); [|auto].
  rewrite (bv_pull m G), (bv_pull _ (bvg_pull m G)). auto using bvg_pull.
Qed.

Lemma bv_lenx here m : bv_good m ->
  fi_lenx here (V m) = (fst (fi_lenx here m), V (snd (fi_lenx here m))) /\ bv_good (snd (fi_lenx here m)).
Proof.
  intros G. unfold fi_lenx, fpull. destruct (negb (Z.land (e_op here) 15 =? 0)); [|auto].
  rewrite bv_bits. destruct (m_bits m <? Z.land (e_op here) 15).
  - rewrite (bv_pull m G). split; [reflexivity|]. apply bvg_pull in G. auto.
  - auto.
Qed.

Lemma bv_dpull opx m : bv_good m -> fi_dpull opx (V m) = V (fi_dpull opx m) /\ bv_good (fi_dpull opx m).
Proof.
  intros G. unfold fi_dpull, fpull. rewrite bv_bits. destruct (m_bits m <? opx); [|auto].
  rewrite (bv_pull m G), bv_bits. pose proof (bvg_pull m G) as G1.
  destruct (m_bits (pull m) <? opx); [|auto]. rewrite (bv_pull _ G1). auto using bvg_pull.
Qed.

Lemma bv_copy s len dist m :
  fi_copy (bv_rep s) len dist (V m) = (fst (fi_copy s len dist m), V (snd (fi_copy s len dist m))).
Proof.
  unfold fi_copy. rewrite !bvr_whave, !bvr_sane, !bvr_wdata, !bvr_wsize, !bvr_wnext, !bv_ow.
  destruct (Zlength (m_ow m) <? dist).
  - destruct ((i_whave s <? dist - Zlength (m_ow m)) && negb (i_sane s =? 0)).
    + rewrite bv_set_bad. reflexivity.
    + repeat dpair. reflexivity.
  - repeat dpair. reflexivity.
Qed.

Lemma bvg_copy s len dist m : bv_good m -> bv_good (snd (fi_copy s len dist m)).
Proof.
  intros G. unfold fi_copy.
  destruct (Zlength (m_ow m) <? dist).
  - destruct ((i_whave s <? dist - Zlength (m_ow m)) && negb (i_sane s =? 0)).
    + auto.
    + repeat dpair. auto.
  - repeat dpair. auto.
Qed.

Lemma bv_dist fx dx s len m : bv_good m ->
  fi_dist fx dx (bv_rep s) len (V m) = (fst (fi_dist fx dx s len m), V (snd (fi_dist fx dx s len m))) /\
  bv_good (snd (fi_dist fx dx s len m)).
Proof.
  intros G. unfold fi_dist.
  destruct (bv_refill m G) as [E1 G1]. rewrite E1.
  rewrite !bvr_distcode, !bvr_distbits, bv_tab, bv_hold, bv_fwalk.
  pose proof (bv_good_fwalk fx dx 2 dist_link (i_distcode s)
    (tab_entry fx dx s (i_distcode s) (m_hold (fi_refill m) mod 2 ^ i_distbits s)) (fi_refill m) G1) as G2.
  destruct (fwalk_f fx dx 2 dist_link (i_distcode s) _ (fi_refill m)) as [h m2]. cbn [fst snd] in *.
  destruct (negb (Z.land (e_op h) 16 =? 0)); [|auto].
  destruct (bv_dpull (Z.land (e_op h) 15) m2 G2) as [E3 G3]. rewrite E3, bv_hold.
  rewrite bv_bits, bv_set_hold, bv_set_bits, bv_copy.
  split; [reflexivity|]. apply bvg_copy. auto.
Qed.

Lemma bv_fi_iter fx dx m : bv_good m ->
  fi_iter fx dx (V m) = (fst (fi_iter fx dx m), V (snd (fi_iter fx dx m))) /\ bv_good (snd (fi_iter fx dx m)).
Proof.
  intros G. unfold fi_iter.
  destruct (bv_refill m G) as [E1 G1]. rewrite E1.
  rewrite !bv_s, !bvr_lencode, !bvr_lenbits, bv_tab, bv_hold, bv_fwalk.
  pose proof (bv_good_fwalk fx dx 2 len_link (i_lencode (m_s m))
    (tab_entry fx dx (m_s m) (i_lencode (m_s m)) (m_hold (fi_refill m) mod 2 ^ i_lenbits (m_s m))) (fi_refill m) G1)
    as G2.
  destruct (fwalk_f fx dx 2 len_link (i_lencode (m_s m)) _ (fi_refill m)) as [h m2]. cbn [fst snd] in *.
  destruct (e_op h =? 0); [auto|].
  destruct (negb (Z.land (e_op h) 16 =? 0)).
  - destruct (bv_lenx h m2 G2) as [E3 G3]. rewrite E3.
    destruct (fi_lenx h m2) as [ln m3]. cbn [fst snd] in *. apply bv_dist. auto.
  - destruct (negb (Z.land (e_op h) 32 =? 0)); rewrite ?bv_set_mode, ?bv_set_bad; auto.
Qed.

Lemma ltb_shift a b : (a - d <? b - d - 5) = (a <? b - 5).
Proof. destruct (Z.ltb_spec (a - d) (b - d - 5)), (Z.ltb_spec a (b - 5)); auto; lia. Qed.

Lemma bv_fast_loop fx dx k m : bv_good m ->
  fast_loop fx dx k (V m) = V (fast_loop fx dx k m) /\ bv_good (fast_loop fx dx k m).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [fast_loop]; [auto|].
  rewrite (fi_iter_eq fx dx (V m)), (fi_iter_eq fx dx m). destruct (bv_fi_iter fx dx m G) as [E1 G1]. rewrite E1.
  destruct (fi_iter fx dx m) as [go m2]. cbn [fst snd] in *.
  rewrite bv_nx, bv_inplen, bv_ow, bv_aout by (unfold bv_good in G1; lia).
  rewrite ltb_shift.
  destruct (go && (m_nx m2 <? Zlength (m_inp m2) - 5) && (Zlength (m_ow m2) <? m_aout m2 - 257)); auto.
Qed.

Lemma bv_restore m : restore (V m) = bview d (m_nx m - d) (m_hold m) (m_bits m) w c t f (restore m).
Proof. reflexivity. Qed.

End View.

(* inflate_fast on the view: its RESTORE() stores next, hold and bits of the result *)
Lemma bad_view_fast_eq fx dx d x hh bb w c t f m : bv_good d m ->
  fast fx dx (bview d x hh bb w c t f m) =
  bview d (m_nx (fast fx dx m) - d) (m_hold (fast fx dx m)) (m_bits (fast fx dx m)) w c t f (fast fx dx m).
Proof.
  intros G. unfold fast. rewrite bv_aout.
  destruct (bv_fast_loop d x hh bb w c t f fx dx (Z.to_nat (m_aout m) + 1) m G) as [E1 _]. rewrite E1.
  set (m2 := fast_loop fx dx (Z.to_nat (m_aout m) + 1) m). clearbody m2.
  rewrite bv_bits, bv_nx, bv_set_nx, bv_hold, bv_bits, bv_set_hold, bv_set_bits, bv_restore.
  replace (m_nx m2 - d - Z.shiftr (m_bits m2) 3 + d) with (m_nx m2 - Z.shiftr (m_bits m2) 3) by lia.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The primitives of the cases                                                                    *)

(* the same, also skipping the pairs that still contain the view of a state *)
Ltac dpair ::= match goal with |- context [match ?X with pair _ _ => _ end] =>
  lazymatch X with context [bview] => fail | context [bv_rep] => fail | _ => destruct X end end.

Section Step.
Variables (d x hh bb w c t f: Z).
Local Notation V := (bview d x hh bb w c t f).
Local Notation rep := (bv_rep hh bb w c t f).

Local Hint Resolve bvg_set_bits bvg_set_hold bvg_set_ow bvg_set_leave bvg_set_ret bvg_set_s bvg_upd bvg_set_mode
  bvg_set_bad bvg_dropbits bvg_initbits bvg_bytebits bvg_pull : bvg.

(* bv_good through the setters (`auto` is slow here: it tries the hypotheses up to conversion) *)
Ltac bvg_solve :=
  repeat first [ simple apply bvg_set_bits | simple apply bvg_set_hold | simple apply bvg_set_ow
               | simple apply bvg_set_leave | simple apply bvg_set_ret | simple apply bvg_set_s | simple apply bvg_upd
               | simple apply bvg_set_mode | simple apply bvg_set_bad | simple apply bvg_dropbits
               | simple apply bvg_initbits | simple apply bvg_bytebits | simple apply bvg_pull ];
  assumption.

Lemma bv_upd_c m g : (forall s, g (rep s) = rep (g s)) -> upd_s (V m) g = V (upd_s m g).
Proof. intros E. apply bv_upd. apply E. Qed.

Lemma bv_lenlens_zero k s : lenlens_zero k (rep s) = rep (lenlens_zero k s).
Proof.
  revert s. induction k as [|k IH]; intros s; cbn [lenlens_zero]; [auto|].
  rewrite bvr_have. destruct (i_have s <? 19); [|auto]. rewrite <- IH. f_equal.
Qed.

Lemma lens_fill_S k len s :
  lens_fill (S k) len s = lens_fill k len (set_i_have (set_i_lens s (upd_Znth (i_have s) (i_lens s) len)) (i_have s + 1)).
Proof. reflexivity. Qed.

Lemma bv_lens_fill k len s : lens_fill k len (rep s) = rep (lens_fill k len s).
Proof.
  revert s. induction k as [|k IH]; intros s; [reflexivity|].
  rewrite !lens_fill_S, bvr_have, bvr_lens. etransitivity; [|apply IH]. f_equal.
Qed.

Lemma bv_call_table type lo n req s : call_table type lo n req (rep s) = call_table type lo n req s.
Proof. unfold call_table. rewrite bvr_next, bvr_codes, bvr_lens. reflexivity. Qed.

Lemma bvr_set_lenbits s v : set_i_lenbits (rep s) v = rep (set_i_lenbits s v).    Proof. reflexivity. Qed.
Lemma bvr_set_distbits s v : set_i_distbits (rep s) v = rep (set_i_distbits s v).  Proof. reflexivity. Qed.
Lemma bvr_set_lencode s v : set_i_lencode (rep s) v = rep (set_i_lencode s v).    Proof. reflexivity. Qed.
Lemma bvr_set_distcode s v : set_i_distcode (rep s) v = rep (set_i_distcode s v).  Proof. reflexivity. Qed.
Lemma bvr_set_next s v : set_i_next (rep s) v = rep (set_i_next s v).             Proof. reflexivity. Qed.
Lemma bvr_set_codes s v : set_i_codes (rep s) v = rep (set_i_codes s v).          Proof. reflexivity. Qed.

Lemma bv_upd_fill m k len : upd_s (V m) (lens_fill k len) = V (upd_s m (lens_fill k len)).
Proof. apply bv_upd. apply bv_lens_fill. Qed.

(* the lemma that pushes the view out of `g (view ..)`, chosen by the head g *)
Ltac bvhead g :=
  lazymatch g with
  | m_s => rewrite bv_s | m_mode => rewrite bv_mode | m_hold => rewrite bv_hold | m_bits => rewrite bv_bits
  | m_ow => rewrite bv_ow | m_aout => rewrite bv_aout | m_out => rewrite bv_out | m_leave => rewrite bv_leave
  | m_ret => rewrite bv_ret | m_left => rewrite bv_left | set_leave => rewrite bv_set_leave'
  | dropbits _ => rewrite bv_dropbits | initbits => rewrite bv_initbits | bytebits => rewrite bv_bytebits
  end.
Ltac bvhead2 g :=
  lazymatch g with
  | set_m_bits => rewrite bv_set_bits | set_m_hold => rewrite bv_set_hold | set_m_ow => rewrite bv_set_ow
  | set_m_leave => rewrite bv_set_leave | set_m_ret => rewrite bv_set_ret | set_m_msg => rewrite bv_set_msg
  | set_mode => rewrite bv_set_mode | set_bad => rewrite bv_set_bad | bitsn => rewrite bv_bitsn
  | set_m_s => rewrite bv_set_s
  | upd_s => first [ rewrite bv_upd_fill | rewrite bv_upd_c by (intro; reflexivity) ]
  end.
Ltac bvrhead g :=
  lazymatch g with
  | i_mode => rewrite bvr_mode | i_last => rewrite bvr_last | i_length => rewrite bvr_length
  | i_offset => rewrite bvr_offset | i_extra => rewrite bvr_extra | i_lencode => rewrite bvr_lencode
  | i_distcode => rewrite bvr_distcode | i_lenbits => rewrite bvr_lenbits | i_distbits => rewrite bvr_distbits
  | i_ncode => rewrite bvr_ncode | i_nlen => rewrite bvr_nlen | i_ndist => rewrite bvr_ndist
  | i_have => rewrite bvr_have | i_next => rewrite bvr_next | i_lens => rewrite bvr_lens
  | i_codes => rewrite bvr_codes | i_wdata => rewrite bvr_wdata | i_wsize => rewrite bvr_wsize
  | i_whave => rewrite bvr_whave | i_wnext => rewrite bvr_wnext | i_sane => rewrite bvr_sane
  | i_back => rewrite bvr_back | i_was => rewrite bvr_was
  | lenlens_zero _ => rewrite bv_lenlens_zero | call_table _ _ _ _ => rewrite bv_call_table
  end.
Ltac bvrhead2 g :=
  lazymatch g with
  | set_i_lenbits => rewrite bvr_set_lenbits | set_i_distbits => rewrite bvr_set_distbits
  | set_i_lencode => rewrite bvr_set_lencode | set_i_distcode => rewrite bvr_set_distcode
  | set_i_next => rewrite bvr_set_next | set_i_codes => rewrite bvr_set_codes
  end.

(* pushes the view out of the getters and setters: one subterm `g (view ..)` at a time, the lemma chosen by
   the head g *)
Ltac bvp :=
  repeat match goal with
  | |- context [?g (bview _ _ _ _ _ _ _ _ _)] => bvhead g
  | |- context [?g (bview _ _ _ _ _ _ _ _ _) _] => bvhead2 g
  | |- context [?g (bv_rep _ _ _ _ _ _ _)] => bvrhead g
  | |- context [?g (bv_rep _ _ _ _ _ _ _) _] => bvrhead2 g
  | |- context [tab_entry _ _ (bv_rep _ _ _ _ _ _ _) _ _] => rewrite bv_tab
  end.

Lemma bv_needbits k n m : bv_good d m ->
  needbits_f k n (V m) = V (needbits_f k n m) /\ bv_good d (needbits_f k n m).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [needbits_f]; [auto|].
  rewrite bv_bits, bv_have by (unfold bv_good in G; lia).
  destruct (m_bits m <? n); [|auto]. destruct (m_have m =? 0); [auto with bvg|].
  rewrite (bv_pull _ _ _ _ _ _ _ _ m G). apply IH. auto with bvg.
Qed.

Lemma bv_lookup1 fx dx k tr nb m : bv_good d m ->
  lookup1_f k fx dx tr nb (V m) =
    (fst (fst (lookup1_f k fx dx tr nb m)), V (snd (fst (lookup1_f k fx dx tr nb m))),
     snd (lookup1_f k fx dx tr nb m)) /\
  bv_good d (snd (fst (lookup1_f k fx dx tr nb m))).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [lookup1_f]; bvp; [auto|].
  rewrite bv_have by (unfold bv_good in G; lia).
  destruct (e_bits _ <=? m_bits m); [auto|]. destruct (m_have m =? 0); [auto with bvg|].
  rewrite (bv_pull _ _ _ _ _ _ _ _ m G). apply IH. auto with bvg.
Qed.

Lemma bv_lookup2 fx dx k tr last m : bv_good d m ->
  lookup2_f k fx dx tr last (V m) =
    (fst (fst (lookup2_f k fx dx tr last m)), V (snd (fst (lookup2_f k fx dx tr last m))),
     snd (lookup2_f k fx dx tr last m)) /\
  bv_good d (snd (fst (lookup2_f k fx dx tr last m))).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [lookup2_f]; bvp; [auto|].
  rewrite bv_have by (unfold bv_good in G; lia).
  destruct (e_bits last + e_bits _ <=? m_bits m); [auto|]. destruct (m_have m =? 0); [auto with bvg|].
  rewrite (bv_pull _ _ _ _ _ _ _ _ m G). apply IH. auto with bvg.
Qed.

Lemma bv_lenlens_loop k m : bv_good d m ->
  lenlens_loop k (V m) = V (lenlens_loop k m) /\ bv_good d (lenlens_loop k m).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [lenlens_loop]; [auto|].
  bvp. destruct (i_have (m_s m) <? i_ncode (m_s m)); [|auto].
  destruct (bv_needbits 4 3 m G) as [E1 G1]. unfold needbits. rewrite E1, bv_leave.
  destruct (m_leave (needbits_f 4 3 m) =? 1); [auto|].
  rewrite (bv_upd d x hh bb w c t f _ _
    (fun _ => set_i_have (set_i_lens (m_s (needbits_f 4 3 m))
       (upd_Znth (Znth (i_have (m_s (needbits_f 4 3 m))) order) (i_lens (m_s (needbits_f 4 3 m)))
          (bitsn (needbits_f 4 3 m) 3))) (i_have (m_s (needbits_f 4 3 m)) + 1))) by reflexivity.
  bvp. apply IH. auto with bvg.
Qed.

Lemma bv_lookup1' fx dx k tr nb m h m' ok : bv_good d m -> lookup1_f k fx dx tr nb m = (h, m', ok) ->
  lookup1_f k fx dx tr nb (V m) = (h, V m', ok) /\ bv_good d m'.
Proof. intros G E. destruct (bv_lookup1 fx dx k tr nb m G) as [E1 G1]. rewrite E in E1, G1. auto. Qed.

Lemma bv_lookup2' fx dx k tr last m h m' ok : bv_good d m -> lookup2_f k fx dx tr last m = (h, m', ok) ->
  lookup2_f k fx dx tr last (V m) = (h, V m', ok) /\ bv_good d m'.
Proof. intros G E. destruct (bv_lookup2 fx dx k tr last m G) as [E1 G1]. rewrite E in E1, G1. auto. Qed.

Lemma bv_inbytes m n : bv_good d m -> n <= m_have m -> inbytes (V m) n = inbytes m n.
Proof.
  intros [G1 G2] Hn. unfold inbytes, m_have in *. cbn [bview m_inp m_nx].
  destruct (Z_le_gt_dec n 0).
  - rewrite !sublist_nil_gen by lia. reflexivity.
  - rewrite sublist_sublist by lia. f_equal; lia.
Qed.

(* one step of the case tactic: the input primitives (with their bv_good), the getters and setters, the
   conditions, the pairs *)
Ltac bvstep :=
  first
    [ match goal with |- context [needbits_f ?k ?n (V ?m)] =>
        let G := fresh "G" in let E := fresh "E" in
        destruct (bv_needbits k n m ltac:(bvg_solve)) as [E G]; rewrite E; clear E end
    | match goal with |- context [lookup1_f ?k ?fx ?dx ?tr ?nb (V ?m)] =>
        let G := fresh "G" in let E := fresh "E" in let h := fresh "h" in let m' := fresh "m" in
        let ok := fresh "ok" in
        destruct (lookup1_f k fx dx tr nb m) as [[h m'] ok] eqn:E;
        apply (bv_lookup1' fx dx k tr nb m h m' ok ltac:(bvg_solve)) in E; destruct E as [E G];
        rewrite E; clear E end
    | match goal with |- context [lookup2_f ?k ?fx ?dx ?tr ?la (V ?m)] =>
        let G := fresh "G" in let E := fresh "E" in let h := fresh "h" in let m' := fresh "m" in
        let ok := fresh "ok" in
        destruct (lookup2_f k fx dx tr la m) as [[h m'] ok] eqn:E;
        apply (bv_lookup2' fx dx k tr la m h m' ok ltac:(bvg_solve)) in E; destruct E as [E G];
        rewrite E; clear E end
    | progress cbv beta iota zeta
    | match goal with |- context [if ?b then _ else _] =>
        lazymatch b with context [bview] => fail | _ => destruct b end end
    | dpair ].

Ltac bvcase := unfold needbits, lookup1, lookup2 in *; repeat (bvp; bvstep); cbn [iomap fst snd]; try reflexivity.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases of the switch in the block modes, from the last one (fallthroughs use the next case)  *)

Lemma bv_c_MATCH m : c_MATCH (V m) = iomap V (c_MATCH m).
Proof. unfold c_MATCH. bvcase. Qed.

Lemma bv_c_LIT m : c_LIT (V m) = iomap V (c_LIT m).
Proof. unfold c_LIT. bvcase. Qed.

Lemma bv_c_DISTEXT m : bv_good d m -> c_DISTEXT (V m) = iomap V (c_DISTEXT m).
Proof. intros G. unfold c_DISTEXT. bvcase; apply bv_c_MATCH. Qed.


Lemma bv_c_DIST fx dx m : bv_good d m -> c_DIST fx dx (V m) = iomap V (c_DIST fx dx m).
Proof. intros G. unfold c_DIST. bvcase; apply bv_c_DISTEXT; auto with bvg. Qed.

Lemma bv_c_LENEXT fx dx m : bv_good d m -> c_LENEXT fx dx (V m) = iomap V (c_LENEXT fx dx m).
Proof. intros G. unfold c_LENEXT. bvcase; apply bv_c_DIST; auto with bvg. Qed.

Lemma bv_c_COPY m : bv_good d m -> c_COPY (V m) = iomap V (c_COPY m).
Proof.
  intros G. unfold c_COPY. bvp. rewrite bv_have by (unfold bv_good in G; lia).
  destruct (i_length (m_s m) =? 0); cbn [negb]; [bvcase|].
  destruct (Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) =? 0); [bvcase|].
  rewrite bv_inbytes by (auto; lia). bvp. rewrite bv_nx, bv_set_nx.
  replace (m_nx m - d + Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m) + d)
    with (m_nx m + Z.min (Z.min (i_length (m_s m)) (m_have m)) (m_left m)) by lia.
  bvcase.
Qed.

Lemma bv_c_COPY_ m : bv_good d m -> c_COPY_ (V m) = iomap V (c_COPY_ m).
Proof. intros G. unfold c_COPY_. bvp. apply bv_c_COPY. auto with bvg. Qed.

Lemma bv_c_STORED flush m : bv_good d m -> c_STORED flush (V m) = iomap V (c_STORED flush m).
Proof. intros G. unfold c_STORED. bvcase; apply bv_c_COPY_; auto with bvg. Qed.

Lemma bv_c_TYPEDO flush m : bv_good d m -> c_TYPEDO flush (V m) = iomap V (c_TYPEDO flush m).
Proof. intros G. unfold c_TYPEDO. bvcase. Qed.

Lemma bv_c_TYPE flush m : bv_good d m -> c_TYPE flush (V m) = iomap V (c_TYPE flush m).
Proof. intros G. unfold c_TYPE. bvp. destruct ((flush =? Z_BLOCK) || (flush =? Z_TREES)); [bvcase|].
  apply bv_c_TYPEDO; auto. Qed.

(* LEN: the fast path runs inflate_fast, whose RESTORE() stores next, hold and bits *)
Lemma bv_c_LEN fx dx m : bv_good d m -> exists x' hh' bb',
  c_LEN fx dx (fast fx dx) (V m) = iomap (bview d x' hh' bb' w c t f) (c_LEN fx dx (fast fx dx) m).
Proof.
  intros G. unfold c_LEN at 1 2. rewrite bv_have, bv_left, bv_bits by (unfold bv_good in G; lia).
  destruct ((6 <=? m_have m) && (258 <=? m_left m) && (m_bits m <? 8)).
  - rewrite bv_restore, bad_view_fast_eq by exact G.
    generalize (fast fx dx (restore m)). intros F. exists (m_nx F - d), (m_hold F), (m_bits F).
    cbn [iomap]. rewrite bv_mode. destruct (m_mode F =? TYPE);
    reflexivity.
  - exists x, hh, bb. bvcase; apply bv_c_LENEXT; auto with bvg.
Qed.

Lemma bv_c_LEN_ fx dx m : bv_good d m -> exists x' hh' bb',
  c_LEN_ fx dx (fast fx dx) (V m) = iomap (bview d x' hh' bb' w c t f) (c_LEN_ fx dx (fast fx dx) m).
Proof. intros G. unfold c_LEN_. rewrite bv_set_mode. apply bv_c_LEN. auto with bvg. Qed.

Definition clmap (g: mst -> mst) (o: clout) : clout :=
  match o with CLnext m => CLnext (g m) | CLleave m => CLleave (g m) | CLbad m => CLbad (g m) end.
Definition clgood (o: clout) : Prop :=
  match o with CLnext m | CLleave m | CLbad m => bv_good d m end.

Lemma bv_cl_rep here m m' len copy ok : bv_good d m -> cl_rep here m = (m', len, copy, ok) ->
  cl_rep here (V m) = (V m', len, copy, ok) /\ bv_good d m'.
Proof.
  intros G E.
  enough (H: cl_rep here (V m) = (let '(m', len, copy, ok) := cl_rep here m in (V m', len, copy, ok)) /\
             (let '(m', _, _, _) := cl_rep here m in bv_good d m')) by (rewrite E in H; exact H).
  unfold cl_rep. bvcase; split; (reflexivity || bvg_solve).
Qed.

Lemma bv_codelens_iter fx dx m : bv_good d m ->
  codelens_iter fx dx (V m) = clmap V (codelens_iter fx dx m) /\ clgood (codelens_iter fx dx m).
Proof.
  intros G. rewrite (cl_iter_eq fx dx (V m)), (cl_iter_eq fx dx m). unfold cl_iter, lookup1. bvp. bvstep. cbv beta iota zeta. bvp.
  destruct (negb ok); [cbn [clmap clgood]; split; [reflexivity | assumption]|].
  destruct (e_val h <? 16); [bvcase; cbn [clmap clgood]; (split; [reflexivity | bvg_solve])|].
  destruct (cl_rep h m0) as [[[m1 len] copy] ok'] eqn:E.
  apply (bv_cl_rep h m0 m1 len copy ok' G0) in E. destruct E as [E G1]. rewrite E.
  bvcase; cbn [clmap clgood]; (split; [reflexivity | bvg_solve]).
Qed.

Lemma bv_codelens_loop fx dx k m : bv_good d m ->
  codelens_loop fx dx k (V m) = clmap V (codelens_loop fx dx k m) /\ clgood (codelens_loop fx dx k m).
Proof.
  revert m. induction k as [|k IH]; intros m G; cbn [codelens_loop]; [auto|].
  bvp. destruct (i_have (m_s m) <? i_nlen (m_s m) + i_ndist (m_s m)); [|auto].
  destruct (bv_codelens_iter fx dx m G) as [E1 G1]. rewrite E1.
  destruct (codelens_iter fx dx m); cbn [clmap clgood] in *; auto.
Qed.

Lemma bv_c_CODELENS flush fx dx m : bv_good d m -> exists x' hh' bb',
  c_CODELENS flush fx dx (fast fx dx) (V m) =
  iomap (bview d x' hh' bb' w c t f) (c_CODELENS flush fx dx (fast fx dx) m).
Proof.
  intros G. unfold c_CODELENS.
  destruct (bv_codelens_loop fx dx 320 m G) as [E1 G1]. rewrite E1.
  destruct (codelens_loop fx dx 320 m) as [m1|m1|m1]; cbn [clmap clgood] in *;
    [|exists x, hh, bb; reflexivity|exists x, hh, bb; reflexivity].
  bvcase;
    lazymatch goal with
    | |- exists _ _ _, c_LEN_ _ _ _ _ = _ => apply bv_c_LEN_; bvg_solve
    | |- exists _ _ _, c_LEN_ _ _ _ _ _ = _ => apply bv_c_LEN_; bvg_solve
    | |- _ => exists x, hh, bb; reflexivity
    end.
Qed.

Lemma bv_c_LENLENS flush fx dx m : bv_good d m -> exists x' hh' bb',
  c_LENLENS flush fx dx (fast fx dx) (V m) =
  iomap (bview d x' hh' bb' w c t f) (c_LENLENS flush fx dx (fast fx dx) m).
Proof.
  intros G. unfold c_LENLENS.
  destruct (bv_lenlens_loop 19 m G) as [E1 G1]. rewrite E1.
  bvcase;
    lazymatch goal with
    | |- exists _ _ _, c_CODELENS _ _ _ _ = _ => apply bv_c_CODELENS; bvg_solve
    | |- exists _ _ _, c_CODELENS _ _ _ _ _ = _ => apply bv_c_CODELENS; bvg_solve
    | |- _ => exists x, hh, bb; reflexivity
    end.
Qed.

Lemma bv_c_TABLE flush fx dx m : bv_good d m -> exists x' hh' bb',
  c_TABLE flush fx dx (fast fx dx) (V m) =
  iomap (bview d x' hh' bb' w c t f) (c_TABLE flush fx dx (fast fx dx) m).
Proof.
  intros G. unfold c_TABLE.
  bvcase;
    lazymatch goal with
    | |- exists _ _ _, c_LENLENS _ _ _ _ = _ => apply bv_c_LENLENS; bvg_solve
    | |- exists _ _ _, c_LENLENS _ _ _ _ _ = _ => apply bv_c_LENLENS; bvg_solve
    | |- _ => exists x, hh, bb; reflexivity
    end.
Qed.

End Step.

Lemma bad_view_fast d x hh bb w c t f m :
  0 <= d <= m_nx m -> m_nx m <= Zlength (m_inp m) ->
  exists x' hh' bb',
    fast lenfix_list distfix_list (bview d x hh bb w c t f m) =
    bview d x' hh' bb' w c t f (fast lenfix_list distfix_list m).
Proof.
  intros. eexists _, _, _. apply bad_view_fast_eq. unfold bv_good. lia.
Qed.

Lemma bad_view_step flush d x hh bb w c t f m :
  0 <= d <= m_nx m -> m_nx m <= Zlength (m_inp m) -> blk_mode (m_mode m) ->
  exists x' hh' bb',
    stepf2 flush lenfix_list distfix_list (bview d x hh bb w c t f m) =
    iomap (bview d x' hh' bb' w c t f) (stepf2 flush lenfix_list distfix_list m).
Proof.
  intros H1 H2 Hb. assert (G: bv_good d m) by (unfold bv_good; lia).
  unfold stepf2, step2. rewrite bv_mode.
  destruct Hb as [[E|[E|[E|[E|E]]]]|[[E|[E|E]]|[E|[E|[E|[E|[E|[E|E]]]]]]]]; rewrite E;
    cbv beta iota delta [HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_
      COPY TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT Z.eqb Pos.eqb];
    lazymatch goal with
    | |- exists _ _ _, c_TABLE _ _ _ _ _ = _ => apply bv_c_TABLE; exact G
    | |- exists _ _ _, c_LENLENS _ _ _ _ _ = _ => apply bv_c_LENLENS; exact G
    | |- exists _ _ _, c_CODELENS _ _ _ _ _ = _ => apply bv_c_CODELENS; exact G
    | |- exists _ _ _, c_LEN_ _ _ _ _ = _ => apply bv_c_LEN_; exact G
    | |- exists _ _ _, c_LEN _ _ _ _ = _ => apply bv_c_LEN; exact G
    | |- exists _ _ _, c_TYPE _ _ = _ => exists x, hh, bb; apply bv_c_TYPE; exact G
    | |- exists _ _ _, c_TYPEDO _ _ = _ => exists x, hh, bb; apply bv_c_TYPEDO; exact G
    | |- exists _ _ _, c_STORED _ _ = _ => exists x, hh, bb; apply bv_c_STORED; exact G
    | |- exists _ _ _, c_COPY_ _ = _ => exists x, hh, bb; apply bv_c_COPY_; exact G
    | |- exists _ _ _, c_COPY _ = _ => exists x, hh, bb; apply bv_c_COPY; exact G
    | |- exists _ _ _, c_LENEXT _ _ _ = _ => exists x, hh, bb; apply bv_c_LENEXT; exact G
    | |- exists _ _ _, c_DIST _ _ _ = _ => exists x, hh, bb; apply bv_c_DIST; exact G
    | |- exists _ _ _, c_DISTEXT _ = _ => exists x, hh, bb; apply bv_c_DISTEXT; exact G
    | |- exists _ _ _, c_MATCH _ = _ => exists x, hh, bb; apply bv_c_MATCH
    | |- exists _ _ _, c_LIT _ = _ => exists x, hh, bb; apply bv_c_LIT
    end.
Qed.
