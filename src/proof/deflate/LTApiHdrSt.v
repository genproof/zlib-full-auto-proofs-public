(** * deflate_api theory: stages 2..7 of deflate(), the headers

    [hdr_stages] after the entry stage: nothing to do in BUSY / FINISH ([hdr_stages_busy]); from a fresh stream
    ([ph0]) or the middle of a gzip header ([ph1]) by [hf_run]: either Z_OK with the output space full, or the
    header done (BUSY, nothing pending, [ph2] with the header [H] at the start of the output). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTApiOut Zlib.proof.deflate.LTApiArith.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** ** The header stages never overdraw the output space (hdr_post does not say it for the done case) *)
Lemma hs_fp : forall s z s' z', c_flush_pending s z = Some (s', z') -> 0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' H Hz. unfold c_flush_pending, bind in H.
  destruct (c_tr_flush_bits (d_out s)) as [o|]; [|discriminate].
  cbv zeta in H.
  match type of H with context [if ?c =? 0 then _ else _] => destruct (c =? 0) end.
  { inversion H; subst; exact Hz. }
  match type of H with context [mb_read ?b ?lo ?len] => destruct (mb_read b lo len) as [l|] eqn:E end;
    [|discriminate].
  unfold out_put in H.
  match type of H with context [Zlength ?l <=? ?a] => destruct (Zlength l <=? a) eqn:E2 end; [|discriminate].
  apply Z.leb_le in E2. unfold mb_read in E.
  destruct (_ && _) eqn:E3 in E; [|discriminate]. inversion E; subst l; clear E.
  apply andb_prop in E3. destruct E3 as [E3 E4]. apply Z.leb_le in E3.
  unfold mb_definedb in E4. apply andb_prop in E4. destruct E4 as [E4 _]. apply andb_prop in E4.
  destruct E4 as [E4 E5]. apply Z.leb_le in E4. apply Z.leb_le in E5.
  rewrite Zlength_sublist in E2 by (simpl in *; lia).
  inversion H; subst; clear H. simpl in *. lia.
Qed.


Lemma hs_hcrc : forall h s z beg z', c_hcrc_update h s z beg = Some z' -> z_avail_out z' = z_avail_out z.
Proof.
  intros h s z beg z' H. unfold c_hcrc_update, bind in H.
  destruct (_ && _); [|inversion H; reflexivity].
  destruct (mb_read _ _ _); inversion H; reflexivity.
Qed.

(* the kernel otherwise unfolds these when checking the case analyses below (Qed of minutes) *)
Local Strategy opaque [c_flush_pending c_hcrc_update mb_write mb_read rds c_dput_byte c_dput_bytes c_putShortMSB loop loop2].

Ltac hs_go H :=
  do 40 (try (cbv beta iota zeta delta [bind then_stage c_flush_or_return] in H;
          match type of H with
          | Some _ = Some _ => fail 1
          | (_, _, _) = _ => fail 1
          | context [match ?x with _ => _ end] =>
              lazymatch x with context [match _ with _ => _ end] => fail | _ => idtac end;
              let E := fresh "E" in destruct x eqn:E; try discriminate H
          end)).

Ltac hs_close0 :=
  simpl;
  repeat first [ assumption | lia
               | match goal with E : c_flush_pending _ _ = Some (_, ?z1) |- 0 <= z_avail_out ?z1 =>
                   eapply hs_fp; [exact E|] end
               | match goal with E : c_hcrc_update _ _ _ _ = Some ?z1 |- 0 <= z_avail_out ?z1 =>
                   rewrite (hs_hcrc _ _ _ _ _ E) end
               | progress simpl ].

Lemma hs_runs {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) :
  (forall a a', P a -> body a = Some (inl a') -> P a') -> (forall a r, P a -> body a = Some (inr r) -> Q r) ->
  forall a r, runs body a r -> P a -> Q r.
Proof. intros H1 H2 a r R. induction R; eauto. Qed.

Definition zof4 (a : dstate * strm * Z * Z) : strm := let '(_, z, _, _) := a in z.
Definition zof3 (a : dstate * strm * Z) : strm := let '(_, z, _) := a in z.

Lemma hs_extra_body : forall h x s z beg lft r, extra_body h x (s, z, beg, lft) = Some r ->
  0 <= z_avail_out z ->
  0 <= z_avail_out (match r with inl a => zof4 a | inr (inl a) => zof4 a | inr (inr (_, z)) => z end).
Proof.
  intros h x s z beg lft r H Hz. unfold extra_body in H.
  hs_go H; inversion H; subst; hs_close0.
Qed.

Lemma hs_str_body : forall h x s z beg r, str_body h x (s, z, beg) = Some r ->
  0 <= z_avail_out z ->
  0 <= z_avail_out (match r with inl a => zof3 a | inr (inl a) => zof3 a | inr (inr (_, z)) => z end).
Proof.
  intros h x s z beg r H Hz. unfold str_body in H.
  hs_go H; inversion H; subst; hs_close0.
Qed.

Lemma hs_extra_loop : forall h x a r, loop FUEL (extra_body h x) a = Some r -> 0 <= z_avail_out (zof4 a) ->
  0 <= z_avail_out (match r with inl a' => zof4 a' | inr (_, z) => z end).
Proof.
  intros h x a r L. apply loop_runs in L. revert a r L.
  apply (hs_runs _ (fun a => 0 <= z_avail_out (zof4 a))
                   (fun r => 0 <= z_avail_out (match r with inl a' => zof4 a' | inr (_, z) => z end))).
  - intros [[[s z] beg] lft] a' Hz H. exact (hs_extra_body _ _ _ _ _ _ _ H Hz).
  - intros [[[s z] beg] lft] r Hz H. exact (hs_extra_body _ _ _ _ _ _ _ H Hz).
Qed.

Lemma hs_str_loop : forall h x a r, loop FUEL (str_body h x) a = Some r -> 0 <= z_avail_out (zof3 a) ->
  0 <= z_avail_out (match r with inl a' => zof3 a' | inr (_, z) => z end).
Proof.
  intros h x a r L. apply loop_runs in L. revert a r L.
  apply (hs_runs _ (fun a => 0 <= z_avail_out (zof3 a))
                   (fun r => 0 <= z_avail_out (match r with inl a' => zof3 a' | inr (_, z) => z end))).
  - intros [[s z] beg] a' Hz H. exact (hs_str_body _ _ _ _ _ _ H Hz).
  - intros [[s z] beg] r Hz H. exact (hs_str_body _ _ _ _ _ _ H Hz).
Qed.

Ltac hs_close :=
  simpl;
  repeat first [ assumption | lia
               | match goal with E : c_flush_pending _ _ = Some (_, ?z1) |- 0 <= z_avail_out ?z1 =>
                   eapply hs_fp; [exact E|] end
               | match goal with E : c_hcrc_update _ _ _ _ = Some ?z1 |- 0 <= z_avail_out ?z1 =>
                   rewrite (hs_hcrc _ _ _ _ _ E) end
               | match goal with E : loop FUEL (extra_body _ _) _ = Some _ |- _ =>
                   let L := fresh "L" in pose proof (hs_extra_loop _ _ _ _ E) as L; simpl in L; clear E end
               | match goal with E : loop FUEL (str_body _ _) _ = Some _ |- _ =>
                   let L := fresh "L" in pose proof (hs_str_loop _ _ _ _ E) as L; simpl in L; clear E end
               | match goal with L : 0 <= z_avail_out ?z -> _ |- _ =>
                   specialize (L ltac:(simpl; assumption)) end
               | progress simpl ].

Lemma hs_zlib : forall s z s' z' o, c_deflate_zlib_header s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_zlib_header in H. hs_go H; inversion H; subst; hs_close.
Qed.

Lemma hs_gzip : forall s z s' z' o, c_deflate_gzip_header s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_gzip_header in H. hs_go H; inversion H; subst; hs_close.
Qed.

Lemma hs_extra : forall s z s' z' o, c_deflate_extra s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_extra in H. hs_go H; inversion H; subst; hs_close.
Qed.

Lemma hs_str : forall h x b s z s' z' o, c_deflate_str h x b s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros h x b s z s' z' o H Hz. unfold c_deflate_str in H. hs_go H; inversion H; subst; hs_close.
Qed.

Lemma hs_name : forall s z s' z' o, c_deflate_name s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_name in H. hs_go H; inversion H; subst; first [assumption | eapply hs_str; [eassumption|assumption]].
Qed.

Lemma hs_comment : forall s z s' z' o, c_deflate_comment s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_comment in H. hs_go H; inversion H; subst; first [assumption | eapply hs_str; [eassumption|assumption]].
Qed.

Lemma hs_hcrc_st : forall s z s' z' o, c_deflate_hcrc s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold c_deflate_hcrc in H. hs_go H; inversion H; subst; hs_close.
Qed.

Lemma hs_then : forall r f s' z' o,
  (forall s1 z1 o1, r = Some (s1, z1, o1) -> 0 <= z_avail_out z1) ->
  (forall s z s' z' o, f s z = Some (s', z', o) -> 0 <= z_avail_out z -> 0 <= z_avail_out z') ->
  then_stage r f = Some (s', z', o) -> 0 <= z_avail_out z'.
Proof.
  intros r f s' z' o H1 H2 H. unfold then_stage, bind in H.
  destruct r as [[[s1 z1] [c|]]|]; try discriminate.
  - inversion H; subst. eapply H1; reflexivity.
  - eapply H2; [exact H|]. eapply H1; reflexivity.
Qed.

Lemma hdr_stages_ao : forall s z s' z' o, hdr_stages s z = Some (s', z', o) ->
  0 <= z_avail_out z -> 0 <= z_avail_out z'.
Proof.
  intros s z s' z' o H Hz. unfold hdr_stages in H.
  refine (hs_then _ _ _ _ _ (fun _ _ _ E => hs_zlib _ _ _ _ _ E Hz) _ H).
  intros s1 z1 s1' z1' o1 H1 Hz1.
  refine (hs_then _ _ _ _ _ (fun _ _ _ E => hs_gzip _ _ _ _ _ E Hz1) _ H1).
  intros s2 z2 s2' z2' o2 H2 Hz2.
  refine (hs_then _ _ _ _ _ (fun _ _ _ E => hs_extra _ _ _ _ _ E Hz2) _ H2).
  intros s3 z3 s3' z3' o3 H3 Hz3.
  refine (hs_then _ _ _ _ _ (fun _ _ _ E => hs_name _ _ _ _ _ E Hz3) _ H3).
  intros s4 z4 s4' z4' o4 H4 Hz4.
  refine (hs_then _ _ _ _ _ (fun _ _ _ E => hs_comment _ _ _ _ _ E Hz4) _ H4).
  intros s5 z5 s5' z5' o5 H5 Hz5.
  exact (hs_hcrc_st _ _ _ _ _ H5 Hz5).
Qed.

(** ** Copies of LTApiArith / LTApiOut facts used here, under names of this file *)
Lemma hs_sym : forall s s', core_eq s s' -> d_sym_next s' = d_sym_next s.
Proof.
  intros s s' [E _]. apply (f_equal (fun x => tr_sym_next (d_tr x))) in E. exact E.
Qed.

Lemma hs_pos : forall s s', core_eq s s' ->
  d_block_start s' = d_block_start s /\ d_strstart s' = d_strstart s /\ d_lookahead s' = d_lookahead s.
Proof.
  intros s s' (A & _). unfold strip in A.
  pose proof (f_equal d_block_start A) as E1. pose proof (f_equal d_strstart A) as E2.
  pose proof (f_equal d_lookahead A) as E3. cbn in E1, E2, E3. auto.
Qed.

Lemma hs_good_raw : forall dict, hdr_good dict 0 [].
Proof.
  intros dict. unfold hdr_good. repeat split; try constructor; intros; lia.
Qed.

Lemma hs_chk_nil : forall wrap a, chk_ok wrap [] (hdr_adler wrap a).
Proof.
  intros wrap a. unfold chk_ok, hdr_adler. split; intros ->; vm_compute; reflexivity.
Qed.

Lemma hs_xfl : forall s, 0 <= xfl_byte s < 256.
Proof.
  intros s. unfold xfl_byte. destruct (_ =? 9); [lia|]. destruct (_ || _); lia.
Qed.

Lemma hs_land255 : forall x, 0 <= Z.land x 255 < 256.
Proof.
  intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)). change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma hs_u8 : forall x, 0 <= u8 x < 256.
Proof. intros x. unfold u8. apply Z.mod_pos_bound. lia. Qed.

Lemma hs_bytes_map_u8 : forall l, bytes (map u8 l).
Proof. intros l. unfold bytes. apply Forall_map. apply Forall_forall. intros; apply hs_u8. Qed.

Lemma hs_adler_fold : forall d x y, 0 <= x < 65521 -> 0 <= y < 65521 ->
  0 <= fst (fold_left Zlib.proof.adler32.Model.adler_ref_step d (x, y)) < 65521 /\
  0 <= snd (fold_left Zlib.proof.adler32.Model.adler_ref_step d (x, y)) < 65521.
Proof.
  induction d as [|b d IH]; intros x y Hx Hy; simpl; [lia|].
  unfold Zlib.proof.adler32.Model.adler_ref_step at 2. simpl.
  unfold Zlib.proof.adler32.Model.ADLER_BASE.
  apply IH; apply Z.mod_pos_bound; lia.
Qed.

Lemma hs_radler_range : forall d, 0 <= radler 1 d < 2 ^ 32.
Proof.
  intros d. unfold Zlib.proof.adler32.Model.ref_adler32, Zlib.proof.adler32.Model.adler_pack.
  change (Zlib.proof.adler32.Model.adler_lo 1) with 1. change (Zlib.proof.adler32.Model.adler_hi 1) with 0.
  destruct (hs_adler_fold d 1 0 ltac:(lia) ltac:(lia)) as [A B].
  destruct (fold_left _ d _) as [u v]; simpl in *. lia.
Qed.

Lemma hs_u8_split : forall x, 0 <= x < 65536 -> u8 (Z.shiftr x 8) = x / 256 /\ u8 (Z.land x 255) = x mod 256.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  change (2 ^ 8) with 256. unfold u8. rewrite Zmod_mod. split; [|reflexivity].
  apply Z.mod_small. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma hs_be32 : forall a, 0 <= a < 2 ^ 32 ->
  be32 (msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))) = a.
Proof.
  intros a Ha.
  assert (E1 : Z.shiftr a 16 = a / 65536) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (E2 : Z.land a 65535 = a mod 65536) by (change 65535 with (Z.ones 16); rewrite Z.land_ones by lia; reflexivity).
  rewrite E1, E2.
  assert (Hhi : 0 <= a / 65536 < 65536) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hlo : 0 <= a mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  unfold u32. rewrite (Z.mod_small (a / 65536)), (Z.mod_small (a mod 65536)) by lia.
  unfold be32, msb2.
  destruct (hs_u8_split _ Hhi) as [-> ->]. destruct (hs_u8_split _ Hlo) as [-> ->].
  pose proof (Z.div_mod a 65536 ltac:(lia)). pose proof (Z.div_mod (a / 65536) 256 ltac:(lia)).
  pose proof (Z.div_mod (a mod 65536) 256 ltac:(lia)).
  remember (a / 65536 / 256) as q1. remember ((a / 65536) mod 256) as q2.
  remember (a mod 65536 / 256) as q3. remember ((a mod 65536) mod 256) as q4.
  remember (a / 65536) as hi. remember (a mod 65536) as lo.
  unfold Znth; simpl. lia.
Qed.

(** The zlib header word, as a function of the parameters it reads. *)
Definition hs_zh (wb st lv : Z) (nd : bool) : Z :=
  let header := u32 (Z.shiftl (u32 (Z_DEFLATED + u32 (Z.shiftl (u32 (wb - 8)) 4))) 8) in
  let level_flags :=
    if (st >=? Z_HUFFMAN_ONLY) || (lv <? 2) then 0
    else if lv <? 6 then 1
    else if lv =? 6 then 2
    else 3 in
  let header := Z.lor header (Z.shiftl level_flags 6) in
  let header := if nd then header else Z.lor header PRESET_DICT in
  u32 (header + u32 (31 - header mod 31)).

Lemma hs_zh_eq : forall s, zlib_header s = hs_zh (d_w_bits s) (d_strategy s) (d_level s) (d_strstart s =? 0).
Proof. intros s. reflexivity. Qed.

Definition hs_zh_ok (wb st lv : Z) (nd : bool) : bool :=
  let h := hs_zh wb st lv nd in
  let b0 := u8 (Z.shiftr h 8) in let b1 := u8 (Z.land h 255) in
  (Z.land b0 15 =? 8) && (Z.shiftr b0 4 <=? 7) && ((b0 * 256 + b1) mod 31 =? 0) &&
  Bool.eqb (negb (Z.land b1 32 =? 0)) (negb nd).

Definition hs_zr (lo n : Z) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 (Z.to_nat n)).

Lemma hs_zr_in : forall lo n x, lo <= x < lo + n -> In x (hs_zr lo n).
Proof.
  intros lo n x H. unfold hs_zr. apply in_map_iff. exists (Z.to_nat (x - lo)). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma hs_zh_all : forallb (fun wb => forallb (fun st => forallb (fun lv =>
    hs_zh_ok wb st lv true && hs_zh_ok wb st lv false) (hs_zr 0 10)) (hs_zr 0 5)) (hs_zr 9 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hs_zh_good : forall wb st lv nd, 9 <= wb <= 15 -> 0 <= st <= 4 -> 0 <= lv <= 9 ->
  hs_zh_ok wb st lv nd = true.
Proof.
  intros wb st lv nd Hw Hs Hl. pose proof hs_zh_all as A.
  rewrite forallb_forall in A. specialize (A wb (hs_zr_in 9 7 wb ltac:(lia))).
  rewrite forallb_forall in A. specialize (A st (hs_zr_in 0 5 st ltac:(lia))).
  rewrite forallb_forall in A. specialize (A lv (hs_zr_in 0 10 lv ltac:(lia))).
  apply andb_prop in A. destruct nd; apply A.
Qed.

Lemma hs_zlib_good : forall s dict a,
  prm s -> (d_strstart s = 0 <-> dict = []) -> (dict <> [] -> a = radler 1 dict) ->
  hdr_good dict 1 (zlib_hdr_bytes s a).
Proof.
  intros s dict a Hp Hss Ha.
  destruct Hp as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & Hs & _).
  pose proof (hs_zh_good (d_w_bits s) (d_strategy s) (d_level s) (d_strstart s =? 0)
                ltac:(lia) ltac:(lia) ltac:(lia)) as G.
  unfold hs_zh_ok in G. rewrite <- hs_zh_eq in G.
  set (h := zlib_header s) in *.
  repeat rewrite andb_true_iff in G. destruct G as [[[G1 G2] G3] G4].
  apply Z.eqb_eq in G1. apply Z.leb_le in G2. apply Z.eqb_eq in G3. apply Bool.eqb_prop in G4.
  unfold hdr_good, zlib_hdr_bytes. fold h.
  assert (HB : bytes (msb2 h)) by (unfold msb2; repeat constructor; apply hs_u8).
  split.
  { apply Forall_app; split; [exact HB|]. destruct (d_strstart s =? 0); [constructor|].
    apply Forall_app; split; unfold msb2; repeat constructor; apply hs_u8. }
  split; [intros; lia|]. split; [|intros; lia]. intros _.
  replace (msb2 h) with [u8 (Z.shiftr h 8); u8 (Z.land h 255)] by reflexivity. cbn [app]. rewrite Znth_0_cons, Znth_pos_cons by lia. simpl Z.sub. rewrite Znth_0_cons.
  destruct (d_strstart s =? 0) eqn:E.
  - apply Z.eqb_eq in E. assert (dict = []) as -> by (apply Hss; exact E).
    simpl in G4. split; [reflexivity|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
    split; [split; [intros N; rewrite negb_false_iff, Z.eqb_eq in G4; congruence|intros N; congruence]|].
    intros N; congruence.
  - apply Z.eqb_neq in E. assert (Hd : dict <> []) by (intros N; apply E, Hss, N).
    simpl in G4. rewrite negb_true_iff, Z.eqb_neq in G4.
    split. { destruct dict; [congruence|]. reflexivity. }
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [tauto|].
    intros _. transitivity a; [|apply Ha, Hd].
    replace (sublist 2 6 _) with (msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535)))
      by (unfold msb2; reflexivity).
    apply hs_be32. rewrite (Ha Hd). apply hs_radler_range.
Qed.

Lemma hs_cstr_bytes : forall o, cstr_ok o -> bytes (cstr_bytes o).
Proof.
  intros [l|] H; simpl; [|constructor].
  destruct (H l eq_refl) as (l0 & -> & _ & F). apply Forall_app. split; [|constructor; [lia|constructor]].
  eapply Forall_impl; [|exact F]. intros b Hb; cbv beta in *; lia.
Qed.

Lemma hs_gz_good : forall o xfl,
  (forall h, o = Some h -> hdr_ok h) -> (o = None -> 0 <= xfl < 256) ->
  hdr_good [] 2 (gz_hdr_bytes o xfl).
Proof.
  intros o xfl Hh Hx. unfold hdr_good.
  split; [|split; [intros; lia|split; [intros; lia|intros _]]].
  - destruct o as [h|].
    + destruct (Hh h eq_refl) as (_ & _ & _ & _ & _ & Hex & Hn & Hc).
      unfold gz_hdr_bytes.
      set (c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl)).
      apply Forall_app; split.
      * unfold gz_body. apply Forall_app; split; [apply hs_bytes_map_u8|].
        apply Forall_app; split; [|apply Forall_app; split; apply hs_cstr_bytes; assumption].
        unfold gz_extra_bytes. destruct (gz_extra h) as [x|] eqn:E; [|constructor].
        apply Forall_app; split; [apply hs_bytes_map_u8|]. apply Forall_sublist. apply (Hex x eq_refl).
      * destruct (gz_hcrc h =? 0); [constructor|].
        constructor; [apply hs_land255|constructor; [apply hs_land255|constructor]].
    + specialize (Hx eq_refl). unfold gz_hdr_bytes, OS_CODE.
      repeat (constructor; [lia|]). constructor.
  - destruct o as [h|].
    + unfold gz_hdr_bytes.
      set (c := Zlib.proof.crc32.Model.ref_crc32 0 (gz_body h xfl)).
      set (tl := if gz_hcrc h =? 0 then [] else [Z.land c 255; Z.land (Z.shiftr c 8) 255]).
      unfold gz_body, gz_pre.
      set (X := gz_extra_bytes h ++ cstr_bytes (gz_name h) ++ cstr_bytes (gz_comment h)).
      cbn [map app].
      change (u8 31) with 31. change (u8 139) with 139. change (u8 8) with 8.
      split; [|reflexivity].
      rewrite !Zlength_cons. pose proof (Zlength_nonneg ((X ++ tl))). rewrite Zlength_app in *. lia.
    + split; reflexivity.
Qed.

(** ** From hdr_post back to Mid *)
Lemma pend_nil : forall s, d_pending s = 0 -> pend s = [].
Proof. intros s H. unfold pend. rewrite H, Z.add_0_r. apply sublist_nil. Qed.

Lemma hdr_good_ne : forall dict wrap H, hdr_good dict wrap H -> wrap <> 0 -> 0 <= wrap <= 2 -> H <> [].
Proof.
  intros dict wrap H (Hb & H0 & H1 & H2) Hw Hr Hn. subst H.
  assert (wrap = 1 \/ wrap = 2) as [->| ->] by lia.
  - destruct (H1 eq_refl) as [L _]. rewrite Zlength_nil in L. destruct dict; lia.
  - destruct (H2 eq_refl) as [L _]. rewrite Zlength_nil in L. lia.
Qed.

Lemma hdr_tail : forall W HI dict wrap D O inb aout tin tout flush s z H k s' z' r,
  core_facts W -> hdr_facts HI -> Mid W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z ->
  d_wrap s = wrap -> d_bi_valid s = 0 -> d_sym_next s = 0 -> hdr_good dict wrap H -> 0 <= k ->
  D ++ sublist 0 (z_next_in z) inb = [] -> O ++ z_out z = sublist 0 k H ->
  hdr_stages s z = Some (s', z', r) -> hdr_post HI s z H k s' z' r ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_gzhead s2 = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s2 z2 /\ z_next_in z2 = z_next_in z /\
    match r with
    | Some c => c = Z_OK
    | None => d_pending s2 = 0 /\
              (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z H k s' z' r CF HF M Hpend Hlf Hfl Hao
    Hwr Hbv Hsym HG Hk0 HD HO HS HP.
  destruct M as (ZR & Hsz1 & Hsz2 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & Htin & HF6 & Hdz & Hph).
  destruct ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  destruct HP as (Hce & Hout' & Hwr' & Hgz' & Hbv' & x & k' & Hk & Hx & ZS & Hr).
  destruct ZS as (Zin' & Zni' & Zai' & Zti' & Zo' & Zao' & Zto' & Zad' & Zmsg').
  pose proof (hdr_stages_ao _ _ _ _ _ HS ltac:(lia)) as Hao2.
  pose proof (hs_sym _ _ Hce) as CEF.
  assert (HbH : bytes H) by apply HG.
  assert (Hbx : bytes x).
  { assert (B : bytes (x ++ pend s')) by (rewrite Hx; apply Forall_sublist; exact HbH).
    apply Forall_app in B. apply B. }
  assert (Hlx : Zlength x <= z_avail_out z) by lia.
  assert (Hto' : z_total_out z' = z_total_out z + Zlength x).
  { rewrite Zto'. unfold u64. apply Z.mod_small. rewrite Hto, Zlength_app. 
    pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). pose proof (Zlength_nonneg x). lia. }
  assert (HO2 : O ++ z_out z' = sublist 0 k H ++ x) by (rewrite Zo', app_assoc, HO; reflexivity).
  assert (Hfin : fin_of flush inb z' = fin_of flush inb z) by (unfold fin_of; rewrite Zni'; reflexivity).
  assert (HJ : sublist 0 k H ++ x ++ pend s' = sublist 0 k' H) by (rewrite Hx; apply sublist_rejoin; lia).
  assert (Hst : d_status s' = BUSY_STATE \/ (exists H1 k1, HI s' (z_adler z') H1 k1)).
  { destruct r as [c|]; [|left; apply Hr]. destruct Hr as (_ & _ & _ & _ & [[A _]|A]); [left; exact A|].
    right; eauto. }
  exists s', z', r. split; [exact HS|]. split; [exact Hgz'|].
  split; [|split; [exact Zni'|]].
  2:{ destruct r as [c|]; [apply Hr|]. destruct Hr as (_ & A & B & _). split; [exact B|left; exact A]. }
  unfold Mid. rewrite Zni', Hfin.
  split; [|split; [exact Hsz1|split; [exact Hsz2|]]].
  { unfold zrun. rewrite Zin', Zni', Zai', Zti', Zo', Hto', Zlength_app. repeat split; try lia.
    - exact Zin.
    - apply Forall_app; split; assumption. }
  rewrite HD, HO2, Zti', Hto'.
  rewrite HD in Htin, HbD.
  assert (HlO : Zlength (sublist 0 k H) = Zlength (O ++ z_out z)) by (rewrite HO; reflexivity).
  unfold Iapi.
  split; [eapply (cf_frame _ CF); eauto|].
  split; [exact Hout'|].
  split; [exact Hwr0|]. split; [exact Hw2|]. split; [exact Hbd|]. split; [exact Hld|].
  split; [destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                               destruct Hr as (_ & _ & _ & _ & _ & ->); lia]|].
  split; [rewrite Hgz'; exact Hgz|].
  split; [rewrite Hto, (Zlength_app _ (sublist 0 k H)), HlO; lia|].
  split; [apply Forall_app; split; [rewrite <- HO; exact HbO|exact Hbx]|].
  split; [exact HbD|]. split; [exact Htin|].
  split.
  { intros F. exfalso. destruct Hst as [A|(H1 & k1 & A)].
    - rewrite A in F. discriminate.
    - apply (hf_status _ HF) in A. destruct A as (_ & _ & A & _).
      rewrite F in A. unfold FINISH_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE in A. lia. }
  split.
  { intros _. destruct (hs_pos _ _ Hce) as (P1 & P2 & P3). rewrite P1, P2, P3. exact (Hdz HD). }
  right. split.
  { destruct r as [c|]; [destruct Hr as (_ & _ & _ & -> & _); lia|
                         destruct Hr as (_ & _ & _ & _ & _ & ->); lia]. }
  destruct r as [c|].
  - destruct Hr as (-> & Hz0 & Hpn & Hlf' & [(Hb & Hk' & Had)|HI']).
    + right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
      split. { intros _. intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split. { rewrite Had, Hwr. apply hs_chk_nil. }
      exists H, []. split; [exact HG|]. rewrite <- app_assoc, HJ, Hk', app_nil_r.
      apply sublist_same; reflexivity.
    + left. unfold ph1. pose proof (hf_status _ HF _ _ _ _ HI') as (Hw2' & _).
      split; [lia|]. split; [reflexivity|].
      split. { intros E. apply app_eq_nil in E. destruct E as [_ E]. subst x.
        rewrite Zlength_nil in Zao'. lia. }
      split; [lia|]. split; [rewrite CEF; lia|].
      exists H, k'. split; [exact HI'|]. rewrite <- app_assoc. exact HJ.
  - destruct Hr as (Hk' & Hb & Hpn & Hpo & Had & Hlf').
    rewrite (pend_nil _ Hpn), app_nil_r in HJ.
    right; left. unfold ph2. split; [exact Hb|]. split; [lia|]. split; [lia|].
    split. { intros Hw. rewrite HJ, Hk', sublist_same by reflexivity.
      eapply hdr_good_ne; eauto. }
    split. { rewrite Had, Hwr. apply hs_chk_nil. }
    exists H, []. split; [exact HG|]. rewrite (pend_nil _ Hpn), app_nil_r, HJ, Hk', app_nil_r.
    apply sublist_same; reflexivity.
Qed.

Lemma hdr_stage_ok : forall W HI dict wrap D O inb aout tin tout flush s z,
  core_facts W -> hdr_facts HI ->
  Mid W HI dict wrap D O inb aout tin tout flush s z ->
  d_pending s = 0 -> d_last_flush s = flush -> 0 <= flush <= 5 -> 0 < z_avail_out z -> aout <= 1048576 ->
  (d_status s = FINISH_STATE -> z_avail_in z = 0) ->
  exists s2 z2 r, hdr_stages s z = Some (s2, z2, r) /\ d_gzhead s2 = d_gzhead s /\
    Mid W HI dict wrap D O inb aout tin tout flush s2 z2 /\ z_next_in z2 = z_next_in z /\
    match r with
    | Some c => c = Z_OK
    | None => d_pending s2 = 0 /\
              (d_status s2 = BUSY_STATE \/ (d_status s2 = FINISH_STATE /\ z_avail_in z2 = 0))
    end.
Proof.
  intros W HI dict wrap D O inb aout tin tout flush s z CF HF M Hpend Hlf Hfl Hao Haout Hfin.
  pose proof M as M0.
  destruct M as (ZR & Hsz1 & Hsz2 & IA).
  destruct IA as (HW & Hout & Hwr0 & Hw2 & Hbd & Hld & Hlfr & Hgz & Hto & HbO & HbD & Htin & HF6 & _ & Hph).
  pose proof ZR as (Zin & Zni & Zai & Zti & Zao & Zol & Zto & Zbo).
  assert (Hzao : 0 <= z_avail_out z <= 1073741824) by (pose proof (Zlength_nonneg (z_out z)); lia).
  assert (Hzto : 0 <= z_total_out z <= 1099511627776).
  { rewrite Hto, Zlength_app. pose proof (Zlength_nonneg O). pose proof (Zlength_nonneg (z_out z)). lia. }
  pose proof (cf_prm _ CF _ HW) as Hprm.
  destruct Hph as [P0 | [Hlf2 [P1 | [P2 | P3]]]].
  - destruct P0 as (Hst & Hw & HD & HO & _ & Hbv & Hsym & _ & _ & Hss & Had).
    set (H := hdr_bytes s (z_adler z)).
    assert (HG : hdr_good dict wrap H).
    { destruct Hst as [[Hst Hwl]|[Hst Hw2']].
      - assert (wrap = 0 \/ wrap = 1) as [->| ->] by lia.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_good_raw.
        + unfold H, hdr_bytes. rewrite Hw. simpl. apply hs_zlib_good; [exact Hprm|exact Hss|].
          intros _. apply Had. reflexivity.
      - subst wrap. rewrite (Hw2 eq_refl). unfold H, hdr_bytes. rewrite Hw. simpl.
        apply hs_gz_good; [exact Hgz|intros _; apply hs_xfl]. }
    assert (Hpre : hdr_pre HI s z H 0).
    { unfold hdr_pre. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hgz|].
      destruct Hst as [[Hst Hwl]|[Hst Hw2']]; [left|right; left]; repeat split; auto; lia. }
    destruct (hf_run _ HF _ _ _ _ Hpre) as (s' & z' & r & HS & HP).
    refine (hdr_tail W HI dict wrap D O inb aout tin tout flush s z H 0 s' z' r CF HF M0 Hpend Hlf Hfl Hao
              Hw Hbv Hsym HG ltac:(lia) HD _ HS HP).
    rewrite HO. symmetry. apply sublist_nil.
  - destruct P1 as (Hw & HD & HOne & Hbv & Hsym & H & k & HIk & HOk).
    destruct (hf_status _ HF _ _ _ _ HIk) as (Hw' & [h Hh] & _ & [xfl HH] & Hk).
    assert (HG : hdr_good dict wrap H).
    { subst wrap. rewrite (Hw2 eq_refl), HH. apply hs_gz_good; [exact Hgz|congruence]. }
    rewrite (pend_nil _ Hpend), app_nil_r in HOk.
    assert (Hpre : hdr_pre HI s z H k).
    { unfold hdr_pre. split; [exact Hprm|]. split; [exact Hout|]. split; [exact Hpend|].
      split; [exact Hsym|]. split; [exact Hbv|]. split; [exact Hzao|]. split; [exact Hzto|].
      split; [exact Hgz|]. right; right; exact HIk. }
    destruct (hf_run _ HF _ _ _ _ Hpre) as (s' & z' & r & HS & HP).
    exact (hdr_tail W HI dict wrap D O inb aout tin tout flush s z H k s' z' r CF HF M0 Hpend Hlf Hfl Hao
             ltac:(lia) Hbv Hsym HG ltac:(lia) HD HOk HS HP).
  - exists s, z, None. rewrite hdr_stages_busy by (left; apply P2).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|left; apply P2].
  - exists s, z, None. rewrite hdr_stages_busy by (right; apply P3).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact M0|]. split; [reflexivity|].
    split; [exact Hpend|right; split; [apply P3|apply Hfin, P3]].
Qed.
