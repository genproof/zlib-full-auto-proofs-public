(* The pieces of one pass of inflate_fast's loop (SISimFastIter.v): the machine while it reads a symbol
   (`fat`: only next, hold and bits change, the bit buffer holds the input's bits), its refill, table walk and
   extra bits on the input's bits, and the abstract decoder's steps of a symbol. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.harness.api_split_invariant.SIDefs.
Require Import Zlib.proof.harness.api_split_invariant.SISimFastKit.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBits.
Require Import Zlib.proof.harness.api_split_invariant.SIKitBuf.
Require Zlib.proof.rfc1951.DecFastKit.
Import ListNotations.
Local Open Scope Z_scope.

Module DK := Zlib.proof.rfc1951.DecFastKit.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine while it reads                                                                     *)

(* mt is the machine m with only the locals next, put, hold and bits changed *)
Definition fk (m mt: mst) : Prop := mt = fset m (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt).

Lemma fk_refl m : fk m m.
Proof. destruct m; reflexivity. Qed.

Lemma fk_pull m mt : fk m mt -> fk m (pull mt).
Proof. intros ->. reflexivity. Qed.

Lemma fk_drop m mt k : fk m mt -> fk m (dropbits k mt).
Proof. intros ->. reflexivity. Qed.

Lemma fk_ow m mt ow : fk m mt -> fk m (set_m_ow mt ow).
Proof. intros ->. reflexivity. Qed.

Lemma fk_s m mt : fk m mt -> m_s mt = m_s m /\ m_inp mt = m_inp m /\ m_aout mt = m_aout m.
Proof. intros ->. auto. Qed.

(* the machine mt of the call that started at input byte P0, derived from m, at bit position q, with next nx and
   bits b, the output not changed *)
Definition fat (src: list Z) (P0: Z) (m mt: mst) (q nx b: Z) : Prop :=
  bitbuf src P0 mt /\ fk m mt /\ mq P0 mt = q /\ m_nx mt = nx /\ m_bits mt = b /\ m_ow mt = m_ow m.

Lemma fat_init src P0 m : bitbuf src P0 m -> fat src P0 m m (mq P0 m) (m_nx m) (m_bits m).
Proof. intros B. split; [exact B|]. split; [apply fk_refl|]. auto. Qed.

Lemma fat_facts src P0 m mt q nx b : fat src P0 m mt q nx b ->
  0 <= b /\ 0 <= nx <= Zlength (m_inp m) /\ q = 8 * (P0 + nx) - b /\ b <= 8 * (P0 + nx) /\ 0 <= P0 /\
  m_s mt = m_s m /\ m_inp mt = m_inp m.
Proof.
  intros (B & K & Q & N & Bi & O). destruct (fk_s _ _ K) as (S & I & _).
  destruct B as [_ BP _ BN [BB1 BB2] _]. rewrite I in BN. unfold mq in Q. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. auto.
Qed.

(* the bit position of a machine of the call is within the call's input *)
Lemma fat_q src P0 m mt q nx b : fat src P0 m mt q nx b -> 0 <= q <= 8 * (P0 + Zlength (m_inp m)).
Proof. intros F. destruct (fat_facts _ _ _ _ _ _ _ F) as (? & ? & ? & ? & ? & _). lia. Qed.

Lemma u32_small x : 0 <= x < 2 ^ 32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.

(* PULLBYTE without the test (the byte is there) *)
Lemma fat_pull src P0 m mt q nx b : fat src P0 m mt q nx b -> nx < Zlength (m_inp m) -> b <= 31 ->
  fat src P0 m (pull mt) q (nx + 1) (b + 8).
Proof.
  intros F Hn Hb. pose proof (fat_facts _ _ _ _ _ _ _ F) as (Hb0 & Hnx & _ & _ & _ & _ & Hi).
  destruct F as (B & K & Q & N & Bi & O).
  destruct (sik_pull src P0 mt B) as [B' Q']; [unfold m_have; rewrite Hi; lia|lia|].
  split; [exact B'|]. split; [apply fk_pull; exact K|]. split; [lia|].
  split; [cbn; lia|]. split; [|exact O].
  cbn. rewrite u32_small; lia.
Qed.

(* DROPBITS(k), with BITS(k) the k bits at the bit position *)
Lemma fat_drop src P0 m mt q nx b k : fat src P0 m mt q nx b -> 0 <= k <= b ->
  fat src P0 m (dropbits k mt) (q + k) nx (b - k) /\ m_hold mt mod 2 ^ k = sbits src q k.
Proof.
  intros F Hk. destruct F as (B & K & Q & N & Bi & O).
  destruct (sik_dropbits src P0 mt k B ltac:(lia)) as (B' & Q' & V).
  split; [|unfold bitsn in V; rewrite V, Q; reflexivity].
  split; [exact B'|]. split; [apply fk_drop; exact K|]. split; [lia|].
  split; [exact N|]. split; [|exact O].
  cbn. rewrite u32_small; [lia|]. pose proof (bb_bits _ _ _ B). lia.
Qed.

(* if (bits < 15) { two bytes } *)
Lemma fat_refill src P0 m mt q nx b : fat src P0 m mt q nx b -> b <= 30 -> (b < 15 -> nx + 2 <= Zlength (m_inp m)) ->
  exists nx' b', fat src P0 m (DK.refill2 mt) q nx' b' /\
    ((b < 15 /\ nx' = nx + 2 /\ b' = b + 16) \/ (15 <= b /\ nx' = nx /\ b' = b)).
Proof.
  intros F Hb Hn. unfold DK.refill2, fpull. pose proof F as (_ & _ & _ & _ & Bi & _).
  rewrite Bi. destruct (Z.ltb_spec b 15) as [L|L].
  - exists (nx + 2), (b + 16). split; [|left; lia].
    replace (nx + 2) with (nx + 1 + 1) by lia. replace (b + 16) with (b + 8 + 8) by lia.
    apply fat_pull; [apply fat_pull| |]; try exact F; lia.
  - exists nx, b. split; [exact F|right; lia].
Qed.

(* the table walk with at least 15 bits: adecode's entry, its code dropped *)
Lemma fat_walk src P0 m mt q nx b kind t nb sz il lk here l :
  fwalk_stmt -> fat src P0 m mt q nx b -> 15 <= b ->
  tvalid_g kind (tab_entry lenfix_list distfix_list (m_s m) t) nb sz ->
  (kind = LENS /\ il = len_link /\ lk = len_islink) \/ (kind = DISTS /\ il = dist_link /\ lk = dist_islink) ->
  adecode lenfix_list distfix_list src (m_s m) t nb lk q = (here, l) ->
  fwalk_f lenfix_list distfix_list 2 il t (tab_entry lenfix_list distfix_list (m_s m) t (m_hold mt mod 2 ^ nb)) mt =
    (here, dropbits l mt) /\
  fat src P0 m (dropbits l mt) (q + l) nx (b - l) /\ 0 <= l <= 15 /\ entry_ok here /\ final_ok kind here /\
  exists i, 0 <= i < sz /\ here = tab_entry lenfix_list distfix_list (m_s m) t i.
Proof.
  intros W F Hb TV KL E.
  pose proof (fat_facts _ _ _ _ _ _ _ F) as (_ & _ & _ & _ & _ & S & _).
  pose proof F as (B & K & Q & N & Bi & O).
  rewrite <- S in TV.
  specialize (W src P0 mt kind t nb sz il lk B TV KL ltac:(lia)).
  rewrite S, Q, E in W. destruct W as (W1 & Hl & Eo & Fo & Ix).
  split; [exact W1|]. split; [|auto].
  apply fat_drop; [exact F|lia].
Qed.

Lemma fat_sbits0 src q : sbits src q 0 = 0.
Proof. apply sik_sbits_0. Qed.

(* the extra bits of a length: one pull at most (bits < op & 15), BITS, DROPBITS *)
Lemma fat_lenx src P0 m mt q nx b here :
  fat src P0 m mt q nx b -> entry_ok here -> Z.land (e_op here) 15 <= 5 -> b <= 31 ->
  (b < Z.land (e_op here) 15 -> nx < Zlength (m_inp m)) ->
  let e := Z.land (e_op here) 15 in
  exists mt' nx' b', DK.lenx here mt = (u32 (e_val here + sbits src q e), mt') /\ fat src P0 m mt' (q + e) nx' b' /\
    ((b < e /\ nx' = nx + 1 /\ b' = b + 8 - e) \/ (e <= b /\ nx' = nx /\ b' = b - e)).
Proof.
  intros F Eo He Hb Hn e.
  assert (He0: 0 <= e) by (apply Z.land_nonneg; lia).
  pose proof F as (_ & _ & _ & _ & Bi & _). pose proof (fat_facts _ _ _ _ _ _ _ F) as (Hb0 & _).
  unfold DK.lenx. fold e. destruct (Z.eqb_spec e 0) as [E0|E0].
  - cbn [negb]. exists mt, nx, b. rewrite E0, fat_sbits0, Z.add_0_r, Z.add_0_r.
    split; [f_equal; symmetry; apply u32_small; destruct Eo as (_ & _ & ?); lia|].
    split; [exact F|right; lia].
  - cbn [negb]. unfold fpull. rewrite Bi. destruct (Z.ltb_spec b e) as [L|L].
    + pose proof (fat_pull _ _ _ _ _ _ _ F ltac:(lia) Hb) as F1.
      destruct (fat_drop _ _ _ _ _ _ _ e F1 ltac:(lia)) as [F2 V].
      exists (dropbits e (pull mt)), (nx + 1), (b + 8 - e).
      split; [rewrite V; reflexivity|]. split; [replace (b + 8 - e) with (b + 8 - e) by lia; exact F2|left; lia].
    + destruct (fat_drop _ _ _ _ _ _ _ e F ltac:(lia)) as [F2 V].
      exists (dropbits e mt), nx, (b - e).
      split; [rewrite V; reflexivity|]. split; [exact F2|right; lia].
Qed.

(* the extra bits of a distance: two pulls at most *)
Lemma fat_distx src P0 m mt q nx b here :
  fat src P0 m mt q nx b -> Z.land (e_op here) 15 <= 13 -> b <= 31 ->
  (b < Z.land (e_op here) 15 -> nx < Zlength (m_inp m)) ->
  (b + 8 < Z.land (e_op here) 15 -> nx + 1 < Zlength (m_inp m)) ->
  let e := Z.land (e_op here) 15 in
  exists mt' nx' b', DK.distx here mt = (u32 (e_val here + sbits src q e), mt') /\ fat src P0 m mt' (q + e) nx' b' /\
    ((b + 8 < e /\ nx' = nx + 2 /\ b' = b + 16 - e) \/ (b < e <= b + 8 /\ nx' = nx + 1 /\ b' = b + 8 - e) \/
     (e <= b /\ nx' = nx /\ b' = b - e)).
Proof.
  intros F He Hb Hn Hn2 e.
  assert (He0: 0 <= e) by (apply Z.land_nonneg; lia).
  pose proof F as (_ & _ & _ & _ & Bi & _). pose proof (fat_facts _ _ _ _ _ _ _ F) as (Hb0 & _).
  unfold DK.distx. fold e. unfold fpull. rewrite Bi. destruct (Z.ltb_spec b e) as [L|L].
  - pose proof (fat_pull _ _ _ _ _ _ _ F ltac:(lia) Hb) as F1.
    pose proof F1 as (_ & _ & _ & _ & Bi1 & _). rewrite Bi1.
    destruct (Z.ltb_spec (b + 8) e) as [L2|L2].
    + pose proof (fat_pull _ _ _ _ _ _ _ F1 ltac:(lia) ltac:(lia)) as F2.
      destruct (fat_drop _ _ _ _ _ _ _ e F2 ltac:(lia)) as [F3 V].
      eexists _, (nx + 1 + 1), (b + 8 + 8 - e).
      split; [rewrite V; reflexivity|]. split; [exact F3|left; lia].
    + destruct (fat_drop _ _ _ _ _ _ _ e F1 ltac:(lia)) as [F3 V].
      eexists _, (nx + 1), (b + 8 - e).
      split; [rewrite V; reflexivity|]. split; [exact F3|right; left; lia].
  - destruct (fat_drop _ _ _ _ _ _ _ e F ltac:(lia)) as [F2 V].
    eexists _, nx, (b - e).
    split; [rewrite V; reflexivity|]. split; [exact F2|right; right; lia].
Qed.

Lemma bitbuf_ow src P0 mt ow : bitbuf src P0 mt -> bitbuf src P0 (set_m_ow mt ow).
Proof. intros [B P I N Bb H]. constructor; [exact B|exact P|exact I|exact N|exact Bb|exact H]. Qed.

Lemma bitbuf_bad src P0 mt e : bitbuf src P0 mt -> bitbuf src P0 (set_bad mt e).
Proof. intros [B P I N Bb H]. constructor; [exact B|exact P|exact I|exact N|exact Bb|exact H]. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The tables: an entry depends on the state only through state->codes                            *)

Lemma tab_entry_codes fx dx s s' t i : i_codes s = i_codes s' -> tab_entry fx dx s t i = tab_entry fx dx s' t i.
Proof. intros E. destruct t; cbn; [reflexivity|reflexivity|rewrite E; reflexivity]. Qed.

Lemma adecode_codes fx dx src s s' t nb lk q :
  i_codes s = i_codes s' -> adecode fx dx src s t nb lk q = adecode fx dx src s' t nb lk q.
Proof. intros E. unfold adecode. rewrite !(tab_entry_codes fx dx s s' t) by exact E. reflexivity. Qed.

Lemma tvalid_g_codes kind s s' t nb sz : i_codes s = i_codes s' ->
  tvalid_g kind (tab_entry lenfix_list distfix_list s t) nb sz -> tvalid_g kind (tab_entry lenfix_list distfix_list s' t) nb sz.
Proof. intros E. apply tvalid_g_ext. intros i _. apply tab_entry_codes. exact E. Qed.

Lemma final_ok_LENS e : final_ok LENS e ->
  (e_op e = 0 /\ 0 <= e_val e <= 255) \/ (16 <= e_op e <= 21 /\ 3 <= e_val e <= 258) \/ e_op e = 96 \/
  (Z.land (e_op e) 64 <> 0 /\ Z.land (e_op e) 48 = 0).
Proof. intros H. exact H. Qed.

Lemma final_ok_DISTS e : final_ok DISTS e ->
  (16 <= e_op e <= 29 /\ 1 <= e_val e <= 32768) \/ (Z.land (e_op e) 64 <> 0 /\ Z.land (e_op e) 48 = 0).
Proof. intros H. exact H. Qed.

(* the bits of an op *)
Lemma op_code op : 16 <= op <= 29 ->
  Z.land op 15 = op - 16 /\ Z.land op 16 <> 0 /\ Z.land op 32 = 0 /\ Z.land op 64 = 0 /\ op <> 0.
Proof.
  intros H.
  assert (E: op = 16 \/ op = 17 \/ op = 18 \/ op = 19 \/ op = 20 \/ op = 21 \/ op = 22 \/ op = 23 \/
             op = 24 \/ op = 25 \/ op = 26 \/ op = 27 \/ op = 28 \/ op = 29) by lia.
  repeat (destruct E as [E|E]; [subst op; vm_compute; repeat split; discriminate|]).
  subst op; vm_compute; repeat split; discriminate.
Qed.

Lemma op_invalid op : Z.land op 64 <> 0 -> Z.land op 48 = 0 ->
  op <> 0 /\ Z.land op 16 = 0 /\ Z.land op 32 = 0.
Proof.
  intros H1 H2. split; [intros ->; apply H1; reflexivity|].
  split.
  - change 16 with (Z.land 48 16). rewrite Z.land_assoc, H2. reflexivity.
  - change 32 with (Z.land 48 32). rewrite Z.land_assoc, H2. reflexivity.
Qed.

Lemma op_eob : Z.land 96 16 = 0 /\ Z.land 96 32 <> 0 /\ 96 <> 0.
Proof. vm_compute. repeat split; discriminate. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract steps of a symbol                                                                 *)

Section Steps.
Variable src: list Z.

Notation astep := (astep lenfix_list distfix_list src).

Lemma astep_LEN a : a_mode a = LEN -> astep a = a_LEN lenfix_list distfix_list src a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

Lemma astep_LENEXT a : a_mode a = LENEXT -> astep a = a_LENEXT src a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

Lemma astep_DIST a : a_mode a = DIST -> astep a = a_DIST lenfix_list distfix_list src a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

Lemma astep_DISTEXT a : a_mode a = DISTEXT -> astep a = a_DISTEXT src a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

Lemma astep_MATCH a : a_mode a = MATCH -> astep a = a_MATCH a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

Lemma astep_LIT a : a_mode a = LIT -> astep a = a_LIT a.
Proof. intros H. unfold SIAbs.astep. rewrite H. reflexivity. Qed.

(* LEN: the code of a literal, of a length, the end of the block, an invalid code *)
Lemma aLEN_lit s q O here l : i_mode s = LEN ->
  adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (here, l) -> e_op here = 0 ->
  astep (AS s q O) = AGo (q + l) false (AS (set_i_mode (set_i_length s (e_val here)) LIT) (q + l) O).
Proof.
  intros Hm E Hop. rewrite astep_LEN by exact Hm. unfold a_LEN. cbn [a_s a_q]. rewrite E, Hop. reflexivity.
Qed.

Lemma aLEN_eob s q O here l : i_mode s = LEN ->
  adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (here, l) -> e_op here = 96 ->
  astep (AS s q O) = AGo (q + l) false (AS (set_i_mode (set_i_length s (e_val here)) Zlib.proof.inflate.Model.TYPE) (q + l) O).
Proof.
  intros Hm E Hop. rewrite astep_LEN by exact Hm. unfold a_LEN. cbn [a_s a_q]. rewrite E, Hop. reflexivity.
Qed.

Lemma aLEN_bad s q O here l : i_mode s = LEN ->
  adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (here, l) ->
  e_op here <> 0 -> Z.land (e_op here) 32 = 0 -> Z.land (e_op here) 64 <> 0 ->
  astep (AS s q O) = AGo (q + l) false (AS (set_i_mode s BAD) (q + l) O).
Proof.
  intros Hm E H0 H32 H64. rewrite astep_LEN by exact Hm. unfold a_LEN. cbn [a_s a_q]. rewrite E.
  rewrite (proj2 (Z.eqb_neq _ _) H0), H32, (proj2 (Z.eqb_neq _ _) H64). reflexivity.
Qed.

Lemma aLEN_len s q O here l : i_mode s = LEN ->
  adecode lenfix_list distfix_list src s (i_lencode s) (i_lenbits s) len_islink q = (here, l) ->
  e_op here <> 0 -> Z.land (e_op here) 32 = 0 -> Z.land (e_op here) 64 = 0 ->
  astep (AS s q O) =
    AGo (q + l) false (AS (set_i_mode (set_i_extra (set_i_length s (e_val here)) (Z.land (e_op here) 15)) LENEXT) (q + l) O).
Proof.
  intros Hm E H0 H32 H64. rewrite astep_LEN by exact Hm. unfold a_LEN. cbn [a_s a_q]. rewrite E.
  rewrite (proj2 (Z.eqb_neq _ _) H0), H32, H64. reflexivity.
Qed.

Lemma aLIT s q O : i_mode s = LIT ->
  astep (AS s q O) = AGo q true (AS (set_i_mode s LEN) q (O ++ [i_length s mod 256])).
Proof. intros Hm. rewrite astep_LIT by exact Hm. reflexivity. Qed.

Lemma set_i_length_same s : set_i_length s (i_length s) = s.
Proof. destruct s; reflexivity. Qed.

Lemma set_i_offset_same s : set_i_offset s (i_offset s) = s.
Proof. destruct s; reflexivity. Qed.

(* the extra bits of a length (none: the same step without bits) *)
Lemma aLENEXT s q O : i_mode s = LENEXT -> 0 <= i_length s < 2 ^ 32 ->
  astep (AS s q O) = AGo (q + i_extra s) false
    (AS (set_i_mode (set_i_length s (u32 (i_length s + sbits src q (i_extra s)))) DIST) (q + i_extra s) O).
Proof.
  intros Hm Hl. rewrite astep_LENEXT by exact Hm. unfold a_LENEXT. cbn [a_s a_q].
  destruct (Z.eqb_spec (i_extra s) 0) as [E|E].
  - cbn [negb]. unfold ago. cbn [a_O].
    rewrite E, sik_sbits_0, !Z.add_0_r, u32_small, set_i_length_same by exact Hl. reflexivity.
  - reflexivity.
Qed.

Lemma aDIST_ok s q O here l : i_mode s = DIST ->
  adecode lenfix_list distfix_list src s (i_distcode s) (i_distbits s) dist_islink q = (here, l) ->
  Z.land (e_op here) 64 = 0 ->
  astep (AS s q O) =
    AGo (q + l) false (AS (set_i_mode (set_i_extra (set_i_offset s (e_val here)) (Z.land (e_op here) 15)) DISTEXT) (q + l) O).
Proof.
  intros Hm E H64. rewrite astep_DIST by exact Hm. unfold a_DIST. cbn [a_s a_q]. rewrite E, H64. reflexivity.
Qed.

Lemma aDIST_bad s q O here l : i_mode s = DIST ->
  adecode lenfix_list distfix_list src s (i_distcode s) (i_distbits s) dist_islink q = (here, l) ->
  Z.land (e_op here) 64 <> 0 ->
  astep (AS s q O) = AGo (q + l) false (AS (set_i_mode s BAD) (q + l) O).
Proof.
  intros Hm E H64. rewrite astep_DIST by exact Hm. unfold a_DIST. cbn [a_s a_q]. rewrite E.
  rewrite (proj2 (Z.eqb_neq _ _) H64). reflexivity.
Qed.

Lemma aDISTEXT s q O : i_mode s = DISTEXT -> 0 <= i_offset s < 2 ^ 32 ->
  astep (AS s q O) = AGo (q + i_extra s) false
    (AS (set_i_mode (set_i_offset s (u32 (i_offset s + sbits src q (i_extra s)))) MATCH) (q + i_extra s) O).
Proof.
  intros Hm Hl. rewrite astep_DISTEXT by exact Hm. unfold a_DISTEXT. cbn [a_s a_q].
  destruct (Z.eqb_spec (i_extra s) 0) as [E|E].
  - cbn [negb]. unfold ago. cbn [a_O].
    rewrite E, sik_sbits_0, !Z.add_0_r, u32_small, set_i_offset_same by exact Hl. reflexivity.
  - reflexivity.
Qed.

Lemma aMATCH_far s q O : i_mode s = MATCH -> Zlength O < i_offset s ->
  astep (AS s q O) = AGo q true (AS (set_i_mode s BAD) q O).
Proof.
  intros Hm H. rewrite astep_MATCH by exact Hm. unfold a_MATCH. cbn [a_s a_O a_q].
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

End Steps.

(* the states after the steps of a symbol, as fsx *)
Lemma st_lit s v : set_i_mode (set_i_mode (set_i_length s v) LIT) LEN = fsx s LEN v (i_offset s) (i_extra s).
Proof. destruct s; reflexivity. Qed.

Lemma st_eob s v : set_i_mode (set_i_length s v) Zlib.proof.inflate.Model.TYPE =
  fsx s Zlib.proof.inflate.Model.TYPE v (i_offset s) (i_extra s).
Proof. destruct s; reflexivity. Qed.

(* LEN, LENEXT, DIST, DISTEXT: the state in MATCH *)
Definition s_match (s: istate) (val e1 len dval e2 dist: Z) : istate :=
  set_i_mode (set_i_offset (set_i_mode (set_i_extra (set_i_offset
    (set_i_mode (set_i_length (set_i_mode (set_i_extra (set_i_length s val) e1) LENEXT) len) DIST) dval) e2) DISTEXT)
    dist) MATCH.

Lemma s_match_fields s val e1 len dval e2 dist :
  let t := s_match s val e1 len dval e2 dist in
  i_mode t = MATCH /\ i_length t = len /\ i_offset t = dist.
Proof. split; [reflexivity|]. split; reflexivity. Qed.

Lemma st_match s val e1 len dval e2 dist :
  set_i_mode (set_i_length (s_match s val e1 len dval e2 dist) 0) LEN = fsx s LEN 0 dist e2.
Proof. destruct s; reflexivity. Qed.

(* the machine at the end of the pass: with the output ow' appended, or as it is *)
Lemma fin_ow src P0 m mk q nx b ow' : fat src P0 m mk q nx b ->
  let mt := set_m_ow mk ow' in
  fk m mt /\ bitbuf src P0 mt /\ m_bits mt = b /\ m_nx mt = nx /\ m_ow mt = ow' /\ mq P0 mt = q.
Proof.
  intros (B & K & Q & N & Bi & O) mt. split; [apply fk_ow; exact K|]. split; [apply bitbuf_ow; exact B|].
  split; [exact Bi|]. split; [exact N|]. split; [reflexivity|exact Q].
Qed.

Lemma fin_same src P0 m mk q nx b : fat src P0 m mk q nx b ->
  fk m mk /\ bitbuf src P0 mk /\ m_bits mk = b /\ m_nx mk = nx /\ m_ow mk = m_ow m /\ mq P0 mk = q.
Proof. intros (B & K & Q & N & Bi & O). auto 7. Qed.

(* one step within the limits, then the rest of the trace *)
Lemma areach_cons src I R a n w a1 a' :
  SIAbs.astep lenfix_list distfix_list src a = AGo n w a1 -> n <= 8 * I -> (w = true -> Zlength (a_O a) < R) ->
  areach src I R a1 a' -> areach src I R a a'.
Proof. intros S Hn Hw H. apply (areach_trans _ _ _ _ a1); [eapply areach_one; eauto|exact H]. Qed.

Lemma Zlength_lz_copy n d out : Zlength (lz_copy n d out) = Zlength out + Z.of_nat n.
Proof.
  revert out. induction n as [|n IH]; intros out; cbn [Zlib.proof.rfc1951.Format.lz_copy]; [lia|].
  rewrite IH, Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma adecode_eq fx dx src s s' t t' nb nb' lk q :
  i_codes s = i_codes s' -> t = t' -> nb = nb' -> adecode fx dx src s t nb lk q = adecode fx dx src s' t' nb' lk q.
Proof. intros E -> ->. apply adecode_codes. exact E. Qed.

(* the refill and the walk with the resulting machine as a variable *)
Lemma fat_refill_v src P0 m mt q nx b : fat src P0 m mt q nx b -> b <= 30 -> (b < 15 -> nx + 2 <= Zlength (m_inp m)) ->
  exists mt' nx' b', DK.refill2 mt = mt' /\ fat src P0 m mt' q nx' b' /\
    ((b < 15 /\ nx' = nx + 2 /\ b' = b + 16) \/ (15 <= b /\ nx' = nx /\ b' = b)).
Proof.
  intros F Hb Hn. destruct (fat_refill _ _ _ _ _ _ _ F Hb Hn) as (nx' & b' & F' & H).
  exists (DK.refill2 mt), nx', b'. auto.
Qed.

Lemma fat_walk_v src P0 m mt q nx b kind t nb sz il lk here l :
  fwalk_stmt -> fat src P0 m mt q nx b -> 15 <= b ->
  tvalid_g kind (tab_entry lenfix_list distfix_list (m_s m) t) nb sz ->
  (kind = LENS /\ il = len_link /\ lk = len_islink) \/ (kind = DISTS /\ il = dist_link /\ lk = dist_islink) ->
  adecode lenfix_list distfix_list src (m_s m) t nb lk q = (here, l) ->
  exists mt', fwalk_f lenfix_list distfix_list 2 il t (tab_entry lenfix_list distfix_list (m_s m) t (m_hold mt mod 2 ^ nb)) mt =
    (here, mt') /\
  fat src P0 m mt' (q + l) nx (b - l) /\ 0 <= l <= 15 /\ entry_ok here /\ final_ok kind here /\
  exists i, 0 <= i < sz /\ here = tab_entry lenfix_list distfix_list (m_s m) t i.
Proof.
  intros W F Hb TV KL E. destruct (fat_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W F Hb TV KL E) as (A & B & C).
  exists (dropbits l mt). auto.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The arithmetic of the bit buffer over one pass: the pulls stay within the input (the loop's     *)
(* test leaves 6 bytes), the buffer keeps at most 30 bits, the bits consumed are the bytes read     *)

Lemma ar_walk b0 nx0 n b1 nx1 l :
  0 <= b0 <= 30 -> nx0 + 6 <= n -> 0 <= l <= 15 ->
  (b0 < 15 /\ nx1 = nx0 + 2 /\ b1 = b0 + 16) \/ (15 <= b0 /\ nx1 = nx0 /\ b1 = b0) ->
  l <= b1 /\ b1 - l <= 30 /\ b1 - l - 8 * nx1 <= b0 - 8 * nx0 /\ nx1 + 4 <= n.
Proof. intros. lia. Qed.

Lemma ar_lenx b0 nx0 n b1 nx1 l e1 nx3 b3 :
  0 <= b0 <= 30 -> nx0 + 6 <= n -> 0 <= l <= 15 -> 0 <= e1 <= 5 ->
  (b0 < 15 /\ nx1 = nx0 + 2 /\ b1 = b0 + 16) \/ (15 <= b0 /\ nx1 = nx0 /\ b1 = b0) -> l <= b1 ->
  (b1 - l < e1 -> nx1 < n) /\
  (((b1 - l < e1 /\ nx3 = nx1 + 1 /\ b3 = b1 - l + 8 - e1) \/ (e1 <= b1 - l /\ nx3 = nx1 /\ b3 = b1 - l - e1)) ->
   0 <= b3 <= 30 /\ (b3 < 15 -> nx3 + 2 <= n)).
Proof. intros. lia. Qed.

Lemma ar_dist b0 nx0 n b1 nx1 l e1 nx3 b3 nx4 b4 l2 e2 :
  0 <= b0 <= 30 -> nx0 + 6 <= n -> 0 <= l <= 15 -> 0 <= e1 <= 5 -> 0 <= l2 <= 15 -> 0 <= e2 <= 13 ->
  (b0 < 15 /\ nx1 = nx0 + 2 /\ b1 = b0 + 16) \/ (15 <= b0 /\ nx1 = nx0 /\ b1 = b0) -> l <= b1 ->
  (b1 - l < e1 /\ nx3 = nx1 + 1 /\ b3 = b1 - l + 8 - e1) \/ (e1 <= b1 - l /\ nx3 = nx1 /\ b3 = b1 - l - e1) ->
  (b3 < 15 /\ nx4 = nx3 + 2 /\ b4 = b3 + 16) \/ (15 <= b3 /\ nx4 = nx3 /\ b4 = b3) ->
  l2 <= b4 /\ b4 - l2 <= 30 /\ b4 - l2 - 8 * nx4 <= b0 - 8 * nx0 /\
  (b4 - l2 < e2 -> nx4 < n) /\ (b4 - l2 + 8 < e2 -> nx4 + 1 < n).
Proof. intros. lia. Qed.

Lemma ar_distx b0 nx0 b4 nx4 l2 e2 nx6 b6 :
  0 <= e2 <= 13 -> l2 <= b4 -> b4 - l2 <= 30 -> b4 - l2 - 8 * nx4 <= b0 - 8 * nx0 ->
  (b4 - l2 + 8 < e2 /\ nx6 = nx4 + 2 /\ b6 = b4 - l2 + 16 - e2) \/
  (b4 - l2 < e2 <= b4 - l2 + 8 /\ nx6 = nx4 + 1 /\ b6 = b4 - l2 + 8 - e2) \/
  (e2 <= b4 - l2 /\ nx6 = nx4 /\ b6 = b4 - l2 - e2) ->
  b6 <= 30 /\ b6 - 8 * nx6 <= b0 - 8 * nx0.
Proof. intros. lia. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The abstract traces of a symbol                                                                *)

Section Traces.
Variables (src: list Z) (I R: Z).

Lemma at_lit sa q O here l : i_mode sa = LEN ->
  adecode lenfix_list distfix_list src sa (i_lencode sa) (i_lenbits sa) len_islink q = (here, l) -> e_op here = 0 ->
  q + l <= 8 * I -> Zlength O < R ->
  areach src I R (AS sa q O) (AS (fsx sa LEN (e_val here) (i_offset sa) (i_extra sa)) (q + l) (O ++ [e_val here mod 256])).
Proof.
  intros Hm E Hop HI HR. rewrite <- st_lit.
  eapply areach_cons; [exact (aLEN_lit src sa q O here l Hm E Hop)|exact HI|discriminate|].
  eapply areach_one; [apply aLIT; reflexivity|exact HI|intros _; exact HR].
Qed.

Lemma at_eob sa q O here l : i_mode sa = LEN ->
  adecode lenfix_list distfix_list src sa (i_lencode sa) (i_lenbits sa) len_islink q = (here, l) -> e_op here = 96 ->
  q + l <= 8 * I ->
  areach src I R (AS sa q O)
    (AS (fsx sa Zlib.proof.inflate.Model.TYPE (e_val here) (i_offset sa) (i_extra sa)) (q + l) O).
Proof.
  intros Hm E Hop HI. rewrite <- st_eob.
  eapply areach_one; [exact (aLEN_eob src sa q O here l Hm E Hop)|exact HI|discriminate].
Qed.

Lemma at_lbad sa q O here l : i_mode sa = LEN ->
  adecode lenfix_list distfix_list src sa (i_lencode sa) (i_lenbits sa) len_islink q = (here, l) ->
  e_op here <> 0 -> Z.land (e_op here) 32 = 0 -> Z.land (e_op here) 64 <> 0 -> q + l <= 8 * I ->
  exists a', areach src I R (AS sa q O) a' /\ a_mode a' = BAD /\ a_O a' = O.
Proof.
  intros Hm E H0 H32 H64 HI. eexists. split.
  { eapply areach_one; [exact (aLEN_bad src sa q O here l Hm E H0 H32 H64)|exact HI|discriminate]. }
  split; reflexivity.
Qed.

(* LEN and LENEXT of a length code, then DIST: refused, or DISTEXT into MATCH *)
Lemma at_len sa q O here l here2 l2 : i_mode sa = LEN ->
  adecode lenfix_list distfix_list src sa (i_lencode sa) (i_lenbits sa) len_islink q = (here, l) ->
  e_op here <> 0 -> Z.land (e_op here) 32 = 0 -> Z.land (e_op here) 64 = 0 -> 0 <= e_val here < 2 ^ 32 -> 0 <= l ->
  adecode lenfix_list distfix_list src sa (i_distcode sa) (i_distbits sa) dist_islink
    (q + l + Z.land (e_op here) 15) = (here2, l2) -> 0 <= l2 ->
  q + l + Z.land (e_op here) 15 + l2 <= 8 * I ->
  (Z.land (e_op here2) 64 <> 0 -> exists a', areach src I R (AS sa q O) a' /\ a_mode a' = BAD /\ a_O a' = O) /\
  (Z.land (e_op here2) 64 = 0 -> 0 <= e_val here2 < 2 ^ 32 ->
   q + l + Z.land (e_op here) 15 + l2 + Z.land (e_op here2) 15 <= 8 * I ->
   areach src I R (AS sa q O)
     (AS (s_match sa (e_val here) (Z.land (e_op here) 15) (u32 (e_val here + sbits src (q + l) (Z.land (e_op here) 15)))
                  (e_val here2) (Z.land (e_op here2) 15)
                  (u32 (e_val here2 + sbits src (q + l + Z.land (e_op here) 15 + l2) (Z.land (e_op here2) 15))))
         (q + l + Z.land (e_op here) 15 + l2 + Z.land (e_op here2) 15) O)).
Proof.
  intros Hm E H0 H32 H64 Hv Hl E2 Hl2 HI.
  assert (He1: 0 <= Z.land (e_op here) 15) by (apply Z.land_nonneg; lia).
  pose proof (aLEN_len src sa q O here l Hm E H0 H32 H64) as A1.
  pose proof (aLENEXT src (set_i_mode (set_i_extra (set_i_length sa (e_val here)) (Z.land (e_op here) 15)) LENEXT)
                (q + l) O eq_refl Hv) as A2.
  cbn [i_extra i_length set_i_mode set_i_extra set_i_length] in A2.
  match type of A2 with _ = AGo _ _ (AS ?s2 _ _) =>
    assert (E2a: adecode lenfix_list distfix_list src s2 (i_distcode s2) (i_distbits s2) dist_islink
                   (q + l + Z.land (e_op here) 15) = (here2, l2)) by (rewrite <- E2; apply adecode_eq; reflexivity) end.
  split.
  - intros H64'. eexists. split.
    { eapply areach_cons; [exact A1|lia|discriminate|].
      eapply areach_cons; [exact A2|lia|discriminate|].
      pose proof (fun H => aDIST_bad src _ _ O _ _ H E2a H64') as A3. specialize (A3 eq_refl).
      eapply areach_one; [exact A3|lia|discriminate]. }
    split; reflexivity.
  - intros H64' Hv2 HI2.
    assert (He2: 0 <= Z.land (e_op here2) 15) by (apply Z.land_nonneg; lia).
    pose proof (fun H => aDIST_ok src _ _ O _ _ H E2a H64') as A3. specialize (A3 eq_refl).
    match type of A3 with _ = AGo _ _ (AS ?s3 _ _) =>
      pose proof (aDISTEXT src s3 (q + l + Z.land (e_op here) 15 + l2) O eq_refl Hv2) as A4 end.
    cbn [i_extra i_offset set_i_mode set_i_extra set_i_offset] in A4.
    eapply areach_cons; [exact A1|lia|discriminate|].
    eapply areach_cons; [exact A2|lia|discriminate|].
    eapply areach_cons; [exact A3|lia|discriminate|].
    eapply areach_one; [exact A4|lia|discriminate].
Qed.

(* MATCH: a distance past the whole output, or the copy (the steps of fmatch_stmt) *)
Lemma at_far a s q O : areach src I R a (AS s q O) -> i_mode s = MATCH -> Zlength O < i_offset s -> q <= 8 * I ->
  Zlength O < R -> exists a', areach src I R a a' /\ a_mode a' = BAD /\ a_O a' = O.
Proof.
  intros H Hm Hf HI HR. eexists. split.
  { apply (areach_trans _ _ _ _ _ _ H). eapply areach_one; [exact (aMATCH_far src s q O Hm Hf)|exact HI|intros _; exact HR]. }
  split; reflexivity.
Qed.

Lemma at_near a sa val e1 len dval e2 dist q O : fmatch_stmt ->
  areach src I R a (AS (s_match sa val e1 len dval e2 dist) q O) ->
  1 <= len -> 1 <= dist <= Zlength O -> q <= 8 * I -> Zlength O + len <= R ->
  areach src I R a (AS (fsx sa LEN 0 dist e2) q (lz_copy (Z.to_nat len) dist O)).
Proof.
  intros M H Hl Hd HI HR. apply (areach_trans _ _ _ _ _ _ H).
  pose proof (M src I R (AS (s_match sa val e1 len dval e2 dist) q O) eq_refl Hl Hd HI HR) as HM.
  cbn [a_s a_q a_O] in HM. rewrite st_match in HM. exact HM.
Qed.

End Traces.

(* ---------------------------------------------------------------------------------------------- *)
(* The conclusion of one pass                                                                     *)

Definition fpost (src: list Z) (P0: Z) (O0: list Z) (m: mst) (a: ast) (go: bool) (m': mst) : Prop :=
  exists a' mt, areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' /\
      mt = fset m (m_nx mt) (m_ow mt) (m_hold mt) (m_bits mt) /\
      bitbuf src P0 mt /\ m_bits mt <= 30 /\ m_bits mt - 8 * m_nx mt <= m_bits m - 8 * m_nx m /\
      a_O a' = O0 ++ m_ow mt /\ Zlength (m_ow mt) <= Zlength (m_ow m) + 258 /\
      ((go = true /\ m' = mt /\ Zlength (m_ow m) < Zlength (m_ow mt) /\ a_q a' = mq P0 mt /\
        exists l o e, a_s a' = fsx (a_s a) LEN l o e) \/
       (go = false /\ m' = set_mode mt Zlib.proof.inflate.Model.TYPE /\ a_q a' = mq P0 mt /\
        exists l o e, a_s a' = fsx (a_s a) Zlib.proof.inflate.Model.TYPE l o e) \/
       (go = false /\ a_mode a' = BAD /\ exists e, m' = set_bad mt e)).

Lemma close_go src P0 O0 m a a' mk q nx b ow' :
  areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' -> fat src P0 m mk q nx b ->
  b <= 30 -> b - 8 * nx <= m_bits m - 8 * m_nx m -> a_O a' = O0 ++ ow' ->
  Zlength (m_ow m) < Zlength ow' <= Zlength (m_ow m) + 258 -> a_q a' = q ->
  (exists l o e, a_s a' = fsx (a_s a) LEN l o e) ->
  fpost src P0 O0 m a true (set_m_ow mk ow').
Proof.
  intros H F Hb Hm HO Hl Hq Hs. destruct (fin_ow _ _ _ _ _ _ _ ow' F) as (K & B & Bi & N & O & Q).
  exists a', (set_m_ow mk ow').
  split; [exact H|]. split; [exact K|]. split; [exact B|]. rewrite Bi, N, O, Q. split; [exact Hb|]. split; [exact Hm|].
  split; [exact HO|]. split; [lia|]. left.
  split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hq|exact Hs].
Qed.

Lemma close_type src P0 O0 m a a' mk q nx b :
  areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' -> fat src P0 m mk q nx b ->
  b <= 30 -> b - 8 * nx <= m_bits m - 8 * m_nx m -> a_O a' = O0 ++ m_ow m -> a_q a' = q ->
  (exists l o e, a_s a' = fsx (a_s a) Zlib.proof.inflate.Model.TYPE l o e) ->
  fpost src P0 O0 m a false (set_mode mk Zlib.proof.inflate.Model.TYPE).
Proof.
  intros H F Hb Hm HO Hq Hs. destruct (fin_same _ _ _ _ _ _ _ F) as (K & B & Bi & N & O & Q).
  exists a', mk.
  split; [exact H|]. split; [exact K|]. split; [exact B|]. rewrite Bi, N, O, Q. split; [exact Hb|]. split; [exact Hm|].
  split; [exact HO|]. split; [lia|]. right; left.
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hq|exact Hs].
Qed.

Lemma close_bad src P0 O0 m a a' mk q nx b e :
  areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) a a' -> fat src P0 m mk q nx b ->
  b <= 30 -> b - 8 * nx <= m_bits m - 8 * m_nx m -> a_O a' = O0 ++ m_ow m -> a_mode a' = BAD ->
  fpost src P0 O0 m a false (set_bad mk e).
Proof.
  intros H F Hb Hm HO Hs. destruct (fin_same _ _ _ _ _ _ _ F) as (K & B & Bi & N & O & Q).
  exists a', mk.
  split; [exact H|]. split; [exact K|]. split; [exact B|]. rewrite Bi, N, O. split; [exact Hb|]. split; [exact Hm|].
  split; [exact HO|]. split; [lia|]. right; right. split; [reflexivity|]. split; [exact Hs|]. exists e. reflexivity.
Qed.

(* the end of a match: the distance refused (too far back), or the copy *)
Lemma close_dist src P0 O0 m sa q0 Oa val e1 len dval e2 dist m6 q4 nx6 b6 go m' :
  fcopy_stmt -> fmatch_stmt ->
  areach src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (AS sa q0 Oa)
    (AS (s_match sa val e1 len dval e2 dist) q4 Oa) ->
  fat src P0 m m6 q4 nx6 b6 -> b6 <= 30 -> b6 - 8 * nx6 <= m_bits m - 8 * m_nx m ->
  3 <= len <= 258 -> 1 <= dist <= 32768 -> swin_ok (m_s m) O0 -> i_sane (m_s m) = 1 ->
  Oa = O0 ++ m_ow m -> Zlength (m_ow m) + 258 <= m_aout m ->
  DK.fcopy (m_s m) len dist m6 = (go, m') ->
  fpost src P0 O0 m (AS sa q0 Oa) go m'.
Proof.
  intros C M H F Hb Hmo Hlen Hdist Hw Hs HO Hout EF.
  pose proof (fat_q _ _ _ _ _ _ _ F) as Q. pose proof F as (_ & _ & _ & _ & _ & O6).
  destruct (s_match_fields sa val e1 len dval e2 dist) as (Fm & Fl & Fo).
  destruct (C (m_s m) O0 m6 len dist Hw Hs Hdist Hlen) as [(Hfar & EC)|(Hnear & ow' & EC & Eow)];
    rewrite EC in EF; injection EF as <- <-.
  - destruct (at_far src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) (AS sa q0 Oa) _ q4 Oa H Fm)
      as (a' & Ar & Am & AO).
    + rewrite Fo, HO, Zlength_app, <- O6. exact Hfar.
    + exact (proj2 Q).
    + rewrite HO, Zlength_app. lia.
    + apply (close_bad _ _ _ _ _ _ _ _ _ _ _ Ar F Hb Hmo); [rewrite AO, HO; reflexivity|exact Am].
  - rewrite O6, <- HO in Eow.
    assert (Low: Zlength ow' = Zlength (m_ow m) + len).
    { apply (f_equal (@Zlength Z)) in Eow. rewrite Zlength_lz_copy, Zlength_app, HO, Zlength_app in Eow.
      rewrite Z2Nat.id in Eow by lia. lia. }
    assert (Hd2: dist <= Zlength Oa) by (rewrite HO, Zlength_app, <- O6; lia).
    pose proof (at_near src (P0 + Zlength (m_inp m)) (Zlength O0 + m_aout m) _ sa val e1 len dval e2 dist q4 Oa M H
                  ltac:(lia) ltac:(lia) (proj2 Q) ltac:(rewrite HO, Zlength_app; lia)) as Ar.
    apply (close_go _ _ _ _ _ _ _ _ _ _ ow' Ar F Hb Hmo).
    + cbn [a_O]. symmetry. exact Eow.
    + lia.
    + reflexivity.
    + exists 0, dist, e2. reflexivity.
Qed.
