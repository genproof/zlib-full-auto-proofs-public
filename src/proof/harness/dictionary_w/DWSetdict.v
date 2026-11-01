(* The laws rt_dictionary and api_dict_id: the stream's counters after deflateSetDictionary, pure Coq over the
   model of deflate.c.

   deflateSetDictionary gives (the tail of) the dictionary to fill_window as the stream's input: read_buf adds the
   bytes it reads to total_in modulo 2^64 and may update adler; total_out is not touched.  The deflate loop of the
   two laws counts total_in on from there, for up to 2^63 - 1 bytes of data, so it needs that total_in is at most
   its value before the call plus the length of the dictionary ([setdict_counters]), not only that it is a uLong. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.roundtrip.RTK7.
Require Zlib.proof.adler32.Model.
Require Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.

(* the model's loops have 2^40 iterations of fuel: the kernel must never unfold them *)
Local Strategy opaque [loop loop2].

Lemma dws_runs_pres {A B : Type} (body : A -> option (A + B)) (P : A -> Prop) (Q : B -> Prop) :
  (forall a a', P a -> body a = Some (inl a') -> P a') ->
  (forall a r, P a -> body a = Some (inr r) -> Q r) ->
  forall a r, runs body a r -> P a -> Q r.
Proof. intros Hs He a r H. induction H; eauto. Qed.

Lemma dws_bind_some {A B} (x : option A) (f : A -> option B) r :
  bind x f = Some r -> exists v, x = Some v /\ f v = Some r.
Proof. destruct x; simpl; [eauto | discriminate]. Qed.

(* the stream fill_window reads the dictionary from: its input is [d]; total_in plus the bytes left to read stays
   at most [T] (T < 2^64: the additions modulo 2^64 do not wrap); total_out is [t]; adler a uLong *)
Definition dws_q (d : list Z) (T t : Z) (z : strm) : Prop :=
  z_in z = d /\ 0 <= z_total_in z <= T /\ (0 <= z_avail_in z -> z_total_in z + z_avail_in z <= T) /\
  z_total_out z = t /\ 0 <= z_adler z <= 18446744073709551615.

Lemma dws_read_buf d T t s z size z' data :
  rbytes d -> T < 18446744073709551616 -> dws_q d T t z -> c_read_buf s z size = Some (z', data) ->
  dws_q d T t z'.
Proof.
  intros Hd HT (Hi & Ht & Hta & Ho & Ha) H. unfold c_read_buf in H.
  set (len := if z_avail_in z >? size then size else z_avail_in z) in H.
  destruct (len =? 0); [inversion H; subst; repeat split; auto; lia|].
  unfold bind, rds in H.
  match type of H with context [if ?c then _ else _] => destruct c eqn:Ec end; [|discriminate].
  injection H as <- <-. cbn in Ec |- *.
  repeat rewrite andb_true_iff in Ec. destruct Ec as [[E1 E2] E3].
  apply Z.leb_le in E1, E2, E3.
  assert (Hl : len <= z_avail_in z) by (unfold len; destruct (z_avail_in z >? size) eqn:X; lia).
  rewrite Hi in *.
  assert (Hb : Zlib.proof.adler32.Bytes.is_bytes (sublist (z_next_in z) (z_next_in z + len) d)).
  { unfold Zlib.proof.adler32.Bytes.is_bytes. apply Forall_sublist.
    eapply Forall_impl; [|exact Hd]. simpl. rep_lia. }
  assert (Hu : u64 (z_total_in z + len) = z_total_in z + len) by (unfold u64; apply Z.mod_small; lia).
  destruct (d_wrap s =? 1); [|destruct (d_wrap s =? 2)];
    unfold dws_q, set_z_total_in, set_z_next_in, set_z_adler, set_z_avail_in; cbn; rewrite ?Hu;
    (split; [exact Hi|]); (split; [lia|]); (split; [lia|]); (split; [assumption|]).
  - pose proof (Zlib.proof.adler32.Model.adler32_z_val_range (z_adler z) _ Hb). rep_lia.
  - pose proof (Zlib.proof.crc32.Combine.ref_crc32_range (z_adler z) _ Hb).
    unfold Zlib.proof.crc32.GF2.is32 in *. rep_lia.
  - assumption.
Qed.

Lemma dws_fw_body d T t s0 z0 x :
  rbytes d -> T < 18446744073709551616 -> dws_q d T t z0 -> fw_body (s0, z0) = Some x ->
  dws_q d T t (match x with inl a => snd a | inr r => snd r end).
Proof.
  intros Hd HT Hq Hb. unfold fw_body, bind in Hb.
  destruct (c_fw_slide s0 _) as [[s2 m2]|]; [|discriminate].
  destruct (z_avail_in z0 =? 0); [injection Hb as <-; exact Hq|].
  destruct (c_read_buf s2 z0 m2) as [[z2 data]|] eqn:Er; [|discriminate].
  destruct (mb_write _ _ _); [|discriminate]. destruct (c_fw_insert _); [|discriminate].
  pose proof (dws_read_buf d T t s2 z0 m2 z2 data Hd HT Hq Er) as Hz2.
  match type of Hb with context [if ?c then _ else _] => destruct c end; injection Hb as <-; exact Hz2.
Qed.

Lemma dws_fill_window d T t s z s' z' :
  rbytes d -> T < 18446744073709551616 -> dws_q d T t z -> c_fill_window s z = Some (s', z') -> dws_q d T t z'.
Proof.
  intros Hd HT Hz H. unfold c_fill_window in H.
  destruct (dws_bind_some _ _ _ H) as [[s1 z1] [E H1]].
  destruct (dws_bind_some _ _ _ H1) as [s2 [_ H2]].
  injection H2 as _ <-.
  refine (dws_runs_pres fw_body (fun a => dws_q d T t (snd a)) (fun r => dws_q d T t (snd r)) _ _ (s, z) (s1, z1)
            (loop_runs FUEL fw_body (s, z) (s1, z1) E) Hz).
  - intros [s0 z0] a' Hq Hb. exact (dws_fw_body d T t s0 z0 (inl a') Hd HT Hq Hb).
  - intros [s0 z0] r Hq Hb. exact (dws_fw_body d T t s0 z0 (inr r) Hd HT Hq Hb).
Qed.

Lemma dws_sd_body d T t : rbytes d -> T < 18446744073709551616 ->
  forall a x, dws_q d T t (snd a) -> sd_body a = Some x ->
  dws_q d T t (match x with inl a' => snd a' | inr r => snd r end).
Proof.
  intros Hd HT [s0 z0] x Hq Hb. unfold sd_body in Hb.
  destruct (d_lookahead s0 >=? MIN_MATCH); [|injection Hb as <-; exact Hq].
  destruct (dws_bind_some _ _ _ Hb) as [[s1 str] [_ H1]].
  destruct (dws_bind_some _ _ _ H1) as [[s2 z2] [E2 H2]].
  injection H2 as <-. exact (dws_fill_window d T t _ z0 s2 z2 Hd HT Hq E2).
Qed.

(* deflateSetDictionary, whatever its return code: total_in is at most its value before plus the length of the
   dictionary, total_out is kept, adler stays a uLong *)
Lemma setdict_counters s z d s' z' code :
  rbytes d -> 0 <= z_total_in z -> z_total_in z + Zlength d < 18446744073709551616 ->
  0 <= z_adler z <= 18446744073709551615 ->
  c_deflateSetDictionary s z (Some d) = Some (s', z', code) ->
  0 <= z_total_in z' <= z_total_in z + Zlength d /\ z_total_out z' = z_total_out z /\
  0 <= z_adler z' <= 18446744073709551615.
Proof.
  intros Hd Ht HT Ha H. unfold c_deflateSetDictionary in H.
  destruct (bad_state s); [injection H as _ <- _; pose proof (Zlength_nonneg d); repeat split; auto; lia|].
  match type of H with context [if ?c then _ else _] => destruct c end;
    [injection H as _ <- _; pose proof (Zlength_nonneg d); repeat split; auto; lia|].
  set (z1 := if d_wrap s =? 1 then set_z_adler z (Zlib.proof.adler32.Model.adler32_z_val (z_adler z) d) else z)
    in H.
  destruct (dws_bind_some _ _ _ H) as [[[s1 off] len] [Eo H1]].
  destruct (dws_bind_some _ _ _ H1) as [[s2 z2] [E2 H2]].
  destruct (dws_bind_some _ _ _ H2) as [[s3 z3] [E3 H3]].
  injection H3 as _ <- _.
  assert (Q1 : z_total_in z1 = z_total_in z /\ z_total_out z1 = z_total_out z /\
               0 <= z_adler z1 <= 18446744073709551615).
  { unfold z1. destruct (d_wrap s =? 1); [|auto].
    assert (Hb : Zlib.proof.adler32.Bytes.is_bytes d).
    { unfold Zlib.proof.adler32.Bytes.is_bytes. eapply Forall_impl; [|exact Hd]. simpl. rep_lia. }
    pose proof (Zlib.proof.adler32.Model.adler32_z_val_range (z_adler z) d Hb).
    unfold set_z_adler; simpl. repeat split; try rep_lia. }
  assert (Hlen : len <= Zlength d).
  { destruct (Zlength d >=? d_w_size (set_d_wrap s 0)) eqn:X.
    - destruct (dws_bind_some _ _ _ Eo) as [s4 [Es4 E4]]. injection E4 as _ _ <-.
      apply Z.geb_le in X.
      assert (W4 : d_w_size s4 = d_w_size (set_d_wrap s 0)).
      { destruct (d_wrap s =? 0); [|injection Es4 as <-; reflexivity].
        destruct (dws_bind_some _ _ _ Es4) as [s5 [Ec E5]]. injection E5 as <-.
        unfold c_clear_hash in Ec.
        destruct (dws_bind_some _ _ _ Ec) as [h [_ Ec1]].
        destruct (dws_bind_some _ _ _ Ec1) as [g [_ Ec2]].
        injection Ec2 as <-. reflexivity. }
      lia.
    - injection Eo as _ _ <-. lia. }
  set (T := z_total_in z + Zlength d).
  assert (Q0 : dws_q d T (z_total_out z) (mkST d off len (z_total_in z1) (z_out z1) (z_avail_out z1)
                                              (z_total_out z1) (z_adler z1) (z_msg z1))).
  { unfold dws_q, T; simpl. destruct Q1 as (-> & -> & Q). pose proof (Zlength_nonneg d).
    repeat split; auto; lia. }
  pose proof (dws_fill_window d T _ s1 _ s2 z2 Hd HT Q0 E2) as Q2.
  pose proof (dws_runs_pres sd_body (fun a => dws_q d T (z_total_out z) (snd a))
                (fun r => dws_q d T (z_total_out z) (snd r))
                (fun a a' Hq Hb => dws_sd_body d T _ Hd HT a (inl a') Hq Hb)
                (fun a r Hq Hb => dws_sd_body d T _ Hd HT a (inr r) Hq Hb)
                (s2, z2) (s3, z3) (loop_runs _ _ _ _ E3) Q2) as Q3.
  destruct Q3 as (_ & Q3i & _ & Q3o & Q3a). simpl in Q3i, Q3o, Q3a |- *. rewrite Q3o.
  unfold T in Q3i. auto.
Qed.
