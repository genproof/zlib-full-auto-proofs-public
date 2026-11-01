(* Law rfc_stored, the padding simulation (RSSim.v): the shared definitions and the input kit.

   The real machine is the canonical one with another input (set_m_inp m' x).  A pass of the switch reads its
   input only through PULLBYTE (Model.pull, inside NEEDBITS) and Model.inbytes (COPY); if the bytes it reads
   are the same in both inputs, the real pass is the canonical pass with the real input ([rs_iom]).
   [rs_needbits_inp]: NEEDBITS(n) from the bit position q = 8 nx - bits reads exactly the bytes i >= nx with
   8 i < q + n.  [rs_padat G i]: byte i of the source is the first byte of a block, the only bytes where the
   real source differs from the canonical one ([rs_xrel]).  [rs_lay_stmt]: the layout of a stream of stored
   blocks (byte-aligned blocks of 5 + n bytes), proved in RSSimLay.v.  [rs_pass_ok P]: a pass from a loop head
   of the canonical machine whose mode satisfies P does the same on the real input. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist VST.zlist.list_solver.
Require Export Zlib.proof.rfc1951.Decode7Step.
Require Export Zlib.proof.harness.rfc_stored.RSCanon.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* Definitions                                                                                    *)

(* the outcome of a pass with the input x in place of the machine's *)
Definition rs_iom (x: list Z) (o: iout) : iout :=
  match o with IBrk m => IBrk (set_m_inp m x) | IRet r m => IRet r (set_m_inp m x) end.

(* byte i of the source is the first byte of a block *)
Definition rs_padat (G: dctx) (i: Z) : Prop := exists k, 0 <= k < nblk G /\ 8 * i = bpos G k.

(* x, the real input of a call that starts at byte pos of the source, against inp', the canonical one: the same
   bytes but at the first bytes of blocks, which keep their three low bits (BFINAL, BTYPE) and are below 8 in
   the canonical stream *)
Definition rs_xrel (G: dctx) (pos: Z) (x inp': list Z) : Prop :=
  Zlength x = Zlength inp' /\ bytes_ok x /\
  forall i, 0 <= i < Zlength x ->
    Znth i x = Znth i inp' \/
    (rs_padat G (pos + i) /\ Znth i x mod 8 = Znth i inp' mod 8 /\ 0 <= Znth i inp' < 8).

(* the layout of a stream of stored blocks *)
Record rs_lay_stmt : Prop := {
  (* every block is stored *)
  rl_stored : forall G k, rs_stored_only G -> 0 <= k < nblk G -> exists bytes, blk G k = Stored bytes;
  (* the blocks start after the header, byte-aligned *)
  rl_D0 : forall G k, 0 <= k <= nblk G -> D0 G <= bpos G k;
  rl_align : forall G k, rs_stored_only G -> 0 <= k <= nblk G -> bpos G k mod 8 = 0;
  (* block k: 5 bytes (BFINAL, BTYPE and the padding; LEN; NLEN), then its bytes *)
  rl_blk : forall G k bytes, dctx_ok7a G -> rs_stored_only G -> 0 <= k < nblk G -> blk G k = Stored bytes ->
    bpos G (k + 1) = bpos G k + 40 + 8 * Zlength bytes /\ Zlength bytes <= 65535 /\
    bpos G (k + 1) <= 8 * slen G /\
    sublist (bpos G k) (bpos G (k + 1)) (sbits G) = enc_block (bpos G k - D0 G) (lastflag G k =? 1) (Stored bytes);
  (* the blocks in order *)
  rl_mono : forall G j k, rs_stored_only G -> 0 <= j < k -> k <= nblk G -> bpos G j + 40 <= bpos G k;
  (* the deflate stream ends after the last block *)
  rl_end : forall G, rs_stored_only G -> endpos G = bpos G (nblk G)
}.

(* a pass of the switch from a loop head of the canonical machine, with mode in P, does the same on the real
   input *)
Definition rs_pass_ok (P: Z -> Prop) : Prop :=
  forall G pos x inp' ob flush m',
    dctx_ok7a G -> rs_stored_only G -> 0 <= pos -> pos + Zlength inp' <= Zlength (dc_src G) ->
    inp' = sublist pos (pos + Zlength inp') (dc_src G) -> rs_xrel G pos x inp' ->
    Kd G pos inp' ob m' -> mwf3W m' -> m_leave m' = 0 -> P (m_mode m') ->
    stepf2 flush lenfix_list distfix_list (set_m_inp m' x) = rs_iom x (stepf2 flush lenfix_list distfix_list m').

(* ---------------------------------------------------------------------------------------------- *)
(* The input kit                                                                                  *)

Lemma rs_inp_inp m x y : set_m_inp (set_m_inp m x) y = set_m_inp m y.
Proof. destruct m; reflexivity. Qed.

Lemma rs_inp_id m : set_m_inp m (m_inp m) = m.
Proof. destruct m; reflexivity. Qed.

Lemma rs_have_inp m x : Zlength x = Zlength (m_inp m) -> m_have (set_m_inp m x) = m_have m.
Proof. intros E. unfold m_have. destruct m; cbn in *. rewrite E. reflexivity. Qed.

Lemma rs_leave_inp m x : set_leave (set_m_inp m x) = set_m_inp (set_leave m) x.
Proof. destruct m; reflexivity. Qed.

(* PULLBYTE reads the byte at nx *)
Lemma rs_pull_inp m x : Znth (m_nx m) x = Znth (m_nx m) (m_inp m) -> pull (set_m_inp m x) = set_m_inp (pull m) x.
Proof. intros E. destruct m; unfold pull; cbn in *. rewrite E. reflexivity. Qed.

(* NEEDBITS(n), n <= 32, from bit position q = 8 nx - bits reads the bytes i >= nx with 8 i < q + n *)
Lemma rs_needbits_inp k : forall n m x,
  Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> n <= 32 ->
  (forall i, m_nx m <= i -> 8 * i < 8 * m_nx m - m_bits m + n -> Znth i x = Znth i (m_inp m)) ->
  needbits_f k n (set_m_inp m x) = set_m_inp (needbits_f k n m) x.
Proof.
  induction k as [|k IH]; intros n m x Hl Hb Hn Ha; [reflexivity|].
  cbn [needbits_f]. change (m_bits (set_m_inp m x)) with (m_bits m).
  destruct (Z.ltb_spec (m_bits m) n) as [Lt|Ge]; [|reflexivity].
  rewrite (rs_have_inp m x Hl).
  destruct (Z.eqb (m_have m) 0); [apply rs_leave_inp|].
  rewrite rs_pull_inp by (apply Ha; lia).
  assert (Bp : m_bits (pull m) = m_bits m + 8).
  { unfold pull, u32. cbn. apply Z.mod_small. lia. }
  assert (Np : m_nx (pull m) = m_nx m + 1) by reflexivity.
  assert (Ip : m_inp (pull m) = m_inp m) by reflexivity.
  apply IH; rewrite ?Bp, ?Np, ?Ip; auto; try lia.
  intros i H1 H2. apply Ha; lia.
Qed.

Lemma rs_needbits_inp4 n m x :
  Zlength x = Zlength (m_inp m) -> 0 <= m_bits m -> n <= 32 ->
  (forall i, m_nx m <= i -> 8 * i < 8 * m_nx m - m_bits m + n -> Znth i x = Znth i (m_inp m)) ->
  needbits n (set_m_inp m x) = set_m_inp (needbits n m) x.
Proof. apply rs_needbits_inp. Qed.

(* the bytes [nx, nx + n) *)
Lemma rs_inbytes_inp m x n : Zlength x = Zlength (m_inp m) -> 0 <= m_nx m -> 0 <= n ->
  (forall i, m_nx m <= i < m_nx m + n -> Znth i x = Znth i (m_inp m)) ->
  inbytes (set_m_inp m x) n = inbytes m n.
Proof.
  intros Hl Hx Hn Ha. unfold inbytes.
  change (m_nx (set_m_inp m x)) with (m_nx m). change (m_inp (set_m_inp m x)) with x.
  set (a := m_nx m) in *. set (l := m_inp m) in *.
  apply list_solver.Znth_eq_ext; [rewrite !Zlength_sublist2; lia|].
  intros i Hi. rewrite Zlength_sublist2 in Hi. rewrite !Znth_sublist by lia. apply Ha; lia.
Qed.
