(* The cases of inflate's model (Model2.stepf2) do not read the header model where RTH8W.hind holds: replacing the
   header model m_h of the machine by any h before a case gives the case's outcome with its header model replaced
   by h.  The non-header cases (DICTID .. BAD) never mention m_h; the header cases (HEAD .. HCRC) only read or
   write it under `if i_head ...` (or, for NAME / COMMENT, write back the buffer unchanged when i_head is false).

   The proofs relate the two runs by the structure of the case's term (hs_rel): the same test on both sides
   (hr_if, the branches are related), a machine let related to its counterpart (hr_let), a tuple or CODELENS
   outcome related componentwise; the getters and setters agree by conversion, the helpers with loops or tests
   (NEEDBITS, the table lookups, inflate_fast, the LENLENS / CODELENS loops) by their own lemmas (the hr_ lemmas), the case
   a case falls through into by its lemma.  Along the way they show that the outcome keeps RTH8W.hind: a
   non-header case only reaches non-header modes, and no case changes i_head. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.inflate.Model2.
Require Zlib.proof.roundtrip.RTHSpec.
Import ListNotations.
Local Open Scope Z_scope.

Notation hdr_mode := Zlib.proof.roundtrip.RTHSpec.hdr_mode.

Definition out_hk (o: iout) (h: hstate) : iout :=
  match o with IBrk m => IBrk (set_m_h m h) | IRet r m => IRet r (set_m_h m h) end.

(* the outcome's machine is in a non-header mode / has no header attached *)
Definition qmd (o: iout) : Prop := match o with IBrk m | IRet _ m => hdr_mode (m_mode m) = false end.
Definition qhd (o: iout) : Prop := match o with IBrk m | IRet _ m => i_head (m_s m) = false end.

(* the machine is in a non-header mode (for a machine, the machine of a pair, of a CODELENS outcome) *)
Definition qm (m: mst) : Prop := hdr_mode (m_mode m) = false.
Definition qsnd {A} (p: A * mst) : Prop := qm (snd p).
Definition clm (o: clout) : mst := match o with CLnext m | CLleave m | CLbad m => m end.
Definition qcl (o: clout) : Prop := qm (clm o).

(* ---------------------------------------------------------------------------------------------- *)
(* set_m_h through the getters, setters and helpers (by rewriting, for the loop helpers)          *)

Section Push.
Variables (m: mst) (h: hstate).

Lemma hs_g_s : m_s (set_m_h m h) = m_s m. Proof. reflexivity. Qed.
Lemma hs_g_h : m_h (set_m_h m h) = h. Proof. reflexivity. Qed.
Lemma hs_g_inp : m_inp (set_m_h m h) = m_inp m. Proof. reflexivity. Qed.
Lemma hs_g_aout : m_aout (set_m_h m h) = m_aout m. Proof. reflexivity. Qed.
Lemma hs_g_nx : m_nx (set_m_h m h) = m_nx m. Proof. reflexivity. Qed.
Lemma hs_g_ow : m_ow (set_m_h m h) = m_ow m. Proof. reflexivity. Qed.
Lemma hs_g_hold : m_hold (set_m_h m h) = m_hold m. Proof. reflexivity. Qed.
Lemma hs_g_bits : m_bits (set_m_h m h) = m_bits m. Proof. reflexivity. Qed.
Lemma hs_g_in : m_in (set_m_h m h) = m_in m. Proof. reflexivity. Qed.
Lemma hs_g_out : m_out (set_m_h m h) = m_out m. Proof. reflexivity. Qed.
Lemma hs_g_ret : m_ret (set_m_h m h) = m_ret m. Proof. reflexivity. Qed.
Lemma hs_g_leave : m_leave (set_m_h m h) = m_leave m. Proof. reflexivity. Qed.
Lemma hs_g_adler : m_adler (set_m_h m h) = m_adler m. Proof. reflexivity. Qed.
Lemma hs_g_msg : m_msg (set_m_h m h) = m_msg m. Proof. reflexivity. Qed.
Lemma hs_g_tin : m_tin (set_m_h m h) = m_tin m. Proof. reflexivity. Qed.
Lemma hs_g_tout : m_tout (set_m_h m h) = m_tout m. Proof. reflexivity. Qed.
Lemma hs_g_snx : m_snx (set_m_h m h) = m_snx m. Proof. reflexivity. Qed.
Lemma hs_g_sow : m_sow (set_m_h m h) = m_sow m. Proof. reflexivity. Qed.
Lemma hs_g_mode : m_mode (set_m_h m h) = m_mode m. Proof. reflexivity. Qed.
Lemma hs_g_have : m_have (set_m_h m h) = m_have m. Proof. reflexivity. Qed.
Lemma hs_g_left : m_left (set_m_h m h) = m_left m. Proof. reflexivity. Qed.
Lemma hs_g_inbytes n : inbytes (set_m_h m h) n = inbytes m n. Proof. reflexivity. Qed.
Lemma hs_g_bitsn n : bitsn (set_m_h m h) n = bitsn m n. Proof. reflexivity. Qed.

Lemma hs_s_s v : set_m_s (set_m_h m h) v = set_m_h (set_m_s m v) h. Proof. reflexivity. Qed.
Lemma hs_s_inp v : set_m_inp (set_m_h m h) v = set_m_h (set_m_inp m v) h. Proof. reflexivity. Qed.
Lemma hs_s_aout v : set_m_aout (set_m_h m h) v = set_m_h (set_m_aout m v) h. Proof. reflexivity. Qed.
Lemma hs_s_nx v : set_m_nx (set_m_h m h) v = set_m_h (set_m_nx m v) h. Proof. reflexivity. Qed.
Lemma hs_s_ow v : set_m_ow (set_m_h m h) v = set_m_h (set_m_ow m v) h. Proof. reflexivity. Qed.
Lemma hs_s_hold v : set_m_hold (set_m_h m h) v = set_m_h (set_m_hold m v) h. Proof. reflexivity. Qed.
Lemma hs_s_bits v : set_m_bits (set_m_h m h) v = set_m_h (set_m_bits m v) h. Proof. reflexivity. Qed.
Lemma hs_s_in v : set_m_in (set_m_h m h) v = set_m_h (set_m_in m v) h. Proof. reflexivity. Qed.
Lemma hs_s_out v : set_m_out (set_m_h m h) v = set_m_h (set_m_out m v) h. Proof. reflexivity. Qed.
Lemma hs_s_ret v : set_m_ret (set_m_h m h) v = set_m_h (set_m_ret m v) h. Proof. reflexivity. Qed.
Lemma hs_s_leave v : set_m_leave (set_m_h m h) v = set_m_h (set_m_leave m v) h. Proof. reflexivity. Qed.
Lemma hs_s_adler v : set_m_adler (set_m_h m h) v = set_m_h (set_m_adler m v) h. Proof. reflexivity. Qed.
Lemma hs_s_msg v : set_m_msg (set_m_h m h) v = set_m_h (set_m_msg m v) h. Proof. reflexivity. Qed.
Lemma hs_s_tin v : set_m_tin (set_m_h m h) v = set_m_h (set_m_tin m v) h. Proof. reflexivity. Qed.
Lemma hs_s_tout v : set_m_tout (set_m_h m h) v = set_m_h (set_m_tout m v) h. Proof. reflexivity. Qed.
Lemma hs_s_snx v : set_m_snx (set_m_h m h) v = set_m_h (set_m_snx m v) h. Proof. reflexivity. Qed.
Lemma hs_s_sow v : set_m_sow (set_m_h m h) v = set_m_h (set_m_sow m v) h. Proof. reflexivity. Qed.
Lemma hs_s_h v : set_m_h (set_m_h m h) v = set_m_h m v. Proof. reflexivity. Qed.

Lemma hs_upd_s f : upd_s (set_m_h m h) f = set_m_h (upd_s m f) h. Proof. reflexivity. Qed.
Lemma hs_set_mode v : set_mode (set_m_h m h) v = set_m_h (set_mode m v) h. Proof. reflexivity. Qed.
Lemma hs_set_leave : set_leave (set_m_h m h) = set_m_h (set_leave m) h. Proof. reflexivity. Qed.
Lemma hs_set_bad e : set_bad (set_m_h m h) e = set_m_h (set_bad m e) h. Proof. reflexivity. Qed.
Lemma hs_initbits : initbits (set_m_h m h) = set_m_h (initbits m) h. Proof. reflexivity. Qed.
Lemma hs_dropbits n : dropbits n (set_m_h m h) = set_m_h (dropbits n m) h. Proof. reflexivity. Qed.
Lemma hs_bytebits : bytebits (set_m_h m h) = set_m_h (bytebits m) h. Proof. reflexivity. Qed.
Lemma hs_restore : restore (set_m_h m h) = set_m_h (restore m) h. Proof. reflexivity. Qed.
Lemma hs_pull : pull (set_m_h m h) = set_m_h (pull m) h. Proof. reflexivity. Qed.
Lemma hs_fpull : fpull (set_m_h m h) = set_m_h (fpull m) h. Proof. reflexivity. Qed.
Lemma hs_crc_if d : crc_if (set_m_h m h) d = set_m_h (crc_if m d) h.
Proof. unfold crc_if. change (m_s (set_m_h m h)) with (m_s m). destruct (_ && _); reflexivity. Qed.

End Push.

Lemma hs_upd_h m f : upd_h m f = set_m_h m (f (m_h m)). Proof. reflexivity. Qed.

(* the header model through the helpers (used where the header model is written back unchanged) *)
Lemma hh_upd_s m f : m_h (upd_s m f) = m_h m. Proof. reflexivity. Qed.
Lemma hh_set_nx m v : m_h (set_m_nx m v) = m_h m. Proof. reflexivity. Qed.
Lemma hh_crc_if m d : m_h (crc_if m d) = m_h m. Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma hh_set_mode m v : m_h (set_mode m v) = m_h m. Proof. reflexivity. Qed.
Lemma hh_nbuf h : set_h_nbuf h (h_nbuf h) = h. Proof. destruct h; reflexivity. Qed.
Lemma hh_cbuf h : set_h_cbuf h (h_cbuf h) = h. Proof. destruct h; reflexivity. Qed.
Lemma hh_xbuf h : set_h_xbuf h (h_xbuf h) = h. Proof. destruct h; reflexivity. Qed.

(* the copy loop of NAME / COMMENT when nothing is written: the buffer and its size are not read *)
Definition zstr_nw (k: nat) (bytes: list Z) (have length copy: Z) : Z * Z * Z * list Z :=
  zstr_f k bytes have length 0 false [] copy.

Lemma hs_zstr k bytes have : forall length max buf copy,
  zstr_f k bytes have length max false buf copy =
  let '(c, b, l, _) := zstr_nw k bytes have length copy in (c, b, l, buf).
Proof.
  unfold zstr_nw; induction k; intros; cbn [zstr_f andb]; [reflexivity|].
  destruct (_ && _); [|reflexivity]. rewrite (IHk length max buf), (IHk length 0 []). reflexivity.
Qed.

Hint Rewrite hs_g_s hs_g_h hs_g_inp hs_g_aout hs_g_nx hs_g_ow hs_g_hold hs_g_bits hs_g_in hs_g_out hs_g_ret
  hs_g_leave hs_g_adler hs_g_msg hs_g_tin hs_g_tout hs_g_snx hs_g_sow hs_g_mode hs_g_have hs_g_left
  hs_g_inbytes hs_g_bitsn
  hs_s_s hs_s_inp hs_s_aout hs_s_nx hs_s_ow hs_s_hold hs_s_bits hs_s_in hs_s_out hs_s_ret hs_s_leave
  hs_s_adler hs_s_msg hs_s_tin hs_s_tout hs_s_snx hs_s_sow hs_s_h
  hs_upd_s hs_set_mode hs_set_leave hs_set_bad hs_initbits hs_dropbits hs_bytebits hs_restore hs_pull
  hs_fpull hs_crc_if hs_upd_h hh_upd_s hh_set_nx hh_crc_if hh_set_mode hh_nbuf hh_cbuf hh_xbuf hs_zstr
  andb_false_l : hsh.

Lemma hs_needbits_f k n m h : needbits_f k n (set_m_h m h) = set_m_h (needbits_f k n m) h.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [reflexivity|]. autorewrite with hsh.
  destruct (_ <? _); [|reflexivity]. destruct (_ =? 0); [reflexivity|]. rewrite IHk; reflexivity.
Qed.

Lemma hs_needbits n m h : needbits n (set_m_h m h) = set_m_h (needbits n m) h.
Proof. apply hs_needbits_f. Qed.

Lemma hs_lookup1_f k fx dx t nb m h : lookup1_f k fx dx t nb (set_m_h m h) =
  let '(e, m', b) := lookup1_f k fx dx t nb m in (e, set_m_h m' h, b).
Proof.
  revert m; induction k; intros m; cbn [lookup1_f]; autorewrite with hsh; [reflexivity|].
  destruct (_ <=? _); [reflexivity|]. destruct (_ =? 0); [reflexivity|]. rewrite IHk; reflexivity.
Qed.

Lemma hs_lookup1 fx dx t nb m h : lookup1 fx dx t nb (set_m_h m h) =
  let '(e, m', b) := lookup1 fx dx t nb m in (e, set_m_h m' h, b).
Proof. apply hs_lookup1_f. Qed.

Lemma hs_lookup2_f k fx dx t last m h : lookup2_f k fx dx t last (set_m_h m h) =
  let '(e, m', b) := lookup2_f k fx dx t last m in (e, set_m_h m' h, b).
Proof.
  revert m; induction k; intros m; cbn [lookup2_f]; autorewrite with hsh; [reflexivity|].
  destruct (_ <=? _); [reflexivity|]. destruct (_ =? 0); [reflexivity|]. rewrite IHk; reflexivity.
Qed.

Lemma hs_lookup2 fx dx t last m h : lookup2 fx dx t last (set_m_h m h) =
  let '(e, m', b) := lookup2 fx dx t last m in (e, set_m_h m' h, b).
Proof. apply hs_lookup2_f. Qed.

Lemma hs_fwalk_f fx dx k il t here m h : fwalk_f fx dx k il t here (set_m_h m h) =
  let '(e, m') := fwalk_f fx dx k il t here m in (e, set_m_h m' h).
Proof.
  revert here m; induction k; intros here m; cbn [fwalk_f]; autorewrite with hsh; [reflexivity|].
  destruct (il (e_op here)); [rewrite IHk|]; reflexivity.
Qed.

Hint Rewrite hs_needbits hs_lookup1 hs_lookup2 hs_fwalk_f : hsh.

(* ---------------------------------------------------------------------------------------------- *)
(* The machine state facts used to show that the outcome keeps hind                                *)

Lemma hb_needbits_f k n m : m_s (needbits_f k n m) = m_s m.
Proof.
  revert m; induction k; intros m; cbn [needbits_f]; [reflexivity|].
  destruct (_ <? _); [|reflexivity]. destruct (_ =? 0); [reflexivity|]. rewrite IHk; reflexivity.
Qed.
Lemma hb_needbits n m : m_s (needbits n m) = m_s m.
Proof. apply hb_needbits_f. Qed.
Lemma hb_crc_hd m d : i_head (m_s (crc_if m d)) = i_head (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma hb_crc_md m d : i_mode (m_s (crc_if m d)) = i_mode (m_s m).
Proof. unfold crc_if; destruct (_ && _); reflexivity. Qed.
Lemma hb_lens_fill_hd k len s : i_head (lens_fill k len s) = i_head s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [|rewrite IHk]; reflexivity. Qed.
Lemma hb_lens_fill_md k len s : i_mode (lens_fill k len s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lens_fill]; [|rewrite IHk]; reflexivity. Qed.
Lemma hb_lenlens_zero_hd k s : i_head (lenlens_zero k s) = i_head s.
Proof. revert s; induction k; intros s; cbn [lenlens_zero]; [|destruct (_ <? 19); [rewrite IHk|]]; reflexivity. Qed.
Lemma hb_lenlens_zero_md k s : i_mode (lenlens_zero k s) = i_mode s.
Proof. revert s; induction k; intros s; cbn [lenlens_zero]; [|destruct (_ <? 19); [rewrite IHk|]]; reflexivity. Qed.
Lemma hb_updatewindow_hd s d : i_head (updatewindow s d) = i_head s.
Proof. unfold updatewindow; cbv zeta; destruct (i_wsize s =? 0), (_ <=? _); try destruct (negb _); reflexivity. Qed.
Lemma hb_updatewindow_md s d : i_mode (updatewindow s d) = i_mode s.
Proof. unfold updatewindow; cbv zeta; destruct (i_wsize s =? 0), (_ <=? _); try destruct (negb _); reflexivity. Qed.

Lemma hb_lookup1_f k fx dx t nb m e m' b : lookup1_f k fx dx t nb m = (e, m', b) -> m_s m' = m_s m.
Proof.
  revert m; induction k; intros m E; cbn [lookup1_f] in E; [inversion E; reflexivity|].
  destruct (_ <=? _); [inversion E; reflexivity|].
  destruct (m_have m =? 0); [inversion E; reflexivity|]. apply IHk in E; rewrite E; reflexivity.
Qed.
Lemma hb_lookup1 fx dx t nb m e m' b : lookup1 fx dx t nb m = (e, m', b) -> m_s m' = m_s m.
Proof. apply hb_lookup1_f. Qed.
Lemma hb_lookup2_f k fx dx t last m e m' b : lookup2_f k fx dx t last m = (e, m', b) -> m_s m' = m_s m.
Proof.
  revert m; induction k; intros m E; cbn [lookup2_f] in E; [inversion E; reflexivity|].
  destruct (_ <=? _); [inversion E; reflexivity|].
  destruct (m_have m =? 0); [inversion E; reflexivity|]. apply IHk in E; rewrite E; reflexivity.
Qed.
Lemma hb_lookup2 fx dx t last m e m' b : lookup2 fx dx t last m = (e, m', b) -> m_s m' = m_s m.
Proof. apply hb_lookup2_f. Qed.
Lemma hb_fwalk_f fx dx k il t here m e m' : fwalk_f fx dx k il t here m = (e, m') -> m_s m' = m_s m.
Proof.
  revert here m; induction k; intros here m E; cbn [fwalk_f] in E; [inversion E; reflexivity|].
  destruct (il (e_op here)); [apply IHk in E; rewrite E|inversion E]; reflexivity.
Qed.

Hint Rewrite hb_needbits hb_crc_hd hb_crc_md hb_lens_fill_hd hb_lens_fill_md hb_lenlens_zero_hd hb_lenlens_zero_md
  hb_updatewindow_hd hb_updatewindow_md : hsb.

(* ---------------------------------------------------------------------------------------------- *)
(* The tactics                                                                                    *)

(* the named machines back *)
Ltac hs_subst := repeat match goal with
  | E: ?y = _ |- _ => is_var y; subst y
  | E: _ = ?y |- _ => is_var y; subst y
  end.

Ltac hs_cbn := cbn -[needbits needbits_f crc_if lookup1_f lookup1 lookup2_f lookup2 lens_fill lenlens_zero
                     lenlens_loop codelens_iter codelens_loop zstr_f zstr_nw call_table copy_bytes
                     fwalk_f fast_iter fast_loop fast hdr_mode updatewindow].

Ltac hs_facts :=
  repeat match goal with
  | E: lookup1 _ _ _ _ _ = (_, _, _) |- _ => apply hb_lookup1 in E
  | E: lookup2 _ _ _ _ _ = (_, _, _) |- _ => apply hb_lookup2 in E
  | E: fwalk_f _ _ _ _ _ _ _ = (_, _) |- _ => apply hb_fwalk_f in E
  end.

Ltac hs_srw := repeat match goal with E: m_s ?v = _ |- context [m_s ?v] => is_var v; rewrite E end.

(* the equations of the destructed tuples built by an if *)
Ltac hs_inj :=
  repeat match goal with
  | E: (if ?c then _ else _) = (_, _) |- _ => destruct c
  | E: (let _ := _ in _) = (_, _) |- _ => cbv zeta in E
  | E: (_, _) = (_, _) |- _ => injection E; clear E; intros
  end.

(* the mode facts of the helpers with loops (extended below) *)
Ltac hs_mfacts := fail.

(* close a side goal on the machine state: i_head false or a non-header mode *)
Ltac hs_ifs := repeat match goal with |- context [if ?c then _ else _] => let Ei := fresh "Ei" in destruct c eqn:Ei end.
Ltac hs_bclose := try unfold qm; hs_inj; hs_subst; hs_facts; unfold m_mode;
  repeat progress (hs_cbn; autorewrite with hsb; hs_srw; hs_ifs);
  first [assumption | reflexivity | discriminate | congruence | hs_mfacts].

(* the tests on i_head false (header cases with no header attached) *)
Ltac hs_kill :=
  match goal with |- context [i_head (m_s ?X)] =>
    let H := fresh in assert (H: i_head (m_s X) = false) by hs_bclose; rewrite H; clear H
  end.

(* unfold f without zeta (unfold would duplicate the lets) *)
Tactic Notation "hs_unf" constr(f) := cbv delta [f]; cbv beta.

(* ---------------------------------------------------------------------------------------------- *)
(* The commutation as a relation between the two runs, proved by the structure of the terms        *)

(* the transports of a value of the run on m to the run on set_m_h m h *)
Definition mh (h: hstate) (m: mst) : mst := set_m_h m h.
Definition oh (h: hstate) (o: iout) : iout := out_hk o h.
Definition ch (h: hstate) (o: clout) : clout :=
  match o with CLnext m => CLnext (mh h m) | CLleave m => CLleave (mh h m) | CLbad m => CLbad (mh h m) end.
Definition pr {A B} (ta: A -> A) (tb: B -> B) (x: A * B) : A * B := (ta (fst x), tb (snd x)).
Definition idt {A} (x: A) : A := x.


Lemma hr_crc_if m d h : crc_if (mh h m) d = mh h (crc_if m d).
Proof. apply hs_crc_if. Qed.

Lemma hr_if {A B} (W: B -> A) (c: bool) a1 a2 b1 b2 :
  (c = true -> a1 = W a2) -> (c = false -> b1 = W b2) -> (if c then a1 else b1) = W (if c then a2 else b2).
Proof. destruct c; auto. Qed.
Lemma hr_ifq {A B} (W: B -> A) (Q: B -> Prop) (c: bool) a1 a2 b1 b2 :
  (c = true -> a1 = W a2 /\ Q a2) -> (c = false -> b1 = W b2 /\ Q b2) ->
  (if c then a1 else b1) = W (if c then a2 else b2) /\ Q (if c then a2 else b2).
Proof. destruct c; auto. Qed.
Lemma hr_let {A B} h (W: B -> A) v1 v2 (b1: mst -> A) (b2: mst -> B) :
  v1 = mh h v2 -> (forall y, y = v2 -> b1 (mh h y) = W (b2 y)) -> (let x := v1 in b1 x) = W (let x := v2 in b2 x).
Proof. intros -> H. apply H. reflexivity. Qed.
Lemma hr_letq {A B} h (W: B -> A) (Q: B -> Prop) v1 v2 (b1: mst -> A) (b2: mst -> B) :
  v1 = mh h v2 -> (forall y, y = v2 -> b1 (mh h y) = W (b2 y) /\ Q (b2 y)) ->
  (let x := v1 in b1 x) = W (let x := v2 in b2 x) /\ Q (let x := v2 in b2 x).
Proof. intros -> H. apply H. reflexivity. Qed.
Lemma hr_ibrk h a1 a2 : a1 = mh h a2 -> IBrk a1 = oh h (IBrk a2).
Proof. intros ->; reflexivity. Qed.
Lemma hr_iret h r a1 a2 : a1 = mh h a2 -> IRet r a1 = oh h (IRet r a2).
Proof. intros ->; reflexivity. Qed.
Lemma hr_clnext h a1 a2 : a1 = mh h a2 -> CLnext a1 = ch h (CLnext a2).
Proof. intros ->; reflexivity. Qed.
Lemma hr_clleave h a1 a2 : a1 = mh h a2 -> CLleave a1 = ch h (CLleave a2).
Proof. intros ->; reflexivity. Qed.
Lemma hr_clbad h a1 a2 : a1 = mh h a2 -> CLbad a1 = ch h (CLbad a2).
Proof. intros ->; reflexivity. Qed.
Lemma hr_pair {A B} (ta: A -> A) (tb: B -> B) a1 a2 b1 b2 : a1 = ta a2 -> b1 = tb b2 -> (a1, b1) = pr ta tb (a2, b2).
Proof. intros -> ->; reflexivity. Qed.
Lemma hr_pr_pair {A B} (ta: A -> A) (tb: B -> B) a b : pr ta tb (a, b) = (ta a, tb b).
Proof. reflexivity. Qed.
Lemma hr_ch_next h m : ch h (CLnext m) = CLnext (mh h m). Proof. reflexivity. Qed.
Lemma hr_ch_leave h m : ch h (CLleave m) = CLleave (mh h m). Proof. reflexivity. Qed.
Lemma hr_ch_bad h m : ch h (CLbad m) = CLbad (mh h m). Proof. reflexivity. Qed.

Ltac hs_tr T h :=
  lazymatch T with
  | mst => constr:(mh h)
  | iout => constr:(oh h)
  | clout => constr:(ch h)
  | prod ?A ?B => let ta := hs_tr A h in let tb := hs_tr B h in
                  lazymatch ta with
                  | @idt _ => lazymatch tb with @idt _ => constr:(@idt (A * B)) | _ => constr:(@pr A B ta tb) end
                  | _ => constr:(@pr A B ta tb)
                  end
  | _ => constr:(@idt T)
  end.

(* the calls of the helpers and cases (extended below as their lemmas are proved) *)
Ltac hs_app := fail.
Ltac hs_cases := fail.

(* a call of a case (or of a loop) whose lemma gives the relation and the predicate *)
(* conversion, after the CRC updates are moved out of the header model *)
Ltac hs_reflx := first [reflexivity | progress (rewrite ?hr_crc_if); reflexivity].

(* the argument of the call as mh h of the other one, by an equation: with a change of the whole goal the
   kernel may unfold the body of the case *)
Ltac hs_marg h a1 a2 :=
  let t := constr:(mh h a2) in
  tryif constr_eq a1 t then idtac else
  (let H := fresh "Ha" in assert (H: a1 = t) by hs_reflx; rewrite H; clear H).

Ltac hs_qcall h :=
  lazymatch goal with |- ?f ?a1 = ?W (?f ?a2) /\ ?Q _ =>
    hs_marg h a1 a2;
    first [ hs_cases | match goal with HG: forall (_ : mst) (_ : hstate), _ -> f _ = _ /\ _ |- _ => apply HG end ];
    try (unfold qm; first [reflexivity | hs_bclose])
  end.

(* the case a case falls through into, hidden behind a variable with its lemma (so that the kernel does not
   unfold it) *)
Tactic Notation "hs_hide" constr(c) constr(L) :=
  let HG := fresh "HG" in let G := fresh "G" in
  pose proof L as HG; revert HG; generalize c; intros G HG.


(* a leaf of the relation: constructors, calls, conversion *)
Ltac hs_leaf h :=
  first
  [ discriminate
  | lazymatch goal with |- upd_h _ _ = _ =>
      unfold upd_h, mh, upd_s; cbn [m_h set_m_h set_m_s]; rewrite ?hh_nbuf, ?hh_cbuf, ?hh_xbuf; reflexivity end
  | lazymatch goal with
    | |- IBrk _ = oh _ (IBrk _) => refine (hr_ibrk _ _ _ _)
    | |- IRet _ _ = oh _ (IRet _ _) => refine (hr_iret _ _ _ _ _)
    | |- CLnext _ = ch _ (CLnext _) => refine (hr_clnext _ _ _ _)
    | |- CLleave _ = ch _ (CLleave _) => refine (hr_clleave _ _ _ _)
    | |- CLbad _ = ch _ (CLbad _) => refine (hr_clbad _ _ _ _)
    | |- (_, _) = pr _ _ (_, _) => refine (hr_pair _ _ _ _ _ _ _ _)
    end
  | lazymatch goal with |- ?f ?a1 = ?W (?g ?a2) => change (g (mh h a2) = W (g a2)); hs_app end
  | lazymatch goal with |- crc_if _ ?d1 = ?W (crc_if ?a2 ?d2) =>
      change (crc_if (mh h a2) d2 = W (crc_if a2 d2)); apply hr_crc_if end
  | hs_reflx ].

Ltac hs_qleaf :=
  cbv beta iota delta [qmd qhd qm qsnd qcl clm fst snd];
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  hs_bclose.

(* replace X1 by the convertible X2 *)
Ltac hs_conv X1 X2 := change X1 with X2.

Ltac hs_tdest X2 :=
  let E := fresh "E" in destruct X2 eqn:E;
  rewrite ?hr_pr_pair, ?hr_ch_next, ?hr_ch_leave, ?hr_ch_bad; cbv beta iota; cbn beta iota delta [negb andb orb].

Ltac hs_tuple h X1 X2 :=
  lazymatch X2 with
  | match ?Y2 with _ => _ end => lazymatch X1 with match ?Y1 with _ => _ end => hs_tuple h Y1 Y2 end
  | _ =>
    let T := type of X2 in let tr := hs_tr T h in
    lazymatch tr with
    | @idt _ => hs_conv X1 X2; hs_tdest X2
    | _ =>
      let t := constr:(tr X2) in
      tryif constr_eq X1 t then hs_tdest X2 else
      (let HX := fresh "HX" in assert (HX: X1 = t); [ | rewrite HX; clear HX; hs_tdest X2 ])
    end
  end.

Ltac hs_step h :=
  match goal with
  | |- (let x := ?v1 in @?b1 x) = ?W (let y := ?v2 in @?b2 y) /\ ?Q _ =>
      lazymatch type of v2 with
      | mst => refine (hr_letq h W Q v1 v2 b1 b2 _ _);
               [ | let y := fresh "y" in let Ey := fresh "Ey" in intros y Ey; cbv beta ]
      | _ => change (b1 v1 = W (b2 v2) /\ Q (b2 v2)); cbv beta
      end
  | |- (let x := ?v1 in @?b1 x) = ?W (let y := ?v2 in @?b2 y) =>
      lazymatch type of v2 with
      | mst => refine (hr_let h W v1 v2 b1 b2 _ _);
               [ | let y := fresh "y" in let Ey := fresh "Ey" in intros y Ey; cbv beta ]
      | _ => change (b1 v1 = W (b2 v2)); cbv beta
      end
  | |- (if _ then _ else _) = ?W (if ?c then _ else _) /\ ?Q _ =>
      lazymatch type of c with bool => idtac end;
      refine (hr_ifq W Q c _ _ _ _ _ _); let Hc := fresh "Hc" in intro Hc
  | |- (if _ then _ else _) = ?W (if ?c then _ else _) =>
      lazymatch type of c with bool => idtac end;
      refine (hr_if W c _ _ _ _ _ _); let Hc := fresh "Hc" in intro Hc
  | |- (match ?X1 with _ => _ end) = _ (match ?X2 with _ => _ end) /\ _ => hs_tuple h X1 X2
  | |- (match ?X1 with _ => _ end) = _ (match ?X2 with _ => _ end) => hs_tuple h X1 X2
  | |- _ = _ /\ _ => first [hs_qcall h | split; [hs_leaf h | hs_qleaf]]
  | |- _ = _ => hs_leaf h
  end.

(* the relation of the two runs, step by step; pre rewrites the goal first (the i_head tests of the header cases) *)
Ltac hs_rel h pre := repeat (try (progress pre); hs_step h).

Lemma hr_needbits n m h : needbits n (mh h m) = mh h (needbits n m).
Proof. apply hs_needbits. Qed.
Lemma hr_lookup1 fx dx t nb m h : lookup1 fx dx t nb (mh h m) = pr (pr idt (mh h)) idt (lookup1 fx dx t nb m).
Proof. unfold mh; rewrite hs_lookup1. destruct (lookup1 fx dx t nb m) as [[? ?] ?]; reflexivity. Qed.
Lemma hr_lookup2 fx dx t last m h : lookup2 fx dx t last (mh h m) = pr (pr idt (mh h)) idt (lookup2 fx dx t last m).
Proof. unfold mh; rewrite hs_lookup2. destruct (lookup2 fx dx t last m) as [[? ?] ?]; reflexivity. Qed.
Lemma hr_fwalk fx dx k il t here m h : fwalk_f fx dx k il t here (mh h m) = pr idt (mh h) (fwalk_f fx dx k il t here m).
Proof. unfold mh; rewrite hs_fwalk_f. destruct (fwalk_f fx dx k il t here m); reflexivity. Qed.

Ltac hs_app ::= first [apply hr_needbits | apply hr_lookup1 | apply hr_lookup2 | apply hr_fwalk].

(* inflate_fast *)
Lemma hq_fast_iter fx dx m h : qm m ->
  fast_iter fx dx (mh h m) = pr idt (mh h) (fast_iter fx dx m) /\ qsnd (fast_iter fx dx m).
Proof. intros Hm; unfold qm in Hm. hs_unf fast_iter. hs_rel h idtac. Qed.

Lemma hr_fast_iter fx dx m h : fast_iter fx dx (mh h m) = pr idt (mh h) (fast_iter fx dx m).
Proof. hs_unf fast_iter. hs_rel h idtac. Qed.

Lemma hm_fast_iter fx dx m g m' : fast_iter fx dx m = (g, m') -> qm m -> qm m'.
Proof. intros E Hm. destruct (hq_fast_iter fx dx m (m_h m) Hm) as [_ H]. rewrite E in H. exact H. Qed.

Ltac hs_app ::= first [apply hr_needbits | apply hr_lookup1 | apply hr_lookup2 | apply hr_fwalk | apply hr_fast_iter
                      | match goal with IH: forall _ : mst, _ = _ |- _ => apply IH end].
Ltac hs_mfacts ::=
  match goal with E: fast_iter _ _ _ = (_, _) |- _ => eapply (hm_fast_iter _ _ _ _ _ E); hs_bclose end.
Ltac hs_cases ::= match goal with IH: forall _ : mst, _ -> _ = _ /\ _ |- _ => apply IH end.

Lemma hq_fast_loop fx dx k m h : qm m ->
  fast_loop fx dx k (mh h m) = mh h (fast_loop fx dx k m) /\ qm (fast_loop fx dx k m).
Proof.
  revert m; induction k; intros m Hm; cbn [fast_loop]; [split; [reflexivity | exact Hm]|].
  unfold qm in Hm. hs_rel h idtac.
Qed.

Lemma hr_fast_loop fx dx k m h : fast_loop fx dx k (mh h m) = mh h (fast_loop fx dx k m).
Proof. revert m; induction k; intros m; cbn [fast_loop]; [reflexivity|]. hs_rel h idtac. Qed.

Lemma hm_fast_loop fx dx k m : qm m -> qm (fast_loop fx dx k m).
Proof. intros H. exact (proj2 (hq_fast_loop fx dx k m (m_h m) H)). Qed.

Ltac hs_app ::= first [apply hr_needbits | apply hr_lookup1 | apply hr_lookup2 | apply hr_fwalk | apply hr_fast_iter
                      | apply hr_fast_loop
                      | match goal with IH: forall _ : mst, _ = _ |- _ => apply IH end].
Ltac hs_mfacts ::= first
  [ match goal with E: fast_iter _ _ _ = (_, _) |- _ => eapply (hm_fast_iter _ _ _ _ _ E); hs_bclose end
  | apply hm_fast_loop; hs_bclose ].

Lemma hq_fast fx dx m h : qm m -> fast fx dx (mh h m) = mh h (fast fx dx m) /\ qm (fast fx dx m).
Proof. intros Hm; unfold qm in Hm. hs_unf fast. hs_rel h idtac. Qed.
Lemma hr_fast fx dx m h : fast fx dx (mh h m) = mh h (fast fx dx m).
Proof. hs_unf fast. hs_rel h idtac. Qed.
Lemma hm_fast fx dx m : qm m -> qm (fast fx dx m).
Proof. intros H. exact (proj2 (hq_fast fx dx m (m_h m) H)). Qed.

(* the loops of LENLENS and CODELENS *)
Lemma hr_lenlens k m h : lenlens_loop k (mh h m) = mh h (lenlens_loop k m).
Proof. revert m; induction k; intros m; cbv delta [lenlens_loop] beta iota; fold lenlens_loop; [reflexivity|]. hs_rel h idtac. Qed.
Lemma hq_lenlens k m h : qm m -> lenlens_loop k (mh h m) = mh h (lenlens_loop k m) /\ qm (lenlens_loop k m).
Proof.
  revert m; induction k; intros m Hm; cbv delta [lenlens_loop] beta iota; fold lenlens_loop; [split; [reflexivity | exact Hm]|].
  unfold qm in Hm. hs_rel h idtac.
Qed.
Lemma hm_lenlens k m : qm m -> qm (lenlens_loop k m).
Proof. intros H. exact (proj2 (hq_lenlens k m (m_h m) H)). Qed.

Ltac hs_app ::= first [apply hr_needbits | apply hr_lookup1 | apply hr_lookup2 | apply hr_fwalk | apply hr_fast_iter
                      | apply hr_fast_loop | apply hr_fast | apply hr_lenlens
                      | match goal with IH: forall _ : mst, _ = _ |- _ => apply IH end].

Lemma hr_cl_iter fx dx m h : codelens_iter fx dx (mh h m) = ch h (codelens_iter fx dx m).
Proof. hs_unf codelens_iter. hs_rel h idtac. Qed.
Lemma hq_cl_iter fx dx m h : qm m ->
  codelens_iter fx dx (mh h m) = ch h (codelens_iter fx dx m) /\ qcl (codelens_iter fx dx m).
Proof. intros Hm; unfold qm in Hm. hs_unf codelens_iter. hs_rel h idtac. Qed.
Lemma hm_cl_iter fx dx X o m' : codelens_iter fx dx X = o -> clm o = m' -> qm X -> qm m'.
Proof. intros E C H. destruct (hq_cl_iter fx dx X (m_h X) H) as [_ Q]. rewrite E in Q. rewrite <- C. exact Q. Qed.

Ltac hs_app ::= first [apply hr_needbits | apply hr_lookup1 | apply hr_lookup2 | apply hr_fwalk | apply hr_fast_iter
                      | apply hr_fast_loop | apply hr_fast | apply hr_lenlens | apply hr_cl_iter
                      | match goal with IH: forall _ : mst, _ = _ |- _ => apply IH end].
Ltac hs_mfacts ::= first
  [ match goal with E: fast_iter _ _ _ = (_, _) |- _ => eapply (hm_fast_iter _ _ _ _ _ E); hs_bclose end
  | apply hm_fast_loop; hs_bclose
  | apply hm_fast; hs_bclose
  | apply hm_lenlens; hs_bclose
  | match goal with E: codelens_iter _ _ _ = _ |- _ => eapply (hm_cl_iter _ _ _ _ _ E); [reflexivity | hs_bclose] end ].

Lemma hr_cl_loop fx dx k m h : codelens_loop fx dx k (mh h m) = ch h (codelens_loop fx dx k m).
Proof. revert m; induction k; intros m; cbn [codelens_loop]; [reflexivity|]. hs_rel h idtac. Qed.
Lemma hq_cl_loop fx dx k m h : qm m ->
  codelens_loop fx dx k (mh h m) = ch h (codelens_loop fx dx k m) /\ qcl (codelens_loop fx dx k m).
Proof.
  revert m; induction k; intros m Hm; cbn [codelens_loop]; [split; [reflexivity | exact Hm]|].
  unfold qm in Hm. hs_rel h idtac.
Qed.
Lemma hm_cl_loop fx dx k X o m' : codelens_loop fx dx k X = o -> clm o = m' -> qm X -> qm m'.
Proof. intros E C H. destruct (hq_cl_loop fx dx k X (m_h X) H) as [_ Q]. rewrite E in Q. rewrite <- C. exact Q. Qed.

Ltac hs_mfacts ::= first
  [ match goal with E: fast_iter _ _ _ = (_, _) |- _ => eapply (hm_fast_iter _ _ _ _ _ E); hs_bclose end
  | apply hm_fast_loop; hs_bclose
  | apply hm_fast; hs_bclose
  | apply hm_lenlens; hs_bclose
  | match goal with E: codelens_iter _ _ _ = _ |- _ => eapply (hm_cl_iter _ _ _ _ _ E); [reflexivity | hs_bclose] end
  | match goal with E: codelens_loop _ _ _ _ = _ |- _ => eapply (hm_cl_loop _ _ _ _ _ _ E); [reflexivity | hs_bclose] end ].
Ltac hs_app ::=
  lazymatch goal with
  | |- needbits _ _ = _ => apply hr_needbits
  | |- lookup1 _ _ _ _ _ = _ => apply hr_lookup1
  | |- lookup2 _ _ _ _ _ = _ => apply hr_lookup2
  | |- fwalk_f _ _ _ _ _ _ _ = _ => apply hr_fwalk
  | |- fast_iter _ _ _ = _ => apply hr_fast_iter
  | |- fast_loop _ _ _ _ = _ => apply hr_fast_loop
  | |- fast _ _ _ = _ => apply hr_fast
  | |- lenlens_loop _ _ = _ => apply hr_lenlens
  | |- codelens_iter _ _ _ = _ => apply hr_cl_iter
  | |- codelens_loop _ _ _ _ = _ => apply hr_cl_loop
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The cases after the header: the relation, and the outcome is in a non-header mode               *)

Lemma hc_DONE m h : qm m -> c_DONE (mh h m) = oh h (c_DONE m) /\ qmd (c_DONE m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_DONE. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  end.
Lemma hc_BAD m h : qm m -> c_BAD (mh h m) = oh h (c_BAD m) /\ qmd (c_BAD m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_BAD. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  end.
Lemma hc_LENGTH m h : qm m -> c_LENGTH (mh h m) = oh h (c_LENGTH m) /\ qmd (c_LENGTH m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LENGTH. hs_hide c_DONE hc_DONE. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  end.
Lemma hc_CHECK m h : qm m -> c_CHECK (mh h m) = oh h (c_CHECK m) /\ qmd (c_CHECK m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_CHECK. hs_hide c_LENGTH hc_LENGTH. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  end.
Lemma hc_LIT m h : qm m -> c_LIT (mh h m) = oh h (c_LIT m) /\ qmd (c_LIT m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LIT. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  end.
Lemma hc_MATCH m h : qm m -> c_MATCH (mh h m) = oh h (c_MATCH m) /\ qmd (c_MATCH m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_MATCH. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  end.
Lemma hc_DISTEXT m h : qm m -> c_DISTEXT (mh h m) = oh h (c_DISTEXT m) /\ qmd (c_DISTEXT m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_DISTEXT. hs_hide c_MATCH hc_MATCH. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  end.
Lemma hc_DIST fx dx m h : qm m -> c_DIST fx dx (mh h m) = oh h (c_DIST fx dx m) /\ qmd (c_DIST fx dx m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_DIST. hs_hide c_DISTEXT hc_DISTEXT. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  end.
Lemma hc_LENEXT fx dx m h : qm m -> c_LENEXT fx dx (mh h m) = oh h (c_LENEXT fx dx m) /\ qmd (c_LENEXT fx dx m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LENEXT. hs_hide (c_DIST fx dx) (hc_DIST fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  end.
Lemma hc_LEN fx dx m h : qm m -> c_LEN fx dx (fast fx dx) (mh h m) = oh h (c_LEN fx dx (fast fx dx) m) /\ qmd (c_LEN fx dx (fast fx dx) m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LEN. hs_hide (c_LENEXT fx dx) (hc_LENEXT fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  end.
Lemma hc_LEN_ fx dx m h : qm m -> c_LEN_ fx dx (fast fx dx) (mh h m) = oh h (c_LEN_ fx dx (fast fx dx) m) /\ qmd (c_LEN_ fx dx (fast fx dx) m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LEN_. hs_hide (c_LEN fx dx (fast fx dx)) (hc_LEN fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  end.
Lemma hc_CODELENS fl fx dx m h : qm m -> c_CODELENS fl fx dx (fast fx dx) (mh h m) = oh h (c_CODELENS fl fx dx (fast fx dx) m) /\ qmd (c_CODELENS fl fx dx (fast fx dx) m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_CODELENS. hs_hide (c_LEN_ fx dx (fast fx dx)) (hc_LEN_ fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  end.
Lemma hc_LENLENS fl fx dx m h : qm m -> c_LENLENS fl fx dx (fast fx dx) (mh h m) = oh h (c_LENLENS fl fx dx (fast fx dx) m) /\ qmd (c_LENLENS fl fx dx (fast fx dx) m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_LENLENS. hs_hide (c_CODELENS fl fx dx (fast fx dx)) (hc_CODELENS fl fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  end.
Lemma hc_TABLE fl fx dx m h : qm m -> c_TABLE fl fx dx (fast fx dx) (mh h m) = oh h (c_TABLE fl fx dx (fast fx dx) m) /\ qmd (c_TABLE fl fx dx (fast fx dx) m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_TABLE. hs_hide (c_LENLENS fl fx dx (fast fx dx)) (hc_LENLENS fl fx dx). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  end.
Lemma hc_COPY m h : qm m -> c_COPY (mh h m) = oh h (c_COPY m) /\ qmd (c_COPY m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_COPY. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  end.
Lemma hc_COPY_ m h : qm m -> c_COPY_ (mh h m) = oh h (c_COPY_ m) /\ qmd (c_COPY_ m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_COPY_. hs_hide c_COPY hc_COPY. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  end.
Lemma hc_STORED fl m h : qm m -> c_STORED fl (mh h m) = oh h (c_STORED fl m) /\ qmd (c_STORED fl m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_STORED. hs_hide c_COPY_ hc_COPY_. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  end.
Lemma hc_TYPEDO fl m h : qm m -> c_TYPEDO fl (mh h m) = oh h (c_TYPEDO fl m) /\ qmd (c_TYPEDO fl m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_TYPEDO. hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  end.
Lemma hc_TYPE fl m h : qm m -> c_TYPE fl (mh h m) = oh h (c_TYPE fl m) /\ qmd (c_TYPE fl m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_TYPE. hs_hide (c_TYPEDO fl) (hc_TYPEDO fl). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  end.
Lemma hc_DICT fl m h : qm m -> c_DICT fl (mh h m) = oh h (c_DICT fl m) /\ qmd (c_DICT fl m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_DICT. hs_hide (c_TYPE fl) (hc_TYPE fl). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  end.
Lemma hc_DICTID fl m h : qm m -> c_DICTID fl (mh h m) = oh h (c_DICTID fl m) /\ qmd (c_DICTID fl m).
Proof. intros Hm; unfold qm in Hm. hs_unf c_DICTID. hs_hide (c_DICT fl) (hc_DICT fl). hs_rel h idtac. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The header cases with no header attached: the relation, and i_head stays false                  *)

Ltac hs_hpre := first [hs_kill | progress (rewrite ?andb_false_l) | progress (repeat rewrite hs_zstr)].

Lemma hd_HCRC m h : i_head (m_s m) = false -> c_HCRC (mh h m) = oh h (c_HCRC m) /\ qhd (c_HCRC m).
Proof. intros Hh. hs_unf c_HCRC. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  end.
Lemma hd_COMMENT2 m h : i_head (m_s m) = false -> c_COMMENT2 (mh h m) = oh h (c_COMMENT2 m) /\ qhd (c_COMMENT2 m).
Proof. intros Hh. hs_unf c_COMMENT2. hs_hide c_HCRC hd_HCRC. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  end.
Lemma hd_NAME2 m h : i_head (m_s m) = false -> c_NAME2 (mh h m) = oh h (c_NAME2 m) /\ qhd (c_NAME2 m).
Proof. intros Hh. hs_unf c_NAME2. hs_hide c_COMMENT2 hd_COMMENT2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  end.
Lemma hd_EXTRA2 m h : i_head (m_s m) = false -> c_EXTRA2 (mh h m) = oh h (c_EXTRA2 m) /\ qhd (c_EXTRA2 m).
Proof. intros Hh. hs_unf c_EXTRA2. hs_hide c_NAME2 hd_NAME2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  end.
Lemma hd_EXLEN2 m h : i_head (m_s m) = false -> c_EXLEN2 (mh h m) = oh h (c_EXLEN2 m) /\ qhd (c_EXLEN2 m).
Proof. intros Hh. hs_unf c_EXLEN2. hs_hide c_EXTRA2 hd_EXTRA2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  | |- c_EXLEN2 _ = _ /\ _ => apply hd_EXLEN2
  end.
Lemma hd_OS2 m h : i_head (m_s m) = false -> c_OS2 (mh h m) = oh h (c_OS2 m) /\ qhd (c_OS2 m).
Proof. intros Hh. hs_unf c_OS2. hs_hide c_EXLEN2 hd_EXLEN2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  | |- c_EXLEN2 _ = _ /\ _ => apply hd_EXLEN2
  | |- c_OS2 _ = _ /\ _ => apply hd_OS2
  end.
Lemma hd_TIME2 m h : i_head (m_s m) = false -> c_TIME2 (mh h m) = oh h (c_TIME2 m) /\ qhd (c_TIME2 m).
Proof. intros Hh. hs_unf c_TIME2. hs_hide c_OS2 hd_OS2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  | |- c_EXLEN2 _ = _ /\ _ => apply hd_EXLEN2
  | |- c_OS2 _ = _ /\ _ => apply hd_OS2
  | |- c_TIME2 _ = _ /\ _ => apply hd_TIME2
  end.
Lemma hd_FLAGS2 m h : i_head (m_s m) = false -> c_FLAGS2 (mh h m) = oh h (c_FLAGS2 m) /\ qhd (c_FLAGS2 m).
Proof. intros Hh. hs_unf c_FLAGS2. hs_hide c_TIME2 hd_TIME2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  | |- c_EXLEN2 _ = _ /\ _ => apply hd_EXLEN2
  | |- c_OS2 _ = _ /\ _ => apply hd_OS2
  | |- c_TIME2 _ = _ /\ _ => apply hd_TIME2
  | |- c_FLAGS2 _ = _ /\ _ => apply hd_FLAGS2
  end.
Lemma hd_HEAD2 m h : i_head (m_s m) = false -> c_HEAD2 (mh h m) = oh h (c_HEAD2 m) /\ qhd (c_HEAD2 m).
Proof. intros Hh. hs_unf c_HEAD2. hs_rel h hs_hpre. Qed.
Ltac hs_cases ::=
  lazymatch goal with
  | |- c_DONE _ = _ /\ _ => apply hc_DONE
  | |- c_BAD _ = _ /\ _ => apply hc_BAD
  | |- c_LENGTH _ = _ /\ _ => apply hc_LENGTH
  | |- c_CHECK _ = _ /\ _ => apply hc_CHECK
  | |- c_LIT _ = _ /\ _ => apply hc_LIT
  | |- c_MATCH _ = _ /\ _ => apply hc_MATCH
  | |- c_DISTEXT _ = _ /\ _ => apply hc_DISTEXT
  | |- c_DIST _ _ _ = _ /\ _ => apply hc_DIST
  | |- c_LENEXT _ _ _ = _ /\ _ => apply hc_LENEXT
  | |- c_LEN _ _ _ _ = _ /\ _ => apply hc_LEN
  | |- c_LEN_ _ _ _ _ = _ /\ _ => apply hc_LEN_
  | |- c_CODELENS _ _ _ _ _ = _ /\ _ => apply hc_CODELENS
  | |- c_LENLENS _ _ _ _ _ = _ /\ _ => apply hc_LENLENS
  | |- c_TABLE _ _ _ _ _ = _ /\ _ => apply hc_TABLE
  | |- c_COPY _ = _ /\ _ => apply hc_COPY
  | |- c_COPY_ _ = _ /\ _ => apply hc_COPY_
  | |- c_STORED _ _ = _ /\ _ => apply hc_STORED
  | |- c_TYPEDO _ _ = _ /\ _ => apply hc_TYPEDO
  | |- c_TYPE _ _ = _ /\ _ => apply hc_TYPE
  | |- c_DICT _ _ = _ /\ _ => apply hc_DICT
  | |- c_DICTID _ _ = _ /\ _ => apply hc_DICTID
  | |- c_HCRC _ = _ /\ _ => apply hd_HCRC
  | |- c_COMMENT2 _ = _ /\ _ => apply hd_COMMENT2
  | |- c_NAME2 _ = _ /\ _ => apply hd_NAME2
  | |- c_EXTRA2 _ = _ /\ _ => apply hd_EXTRA2
  | |- c_EXLEN2 _ = _ /\ _ => apply hd_EXLEN2
  | |- c_OS2 _ = _ /\ _ => apply hd_OS2
  | |- c_TIME2 _ = _ /\ _ => apply hd_TIME2
  | |- c_FLAGS2 _ = _ /\ _ => apply hd_FLAGS2
  | |- c_HEAD2 _ = _ /\ _ => apply hd_HEAD2
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* The exit inf_leave                                                                             *)

Definition rh (h: hstate) (res: result) : result := Res (r_ret res) (mh h (r_m res)) (r_dtype res).

Lemma hr_leave_fin fl m h : leave_fin fl (mh h m) = rh h (leave_fin fl m).
Proof. hs_unf leave_fin. hs_rel h idtac. Qed.

(* the exit keeps i_head and the mode *)
Lemma hb_leave_fin fl m :
  i_head (m_s (r_m (leave_fin fl m))) = i_head (m_s m) /\ i_mode (m_s (r_m (leave_fin fl m))) = i_mode (m_s m).
Proof.
  unfold leave_fin. cbv zeta.
  destruct (leave_ok fl m); cbv beta iota;
  repeat match goal with |- context [if ?c then _ else _] => destruct c end;
  split; first [reflexivity | etransitivity; [apply hb_updatewindow_hd | reflexivity]
                            | etransitivity; [apply hb_updatewindow_md | reflexivity]].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One pass, the loop, the exit, the run                                                          *)

(* RTH8W.hind: no header attached, or a mode after the header *)
Definition hk (m: mst) : Prop := i_head (m_s m) = false \/ hdr_mode (m_mode m) = false.
Definition qk (o: iout) : Prop := match o with IBrk m | IRet _ m => hk m end.

Lemma qmd_qk o : qmd o -> qk o.
Proof. destruct o; cbn; intros H; right; exact H. Qed.
Lemma qhd_qk o : qhd o -> qk o.
Proof. destruct o; cbn; intros H; left; exact H. Qed.

Lemma hs_eta m : set_m_h m (m_h m) = m.
Proof. destruct m; reflexivity. Qed.

Ltac hs_hdr_case m h Hi E L :=
  let A := fresh "A" in let B := fresh "B" in
  assert (Hh: i_head (m_s m) = false)
    by (destruct Hi as [Hi'|Hi']; [exact Hi' | rewrite E in Hi'; vm_compute in Hi'; discriminate]);
  destruct (L m h Hh) as [A B]; split; [exact A | apply qhd_qk; exact B].
Ltac hs_nh_case m h E L :=
  let A := fresh "A" in let B := fresh "B" in
  assert (Hq: qm m) by (unfold qm; rewrite E; reflexivity);
  destruct (L m h Hq) as [A B]; split; [exact A | apply qmd_qk; exact B].

Lemma hs_step_sim fl fx dx m h : hk m ->
  stepf2 fl fx dx (mh h m) = oh h (stepf2 fl fx dx m) /\ qk (stepf2 fl fx dx m).
Proof.
  intros Hi. unfold stepf2, step2. change (m_mode (mh h m)) with (m_mode m).
  repeat match goal with |- context [if m_mode m =? ?X then _ else _] =>
    let E := fresh "E" in destruct (m_mode m =? X) eqn:E;
    [ apply Z.eqb_eq in E;
      lazymatch goal with
      | |- c_HEAD2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_HEAD2
      | |- c_FLAGS2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_FLAGS2
      | |- c_TIME2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_TIME2
      | |- c_OS2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_OS2
      | |- c_EXLEN2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_EXLEN2
      | |- c_EXTRA2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_EXTRA2
      | |- c_NAME2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_NAME2
      | |- c_COMMENT2 _ = _ /\ _ => hs_hdr_case m h Hi E hd_COMMENT2
      | |- c_HCRC _ = _ /\ _ => hs_hdr_case m h Hi E hd_HCRC
      | |- c_DICTID _ _ = _ /\ _ => hs_nh_case m h E (hc_DICTID fl)
      | |- c_DICT _ _ = _ /\ _ => hs_nh_case m h E (hc_DICT fl)
      | |- c_TYPE _ _ = _ /\ _ => hs_nh_case m h E (hc_TYPE fl)
      | |- c_TYPEDO _ _ = _ /\ _ => hs_nh_case m h E (hc_TYPEDO fl)
      | |- c_STORED _ _ = _ /\ _ => hs_nh_case m h E (hc_STORED fl)
      | |- c_COPY_ _ = _ /\ _ => hs_nh_case m h E hc_COPY_
      | |- c_COPY _ = _ /\ _ => hs_nh_case m h E hc_COPY
      | |- c_TABLE _ _ _ _ _ = _ /\ _ => hs_nh_case m h E (hc_TABLE fl fx dx)
      | |- c_LENLENS _ _ _ _ _ = _ /\ _ => hs_nh_case m h E (hc_LENLENS fl fx dx)
      | |- c_CODELENS _ _ _ _ _ = _ /\ _ => hs_nh_case m h E (hc_CODELENS fl fx dx)
      | |- c_LEN_ _ _ _ _ = _ /\ _ => hs_nh_case m h E (hc_LEN_ fx dx)
      | |- c_LEN _ _ _ _ = _ /\ _ => hs_nh_case m h E (hc_LEN fx dx)
      | |- c_LENEXT _ _ _ = _ /\ _ => hs_nh_case m h E (hc_LENEXT fx dx)
      | |- c_DIST _ _ _ = _ /\ _ => hs_nh_case m h E (hc_DIST fx dx)
      | |- c_DISTEXT _ = _ /\ _ => hs_nh_case m h E hc_DISTEXT
      | |- c_MATCH _ = _ /\ _ => hs_nh_case m h E hc_MATCH
      | |- c_LIT _ = _ /\ _ => hs_nh_case m h E hc_LIT
      | |- c_CHECK _ = _ /\ _ => hs_nh_case m h E hc_CHECK
      | |- c_LENGTH _ = _ /\ _ => hs_nh_case m h E hc_LENGTH
      | |- c_DONE _ = _ /\ _ => hs_nh_case m h E hc_DONE
      | |- c_BAD _ = _ /\ _ => hs_nh_case m h E hc_BAD
      | |- IRet _ _ = _ /\ _ => split; [reflexivity | exact Hi]
      end
    | ] end.
  split; [reflexivity | exact Hi].
Qed.

(* one pass: the statement of RTH8W.sim_stmt (1) *)
Lemma hs_step fl fx dx m h : hk m ->
  match stepf2 fl fx dx m with
  | IBrk m1 => stepf2 fl fx dx (set_m_h m h) = IBrk (set_m_h m1 h) /\ m_h m1 = m_h m /\ hk m1
  | IRet r m1 => stepf2 fl fx dx (set_m_h m h) = IRet r (set_m_h m1 h) /\ m_h m1 = m_h m /\ hk m1
  end.
Proof.
  intros Hi.
  destruct (hs_step_sim fl fx dx m h Hi) as [A B].
  destruct (hs_step_sim fl fx dx m (m_h m) Hi) as [A' _].
  change (mh (m_h m) m) with (set_m_h m (m_h m)) in A'. rewrite hs_eta in A'.
  change (mh h m) with (set_m_h m h) in A.
  destruct (stepf2 fl fx dx m) as [m1|r m1]; cbn in A, A', B;
    (split; [exact A | split; [|exact B]]);
    injection A'; intros E; rewrite E; reflexivity.
Qed.

Lemma hs_loop fl fx dx m h o : hk m -> loop2 fl fx dx m o ->
  loop2 fl fx dx (set_m_h m h) (out_hk o h) /\
  match o with IBrk m1 => m_h m1 = m_h m /\ hk m1 | IRet _ m1 => m_h m1 = m_h m /\ hk m1 end.
Proof.
  intros Hi L; revert Hi; induction L as [m r m' S|m m' S Lv|m m' o S Lv L IH]; intros Hi.
  - pose proof (hs_step fl fx dx m h Hi) as P. rewrite S in P. destruct P as [A B].
    split; [apply loop2_ret; exact A | exact B].
  - pose proof (hs_step fl fx dx m h Hi) as P. rewrite S in P. destruct P as [A B].
    split; [eapply loop2_leave; [exact A | exact Lv] | exact B].
  - pose proof (hs_step fl fx dx m h Hi) as P. rewrite S in P. destruct P as [A [B C]].
    destruct (IH C) as [L' R].
    split; [eapply loop2_next; [exact A | exact Lv | exact L'] |].
    destruct o as [m1|r m1]; destruct R as [R1 R2]; (split; [congruence | exact R2]).
Qed.

Lemma hs_leave fl m h res : hk m -> inf_leave fl m res ->
  inf_leave fl (set_m_h m h) (rh h res) /\ m_h (r_m res) = m_h m /\ hk (r_m res).
Proof.
  intros Hi L. destruct L as [U W|].
  - split; [|split; [reflexivity | right; reflexivity]].
    change (rh h (Res Z_MEM_ERROR (set_mode (restore m) MEM) None))
      with (Res Z_MEM_ERROR (set_mode (restore (set_m_h m h)) MEM) None).
    apply il_mem; [exact U | exact W].
  - split; [|split].
    + change (set_m_h m h) with (mh h m). rewrite <- hr_leave_fin. apply il_ok.
    + pose proof (hr_leave_fin fl m (m_h m)) as E.
      change (mh (m_h m) m) with (set_m_h m (m_h m)) in E. rewrite hs_eta in E.
      rewrite E. reflexivity.
    + destruct (hb_leave_fin fl m) as [E1 E2].
      destruct Hi as [Hi|Hi]; [left; rewrite E1; exact Hi | right; unfold m_mode in *; rewrite E2; exact Hi].
Qed.

Lemma hs_run fl fx dx m h res : hk m -> run2 fl fx dx m res ->
  run2 fl fx dx (set_m_h m h) (rh h res) /\ m_h (r_m res) = m_h m.
Proof.
  intros Hi [o [L R]].
  destruct (hs_loop fl fx dx m h o Hi L) as [L' P].
  destruct o as [m1|r m1].
  - destruct P as [P1 P2]. destruct (hs_leave fl m1 h res P2 R) as [A [B _]].
    split; [exists (IBrk (set_m_h m1 h)); split; [exact L' | exact A] | congruence].
  - destruct P as [P1 P2]. subst res.
    split; [exists (IRet r (set_m_h m1 h)); split; [exact L' | reflexivity] | exact P1].
Qed.
