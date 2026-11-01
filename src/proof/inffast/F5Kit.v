(* The kit of the proof of inflate_fast's body (BodyF5.v): the sub-statements of the Clight body, the
   context, the decomposition of the model's pass (fast_iter) along the C code, the assertions of the
   loop (fs_state: the temps of the loop and the memory split in five items), and the statements of the
   pieces (the *_stmt definitions: each is proved in its own file, BodyF5.v assembles them).

   Memory during the loop: mem_rep F m = tab_mem (the decoding tables: state->codes, lenfix, distfix) *
   win_rep (the window) * in_rep * out_rep (m_ow) * rest_mem (everything else).  The machine m of the
   loop is the model's: nx/hold/bits/ow change, the state (m_s m) does not (except mode on a break);
   state->hold/bits and strm->next_in/... are written back only by the epilogue (the model's restore). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inffast.code.
Require Export Zlib.proof.inflate.Callees3.
Require Export Zlib.proof.inffast.Body.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* ---------------------------------------------------------------------------------------------- *)
(* sub-statements of the body, by their path (0 = first / then part, 1 = second / else part)       *)

Definition child (i: nat) (s: statement) : statement :=
  match s, i with
  | Ssequence a _, O => a | Ssequence _ b, S O => b
  | Sloop a _, O => a | Sloop _ b, S O => b
  | Sifthenelse _ a _, O => a | Sifthenelse _ _ b, S O => b
  | _, _ => Sskip
  end.
Fixpoint at_path (p: list nat) (s: statement) : statement :=
  match p with nil => s | i :: p' => at_path p' (child i s) end.

Definition p_loop : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]%nat.
Definition p_iter : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0]%nat.
Definition p_incr : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;1]%nat.
Definition p_epi : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat.
Definition p_lhere : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;0]%nat.
Definition p_lloop : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;0]%nat.
Definition p_lenbr : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0]%nat.
Definition p_dhere : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;0]%nat.
Definition p_dloop : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;0]%nat.
Definition p_copy : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1]%nat.
Definition p_window : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0]%nat.
Definition p_direct : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1]%nat.
Definition p_tail : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;1]%nat.
Definition p_wloop1 : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;0;0;1;0;1;0]%nat.
Definition p_wloop2 : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;0;1;0;1;1;0;1;0]%nat.
Definition p_wloop3 : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;0;1;0;1;1;0;1;1;1;0;1;1;0]%nat.
Definition p_wloop4 : list nat := [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0;0;1;1;1;1;0;1;1;1;1;1;1;0;1;1;1;1;1;1;1;0;1;1;1;0;1;1;1;0;1;0]%nat.

Definition fbody : statement := fn_body f_inflate_fast.
(* the do-while: Sloop s_iter s_incr *)
Definition s_loop := at_path p_loop fbody.
(* the loop body (from `if (bits < 15)` to the end of the if-else chain) *)
Definition s_iter := at_path p_iter fbody.
(* `in < last && out < end` (the do-while test) *)
Definition s_incr := at_path p_incr fbody.
(* after the loop: `len = bits >> 3; ... return;` *)
Definition s_epi := at_path p_epi fbody.
(* here = lcode + (hold & lmask);  for (;;) { ... } *)
Definition s_lhere := at_path p_lhere fbody.
Definition s_lloop := at_path p_lloop fbody.
(* the length branch: the then part of `else if (op & 16)` *)
Definition s_lenbr := at_path p_lenbr fbody.
(* here = dcode + (hold & dmask);  for (;;) { ... } *)
Definition s_dhere := at_path p_dhere fbody.
Definition s_dloop := at_path p_dloop fbody.
(* op = (unsigned)(out - beg);  if (dist > op) { window } else { direct } *)
Definition s_copy := at_path p_copy fbody.
Definition s_window := at_path p_window fbody.
Definition s_direct := at_path p_direct fbody.
(* while (len > 2) { 3 bytes } if (len) { ... } (from `from`, window or output) *)
Definition s_tail := at_path p_tail fbody.
(* the four `do { *out++ = *from++; } while (--op);` copies from the window *)
Definition s_wloop1 := at_path p_wloop1 fbody.
Definition s_wloop2 := at_path p_wloop2 fbody.
Definition s_wloop3 := at_path p_wloop3 fbody.
Definition s_wloop4 := at_path p_wloop4 fbody.

(* turn the s_X of the goal's statement into its Clight term *)
Ltac stmt_simpl :=
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [
      s_loop s_iter s_incr s_epi s_lhere s_lloop s_lenbr s_dhere s_dloop s_copy s_window s_direct s_tail
      s_wloop1 s_wloop2 s_wloop3 s_wloop4
      p_loop p_iter p_incr p_epi p_lhere p_lloop p_lenbr p_dhere p_dloop p_copy p_window p_direct p_tail
      p_wloop1 p_wloop2 p_wloop3 p_wloop4 at_path child fbody f_inflate_fast fn_body] in c in
    change c with c'
  end.

(* the context of inflate_fast's body *)
Definition Delta_fast : tycontext := func_tycontext f_inflate_fast Vprog_fast Gprog_fast nil.

(* ---------------------------------------------------------------------------------------------- *)
(* the model's pass, along the C code (fast_iter_eq)                                              *)

(* if (bits < 15) { two bytes } *)
Definition refill2 (m: mst) : mst := if m_bits m <? 15 then fpull (fpull m) else m.

(* here = lcode + (hold & lmask); for (;;) { ... } *)
Definition lwalk (s: istate) (m: mst) : entry * mst :=
  fwalk_f lenfix_list distfix_list 2 len_link (i_lencode s)
    (tab_entry lenfix_list distfix_list s (i_lencode s) (m_hold m mod 2 ^ i_lenbits s)) m.
Definition dwalk (s: istate) (m: mst) : entry * mst :=
  fwalk_f lenfix_list distfix_list 2 dist_link (i_distcode s)
    (tab_entry lenfix_list distfix_list s (i_distcode s) (m_hold m mod 2 ^ i_distbits s)) m.

(* len = here->val; op &= 15; if (op) { ... } *)
Definition lenx (here: entry) (m: mst) : Z * mst :=
  let len := e_val here in
  let opx := Z.land (e_op here) 15 in
  if negb (opx =? 0) then
    let m := if m_bits m <? opx then fpull m else m in
    (u32 (len + m_hold m mod 2 ^ opx), set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)))
  else (len, m).

(* dist = here->val; op &= 15; pulls; dist += ...; hold >>= op; bits -= op; *)
Definition distx (here: entry) (m: mst) : Z * mst :=
  let dist := e_val here in
  let opx := Z.land (e_op here) 15 in
  let m := if m_bits m <? opx then (let m := fpull m in if m_bits m <? opx then fpull m else m) else m in
  let dist := u32 (dist + m_hold m mod 2 ^ opx) in
  let m := set_m_bits (set_m_hold m (Z.shiftr (m_hold m) opx)) (u32 (m_bits m - opx)) in
  (dist, m).

(* op = out - beg; the window or the direct copy (s_copy) *)
Definition fcopy (s: istate) (len dist: Z) (m: mst) : bool * mst :=
  let op := Zlength (m_ow m) in
  if op <? dist then
    let op := dist - op in
    if andb (i_whave s <? op) (negb (i_sane s =? 0)) then (false, set_bad m F_far) else
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

(* the length branch (s_lenbr) *)
Definition flen (s: istate) (here: entry) (m: mst) : bool * mst :=
  let '(len, m) := lenx here m in
  let m := refill2 m in
  let '(here, m) := dwalk s m in
  if negb (Z.land (e_op here) 16 =? 0) then
    let '(dist, m) := distx here m in fcopy s len dist m
  else (false, set_bad m F_d_code).

(* the if-else chain after the length/literal walk *)
Definition fdisp (s: istate) (here: entry) (m: mst) : bool * mst :=
  let op := e_op here in
  if op =? 0 then (true, set_m_ow m (m_ow m ++ (e_val here mod 256)%Z :: nil))
  else if negb (Z.land op 16 =? 0) then flen s here m
  else if negb (Z.land op 32 =? 0) then (false, set_mode m Zlib.proof.inflate.Model.TYPE)
  else (false, set_bad m F_ll_code).

Lemma fast_iter_eq: forall m,
  fast_iter lenfix_list distfix_list m =
  (let '(here, m1) := lwalk (m_s m) (refill2 m) in fdisp (m_s m) here m1).
Proof. intros m. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the memory of the loop                                                                         *)

(* &tab[j] *)
Definition entry_ptr (F: frame) (t: tref) (j: Z) : val := offset_val (4 * j) (tref_val (f_gv F) (f_sp F) t).
(* the share of a table's entries *)
Definition tab_sh (F: frame) (t: tref) : share := match t with TCodes _ => Ews | _ => f_gsh F end.

(* the decoding tables: state->codes, lenfix, distfix *)
Definition tab_mem (F: frame) (s: istate) : mpred :=
  field_at Ews t_state (DOT _codes) (map ent (i_codes s)) (f_sp F) *
  data_at (f_gsh F) (tarray t_code 512) (map ent lenfix_list) (f_gv F g_lenfix) *
  data_at (f_gsh F) (tarray t_code 32) (map ent distfix_list) (f_gv F g_distfix).

(* state_rep without the codes field *)
Definition state_rep_nc (gv: globals) (sp strmp headp winp: val) (s: istate) : mpred :=
  field_at Ews t_state (DOT _strm) strmp sp *
  field_at Ews t_state (DOT _mode) (zv (i_mode s)) sp *
  field_at Ews t_state (DOT _last) (zv (i_last s)) sp *
  field_at Ews t_state (DOT _wrap) (zv (i_wrap s)) sp *
  field_at Ews t_state (DOT _havedict) (zv (i_havedict s)) sp *
  field_at Ews t_state (DOT _flags) (zv (i_flags s)) sp *
  field_at Ews t_state (DOT _dmax) (zv (i_dmax s)) sp *
  field_at Ews t_state (DOT _check) (lv (i_check s)) sp *
  field_at Ews t_state (DOT _total) (lv (i_total s)) sp *
  field_at Ews t_state (DOT _head) (if i_head s then headp else nullval) sp *
  field_at Ews t_state (DOT _wbits) (zv (i_wbits s)) sp *
  field_at Ews t_state (DOT _wsize) (zv (i_wsize s)) sp *
  field_at Ews t_state (DOT _whave) (zv (i_whave s)) sp *
  field_at Ews t_state (DOT _wnext) (zv (i_wnext s)) sp *
  field_at Ews t_state (DOT _window) (if i_win s then winp else nullval) sp *
  field_at Ews t_state (DOT _hold) (lv (i_hold s)) sp *
  field_at Ews t_state (DOT _bits) (zv (i_bits s)) sp *
  field_at Ews t_state (DOT _length) (zv (i_length s)) sp *
  field_at Ews t_state (DOT _offset) (zv (i_offset s)) sp *
  field_at Ews t_state (DOT _extra) (zv (i_extra s)) sp *
  field_at Ews t_state (DOT _lencode) (tref_val gv sp (i_lencode s)) sp *
  field_at Ews t_state (DOT _distcode) (tref_val gv sp (i_distcode s)) sp *
  field_at Ews t_state (DOT _lenbits) (zv (i_lenbits s)) sp *
  field_at Ews t_state (DOT _distbits) (zv (i_distbits s)) sp *
  field_at Ews t_state (DOT _ncode) (zv (i_ncode s)) sp *
  field_at Ews t_state (DOT _nlen) (zv (i_nlen s)) sp *
  field_at Ews t_state (DOT _ndist) (zv (i_ndist s)) sp *
  field_at Ews t_state (DOT _have) (zv (i_have s)) sp *
  field_at Ews t_state (DOT _next) (codes_at sp (i_next s)) sp *
  field_at Ews t_state (DOT _lens) (map (fun z => Vint (Int.repr z)) (i_lens s)) sp *
  field_at_ Ews t_state (DOT _work) sp *
  field_at Ews t_state (DOT _sane) (zv (i_sane s)) sp *
  field_at Ews t_state (DOT _back) (zv (i_back s)) sp *
  field_at Ews t_state (DOT _was) (zv (i_was s)) sp.

(* everything but the tables, the window, the input and the output *)
Definition rest_mem (F: frame) (m: mst) : mpred :=
  state_rep_nc (f_gv F) (f_sp F) (f_strmp F) (f_headp F) (f_winp F) (m_s m) *
  head_part F m *
  strm_rep (f_gv F) (f_shs F) (f_strmp F)
    (in_ptr (f_ib F) (m_snx m)) (zv (Zlength (m_inp m) - m_snx m)) (m_tin m)
    (out_ptr (f_ob F) (m_sow m)) (zv (m_aout m - m_sow m)) (m_tout m)
    (msg_val (f_gv F) (m_msg m)) (f_sp F) (f_dt F) (m_adler m) (f_vres F) *
  data_at (f_gsh F) (tarray tushort 19) (map (fun z => Vint (Int.repr z)) order)
    (f_gv F Zlib.inflate.code._order) *
  Zlib.proof.inftrees.spec.itables (f_gsh F) (f_gv F) *
  crc_table_at (f_tsh F) (f_gv F).

Definition fs_sep (F: frame) (m: mst) : list mpred :=
  [tab_mem F (m_s m); win_rep (f_winp F) (m_s m); in_rep (f_ib F); out_rep (f_ob F) (m_ow m); rest_mem F m].

(* state->window *)
Definition win_val (F: frame) (s: istate) : val := if i_win s then f_winp F else nullval.

(* the temps of the loop (the machine's nx, ow, hold, bits; the state's window and tables) *)
Definition fs_locals (F: frame) (m: mst) : list localdef :=
  [temp _strm (f_strmp F); temp _state (f_sp F);
   temp _in (in_ptr (f_ib F) (m_nx m)); temp _last (in_ptr (f_ib F) (Zlength (m_inp m) - 5));
   temp _out (out_ptr (f_ob F) (Zlength (m_ow m))); temp _beg (out_ptr (f_ob F) 0);
   temp _end (out_ptr (f_ob F) (m_aout m - 257));
   temp _wsize (zv (i_wsize (m_s m))); temp _whave (zv (i_whave (m_s m)));
   temp _wnext (zv (i_wnext (m_s m))); temp _window (win_val F (m_s m));
   temp _hold (lv (m_hold m)); temp _bits (zv (m_bits m));
   temp _lcode (tref_val (f_gv F) (f_sp F) (i_lencode (m_s m)));
   temp _dcode (tref_val (f_gv F) (f_sp F) (i_distcode (m_s m)));
   temp _lmask (zv (2 ^ i_lenbits (m_s m) - 1)); temp _dmask (zv (2 ^ i_distbits (m_s m) - 1));
   gvars (f_gv F)].

(* a point of the loop: the machine m, pure facts P, the temps `extra` besides the loop's *)
Definition fs_state (F: frame) (m: mst) (P: list Prop) (extra: list localdef) : environ -> mpred :=
  PROPx P (LOCALx (extra ++ fs_locals F m) (SEPx (fs_sep F m))).

(* the end of a piece of the loop body whose model result is r: go on (normal) or break *)
Definition fpost (F: frame) (r: bool * mst) : ret_assert :=
  {| RA_normal := EX m': mst, fs_state F m' [r = (true, m')] [];
     RA_break := EX m': mst, fs_state F m' [r = (false, m')] [];
     RA_continue := FF;
     RA_return := fun _ => FF |}.

(* where a copy reads from *)
Definition src_ptr (F: frame) (sr: src) : val :=
  match sr with SWin i => offset_val i (f_winp F) | SOut i => out_ptr (f_ob F) i end.
(* a copy of L bytes from sr is within what is there *)
Definition src_ok (m: mst) (sr: src) (L: Z) : Prop :=
  match sr with
  | SWin i => i_win (m_s m) = true /\ 0 <= i /\ i + L <= i_whave (m_s m)
  | SOut i => 0 <= i < Zlength (m_ow m)
  end.

(* ---------------------------------------------------------------------------------------------- *)
(* the statements of the pieces                                                                   *)

(* the tables: entry j of table t apart *)
Definition tab_focus_stmt : Prop := forall (F: frame) (s: istate) (t: tref) (j: Z),
  tref_ok t -> Zlength (i_codes s) = ENOUGH_CODES -> 0 <= j < tab_size t ->
  tab_mem F s |--
    data_at (tab_sh F t) t_code (ent (tab_entry lenfix_list distfix_list s t j)) (entry_ptr F t j) *
    (data_at (tab_sh F t) t_code (ent (tab_entry lenfix_list distfix_list s t j)) (entry_ptr F t j) -*
     tab_mem F s).

(* the walks: what they find and what they consume *)
Definition lwalk_facts_stmt : Prop := forall m,
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m ->
  let '(e, m') := lwalk (m_s m) m in
  entry_ok e /\ final_ok LENS e /\ len_ok e /\ len_link (e_op e) = false /\
  m_bits m - 15 <= m_bits m' <= m_bits m /\
  m' = set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m - m_bits m'))) (m_bits m').
Definition dwalk_facts_stmt : Prop := forall m,
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m ->
  let '(e, m') := dwalk (m_s m) m in
  entry_ok e /\ final_ok DISTS e /\ dist_link (e_op e) = false /\
  m_bits m - 15 <= m_bits m' <= m_bits m /\
  m' = set_m_bits (set_m_hold m (Z.shiftr (m_hold m) (m_bits m - m_bits m'))) (m_bits m').

(* here = lcode + (hold & lmask); for (;;) { ... }: here = &lcode[j] with the entry the model finds *)
Definition walk_len_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst),
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m <= 30 -> readable_share (f_gsh F) ->
  semax Delta_fast (fs_state F m [] []) (Ssequence s_lhere s_lloop)
    (normal_ret_assert (EX j: Z,
       fs_state F (snd (lwalk (m_s m) m))
         [0 <= j < tab_size (i_lencode (m_s m));
          tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) j = fst (lwalk (m_s m) m)]
         [temp _here (entry_ptr F (i_lencode (m_s m)) j); temp _op (zv (e_op (fst (lwalk (m_s m) m))))])).

Definition walk_dist_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (L: Z),
  fast_ok m -> m_mode m = LEN -> 15 <= m_bits m <= 30 -> readable_share (f_gsh F) ->
  semax Delta_fast (fs_state F m [] [temp _len (zv L)]) (Ssequence s_dhere s_dloop)
    (normal_ret_assert (EX j: Z,
       fs_state F (snd (dwalk (m_s m) m))
         [0 <= j < tab_size (i_distcode (m_s m));
          tab_entry lenfix_list distfix_list (m_s m) (i_distcode (m_s m)) j = fst (dwalk (m_s m) m)]
         [temp _here (entry_ptr F (i_distcode (m_s m)) j); temp _op (zv (e_op (fst (dwalk (m_s m) m))));
          temp _len (zv L)])).

(* do { *out++ = *from++; } while (--op);  from the window, n >= 1 bytes from index i *)
Definition wloop_stmt (c: statement) : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (i n L D: Z),
  fast_ok m -> 1 <= n -> 0 <= i -> i + n <= i_whave (m_s m) -> Zlength (m_ow m) + n <= m_aout m ->
  out_ok (f_ob F) (m_aout m) ->
  semax Delta_fast
    (fs_state F m [] [temp _op (zv n); temp _from (offset_val i (f_winp F)); temp _len (zv L); temp _dist (zv D)])
    c
    (normal_ret_assert
      (fs_state F (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) (SWin i) n (m_ow m)))) []
         [temp _op (zv 0); temp _from (offset_val (i + n) (f_winp F)); temp _len (zv L); temp _dist (zv D)])).

(* while (len > 2) { 3 bytes; len -= 3; } if (len) { 1 or 2 bytes }: L bytes from sr *)
Definition tail_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (sr: src) (L D: Z),
  fast_ok m -> 0 <= L <= 258 -> src_ok m sr L -> Zlength (m_ow m) + L <= m_aout m -> out_ok (f_ob F) (m_aout m) ->
  semax Delta_fast (fs_state F m [] [temp _len (zv L); temp _from (src_ptr F sr); temp _dist (zv D)]) s_tail
    (normal_ret_assert (fs_state F (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) sr L (m_ow m)))) [] [])).

(* from = out - dist; do { 3 bytes; len -= 3; } while (len > 2); if (len) { ... } *)
Definition direct_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (L D: Z),
  fast_ok m -> 3 <= L <= 258 -> 1 <= D <= Zlength (m_ow m) -> Zlength (m_ow m) + L <= m_aout m ->
  out_ok (f_ob F) (m_aout m) ->
  semax Delta_fast (fs_state F m [] [temp _len (zv L); temp _dist (zv D)]) s_direct
    (normal_ret_assert
      (fs_state F (set_m_ow m (fst (copy_bytes (i_wdata (m_s m)) (SOut (Zlength (m_ow m) - D)) L (m_ow m)))) [] [])).

(* op = out - beg; if (dist > op) { the window } else { direct }: the model's fcopy *)
Definition copy_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (L D: Z),
  fast_ok m -> m_mode m = LEN -> 3 <= L <= 258 -> 1 <= D <= 65536 -> Zlength (m_ow m) + 258 <= m_aout m ->
  out_ok (f_ob F) (m_aout m) -> writable_share (f_shs F) ->
  semax Delta_fast (fs_state F m [] [temp _len (zv L); temp _dist (zv D)]) s_copy (fpost F (fcopy (m_s m) L D m)).

(* the length branch, entered with here = &lcode[j], a length entry *)
Definition lenbr_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst) (j: Z) (e: entry),
  fast_ok m -> m_mode m = LEN ->
  0 <= j < tab_size (i_lencode (m_s m)) -> tab_entry lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) j = e ->
  entry_ok e -> 16 <= e_op e <= 21 -> 3 <= e_val e <= 258 -> len_ok e ->
  33 <= 8 * m_have m + m_bits m -> m_bits m <= 30 -> 258 <= m_left m ->
  in_ok (f_ib F) (m_inp m) -> out_ok (f_ob F) (m_aout m) ->
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast
    (fs_state F m [] [temp _here (entry_ptr F (i_lencode (m_s m)) j); temp _op (zv (e_op e))])
    s_lenbr (fpost F (flen (m_s m) e m)).

(* one pass of the loop *)
Definition iter_stmt : Prop := forall {Espec: OracleKind} (F: frame) (m: mst),
  fast_ok m -> m_mode m = LEN -> 6 <= m_have m -> 258 <= m_left m -> m_bits m <= 30 ->
  in_ok (f_ib F) (m_inp m) -> out_ok (f_ob F) (m_aout m) ->
  writable_share (f_shs F) -> readable_share (f_gsh F) ->
  semax Delta_fast (fs_state F m [] []) s_iter (fpost F (fast_iter lenfix_list distfix_list m)).

(* what a pass does to the machine *)
Definition iter_facts_stmt : Prop := forall m go m',
  fast_ok m -> m_mode m = LEN -> 6 <= m_have m -> 258 <= m_left m -> m_bits m <= 30 ->
  fast_iter lenfix_list distfix_list m = (go, m') ->
  m_inp m' = m_inp m /\ m_aout m' = m_aout m /\ m_nx m <= m_nx m' <= Zlength (m_inp m) /\
  0 <= m_bits m' <= 30 /\ m_bits m' - 8 * m_nx m' <= m_bits m - 8 * m_nx m /\ lrange (m_hold m') /\
  Zlength (m_ow m) <= Zlength (m_ow m') <= m_aout m /\
  (go = true -> fast_ok m' /\ m_mode m' = LEN /\ Zlength (m_ow m) < Zlength (m_ow m')).

Lemma fast_ok_mwf: forall m, fast_ok m -> mwf m.
Proof. intros m [W _]. exact W. Qed.
