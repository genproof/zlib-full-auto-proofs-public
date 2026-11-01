(* RT-D part FLUSH: the interface of the parts of _tr_flush_block's proof (interface v2: RTDFlushDefs2.v).

   Every part is a Prop below, proved in its own file (RTDFlush<Part>.v) from the parts it needs
   (as hypotheses); RTDFlush2.v assembles them (flush_ok_bytes).  All parts but the assembly speak of the UNCHECKED trees model
   (src/proof/huffman/Model.v: send_bits, send_code, compress_sep, send_all_trees, build_tree, flush_prep). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.roundtrip.RTDBits.
Require Export Zlib.proof.huffman.Overlay.
Require Zlib.proof.huffman.Header.
Import ListNotations.
Local Open Scope Z_scope.

(** ** Codes *)

(* symbol c of a tree given by its Code / Len arrays implements Format's canonical code of the lengths fl:
   a proper code (length 1..15, value below 2^length) whose bits (as send_bits sends them, least significant
   first) are Format's (the canonical code, most significant first) *)
Definition cimpl (codes lens fl : list Z) (c : Z) : Prop :=
  Znth c lens = Znth c fl /\ 1 <= Znth c lens <= 15 /\ 0 <= Znth c codes < 2 ^ Znth c lens /\
  F.bits_le (Znth c codes) (Znth c lens) = F.send_sym fl c.

(* the codes a list of zlib symbols (dist, lc) uses *)
Definition syms_cimpl (lcodes llens dcodes dlens ll dl : list Z) (syms : list (Z * Z)) : Prop :=
  forall x, In x syms ->
    if fst x =? 0 then cimpl lcodes llens ll (snd x)
    else cimpl lcodes llens ll (257 + F.len_code (snd x + 3)) /\ cimpl dcodes dlens dl (F.dist_code (fst x)).

(* zlib symbols in range: a literal byte, or a match length - 3 in 0..255 at a distance 1..32768 *)
Definition zsyms_ok (syms : list (Z * Z)) : Prop :=
  forall x, In x syms -> if fst x =? 0 then 0 <= snd x < 256 else 0 <= snd x <= 255 /\ 1 <= fst x <= 32768.

(** ** Part W: the unchecked bit writer appends Format bits (from writer_fspec) *)
Definition wsend_stmt : Prop :=
  forall o v n,
    bits_ok o -> 1 <= n <= 16 -> 0 <= v < 2 ^ n -> 0 <= o_pending o -> o_pending o + 2 <= Zlength (o_buf o) ->
    bits_ok (send_bits o v n) /\ obits (send_bits o v n) = obits o ++ F.bits_le v n.
(** ** Part T: the static tables and the length / distance tables are Format's *)
Definition tabs_stmt : Prop :=
  (forall c, 0 <= c < 288 -> cimpl static_ltree_code static_ltree_len F.fixed_ll c) /\
  (forall d, 0 <= d < 30 -> cimpl static_dtree_code static_dtree_len F.fixed_dl d) /\
  (forall lc, 0 <= lc <= 255 ->
     let code := Znth lc length_code_tab in
     code = F.len_code (lc + 3) /\ 0 <= code < 29 /\
     Znth code extra_lbits = Znth code F.len_extra /\ Znth code base_length_tab = Znth code F.len_base - 3 /\
     0 <= Znth code F.len_extra <= 5 /\ 0 <= lc + 3 - Znth code F.len_base < 2 ^ Znth code F.len_extra) /\
  (forall dist, 1 <= dist <= 32768 ->
     let code := d_code (dist - 1) in
     code = F.dist_code dist /\ 0 <= code < 30 /\
     Znth code extra_dbits = Znth code F.dist_extra /\ Znth code base_dist_tab = Znth code F.dist_base - 1 /\
     0 <= Znth code F.dist_extra <= 13 /\ 0 <= dist - Znth code F.dist_base < 2 ^ Znth code F.dist_extra).

(** ** Part C: compress_sep then END_BLOCK sends Format's symbols; Format's syms_ok *)
Definition comp_stmt : Prop :=
  forall o lcodes llens dcodes dlens ll dl syms,
    bits_ok o -> zsyms_ok syms ->
    syms_cimpl lcodes llens dcodes dlens ll dl syms -> cimpl lcodes llens ll END_BLOCK ->
    0 <= o_pending o ->
    o_pending (compress_sep o lcodes llens dcodes dlens syms) + 2 <= Zlength (o_buf o) ->
    let o' := send_code (compress_sep o lcodes llens dcodes dlens syms) END_BLOCK lcodes llens in
    bits_ok o' /\ obits o' = obits o ++ F.send_syms ll dl (map fsym syms).

Definition symsok_stmt : Prop :=
  forall wmax out syms ll dl,
    syms_rok wmax out syms ->
    (forall x, In x syms ->
       if fst x =? 0 then Znth (snd x) ll <> 0
       else 257 + F.len_code (snd x + 3) < Zlength ll /\ Znth (257 + F.len_code (snd x + 3)) ll <> 0 /\
            F.dist_code (fst x) < Zlength dl /\ Znth (F.dist_code (fst x)) dl <> 0) ->
    F.syms_ok wmax ll dl out (map fsym syms).

(** ** Part D: the codes _tr_flush_block's build_tree calls give are the canonical codes of their lengths
    (the literal/length tree up to lmax, the distance tree up to dmax, the bit length tree on its 19 symbols) *)
Definition canon_stmt : Prop :=
  forall t syms sl s' olb slb mbi,
    flush_pre t syms -> 0 < tr_level t -> flush_prep t sl = (s', olb, slb, mbi) ->
    (forall x, 0 <= x <= tr_lmax s' -> Znth x (dl (tr_ltree s')) <> 0 ->
       F.bits_le (Znth x (fc (tr_ltree s'))) (Znth x (dl (tr_ltree s'))) =
       F.send_sym (sublist 0 (tr_lmax s' + 1) (dl (tr_ltree s'))) x) /\
    (forall x, 0 <= x <= tr_dmax s' -> Znth x (dl (tr_dtree s')) <> 0 ->
       F.bits_le (Znth x (fc (tr_dtree s'))) (Znth x (dl (tr_dtree s'))) =
       F.send_sym (sublist 0 (tr_dmax s' + 1) (dl (tr_dtree s'))) x) /\
    (forall x, 0 <= x < 19 -> Znth x (dl (tr_bltree s')) <> 0 ->
       F.bits_le (Znth x (fc (tr_bltree s'))) (Znth x (dl (tr_bltree s'))) =
       F.send_sym (sublist 0 19 (dl (tr_bltree s'))) x).

(** ** Part H: send_all_trees sends Format's dynamic header *)

(* the code length tokens send_tree emits (mirrors Header.syms_loop / Model.send_tree_loop) *)
Fixpoint tl_loop (fuel : nat) (lens : list Z) (max_code : Z)
    (n prevlen nextlen count max_count min_count : Z) : list F.cltok :=
  match fuel with
  | O => []
  | S f =>
    if n <=? max_code then
      let curlen := nextlen in
      let nextlen := Znth (n + 1) lens in
      let count := count + 1 in
      if (count <? max_count) && (curlen =? nextlen) then
        tl_loop f lens max_code (n + 1) prevlen nextlen count max_count min_count
      else
        let out :=
          if count <? min_count then repeat (F.CLen curlen) (Z.to_nat count)
          else if negb (curlen =? 0) then
            (if negb (curlen =? prevlen) then [F.CLen curlen; F.CRep (count - 1)] else [F.CRep count])
          else [F.CZeros count] in
        let '(max_count, min_count) :=
          if nextlen =? 0 then (138, 3)
          else if curlen =? nextlen then (6, 3)
          else (7, 4) in
        out ++ tl_loop f lens max_code (n + 1) curlen nextlen 0 max_count min_count
    else []
  end.

Definition tree_toks (lens : list Z) (max_code : Z) : list F.cltok :=
  let nextlen := Znth 0 lens in
  let '(max_count, min_count) := Header.init_counts nextlen in
  tl_loop (Z.to_nat (max_code + 1)) lens max_code 0 (-1) nextlen 0 max_count min_count.

(* the code length code lengths send_all_trees sends: bl lengths in bl_order, the first blcodes of them *)
Definition clsent_of (bl : tree) (blcodes : Z) : list Z :=
  map (fun i => Znth (Znth (Z.of_nat i) bl_order) (dl bl)) (seq 0 (Z.to_nat blcodes)).

(* the header bits of a dynamic block after its 3 block-type bits *)
Definition dyn_hdr_bits (nlen ndist : Z) (clsent : list Z) (toks : list F.cltok) : list bool :=
  F.bits_le (nlen - 257) 5 ++ F.bits_le (ndist - 1) 5 ++ F.bits_le (Zlength clsent - 4) 4 ++
  flat_map (fun c => F.bits_le c 3) clsent ++ flat_map (F.send_tok (F.cl_lens clsent)) toks.

Definition hdr_stmt : Prop :=
  forall o lt dt bl lcodes dcodes blcodes,
    bits_ok o -> 0 <= o_pending o ->
    257 <= lcodes <= 286 -> 1 <= dcodes <= 30 -> 4 <= blcodes <= 19 ->
    lcodes < Zlength (dl lt) -> dcodes < Zlength (dl dt) -> 19 <= Zlength (dl bl) -> 19 <= Zlength (fc bl) ->
    (forall i, 0 <= i < lcodes -> 0 <= Znth i (dl lt) <= 15) ->
    (forall i, 0 <= i < dcodes -> 0 <= Znth i (dl dt) <= 15) ->
    (forall i, 0 <= i < 19 -> 0 <= Znth i (dl bl) <= 7) ->
    (* the bit length codes not sent have length 0 *)
    (forall r, blcodes <= r < 19 -> Znth (Znth r bl_order) (dl bl) = 0) ->
    (* every symbol send_tree sends has a canonical code *)
    (forall q, In q (Header.tree_syms (dl lt) (lcodes - 1) ++ Header.tree_syms (dl dt) (dcodes - 1)) ->
       cimpl (fc bl) (dl bl) (sublist 0 19 (dl bl)) (fst q)) ->
    o_pending (send_all_trees o lt dt bl lcodes dcodes blcodes) + 2 <= Zlength (o_buf o) ->
    let o' := send_all_trees o lt dt bl lcodes dcodes blcodes in
    F.cl_lens (clsent_of bl blcodes) = sublist 0 19 (dl bl) /\
    bits_ok o' /\
    obits o' = obits o ++ dyn_hdr_bits lcodes dcodes (clsent_of bl blcodes)
                            (tree_toks (dl lt) (lcodes - 1) ++ tree_toks (dl dt) (dcodes - 1)).

(** ** Part K: the tokens expand to the lengths and are valid *)
Definition toks_stmt : Prop :=
  forall lens mc,
    0 <= mc -> mc + 1 < Zlength lens -> Znth (mc + 1) lens = 65535 ->
    (forall i, 0 <= i <= mc -> 0 <= Znth i lens <= 15) ->
    (forall prev, F.tok_expand prev (tree_toks lens mc) = prev ++ sublist 0 (mc + 1) lens) /\
    (forall cl prev, (forall q, In q (Header.tree_syms lens mc) -> Znth (fst q) cl <> 0) ->
       F.toks_ok cl prev (tree_toks lens mc)).

(** ** Part Y: the dynamic block of _tr_flush_block *)

(* the bits of a dynamic block after its 3 block-type bits (F.enc_block p fin (F.Dynamic ..) =
   fin :: [false; true] ++ dyn_body ..) *)
Definition dyn_body (nlen ndist : Z) (clsent : list Z) (toks : list F.cltok) (syms : list F.sym) : list bool :=
  dyn_hdr_bits nlen ndist clsent toks ++ F.send_syms (F.dyn_ll nlen toks) (F.dyn_dl nlen ndist toks) syms.

Definition dyn_stmt : Prop :=
  forall t syms sl s' olb slb mbi wmax out o1,
    flush_pre t syms -> 0 < tr_level t -> flush_prep t sl = (s', olb, slb, mbi) ->
    syms_rok wmax out syms -> bits_ok o1 -> 0 <= o_pending o1 -> Zlength (o_buf o1) = 4 * tr_lit_bufsize t ->
    overlay_ok (tr_lit_bufsize t) syms
      (send_all_trees o1 (tr_ltree s') (tr_dtree s') (tr_bltree s') (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1),
       fc (tr_ltree s'), dl (tr_ltree s'), fc (tr_dtree s'), dl (tr_dtree s')) ->
    exists nlen ndist clsent toks,
      F.block_ok wmax out (F.Dynamic nlen ndist clsent toks (map fsym syms)) /\
      let o2 := send_all_trees o1 (tr_ltree s') (tr_dtree s') (tr_bltree s')
                  (tr_lmax s' + 1) (tr_dmax s' + 1) (mbi + 1) in
      let o3 := send_code (compress_sep o2 (fc (tr_ltree s')) (dl (tr_ltree s')) (fc (tr_dtree s'))
                             (dl (tr_dtree s')) syms) END_BLOCK (fc (tr_ltree s')) (dl (tr_ltree s')) in
      bits_ok o3 /\ obits o3 = obits o1 ++ dyn_body nlen ndist clsent toks (map fsym syms).

Lemma enc_block_dyn : forall p fin nlen ndist clsent toks syms,
  F.enc_block p fin (F.Dynamic nlen ndist clsent toks syms) =
  fin :: [false; true] ++ dyn_body nlen ndist clsent toks syms.
Proof. intros. unfold F.enc_block, dyn_body, dyn_hdr_bits. rewrite !app_assoc. reflexivity. Qed.
