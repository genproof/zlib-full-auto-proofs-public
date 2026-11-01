(** * The checked model of deflate.c, part 5 (v6): which compression function is called, and deflateParams'
      function-pointer comparison

    Floyd cannot prove that the addresses [gv _deflate_stored], [gv _deflate_fast], [gv _deflate_slow] are
    pairwise distinct (the lemma is false for the sealed semax).  The C depends on them twice:
    - deflate() calls [deflate_stored] (level 0) or [configuration_table[level].func]: a function is called
      through its ADDRESS, and when two of these addresses are equal, any of the specifications at that
      address may be used.  [ef f] (for the function index [f] of configuration_table: 0 stored, 1 fast,
      2 slow) is the function whose specification the caller wants used for [f]: any [ef] with
      [cfg_func_ptr gv (ef f) = cfg_func_ptr gv f] (DSpec.ef_ok).  [ef = fun f => f] always qualifies and
      gives exactly DModel4's [c_deflate] ([c_deflate_g_id]).
    - deflateParams flushes when [configuration_table[s->level].func != configuration_table[level].func]:
      an address comparison.  [fe i j] is "the addresses of the functions [i] and [j] are equal"
      (DSpec.gv_feq gv); [fe = Z.eqb] (distinct addresses) gives DModel4's [c_deflateParams].
    Everything else is DModel4 verbatim. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.DModel4.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

(** The compression function of index [f] (0 deflate_stored, 1 deflate_fast, 2 deflate_slow). *)
Definition c_compressor (f : Z) (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * bstate) :=
  if f =? 0 then c_deflate_stored s z flush
  else if f =? 1 then c_deflate_fast s z flush
  else c_deflate_slow s z flush.

(** The dispatch, with the function [ef f] used for the function [f] of configuration_table. *)
Definition c_compress_func_g (ef : Z -> Z) (s : dstate) (z : strm) (flush : Z)
    : option (dstate * strm * bstate) :=
  if d_level s =? 0 then c_compressor (ef 0) s z flush
  else if d_strategy s =? Z_HUFFMAN_ONLY then c_deflate_huff s z flush
  else if d_strategy s =? Z_RLE then c_deflate_rle s z flush
  else
    let* f := cfg_func (d_level s) in
    c_compressor (ef f) s z flush.

Definition c_deflate_compress_g (ef : Z -> Z) (s : dstate) (z : strm) (flush : Z) : option dres :=
  if negb (z_avail_in z =? 0) || negb (d_lookahead s =? 0) ||
     (negb (flush =? Z_NO_FLUSH) && negb (d_status s =? FINISH_STATE)) then
    let* (s, z, bs) := c_compress_func_g ef s z flush in
    let s := match bs with finish_started | finish_done => set_d_status s FINISH_STATE | _ => s end in
    match bs with
    | need_more | finish_started =>
      Some (if z_avail_out z =? 0 then set_d_last_flush s (-1) else s, z, Some Z_OK)
    | block_done =>
      let* s :=
        (if flush =? Z_PARTIAL_FLUSH then
           let* om := c_tr_align (d_out s) in Some (set_d_out s om)
         else if negb (flush =? Z_BLOCK) then
           let* om := c_tr_stored_block (d_out s) [] 0 0 in
           let s := set_d_out s om in
           if flush =? Z_FULL_FLUSH then
             let* s := c_clear_hash s in
             if d_lookahead s =? 0 then
               Some (set_d_insert (set_d_block_start (set_d_strstart s 0) 0) 0)
             else Some s
           else Some s
         else Some s) in
      let* (s, z) := c_flush_pending s z in
      if z_avail_out z =? 0 then Some (set_d_last_flush s (-1), z, Some Z_OK) else Some (s, z, None)
    | finish_done => Some (s, z, None)
    end
  else Some (s, z, None).

(** deflate(strm, flush) with the functions [ef]. *)
Definition c_deflate_g (ef : Z -> Z) (s : dstate) (z : strm) (flush : Z) : option (dstate * strm * Z) :=
  if bad_state s || (flush >? Z_BLOCK) || (flush <? 0) then Some (s, z, Z_STREAM_ERROR) else
  let* (s, z, o) :=
    then_stage (c_deflate_entry s z flush) (fun s z =>
    then_stage (c_deflate_zlib_header s z) (fun s z =>
    then_stage (c_deflate_gzip_header s z) (fun s z =>
    then_stage (c_deflate_extra s z) (fun s z =>
    then_stage (c_deflate_name s z) (fun s z =>
    then_stage (c_deflate_comment s z) (fun s z =>
    then_stage (c_deflate_hcrc s z) (fun s z =>
    c_deflate_compress_g ef s z flush))))))) in
  match o with
  | Some r => Some (s, z, r)
  | None => c_deflate_trailer s z flush
  end.

(** deflateParams(strm, level, strategy): [fe] decides the address comparison of the two functions, [ef] is
    passed to its deflate(strm, Z_BLOCK). *)
Definition c_deflateParams_g (ef : Z -> Z) (fe : Z -> Z -> bool) (s : dstate) (z : strm) (level strategy : Z)
    : option (dstate * strm * Z) :=
  if bad_state s then Some (s, z, Z_STREAM_ERROR) else
  let level := if level =? Z_DEFAULT_COMPRESSION then 6 else level in
  if (level <? 0) || (level >? 9) || (strategy <? 0) || (strategy >? Z_FIXED) then Some (s, z, Z_STREAM_ERROR) else
  let* func := cfg_func (d_level s) in
  let* (s, z, o) :=
    (if (negb (strategy =? d_strategy s) || negb (fe func (cfg_f level))) && negb (d_last_flush s =? -2) then
       let* (s, z, err) := c_deflate_g ef s z Z_BLOCK in
       if err =? Z_STREAM_ERROR then Some (s, z, Some err) else
       if negb (z_avail_in z =? 0) then Some (s, z, Some Z_BUF_ERROR) else
       let* _ := guard (in_long (d_strstart s - d_block_start s)) in
       let* _ := guard (in_long (d_strstart s - d_block_start s + d_lookahead s)) in
       if negb (d_strstart s - d_block_start s + d_lookahead s =? 0) then Some (s, z, Some Z_BUF_ERROR)
       else Some (s, z, None)
     else Some (s, z, None)) in
  match o with
  | Some r => Some (s, z, r)
  | None =>
    let* s :=
      (if negb (d_level s =? level) then
         let* s := (if (d_level s =? 0) && negb (d_matches s =? 0) then
                      let* s := (if d_matches s =? 1 then c_slide_hash s else c_clear_hash s) in
                      Some (set_d_matches s 0)
                    else Some s) in
         let s := set_d_level s level in
         let '(good, lazy, nice, chain, _) := Znth level config_table in
         let s := set_d_max_lazy_match s lazy in
         let s := set_d_good_match s good in
         let s := set_d_nice_match s nice in
         Some (set_d_max_chain_length s chain)
       else Some s) in
    Some (set_d_strategy s strategy, z, Z_OK)
  end.

(** ** With distinct addresses ([ef] the identity, [fe] index equality) these are DModel4's functions. *)
Lemma c_compress_func_g_id : forall s z flush,
    c_compress_func_g (fun f => f) s z flush = c_compress_func s z flush.
Proof. intros. reflexivity. Qed.

Lemma c_deflate_compress_g_id : forall s z flush,
    c_deflate_compress_g (fun f => f) s z flush = c_deflate_compress s z flush.
Proof. intros. reflexivity. Qed.

Lemma c_deflate_g_id : forall s z flush, c_deflate_g (fun f => f) s z flush = c_deflate s z flush.
Proof. intros. reflexivity. Qed.

Lemma c_deflateParams_g_id : forall s z level strategy,
    c_deflateParams_g (fun f => f) Z.eqb s z level strategy = c_deflateParams s z level strategy.
Proof. intros. reflexivity. Qed.

(** [c_deflateParams_g] only depends on [fe] at the functions of configuration_table. *)
Lemma c_deflateParams_g_fe : forall ef fe fe' s z level strategy,
    (forall i j, 0 <= i <= 2 -> 0 <= j <= 2 -> fe i j = fe' i j) ->
    c_deflateParams_g ef fe s z level strategy = c_deflateParams_g ef fe' s z level strategy.
Proof.
  intros ef fe fe' s z level strategy E. unfold c_deflateParams_g.
  destruct (bad_state s); [reflexivity |].
  set (l := if level =? Z_DEFAULT_COMPRESSION then 6 else level).
  destruct ((l <? 0) || (l >? 9) || (strategy <? 0) || (strategy >? Z_FIXED)) eqn:Hl; [reflexivity |].
  unfold cfg_func. destruct ((0 <=? d_level s) && (d_level s <=? 9)) eqn:Hd; [| reflexivity].
  rewrite !orb_false_iff in Hl. destruct Hl as [[[H1 H2] _] _].
  apply Z.ltb_ge in H1. rewrite Z.gtb_ltb in H2. apply Z.ltb_ge in H2.
  apply andb_true_iff in Hd as [Hd1 Hd2]. apply Z.leb_le in Hd1. apply Z.leb_le in Hd2.
  assert (Hc : forall k, 0 <= k <= 9 -> 0 <= (let '(_, _, _, _, f) := Znth k config_table in f) <= 2).
  { intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9)
      as Hk' by lia.
    destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; vm_compute; split; discriminate. }
  pose proof (Hc _ (conj Hd1 Hd2)) as Hf. pose proof (Hc l (conj H1 H2)) as Hg. unfold cfg_f.
  destruct (Znth (d_level s) config_table) as [[[[? ?] ?] ?] f].
  destruct (Znth l config_table) as [[[[? ?] ?] ?] g].
  cbn [bind]. rewrite (E f g Hf Hg). reflexivity.
Qed.
