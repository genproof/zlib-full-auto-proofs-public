(* Law res_memory_inflate: the do-while of main (harness/res_memory_inflate.c), one iteration from the loop
   invariant [mem_inv] to [mem_inv] again (or `return 0` when malloc gives no output space):
     take = upto(clip(input_len - read)); room = nondet_u32(); out = malloc(room);
     set_buffer(&strm, input + read, take, out, room); code = inflate(&strm, any flush);
     gp_assert(code != Z_MEM_ERROR || count.failed); gp_assert(count.peak <= (1ul << w) + 7160);
     read += take - strm.avail_in; free(out);

   [mem_inv]: `read` bytes of the input taken (0 <= read <= input_len), the live stream with any application
   fields z and live part L whose state keeps the law's invariant (res_inv, ModelStmt.v) and the wide machine
   invariant swfW (inflate()'s precondition), the counting allocator's events tr with mem_ok
   (ResIMemTheory.v), the input object of alloc_any_bytes, and the read-only globals. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require Import QuickProof.Assembly.
Require Import Zlib.proof.adler32.Bytes.
Require Import Zlib.proof.adler32.MainLib.
Require Import Zlib.proof.za.inflate_api.USpec.
Require Import Zlib.proof.harness.laws_common.Spec.
Require Import Zlib.proof.harness.counted.Spec.
Require Import Zlib.proof.harness.counted.Kit.
Require Import Zlib.proof.harness.res_inflate.ModelStmt.
Require Import Zlib.proof.harness.res_inflate.ResICS.
Require Import Zlib.proof.harness.res_inflate.ResISpecs.
Require Import Zlib.proof.harness.res_inflate.ResIKit.
Require Import Zlib.proof.harness.res_inflate.ResITheory.
Require Import Zlib.proof.harness.res_inflate.ResIMemTheory.
Require Import Zlib.proof.harness.res_inflate.ResIMemStep.
Require Import Zlib.proof.harness.res_inflate.ResIMemKit.
Require Import Zlib.proof.crc32.Spec.
Require Import Zlib.harness.res_memory_inflate.code.
Local Open Scope logic.

(* the statement at a path of a function body, and the path of its first do-while *)
Fixpoint mem_sub_stmt (path : list nat) (s : statement) : statement :=
  match path, s with
  | nil, _ => s
  | O :: pth, Ssequence a _ => mem_sub_stmt pth a
  | S _ :: pth, Ssequence _ b => mem_sub_stmt pth b
  | O :: pth, Sifthenelse _ a _ => mem_sub_stmt pth a
  | S _ :: pth, Sifthenelse _ _ b => mem_sub_stmt pth b
  | O :: pth, Sloop a _ => mem_sub_stmt pth a
  | S _ :: pth, Sloop _ b => mem_sub_stmt pth b
  | _, _ => Sskip
  end.

Fixpoint mem_find_loop (s : statement) : option (list nat) :=
  let cons_opt k o := match o with Some l => Some (k :: l) | None => None end in
  let or_opt x y := match x with Some _ => x | None => y end in
  match s with
  | Ssequence (Sloop _ _) _ => Some nil
  | Ssequence a b => or_opt (cons_opt O (mem_find_loop a)) (cons_opt 1%nat (mem_find_loop b))
  | Sifthenelse _ a b => or_opt (cons_opt O (mem_find_loop a)) (cons_opt 1%nat (mem_find_loop b))
  | Sloop a b => or_opt (cons_opt O (mem_find_loop a)) (cons_opt 1%nat (mem_find_loop b))
  | _ => None
  end.

(* the body of main's do-while *)
Definition seg_body_mem : statement :=
  ltac:(let p := eval vm_compute in
          (match mem_find_loop (fn_body f_main) with Some l => l ++ [0; 0]%nat | None => nil end) in
        let x := eval cbv beta iota zeta delta [mem_sub_stmt f_main fn_body] in (mem_sub_stmt p (fn_body f_main)) in
        exact x).

Definition Delta_mem : tycontext :=
  func_tycontext f_main (QPvarspecs Zlib.contracts.res_memory_inflate.whole_prog) Gmain nil.
Definition POST_mem : ret_assert :=
  frame_ret_assert (function_body_ret_assert tint (EX r : int, PROP () RETURN (Vint r) SEP (TT))%argsassert)
    (stackframe_of f_main).

(* the allocator of main's stream: its struct count at cp and the two functions of the harness *)
Definition mem_za (gv : globals) (cp : val) : zallocator :=
  counted cp (gv HC._counted_alloc) (gv HC._counted_free).

(* the loop invariant; w is the windowBits given to inflateInit2_, dp and bs the input object *)
Definition mem_inv (gv : globals) (w : Z) (vs cp dp : val) (bs : list Z) : environ -> mpred :=
  EX read : Z, EX tr : list zev, EX z : zfields, EX L : live,
  PROP (0 <= read <= Zlength bs; res_inv (harness_w w) (l_s L); Zlib.proof.inflate.InvW.swfW (l_s L);
        mem_ok (harness_w w) (l_s L) tr)
  LOCAL (temp _read (Vlong (Int64.repr read)); temp _input dp;
         temp _input_len (Vlong (Int64.repr (Zlength bs))); temp _w (Vint (Int.repr (harness_w w)));
         lvar _strm tzs vs; lvar _count__1 tcount cp; gvars gv)
  SEP (@istream_za (mem_za gv cp) (init_cell w) gv Tsh vs z (Some L); count_res cp gv tr;
       @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp;
       @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp;
       tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; hversion_lit ___stringlit_res_memory_inflate_1 gv;
       @za_funcs Zlib.units.Inflate.CS (mem_za gv cp)).

(* VST's after_forward_call simplifies remove_localdef_temp with `simpl rlt_ident_eq`, which runs away on main's
   identifiers (_input against _input_len); each identifier comparison is decided by vm_compute instead. *)
Ltac mem_rlt_fix u :=
  lazymatch u with
  | context C [rlt_ident_eq ?a ?b] =>
      let v := eval vm_compute in (rlt_ident_eq a b) in
      let u2 := context C [v] in mem_rlt_fix u2
  | _ => u
  end.

Ltac simplify_remove_localdef_temp ::=
  match goal with |- context [remove_localdef_temp ?i ?L] =>
    let u := constr:(remove_localdef_temp i L) in
    let u' := eval lazy delta [remove_localdef_temp] beta iota in u in
    let u' := mem_rlt_fix u' in
    let u' := eval lazy beta iota in u' in
    let u' := eval lazy zeta in u' in
    change u with u'
  end.

(* `x = f(...); y = (cast) x;` as two statements *)
Ltac mem_split_call :=
  repeat match goal with |- semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ => apply seq_assoc1 end;
  match goal with |- semax _ _ (Ssequence (Ssequence (Scall _ _ _) _) _) _ => apply seq_assoc1 end.

(* forward_if whose join point adds the value v of the temp t *)
Ltac mem_ifpost t v := match goal with |- semax _ (PROPx _ (LOCALx ?Q (SEPx ?R))) _ _ =>
  forward_if (PROPx [] (LOCALx (temp t v :: Q) (SEPx R))) end.

(* the second assertion holds: count.peak <= (1ul << w) + 7160, computed in unsigned long *)
Lemma mem_peak_test hw p : 8 <= hw <= 15 -> 0 <= p <= 2 ^ hw + 7160 ->
  Int64.ltu (Int64.add (Int64.shl (Int64.repr 1) (Int64.repr hw)) (Int64.repr 7160)) (Int64.repr p) = false.
Proof.
  intros Hh Hp.
  assert (P : 0 < 2 ^ hw <= 2 ^ 15) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  change (2 ^ 15) with 32768 in P.
  assert (Esh : Int64.shl (Int64.repr 1) (Int64.repr hw) = Int64.repr (2 ^ hw)).
  { unfold Int64.shl. rewrite !Int64.unsigned_repr by rep_lia. rewrite Z.shiftl_1_l. reflexivity. }
  rewrite Esh. unfold Int64.add, Int64.ltu.
  rewrite (Int64.unsigned_repr (2 ^ hw)) by rep_lia. rewrite (Int64.unsigned_repr 7160) by rep_lia.
  rewrite (Int64.unsigned_repr p) by rep_lia. rewrite Int64.unsigned_repr by rep_lia.
  destruct (zlt (2 ^ hw + 7160) p); [lia | reflexivity].
Qed.

(* one iteration of the do-while *)
Lemma body_mem_loop {Espec : OracleKind} (MODEL : res_model_stmt) gv w vs cp dp bs read tr z L :
  wbits_ok w = true -> isptr dp -> isptr vs -> isptr cp -> Zlength bs <= 9223372036854775807 -> is_bytes bs ->
  0 <= read <= Zlength bs -> res_inv (harness_w w) (l_s L) -> Zlib.proof.inflate.InvW.swfW (l_s L) ->
  mem_ok (harness_w w) (l_s L) tr ->
  semax Delta_mem
    (PROP ()
     LOCAL (temp _read (Vlong (Int64.repr read)); temp _input dp;
            temp _input_len (Vlong (Int64.repr (Zlength bs))); temp _w (Vint (Int.repr (harness_w w)));
            lvar _strm tzs vs; lvar _count__1 tcount cp; gvars gv)
     SEP (@istream_za (mem_za gv cp) (init_cell w) gv Tsh vs z (Some L); count_res cp gv tr;
          @malloc_token Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) dp;
          @data_at Zlib.units.Adler32.CS Ews (tarray tuchar (Zlength bs)) (bytes_rep bs) dp;
          tables_rep Ers gv; crc_table_at Ers gv; version_lit gv; hversion_lit ___stringlit_res_memory_inflate_1 gv;
          @za_funcs Zlib.units.Inflate.CS (mem_za gv cp)))
    seg_body_mem
    (loop1_ret_assert (mem_inv gv w vs cp dp bs) (overridePost (mem_inv gv w vs cp dp bs) POST_mem)).
Proof.
  intros Hwb Pdp Pvs Pcp Hlen Hbs Hrd HR HW HM.
  unfold seg_body_mem, Delta_mem, POST_mem. simplify_func_tycontext. abbreviate_semax.
  forward_call (Zlength bs - read).
  forward_call (Z.min (Zlength bs - read) Int.max_unsigned). Intros take.
  forward.
  mem_split_call.
  forward_call tt. Intros room.
  forward.
  unfold count_res. Intros.
  forward_call (tarray tuchar room, gv). { simpl; rep_lia. }
  Intros op.
  destruct (eq_dec op nullval) as [Eo | No].
  { subst op. forward_if; [ | contradiction].
    forward. Exists (Int.repr 0).
    sep_apply (@live_local (mem_za gv cp) (init_cell w) gv Tsh vs z L).
    rewrite count_local. sep_apply (@data_at_data_at_ CSi Tsh tcount). entailer!. }
  Intros.
  forward_if.
  { contradiction. }
  rewrite Int.unsigned_repr by rep_lia.
  rewrite istream_zs. Intros. unfold zs_of. simpl za_alloc; simpl za_free; simpl za_opaque.
  forward_call (vs, Tsh, offset_val read dp, take, op, room, zf_ni z, Vint (Int.repr (zf_ai z)),
                Vlong (Int64.repr (zf_tin z)), zf_no z, Vint (Int.repr (zf_ao z)), Vlong (Int64.repr (zf_tout z)),
                msg_val gv (zf_msg z), l_sp L, gv HC._counted_alloc, gv HC._counted_free, cp,
                Vint (Int.repr (zf_dt z)), @adler_val (init_cell w) (zf_adler z), zf_res z).
  assert (Htk : 0 <= take <= Int.max_unsigned /\ read + take <= Zlength bs) by lia.
  sep_apply (@set_buffer_istream (mem_za gv cp) (init_cell w) gv vs z L (offset_val read dp) take op room);
    try lia.
  set (z1 := set_bufz z (offset_val read dp) take op room).
  assert_PROP (isptr op) as Pop by entailer!.
  sep_apply (mem_bufs_pre L dp read bs op room ltac:(lia)).
  forward_call tt. Intros fl.
  rewrite (vint_signed fl). pose proof (Int.signed_range (Int.repr fl)) as Hfl.
  set (flush := Int.signed (Int.repr fl)) in *. clearbody flush.
  pose proof (harness_w_range w Hwb) as Hhw.
  destruct (mem_in_ok dp read take bs) as [Iok Itk]; auto; try rep_lia.
  forward_call (ix cp (gv HC._counted_alloc) (gv HC._counted_free) (init_wrap w =? 0),
                (gv, Tsh, vs, z1, Some L, mem_ib dp read bs, sublist read (read + take) bs, Some (obuf op room),
                 flush, Ers, Ers, true, true, tr)).
  { unfold istream_opt_za, is_live. rewrite !if_false by (destruct vs; try contradiction; discriminate).
    unfold head_opt, head_mem. destruct HR as [Hhd _]. rewrite Hhd.
    cbn [zai_a zai_v ix Ac fst snd]. unfold init_cell, count_res, mem_za. simpl za_res. unfold count_res.
    cancel. }
  { split; [unfold z1, set_bufz, mem_ib, in_ptr; cbn; rewrite Z.add_0_r; reflexivity | ].
    split; [split; [exact Iok | unfold z1, set_bufz; cbn; lia] | ].
    split; [split; [unfold z1, set_bufz, obuf, out_ptr; cbn; rewrite isptr_offset_val_zero by auto; reflexivity
                   | apply mem_out_ok; auto] | ].
    simpl za_cap. eapply mem_cap; [ | exact HM]. lia. }
  Intros vret. destruct vret as [[[r z'] st'] ow]. cbn [fst snd] in *.
  match goal with H : inflate_rel _ _ _ _ _ _ _ _ _ _ _ |- _ => rename H into HRel end.
  assert (Hsn : vs <> nullval) by (destruct vs; try contradiction; discriminate).
  assert (Hib : mem_ib dp read bs <> InNull) by (unfold mem_ib; discriminate).
  destruct st' as [L' | ].
  2: { exfalso. destruct (inflate_rel_some _ _ _ _ _ _ _ _ _ _ _ Hsn Hib HRel) as (? & ? & E & _).
       discriminate E. }
  destruct (mem_rel _ _ _ _ _ _ _ _ _ _ _ Hsn Hib (proj1 (proj2 HR)) HRel)
    as (res & Hrun & EL' & Er & Hr & Hai & Hsnx).
  assert (Z1 : zf_ok z1) by (apply set_bufz_ok; auto; lia).
  destruct (mem_call (proj2 MODEL) (harness_w w) flush z1 L (sublist read (read + take) bs) res tr Hhw HR HW H3 Z1
              (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Iok))))))) ltac:(lia) Hrun HM)
    as (HR' & HM' & Hfail & Hpeak).
  rewrite <- EL' in HR', HM', Hfail, Hpeak.
  unfold istream_opt_za, is_live. rewrite !if_false by exact Hsn.
  unfold head_opt, head_mem. rewrite (proj1 HR').
  sep_apply (mem_bufs_post L dp read bs op room ow).
  set (tr' := tr ++ ZEvents.win_ev (l_s L) (l_s L')) in *.
  change (@za_res _ gv tr') with (count_res cp gv tr').
  unfold count_res. rewrite count_local. Intros.
  forward.
  (* gp_assert(code != Z_MEM_ERROR || count.failed) *)
  assert (Hcf : r = Z_MEM_ERROR -> cnt_failed tr' = 1).
  { intros E. unfold cnt_failed. rewrite Hfail by (rewrite <- Er; exact E). reflexivity. }
  mem_ifpost _t'14 (Vint (Int.repr 1)).
  { forward. apply ENTAIL_refl. }
  { forward. forward.
    assert (Er4 : r = Z_MEM_ERROR).
    { rewrite Int.neg_repr in H5. apply repr_inj_signed in H5; [exact H5 | rep_lia | rep_lia]. }
    rewrite (Hcf Er4). entailer!. }
  forward_call (Int.repr 1).
  (* gp_assert(count.peak <= (1ul << w) + 7160) *)
  forward.
  assert (P15 : 0 < 2 ^ harness_w w <= 2 ^ 15)
    by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  pose proof (cnt_peak_nonneg tr') as Hpk0.
  forward_call (Int.repr 1).
  { change (Int.unsigned Int64.iwordsize') with 64. lia. }
  { entailer!. rewrite mem_peak_test by lia. reflexivity. }
  (* read += take - strm.avail_in *)
  rewrite istream_zs. Intros. rewrite zs_csi. unfold zs_of, zs_val. simpl za_alloc; simpl za_free; simpl za_opaque.
  forward.
  forward.
  set (snx := m_snx (r_m res)) in *. rewrite Itk in Hai, Hsnx.
  assert (Eread : Int64.add (Int64.repr read)
                    (Int64.sub (Int64.repr take) (Int64.repr (Int.unsigned (Int.repr (zf_ai z'))))) =
                  Int64.repr (read + snx)).
  { rewrite Int.unsigned_repr by rep_lia. rewrite Hai. unfold Int64.add, Int64.sub.
    rewrite (Int64.unsigned_repr take), (Int64.unsigned_repr (take - snx)) by rep_lia.
    rewrite (Int64.unsigned_repr (take - (take - snx))), (Int64.unsigned_repr read) by rep_lia.
    f_equal. lia. }
  rewrite Eread.
  (* free(out) *)
  forward_call (tarray tuchar room, op, gv).
  { rewrite if_false by exact No. cancel. }
  unfold mem_inv. Exists (read + snx) tr' z' L'.
  unfold count_res. rewrite count_local. rewrite istream_zs. unfold zs_of. rewrite zs_csi.
  entailer!. apply derives_refl.
Qed.
