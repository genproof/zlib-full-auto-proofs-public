(* The callee specifications of inflate()'s body, third version:
   - inflate_fast_spec3: needs mwf and the length bound of the length table (fast_ok), and the shares of
     the stream (written) and the tables (read);
   - updatewindow_spec3: strm->opaque is NULL (ZALLOC loads it).
   The case lemmas of the switch are proved in Delta_cases3, whose context has only the functions the
   cases call; inflate()'s body (Delta_inflate3) adds inflateStateCheck and updatewindow, and the case
   lemmas move there by semax_Delta_subsumption (sub_cases_inflate3). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Export Zlib.proof.inflate.CaseCommon.
Require Export Zlib.proof.inflate.Inv3.
Require Zlib.proof.crc32.Spec Zlib.proof.adler32.Spec Zlib.proof.inftrees.spec Zlib.proof.zutil.Libc.
Require VST.veric.semax_prog.

#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

(* what inflate_fast needs of the machine *)
Definition fast_ok (m: mst) : Prop :=
  mwf m /\ tvalid_len lenfix_list distfix_list (m_s m) (i_lencode (m_s m)) (i_lenbits (m_s m)).

Definition inflate_fast_spec3 :=
  DECLARE _inflate_fast
  WITH F: frame, m: mst
  PRE [ tptr t_strm, tuint ]
    PROP (fast_ok m; m_mode m = LEN; m_snx m = m_nx m; m_sow m = Zlength (m_ow m);
          i_hold (m_s m) = m_hold m; i_bits (m_s m) = m_bits m;
          6 <= m_have m; 258 <= m_left m; m_bits m < 8; m_out m = m_aout m;
          in_ok (f_ib F) (m_inp m); out_ok (f_ob F) (m_aout m);
          writable_share (f_shs F); readable_share (f_gsh F))
    PARAMS (f_strmp F; Vint (Int.repr (m_out m))) GLOBALS (f_gv F)
    SEP (mem_rep F m)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (mem_rep F (fast lenfix_list distfix_list m)).

(* the stream's fields state, zalloc, zfree, opaque *)
Definition stream_ok_val2 (gv: globals) (sv: reptype t_strm) (st: val) : Prop :=
  let '(_, (_, (_, (_, (_, (_, (_, (st', (za, (zf, (op, _))))))))))) := sv in
  st' = st /\ za = gv _zcalloc /\ zf = gv _zcfree /\ op = nullval.

Definition updatewindow_spec3 :=
  DECLARE _updatewindow
  WITH gv: globals, shs: share, strmp: val, sv: reptype t_strm, sp: val, headp: val, winp: val,
       s: istate, ssh: share, p: val, n: Z, c: list val, e: Z, data: list Z
  PRE [ tptr t_strm, tptr tuchar, tuint ]
    PROP (readable_share shs; stream_ok_val2 gv sv sp; swf s; readable_share ssh;
          0 <= Zlength data <= e; Zlength data <= Int.max_unsigned; e <= n; Zlength c = n;
          n <= Ptrofs.max_unsigned;
          sublist (e - Zlength data) e c = byte_vals data; bytes_ok data;
          i_win s = false -> winp = nullval)
    PARAMS (strmp; offset_val e p; Vint (Int.repr (Zlength data))) GLOBALS (gv)
    SEP (data_at shs t_strm sv strmp; state_rep gv sp strmp headp winp s; win_rep winp s;
         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv)
  POST [ tint ]
    EX r: Z, EX winp': val,
    PROP ((r = 0 /\ (i_win s = true -> winp' = winp)) \/ (r = 1 /\ i_win s = false /\ winp' = nullval))
    RETURN (Vint (Int.repr r))
    SEP (data_at shs t_strm sv strmp;
         state_rep gv sp strmp headp winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
         win_rep winp' (if r =? 0 then set_i_win (updatewindow s data) true else s);
         data_at ssh (tarray tuchar n) c p; mem_mgr gv; zfuncs gv).

(* the functions the switch cases call *)
Definition Gprog_cases3 : funspecs :=
  [Zlib.proof.adler32.Spec.adler32_spec; Zlib.proof.crc32.Spec.crc32_spec;
   inflate_fast_spec3; inflate_fixed_spec; Zlib.proof.inftrees.spec.inflate_table_spec;
   (_memcpy, snd (@Zlib.proof.zutil.Libc.memcpy_spec Zlib.units.Inflate.CS))].

Definition Gprog_inflate3 : funspecs := Gprog_cases3 ++ [inflateStateCheck_spec; updatewindow_spec3].

Definition Delta_cases3 : tycontext := func_tycontext f_inflate Vprog Gprog_cases3 nil.
Definition Delta_inflate3 : tycontext := func_tycontext f_inflate Vprog Gprog_inflate3 nil.

Lemma sub_cases_inflate3 : tycontext_sub Delta_cases3 Delta_inflate3.
Proof.
  apply VST.veric.semax_prog.func_tycontext_sub.
  - apply incl_refl.
  - unfold Gprog_inflate3. apply incl_appl. apply incl_refl.
  - apply list_norepet_NoDup. apply compute_list_norepet_e. vm_compute. reflexivity.
Qed.

Lemma semax_cases_inflate3 {Espec: OracleKind}: forall P c R,
  semax Delta_cases3 P c R -> semax Delta_inflate3 P c R.
Proof. intros. eapply semax_Delta_subsumption; [apply sub_cases_inflate3 | auto]. Qed.
