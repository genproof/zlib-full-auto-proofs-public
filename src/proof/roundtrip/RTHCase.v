(* RT-H: the interface of inflate()'s header world.  In the header modes HEAD .. HCRC with a
   gz_header attached (i_head) the header is the partial RTHSpec.head_rep6, held next to the headless loop
   state RTHLoop.loop_stateH (whose head part is the atom hnoneH = emp); a header case ends either in a header
   mode (headless state + hd6) or, having passed the header (hpass: hfull), in Spec5's world: Loop.loop_state
   with the defined head_rep.  Statements proved by the parts:
     rth_head_stmt (case HEAD), rth_fto_stmt (FLAGS/TIME/OS), rth_ex_stmt (EXLEN/EXTRA),
     rth_nc_stmt (NAME/COMMENT), rth_hcrc_stmt (HCRC), pro_part6_stmt (the prologue). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.roundtrip.RTHSpec.
Require Export Zlib.proof.roundtrip.RTHCaseKitT5.
Require Export Zlib.proof.roundtrip.RTHBody5Parts.
Require Import Zlib.proof.crc32.Spec.
#[local] Existing Instance Zlib.units.Inflate.CS.
Local Open Scope logic.

Module IM := Zlib.proof.inflate.Model.

(* the header of machine m in the frame F *)
Definition hd6 (F: frame) (m: mst) : mpred :=
  head_rep6 (f_hsh F) (f_headp F) (f_xb F) (f_nb F) (f_cb F) (m_s m) (m_h m).

(* after a pass of a header case: still in the header modes, or past the header in Spec5's world *)
Definition post6 (F: frame) (m: mst) : environ -> mpred :=
  if hdr_mode (m_mode m) then loop_stateH F m * (fun _ => hd6 F m) else loop_state F m.

Definition case_post6 (F: frame) (m: mst) : ret_assert :=
  {| RA_normal := EX m': mst, !! (stepf2 (f_flush F) lenfix_list distfix_list m = IBrk m') && post6 F m';
     RA_break := FF;
     RA_continue := FF;
     RA_return := fun _ _ => FF |}.

Lemma case_post6_eq: forall F m m',
  stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' ->
  case_post6 F m = case_post6 F m'.
Proof. intros F m m' E. unfold case_post6. rewrite E. reflexivity. Qed.

(* the lemma of header case i (mode Y) with a header attached, on a call that passes the header *)
Definition case_ok6 {Espec: OracleKind} (F: frame) (Y: Z) (i: nat) : Prop :=
  forall m n, m_mode m = Y -> m_leave m = 0 -> mwf3 m -> hd_ok F m -> i_head (m_s m) = true ->
    hpass (f_flush F) (S n) m ->
    semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
      (seq_of_labeled_statement (ls_drop i inflate_LS))
      (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m)).

(* the end of a header case's body falling into the header mode Y *)
Definition fall_post6 (F: frame) (m: mst) (Y: Z) : environ -> mpred :=
  EX m': mst,
    !! (stepf2 (f_flush F) lenfix_list distfix_list m = stepf2 (f_flush F) lenfix_list distfix_list m' /\
        m_mode m' = Y /\ m_leave m' = 0 /\ mwf3 m' /\ hd_ok F m' /\ hdr_tok F m' = hdr_tok F m /\
        i_head (m_s m') = true) &&
    (loop_stateH F m' * (fun _ => hd6 F m')).

Lemma hpass_same: forall flush n m m',
  hdr_mode (m_mode m) = true -> hdr_mode (m_mode m') = true ->
  stepf2 flush lenfix_list distfix_list m = stepf2 flush lenfix_list distfix_list m' ->
  hpass flush (S n) m -> hpass flush (S n) m'.
Proof.
  intros flush n m m' H H' E P. cbn [hpass] in P |- *. rewrite H in P. rewrite H', <- E. exact P.
Qed.

Lemma case_fallthrough6 {Espec: OracleKind} (F: frame) (m: mst) (n: nat) (Y: Z) (i: nat):
  (i < 32)%nat -> hdr_mode Y = true -> hdr_mode (m_mode m) = true -> hpass (f_flush F) (S n) m ->
  case_ok6 F Y (S i) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m)) (case_body i)
    (overridePost (fall_post6 F m Y * (fun _ => hdr_tok F m))
       (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m))) ->
  semax Delta_cases5 (loop_stateH F m * (fun _ => hdr_tok F m * hd6 F m))
    (seq_of_labeled_statement (ls_drop i inflate_LS))
    (frame_ret_assert (switch_ret_assert (case_post6 F m)) (fun _ => hdr_tok F m)).
Proof.
  intros Hi HY Hm HP HC HB. rewrite seq_split by lia.
  eapply semax_seq; [exact HB | ].
  unfold fall_post6. rewrite exp_sepcon1. apply extract_exists_pre. intros m'.
  rewrite sepcon_andp_prop'. apply semax_extract_prop. intros (E & HM & HL & W & HD & HT & HH).
  rewrite (case_post6_eq F m m' E). rewrite <- HT.
  assert (HP': hpass (f_flush F) (S n) m') by (apply (hpass_same _ n m m'); auto; rewrite HM; exact HY).
  eapply semax_pre; [ | apply (HC m' n); auto].
  intros rho. simpl. apply andp_left2. cancel.
Qed.

(* the parts *)
Definition rth_head_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok6 F IM.HEAD 0.

Definition rth_fto_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok6 F IM.TIME 2 -> case_ok6 F IM.FLAGS 1) /\ (case_ok6 F IM.OS 3 -> case_ok6 F IM.TIME 2) /\
    (case_ok6 F IM.EXLEN 4 -> case_ok6 F IM.OS 3).

Definition rth_ex_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok6 F IM.EXTRA 5 -> case_ok6 F IM.EXLEN 4) /\ (case_ok6 F IM.NAME 6 -> case_ok6 F IM.EXTRA 5).

Definition rth_nc_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F ->
    (case_ok6 F IM.COMMENT 7 -> case_ok6 F IM.NAME 6) /\ (case_ok6 F IM.HCRC 8 -> case_ok6 F IM.COMMENT 7).

Definition rth_hcrc_stmt : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> case_ok6 F IM.HCRC 8.

(* every header case *)
Definition cases6_all : Prop :=
  forall {Espec: OracleKind} (F: frame), frame_ok5 F -> forall i, (i <= 8)%nat -> case_ok6 F (IM.HEAD + Z.of_nat i) i.

Lemma cases6_all_proof: rth_head_stmt -> rth_fto_stmt -> rth_ex_stmt -> rth_nc_stmt -> rth_hcrc_stmt -> cases6_all.
Proof.
  intros HH FT XE NC HC Espec F HF.
  pose proof (HC Espec F HF) as C8.
  destruct (NC Espec F HF) as [N6 N7]. pose proof (N7 C8) as C7. pose proof (N6 C7) as C6.
  destruct (XE Espec F HF) as [E4 E5]. pose proof (E5 C6) as C5. pose proof (E4 C5) as C4.
  destruct (FT Espec F HF) as (F1 & F2 & F3). pose proof (F3 C4) as C3. pose proof (F2 C3) as C2.
  pose proof (F1 C2) as C1. pose proof (HH Espec F HF) as C0.
  intros i Hi.
  do 9 (destruct i as [|i]; [ eassumption | ]). exfalso; lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* the prologue with any header part Hd (it does not touch it) and the header buffers' tokens       *)

Definition htok6 (st: option live) : mpred :=
  match st with
  | Some L => if i_head (l_s L) then hdr_btoks (l_xb L) (l_nb L) (l_cb L) (l_h L) else emp
  | None => emp
  end.

Definition pro_pre6 (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) (ib: inbuf)
    (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool) (vh vl vb: val) (Hd: mpred)
    : environ -> mpred :=
  PROP ()
  LOCAL (lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh;
         gvars gv; temp _strm strmp; temp _flush (Vint (Int.repr flush)))
  SEP (data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
       istream_opt gv shs strmp z st; Hd; htok6 (is_live strmp st);
       bufs_opt (is_live strmp st) ib ob [] itok otok;
       tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv).

Definition pro_post6 (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live) (ib: inbuf)
    (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool) (vh vl vb: val)
    (Hd: mpred) : environ -> mpred :=
  EX L: live, EX o: outbuf,
    !! (st = Some L /\ ob = Some o /\ ~ inflate_bad strmp z st ib ob /\ live_ok L /\ zf_ok z /\
        writable_share shs /\ strmp <> nullval) &&
    lstateH (mkF gv shs strmp L ib o gsh tsh z vh vl vb flush) (xfr L itok otok ib o * Hd) (m_init z L inp).

Definition pro_part6_stmt : Prop :=
  forall {Espec: OracleKind} (gv: globals) (shs: share) (strmp: val) (z: zfields) (st: option live)
    (ib: inbuf) (inp: list Z) (ob: option outbuf) (flush: Z) (gsh tsh: share) (itok otok: bool)
    (vh vl vb: val) (Hd: mpred) (R: ret_assert),
  Int.min_signed <= flush <= Int.max_signed -> readable_share gsh -> readable_share tsh ->
  in_tok_ok itok ib -> out_tok_ok otok ob -> zf_ni z = in_ptr ib 0 ->
  match ib with InNull => inp = [] | InBuf _ _ _ _ _ => in_ok ib inp /\ zf_ai z = Zlength inp end ->
  match ob with None => zf_no z = nullval | Some o => zf_no z = out_ptr o 0 /\ out_ok o (zf_ao z) end ->
  zf_ai z <= Int.max_signed -> zf_ao z <= Int.max_signed ->
  (inflate_bad strmp z st ib ob ->
   ENTAIL Delta_inflate5,
     PROPx [] (LOCALx [lvar _hbuf (tarray tuchar 4) vb; lvar _last t_code vl; lvar _here t_code vh; gvars gv]
       (SEPx [data_at_ Tsh (tarray tuchar 4) vb; data_at_ Tsh t_code vl; data_at_ Tsh t_code vh;
              istream_opt gv shs strmp z st; Hd; htok6 (is_live strmp st);
              bufs_opt (is_live strmp st) ib ob [] itok otok;
              tables_rep gsh gv; crc_table_at tsh gv; mem_mgr gv; zfuncs gv]))
     |-- RA_return R (Some (zv Z_STREAM_ERROR))) ->
  semax Delta_inflate5 (pro_pre6 gv shs strmp z st ib ob flush gsh tsh itok otok vh vl vb Hd)
    (Ssequence inflate_leave0 inflate_pre)
    (overridePost (pro_post6 gv shs strmp z st ib inp ob flush gsh tsh itok otok vh vl vb Hd) R).
