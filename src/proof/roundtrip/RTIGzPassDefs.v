(* RT-I part rti_gz_pass: the shared definitions of the gzip header passes.

   The call: m_init z L O, O = Format's gzip member with the header H = RTFinal.fhdr_of gh xfl, then anything
   (deflate bytes, trailer); all of O offered, so NEEDBITS never runs out.  The passes go through the cases
   at "stages" k = 0 .. 8 (entry of FLAGS, TIME, OS, EXLEN, EXTRA, NAME, COMMENT, HCRC, then TYPE), at the
   absolute positions gp_p k of O (the bytes consumed); at every stage the bit buffer is empty (hold = bits = 0)
   and the machine's other fields are those of m_init (gp_m).  With i_head (inflateGetHeader, hd = true) the
   gz_header is h0 updated with the fields read so far (gh_at k), with buffers of exactly the fields' sizes
   (head_bufs).  With FHCRC the check is the CRC-32 of the bytes consumed (gp_ck). *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Import Zlib.proof.roundtrip.RTIKit.
Require Import Zlib.proof.roundtrip.RTIGDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* the pieces of the gzip header (Format.gz_bytes0 = gA ++ gX ++ gN ++ gC; then gHC when FHCRC) *)
Definition gA (H: gzhdr) : list Z := [31; 139; 8; gz_flg H] ++ le_bytes (gz_mtime H) 4 ++ [gz_xfl H; gz_os H].
Definition gX (H: gzhdr) : list Z := match gz_extra H with Some x => le_bytes (Zlength x) 2 ++ x | None => [] end.
Definition gN (H: gzhdr) : list Z := match gz_name H with Some n => n ++ [0] | None => [] end.
Definition gC (H: gzhdr) : list Z := match gz_comment H with Some c => c ++ [0] | None => [] end.

Lemma gz_bytes0_split H : gz_bytes0 H = gA H ++ gX H ++ gN H ++ gC H.
Proof. unfold gz_bytes0, gA, gX, gN, gC. rewrite <- !app_assoc. reflexivity. Qed.

(* the hypotheses on the context: O starts with the header, bytes, deflateSetHeader's header (or none) *)
Definition gp_ok (gh: option DS.gzh) (xfl: Z) (O: list Z) : Prop :=
  (exists rest, O = gz_bytes (RF.fhdr_of gh xfl) ++ rest) /\ bytes_ok O /\
  (forall g, gh = Some g -> RF.rhdr_ok g) /\ (xfl = 0 \/ xfl = 2 \/ xfl = 4) /\ Zlength O <= 4194304.

Section GP.
Variables (gh: option DS.gzh) (xfl: Z) (src: list Z) (z: zfields) (hd: bool) (h0: hstate).

Definition gp_H : gzhdr := RF.fhdr_of gh xfl.
(* state->flags after FLAGS *)
Definition gp_F : Z := 8 + 256 * gz_flg gp_H.

(* the stages' positions *)
Definition gp_p (k: nat) : Z :=
  match k with
  | 0%nat => 2
  | 1%nat => 4
  | 2%nat => 8
  | 3%nat => 10
  | 4%nat => 10 + (match gz_extra gp_H with Some _ => 2 | None => 0 end)
  | 5%nat => Zlength (gA gp_H ++ gX gp_H)
  | 6%nat => Zlength (gA gp_H ++ gX gp_H ++ gN gp_H)
  | 7%nat => Zlength (gz_bytes0 gp_H)
  | _ => Zlength (gz_bytes gp_H)
  end.

(* the gz_header after stage k (the fields read so far, in the order the cases store them) *)
Definition gh_at (k: nat) (g: DS.gzh) (x nm cm: list Z) : hstate :=
  let h := h0 in
  let h := if (1 <=? k)%nat then set_h_text h (DS.gz_text g) else h in
  let h := if (2 <=? k)%nat then set_h_time h (DS.gz_time g) else h in
  let h := if (3 <=? k)%nat then set_h_os (set_h_xflags h xfl) (DS.gz_os g) else h in
  let h := if (4 <=? k)%nat then set_h_extra_len h (DS.gz_extra_len g) else h in
  let h := if (5 <=? k)%nat then set_h_xbuf h x else h in
  let h := if (6 <=? k)%nat then set_h_nbuf h nm else h in
  let h := if (7 <=? k)%nat then set_h_cbuf h cm else h in
  let h := if (8 <=? k)%nat then set_h_done (set_h_hcrc h (DS.gz_hcrc g)) 1 else h in
  h.

(* the machine at a stage: position p, mode md, empty bit buffer, the rest as m_init left it *)
Record gp_m (p md: Z) (m: mst) : Prop := {
  gm_inp : m_inp m = src;
  gm_nx : m_nx m = p;
  gm_hold : m_hold m = 0;
  gm_bits : m_bits m = 0;
  gm_leave : m_leave m = 0;
  gm_ow : m_ow m = [];
  gm_out : m_out m = zf_ao z;
  gm_aout : m_aout m = zf_ao z;
  gm_ret : m_ret m = Z_OK;
  gm_tout : m_tout m = zf_tout z;
  gm_mode : i_mode (m_s m) = md;
  gm_last : i_last (m_s m) = 0;
  gm_total : i_total (m_s m) = 0;
  (* inflateInit2(32): wrap 7 with bit 3 (fix F8: the window size comes from the header), i.e. init_s 7 0's wrap *)
  gm_wrap : i_wrap (m_s m) = 15;
  gm_wsize : i_wsize (m_s m) = 0;
  gm_wbits : i_wbits (m_s m) = 15;
  gm_head : i_head (m_s m) = hd }.

(* state->flags read *)
Definition gp_fl (m: mst) : Prop := i_flags (m_s m) = gp_F.
(* with FHCRC: the CRC-32 of the bytes consumed *)
Definition gp_ck (p: Z) (m: mst) : Prop :=
  gz_hcrc gp_H = true -> i_check (m_s m) = Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 p src).
(* with a gz_header: its buffers, and its fields after stage k *)
Definition gp_hh (k: nat) (m: mst) : Prop :=
  hd = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0 /\
                                 m_h m = gh_at k g x nm cm.

(* the whole invariant at stage k = 1 .. 7 (entry of the mode md) *)
Definition gp_st (k: nat) (md: Z) (m: mst) : Prop :=
  gp_m (gp_p k) md m /\ gp_fl m /\ gp_ck (gp_p k) m /\ gp_hh k m.

End GP.

(* ---------------------------------------------------------------------------------------------- *)
(* The parts: each case from its stage to the next (the case falls through into the next one)     *)

Definition gp_time_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 1 TIME m ->
  exists m', c_TIME2 m = c_OS2 m' /\ gp_st gh xfl O z hd h0 2 OS m'.

Definition gp_os_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 2 OS m ->
  exists m', c_OS2 m = c_EXLEN2 m' /\ gp_st gh xfl O z hd h0 3 EXLEN m'.

Definition gp_exlen_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 3 EXLEN m ->
  exists m', c_EXLEN2 m = c_EXTRA2 m' /\ gp_st gh xfl O z hd h0 4 EXTRA m' /\
    (forall x, gz_extra (gp_H gh xfl) = Some x -> i_length (m_s m') = Zlength x).

Definition gp_extra_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 4 EXTRA m ->
  (forall x, gz_extra (gp_H gh xfl) = Some x -> i_length (m_s m) = Zlength x) ->
  exists m', c_EXTRA2 m = c_NAME2 m' /\ gp_st gh xfl O z hd h0 5 NAME m' /\ i_length (m_s m') = 0.

Definition gp_name_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 5 NAME m -> i_length (m_s m) = 0 ->
  exists m', c_NAME2 m = c_COMMENT2 m' /\ gp_st gh xfl O z hd h0 6 COMMENT m' /\ i_length (m_s m') = 0.

Definition gp_comment_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 6 COMMENT m -> i_length (m_s m) = 0 ->
  exists m', c_COMMENT2 m = c_HCRC m' /\ gp_st gh xfl O z hd h0 7 HCRC m'.

Definition gp_hcrc_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_st gh xfl O z hd h0 7 HCRC m ->
  exists m', c_HCRC m = IBrk m' /\ gp_m O z hd (gp_p gh xfl 8) Zlib.proof.inflate.Model.TYPE m' /\
    gp_fl gh xfl m' /\ gp_hh gh xfl hd h0 8 m' /\ i_check (m_s m') = 0.

(* the HEAD pass (inflateInit2(32): wrap 7, wbits 0) and the FLAGS case up to TIME *)
Definition gp_head_stmt : Prop := forall gh xfl O z L,
  gp_ok gh xfl O -> (l_s L = init_s 7 0 \/ l_s L = set_i_head (init_s 7 0) true) ->
  exists m1, stepf2 Z_FINISH lenfix_list distfix_list (m_init z L O) = IBrk m1 /\
    gp_m O z (i_head (l_s L)) 2 FLAGS m1 /\
    i_check (m_s m1) = Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 2 O) /\ m_h m1 = l_h L.

Definition gp_flags_stmt : Prop := forall gh xfl O z hd h0 m,
  gp_ok gh xfl O -> gp_m O z hd 2 FLAGS m ->
  i_check (m_s m) = Zlib.proof.crc32.Model.ref_crc32 0 (sublist 0 2 O) -> m_h m = h0 ->
  (hd = true -> exists g x nm cm, gh = Some g /\ head_bufs g x nm cm h0 /\ h_done h0 = 0) ->
  exists m', c_FLAGS2 m = c_TIME2 m' /\ gp_st gh xfl O z hd h0 1 TIME m'.

(* the decode context, and the decode invariant at the TYPE loop head after the header *)
Definition gp_dctx_stmt : Prop := forall gh xfl wb bs D O,
  9 <= wb <= 15 -> wf (2 ^ wb) [] bs -> data [] bs = D -> (xfl = 0 \/ xfl = 2 \/ xfl = 4) ->
  O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs ->
  (forall g, gh = Some g -> RF.rhdr_ok g) ->
  Zlength D <= 1048576 -> Zlength O <= 4194304 ->
  dctx_ok (gz_ctx gh xfl wb bs O).

Definition gp_kd_stmt : Prop := forall gh xfl wb bs O z hd h0 m,
  9 <= wb <= 15 -> O = stream_bytes (WGzip (RF.fhdr_of gh xfl)) [] bs ->
  dctx_ok (gz_ctx gh xfl wb bs O) -> zf_tout z = 0 ->
  gp_m O z hd (gp_p gh xfl 8) Zlib.proof.inflate.Model.TYPE m -> gp_fl gh xfl m -> gp_hh gh xfl hd h0 8 m ->
  i_check (m_s m) = 0 ->
  Kd (gz_ctx gh xfl wb bs O) 0 O [] m.
