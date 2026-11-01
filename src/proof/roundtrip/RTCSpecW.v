(** * compress.c's compress2_z and compress2 for any sizes

    RTCSpec.compress2_z_spec / compress2_spec (compress_roundtrip) take a source and a destination of at most
    (uInt)-1 bytes and destLen > 0: each is given to deflate in one piece.  The short laws give any sizes the
    allocator provides (harness/rj_bad_level.c: any data and any output space, destLen possibly 0, with a level
    outside -1..9; harness/res_compress_bound.c: data of up to PTRDIFF_MAX bytes with destLen = compressBound_z):
    then compress2_z's loop gives deflate pieces of at most (uInt)-1 bytes of input and of output space.  The
    specifications below are those of RTCSpec.v for any sizes (a generalisation: RTCSpec's precondition implies
    this one, the postconditions are the same).  destLen = 0 is allowed with a level deflateInit rejects (the
    destination is then never read nor written); with a valid level destLen must be positive (deflate needs a
    valid next_out).  The result is the model's RTC2.c2_res, whose existence for every allocation outcome the
    caller gives (RTC2W.c2w_bound_stmt for destLen = compressBound_z(n); a rejected level for any sizes).

    The source may be Z_NULL when sourceLen = 0 (zlib.h allows it; compress2_z tests source against NULL only when
    sourceLen > 0): [c2_src] is no resource then (src = []), the source object otherwise.  compress2_z then calls
    deflate with next_in = Z_NULL and avail_in = 0, which DSpec.deflate_spec cannot express (its input object at
    next_in): compress2_z's context has DSpecN.deflate_specN (next_in = Z_NULL allowed, no input object), the
    specification a law that calls compress2_z gives deflate (with deflate's input-carrying callees of
    DSpecNBody.GN). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Import Zlib.proof.deflate.DSpecN.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTC2 Zlib.proof.roundtrip.RTCSpec.
Local Open Scope logic.

(* the precondition's facts: [cap] = destLen any z_size_t ([0] only with a rejected level), the source any
   length, Z_NULL only for no bytes (c2_src) *)
Definition c2w_pre (lvl : Z) (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) : list Prop :=
  [isptr dp; Zlength dc = cap; 0 <= cap <= Int64.max_unsigned; 0 < cap \/ ~ (-1 <= lvl <= 9);
   readable_share ssh; is_pointer_or_null sp; Zlength src <= Int64.max_unsigned;
   rbytes src; rs32 lvl;
   forall a1 a2 a3 a4 a5, exists r out, c2_res src cap lvl a1 a2 a3 a4 a5 zrst0 r out].

(* the source: Z_NULL and no bytes, or the object at sp of exactly the bytes src *)
Definition c2_src (ssh : share) (sp : val) (src : list Z) : mpred :=
  if eq_dec sp nullval then !! (src = []) && emp
  else @data_at Zlib.units.Compress.CS ssh (tarray tuchar (Zlength src)) (map vi src) sp.

(* RTCSpec.c2_sep_pre / c2_sep_post with the source [c2_src] *)
Definition c2w_sep_pre (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) : list mpred :=
  [@data_at Zlib.units.Compress.CS Ews (tarray tuchar cap) dc dp;
   @data_at Zlib.units.Compress.CS Tsh tulong (vl cap) dlp;
   c2_src ssh sp src;
   cversion_lit gv; deflate_globals gv; mem_mgr gv].

Definition c2w_sep_post (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) (out : list Z) : list mpred :=
  [@data_at Zlib.units.Compress.CS Ews (tarray tuchar cap) (map vi out ++ sublist (Zlength out) cap dc) dp;
   @data_at Zlib.units.Compress.CS Tsh tulong (vl (Zlength out)) dlp;
   c2_src ssh sp src;
   cversion_lit gv; deflate_globals gv; mem_mgr gv; TT].

(* a source object: c2_src is its data_at *)
Lemma c2_src_obj ssh sp src :
  isptr sp -> c2_src ssh sp src = @data_at Zlib.units.Compress.CS ssh (tarray tuchar (Zlength src)) (map vi src) sp.
Proof. intros P. unfold c2_src. destruct (eq_dec sp nullval) as [E|]; [subst; contradiction | reflexivity]. Qed.

(* the Z_NULL source: c2_src is emp *)
Lemma c2_src_null ssh : c2_src ssh nullval [] = emp.
Proof. unfold c2_src. rewrite if_true by reflexivity. apply prop_true_andp. reflexivity. Qed.

Definition compress2_z_spec_w :=
 DECLARE Zlib.compress.code._compress2_z
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z, level : Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong, tint ]
  PROPx (c2w_pre level gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: vi level :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2w_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap level a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2w_sep_post gv dp dc cap dlp ssh sp src out))).

Definition compress2_spec_w :=
 DECLARE Zlib.compress.code._compress2
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z, level : Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong, tint ]
  PROPx (c2w_pre level gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: vi level :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2w_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap level a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2w_sep_post gv dp dc cap dlp ssh sp src out))).

(** ** The bodies (compress unit): compress2_z against deflateInit_, deflate (Z_NULL input allowed), deflateEnd *)
Definition Gprog_compress2_z_w : funspecs := [deflateInit__spec; deflate_specN; deflateEnd_spec].
Definition Gprog_compress2_w : funspecs := [compress2_z_spec_w].

Definition ob_compress2_z_w : Prop :=
  @semax_body CSpec.Vprog Gprog_compress2_z_w Zlib.units.Compress.CS Zlib.compress.code.f_compress2_z
    compress2_z_spec_w.
Definition ob_compress2_w : Prop :=
  @semax_body CSpec.Vprog Gprog_compress2_w Zlib.units.Compress.CS Zlib.compress.code.f_compress2
    compress2_spec_w.

Definition rtc_w_bodies_stmt : Prop := ob_compress2_z_w /\ ob_compress2_w.
