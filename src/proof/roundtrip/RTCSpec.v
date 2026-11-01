(* The round-trip laws: THE specifications of deflate.c's deflateInit_ and of compress.c's compress2_z,
   compress2, compress_z, compress (used by compress_roundtrip only), and the statement of their bodies.

   - deflateInit_(strm, level, version, stream_size) = deflateInit2_(strm, level, 8, 15, 8, 0, version,
     stream_size): DSpec9.deflateInit2__spec_v9 with these parameters (deflate unit, DCS.CS).
   - compress2_z(dest, &destLen, source, sourceLen, level) (compress unit, Compress.CS): the result is the model's
     RTC2.c2_res (deflateInit2_ on DSpec9.zrst0, as deflateInit2__spec_v9's model runs); the PRE asks for the
     existence of the model run for every allocation outcome (the client gets it from RTC2.c2_ok); the
     destination is an Ews object of exactly destLen bytes (deflate_spec writes its output space at Ews), the
     bytes after the output unchanged; sizes up to (uInt)-1 (each is given in one piece), cap > 0; the POST
     has a TT (the deflate state is not freed when deflateEnd finds it bad).
   - compress2 the same with uLong lengths; compress_z / compress the same with level Z_DEFAULT_COMPRESSION.
   [rt_compress_bodies_stmt]: the five bodies; deflateEnd's precondition comes from Obligations.ob_dstream_to_end
   (a hypothesis of RTCBodies.rt_compress_bodies, proved in deflate/Api_toend.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import Zlib.proof.deflate.DCS.
Require Import Zlib.proof.deflate.DSpec Zlib.proof.deflate.DSpec9.
Require Zlib.proof.deflate.Obligations.
Require Zlib.proof.compress.CSpec.
Require Zlib.units.Compress.
Require Zlib.deflate.code Zlib.compress.code.
Require Import Zlib.proof.roundtrip.RTC2.
Local Open Scope logic.

(** ** deflateInit_ (deflate unit) *)
Definition deflateInit__spec :=
 DECLARE Zlib.deflate.code._deflateInit_
 WITH strmp : val, level : Z, vp : val, vsh : share,
      vers : list Z, ssize : Z, ni : val, tin : val, tout : val, msgv : val, adler : val,
      op : val, dt : val, st0 : val, gv : globals
 PRE [ tptr t_strm, tint, tptr tschar, tint ]
  PROP (s32_ok level; s32_ok ssize;
        readable_share vsh; 1 <= Zlength vers; -128 <= Znth 0 vers < 128;
        forall a1 a2 a3 a4 a5, exists r,
          c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level 8 15 8 0 a1 a2 a3 a4 a5 zrst0 = Some r)
  PARAMS (strmp; vi level; vp; vi ssize) GLOBALS (gv)
  SEP (@field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) ni strmp;
       reset_fields strmp tin tout msgv adler;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zalloc) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zfree) nullval strmp;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._opaque) op strmp;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._data_type) dt strmp;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._state) st0 strmp;
       @field_at_ DCS.CS Ews t_strm (DOT Zlib.deflate.code._reserved) strmp;
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv)
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : option dstate * strm * Z,
  PROP (c_deflateInit2_ (Znth 0 vers =? 49) (ssize =? 112) false level 8 15 8 0 a1 a2 a3 a4 a5 zrst0 = Some r)
  RETURN (vi (snd r))
  SEP (match fst (fst r) with
       | Some _ => dstream 2 (fst (fst r)) strmp nullval gv
       | None => EX st : val, EX za : val, EX zf : val, EX op' : val, EX dt' : val,
                 !! (snd r = Z_VERSION_ERROR -> st = st0) &&
                 (zfuncs gv * @field_at_ DCS.CS Ews t_strm (DOT Zlib.deflate.code._reserved) strmp *
                  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._state) st strmp *
                  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zalloc) za strmp *
                  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._zfree) zf strmp *
                  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._opaque) op' strmp *
                  @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._data_type) dt' strmp)
       end;
       @field_at DCS.CS Ews t_strm (DOT Zlib.deflate.code._next_in) ni strmp;
       EX msgv' : val,
       !! (if snd r =? Z_VERSION_ERROR then msgv' = msgv else msg_ok (z_msg (snd (fst r))) msgv') &&
       reset_fields strmp (rfv (snd r =? Z_OK) (z_total_in (snd (fst r))) tin)
         (rfv (snd r =? Z_OK) (z_total_out (snd (fst r))) tout) msgv'
         (rfv (snd r =? Z_OK) (z_adler (snd (fst r))) adler);
       @data_at DCS.CS vsh (tarray tschar (Zlength vers)) (map vi vers) vp;
       mem_mgr gv; deflate_globals gv).

Definition Gprog_deflateInit_ : funspecs := [deflateInit2__spec_v9].

(** ** compress.c (compress unit) *)

(* compress.c's ZLIB_VERSION literal "1.3.2" (deflateInit's version argument) *)
Definition cversion_lit (gv : globals) : mpred :=
  @data_at Zlib.units.Compress.CS Ers (tarray tschar 6) (map vi [49; 46; 51; 46; 50; 0])
    (gv Zlib.compress.code.___stringlit_compress_1).

(* the PRE / POST of compress2_z and its variants: [lvl] the level, [dlp] the destination length's cell (destLen
   = cap on entry), the destination dp an Ews object of exactly cap bytes [dc], the source the whole object sp
   of the bytes src *)
Definition c2_pre (lvl : Z) (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) : list Prop :=
  [isptr dp; Zlength dc = cap; 0 < cap <= umax; readable_share ssh; isptr sp; Zlength src <= umax;
   rbytes src; rs32 lvl;
   forall a1 a2 a3 a4 a5, exists r out, c2_res src cap lvl a1 a2 a3 a4 a5 zrst0 r out].

Definition c2_sep_pre (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) : list mpred :=
  [@data_at Zlib.units.Compress.CS Ews (tarray tuchar cap) dc dp;
   @data_at Zlib.units.Compress.CS Tsh tulong (vl cap) dlp;
   @data_at Zlib.units.Compress.CS ssh (tarray tuchar (Zlength src)) (map vi src) sp;
   cversion_lit gv; deflate_globals gv; mem_mgr gv].

Definition c2_sep_post (gv : globals) (dp : val) (dc : list val) (cap : Z) (dlp : val)
    (ssh : share) (sp : val) (src : list Z) (out : list Z) : list mpred :=
  [@data_at Zlib.units.Compress.CS Ews (tarray tuchar cap) (map vi out ++ sublist (Zlength out) cap dc) dp;
   @data_at Zlib.units.Compress.CS Tsh tulong (vl (Zlength out)) dlp;
   @data_at Zlib.units.Compress.CS ssh (tarray tuchar (Zlength src)) (map vi src) sp;
   cversion_lit gv; deflate_globals gv; mem_mgr gv; TT].

Definition compress2_z_spec :=
 DECLARE Zlib.compress.code._compress2_z
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z, level : Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong, tint ]
  PROPx (c2_pre level gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: vi level :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap level a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2_sep_post gv dp dc cap dlp ssh sp src out))).

Definition compress2_spec :=
 DECLARE Zlib.compress.code._compress2
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z, level : Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong, tint ]
  PROPx (c2_pre level gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: vi level :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap level a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2_sep_post gv dp dc cap dlp ssh sp src out))).

Definition compress_z_spec :=
 DECLARE Zlib.compress.code._compress_z
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong ]
  PROPx (c2_pre (-1) gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap (-1) a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2_sep_post gv dp dc cap dlp ssh sp src out))).

Definition compress_spec :=
 DECLARE Zlib.compress.code._compress
 WITH gv : globals, dp : val, dc : list val, cap : Z, dlp : val, ssh : share, sp : val, src : list Z
 PRE [ tptr tuchar, tptr tulong, tptr tuchar, tulong ]
  PROPx (c2_pre (-1) gv dp dc cap dlp ssh sp src)
  (PARAMSx (dp :: dlp :: sp :: vl (Zlength src) :: nil) (GLOBALSx (gv :: nil)
  (SEPx (c2_sep_pre gv dp dc cap dlp ssh sp src))))
 POST [ tint ]
  EX a1 : bool, EX a2 : bool, EX a3 : bool, EX a4 : bool, EX a5 : bool, EX r : Z, EX out : list Z,
  PROPx [c2_res src cap (-1) a1 a2 a3 a4 a5 zrst0 r out; Zlength out <= cap]
  (LOCALx (temp ret_temp (vi r) :: nil)
  (SEPx (c2_sep_post gv dp dc cap dlp ssh sp src out))).

(** ** The callee contexts and the bodies *)
Definition Gprog_compress2_z : funspecs := [deflateInit__spec; deflate_spec; deflateEnd_spec].
Definition Gprog_compress2 : funspecs := [compress2_z_spec].
Definition Gprog_compress_z : funspecs := [compress2_z_spec].
Definition Gprog_compress : funspecs := [compress2_spec].

Definition ob_deflateInit_ : Prop :=
  @semax_body DSpec.Vprog Gprog_deflateInit_ DCS.CS Zlib.deflate.code.f_deflateInit_ deflateInit__spec.
Definition ob_compress2_z : Prop :=
  @semax_body CSpec.Vprog Gprog_compress2_z Zlib.units.Compress.CS Zlib.compress.code.f_compress2_z
    compress2_z_spec.
Definition ob_compress2 : Prop :=
  @semax_body CSpec.Vprog Gprog_compress2 Zlib.units.Compress.CS Zlib.compress.code.f_compress2 compress2_spec.
Definition ob_compress_z : Prop :=
  @semax_body CSpec.Vprog Gprog_compress_z Zlib.units.Compress.CS Zlib.compress.code.f_compress_z compress_z_spec.
Definition ob_compress : Prop :=
  @semax_body CSpec.Vprog Gprog_compress Zlib.units.Compress.CS Zlib.compress.code.f_compress compress_spec.

Definition rt_compress_bodies_stmt : Prop :=
  ob_deflateInit_ /\ ob_compress2_z /\ ob_compress2 /\ ob_compress_z /\ ob_compress.
