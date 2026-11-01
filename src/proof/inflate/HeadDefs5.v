(* inflate(), switch case HEAD (index 0): the pieces of its Clight body (src/inflate/code.v, the
   statement of `(LScons (Some 16180)`), the model's outcomes of its two branches (Model.v c_HEAD), and
   c_HEAD split along the code. *)
Require Import VST.floyd.proofauto.
Require Zlib.units.Inflate.
Require Import Zlib.inflate.code.
Require Import Zlib.proof.inflate.CaseHyps5.
Require Import Zlib.proof.inflate.NeedBits.
#[local] Existing Instance Zlib.units.Inflate.CS.

(* if (state->wrap == 0) { state->mode = TYPEDO; break; } *)
Definition head_WRAP : statement :=
  (Ssequence (Sset _t'443 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct
  _inflate_state noattr)) _wrap tint)) (Sifthenelse (Ebinop Oeq (Etempvar _t'443 tint) (Econst_int (Int.repr 0)
  tint) tint) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _mode tint) (Econst_int (Int.repr 16192) tint)) Sbreak) Sskip)).

(* t'7 = (state->wrap & 2) && hold == 0x8b1f *)
Definition head_W7 : statement :=
  (Ssequence (Sset _t'441 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct
  _inflate_state noattr)) _wrap tint)) (Sifthenelse (Ebinop Oand (Etempvar _t'441 tint) (Econst_int (Int.repr 2)
  tint) tint) (Sset _t'7 (Ecast (Ebinop Oeq (Etempvar _hold tulong) (Econst_int (Int.repr 35615) tint) tint)
  tbool)) (Sset _t'7 (Econst_int (Int.repr 0) tint)))).

(* the gzip header: wbits, check = crc32(0, hbuf, 2) of the two bytes, INITBITS, mode = FLAGS, break *)
Definition head_GZIP : statement :=
  (Ssequence (Ssequence (Sset _t'440 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _wbits tuint)) (Sifthenelse (Ebinop Oeq (Etempvar _t'440 tuint) (Econst_int
  (Int.repr 0) tint) tint) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _wbits tuint) (Econst_int (Int.repr 15) tint)) Sskip)) (Ssequence (Ssequence
  (Scall (Some _t'5) (Evar _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default))
  ((Econst_long (Int64.repr 0) tlong) :: (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0) tint) ::
  nil)) (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct
  _inflate_state noattr)) _check tulong) (Etempvar _t'5 tulong))) (Ssequence (Sloop (Ssequence (Sassign (Ederef
  (Ebinop Oadd (Evar _hbuf (tarray tuchar 4)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) (Ecast
  (Etempvar _hold tulong) tuchar)) (Ssequence (Sassign (Ederef (Ebinop Oadd (Evar _hbuf (tarray tuchar 4))
  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar) (Ecast (Ebinop Oshr (Etempvar _hold tulong) (Econst_int
  (Int.repr 8) tint) tulong) tuchar)) (Ssequence (Ssequence (Sset _t'439 (Efield (Ederef (Etempvar _state (tptr
  (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong)) (Scall (Some _t'6) (Evar
  _crc32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ((Etempvar _t'439 tulong) ::
  (Evar _hbuf (tarray tuchar 4)) :: (Econst_int (Int.repr 2) tint) :: nil))) (Sassign (Efield (Ederef (Etempvar
  _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong) (Etempvar _t'6
  tulong))))) Sbreak) (Ssequence (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sset _bits (Econst_int (Int.repr 0) tint))) Sbreak) (Ssequence (Sassign (Efield (Ederef (Etempvar _state
  (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Econst_int (Int.repr
  16181) tint)) Sbreak))))).

(* the zlib header: head->done = -1, the checks (mod 31, method, window size), dmax, flags, check and
   strm->adler = adler32(0, NULL, 0), mode = DICTID or TYPE, INITBITS, break *)
Definition head_ZLIB : statement :=
  (Ssequence (Ssequence (Sset _t'437 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Sifthenelse (Ebinop Cop.One
  (Etempvar _t'437 (tptr (Tstruct _gz_header_s noattr))) (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
  tint) (Ssequence (Sset _t'438 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _head (tptr (Tstruct _gz_header_s noattr)))) (Sassign (Efield (Ederef
  (Etempvar _t'438 (tptr (Tstruct _gz_header_s noattr))) (Tstruct _gz_header_s noattr)) _done tint) (Eunop Oneg
  (Econst_int (Int.repr 1) tint) tint))) Sskip)) (Ssequence (Ssequence (Ssequence (Sset _t'436 (Efield (Ederef
  (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _wrap tint))
  (Sifthenelse (Eunop Onotbool (Ebinop Oand (Etempvar _t'436 tint) (Econst_int (Int.repr 1) tint) tint) tint)
  (Sset _t'8 (Econst_int (Int.repr 1) tint)) (Sset _t'8 (Ecast (Ebinop Omod (Ebinop Oadd (Ebinop Oshl (Ebinop
  Oand (Ecast (Etempvar _hold tulong) tuint) (Ebinop Osub (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
  (Econst_int (Int.repr 8) tint) tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) (Econst_int (Int.repr 8)
  tint) tuint) (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 8) tint) tulong) tulong) (Econst_int
  (Int.repr 31) tint) tulong) tbool)))) (Sifthenelse (Etempvar _t'8 tint) (Ssequence (Sassign (Efield (Ederef
  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar)) (Ecast
  (Evar ___stringlit_inflate_18 (tarray tschar 23)) (tptr tschar))) (Ssequence (Sassign (Efield (Ederef
  (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint)
  (Econst_int (Int.repr 16209) tint)) Sbreak)) Sskip)) (Ssequence (Sifthenelse (Ebinop Cop.One (Ebinop Oand (Ecast
  (Etempvar _hold tulong) tuint) (Ebinop Osub (Ebinop Oshl (Econst_int (Int.repr 1) tuint) (Econst_int (Int.repr
  4) tint) tuint) (Econst_int (Int.repr 1) tint) tuint) tuint) (Econst_int (Int.repr 8) tint) tint) (Ssequence
  (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr))
  _msg (tptr tschar)) (Ecast (Evar ___stringlit_inflate_16 (tarray tschar 27)) (tptr tschar))) (Ssequence
  (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state
  noattr)) _mode tint) (Econst_int (Int.repr 16209) tint)) Sbreak)) Sskip) (Ssequence (Sloop (Ssequence (Sset
  _hold (Ebinop Oshr (Etempvar _hold tulong) (Econst_int (Int.repr 4) tint) tulong)) (Sset _bits (Ebinop Osub
  (Etempvar _bits tuint) (Ecast (Econst_int (Int.repr 4) tint) tuint) tuint))) Sbreak) (Ssequence (Sset _len
  (Ebinop Oadd (Ebinop Oand (Ecast (Etempvar _hold tulong) tuint) (Ebinop Osub (Ebinop Oshl (Econst_int
  (Int.repr 1) tuint) (Econst_int (Int.repr 4) tint) tuint) (Econst_int (Int.repr 1) tint) tuint) tuint)
  (Econst_int (Int.repr 8) tint) tuint)) (Ssequence (Ssequence (Sifthenelse (Ebinop Ogt (Etempvar _len tuint)
  (Econst_int (Int.repr 15) tint) tint) (Sset _t'9 (Econst_int (Int.repr 1) tint)) (Ssequence (Sset _t'434
  (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr))
  _wbits tuint)) (Sifthenelse (Ebinop Cop.One (Etempvar _t'434 tuint) (Econst_int (Int.repr 0) tint) tint)
  (Ssequence (Ssequence (Sset _t'435 (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
  (Tstruct _inflate_state noattr)) _wbits tuint)) (Sset _t'9 (Ecast (Ebinop Ogt (Etempvar _len tuint) (Etempvar
  _t'435 tuint) tint) tbool))) (Sset _t'9 (Ecast (Etempvar _t'9 tint) tbool))) (Sset _t'9 (Ecast (Econst_int
  (Int.repr 0) tint) tbool))))) (Sifthenelse (Etempvar _t'9 tint) (Ssequence (Sassign (Efield (Ederef (Etempvar
  _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s noattr)) _msg (tptr tschar)) (Ecast (Evar
  ___stringlit_inflate_19 (tarray tschar 20)) (tptr tschar))) (Ssequence (Sassign (Efield (Ederef (Etempvar
  _state (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Econst_int
  (Int.repr 16209) tint)) Sbreak)) Sskip)) (Ssequence (Ssequence (Sset _t'433 (Efield (Ederef (Etempvar _state
  (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _wbits tuint)) (Sifthenelse (Ebinop
  Oeq (Etempvar _t'433 tuint) (Econst_int (Int.repr 0) tint) tint) (Sassign (Efield (Ederef (Etempvar _state
  (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _wbits tuint) (Etempvar _len tuint))
  Sskip)) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct
  _inflate_state noattr)) _dmax tuint) (Ebinop Oshl (Econst_int (Int.repr 1) tuint) (Etempvar _len tuint)
  tuint)) (Ssequence (Sassign (Efield (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr))) (Tstruct
  _inflate_state noattr)) _flags tint) (Econst_int (Int.repr 0) tint)) (Ssequence (Ssequence (Ssequence
  (Ssequence (Scall (Some _t'10) (Evar _adler32 (Tfunction (tulong :: (tptr tuchar) :: tuint :: nil) tulong
  cc_default)) ((Econst_long (Int64.repr 0) tlong) :: (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0)
  tint) :: nil)) (Sset _t'11 (Ecast (Etempvar _t'10 tulong) tulong))) (Sassign (Efield (Ederef (Etempvar _state
  (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _check tulong) (Etempvar _t'11
  tulong))) (Sassign (Efield (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) (Tstruct _z_stream_s
  noattr)) _adler tulong) (Etempvar _t'11 tulong))) (Ssequence (Ssequence (Sifthenelse (Ebinop Oand (Etempvar
  _hold tulong) (Econst_int (Int.repr 512) tint) tulong) (Sset _t'12 (Ecast (Econst_int (Int.repr 16189) tint)
  tint)) (Sset _t'12 (Ecast (Econst_int (Int.repr 16191) tint) tint))) (Sassign (Efield (Ederef (Etempvar _state
  (tptr (Tstruct _inflate_state noattr))) (Tstruct _inflate_state noattr)) _mode tint) (Etempvar _t'12 tint)))
  (Ssequence (Sloop (Ssequence (Sset _hold (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sset _bits
  (Econst_int (Int.repr 0) tint))) Sbreak) Sbreak)))))))))))).

Lemma case_body0_eq:
  case_body 0 =
  Ssequence head_WRAP
    (Ssequence (needbits_stmt 16 _t'4 _t'442)
      (Ssequence (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)
        (Ssequence (Ssequence head_W7 (Sifthenelse (Etempvar _t'7 tint) head_GZIP Sskip)) head_ZLIB))).
Proof. vm_compute. reflexivity. Qed.

(* the model: the outcome of the gzip branch, from the machine after NEEDBITS(16) *)
Definition head_gzip_m (m: mst) : mst :=
  set_mode (initbits (upd_s m (fun s => set_i_check (set_i_wbits s (if i_wbits s =? 0 then 15 else i_wbits s))
                                                    (ref_crc32 0 (hbytes2 (m_hold m)))))) FLAGS.

(* the outcome of the zlib branch, from the machine after NEEDBITS(16) (Model2.v c_HEAD2's tail, patch F7) *)
Definition head_zlib_out (m: mst) : iout :=
  let s := m_s m in
  let m := if i_head s then upd_h m (fun h => set_h_done h (-1)) else m in
  if orb (Z.land (i_wrap s) 1 =? 0)
         (negb (((m_hold m mod 256) * 256 + Z.shiftr (m_hold m) 8) mod 31 =? 0))
  then IBrk (set_bad m M_hdr_check) else
  if negb (m_hold m mod 16 =? 8) then IBrk (set_bad m M_method) else
  let m := dropbits 4 m in
  let len := m_hold m mod 16 + 8 in
  if orb (15 <? len) (andb (negb (i_wbits (m_s m) =? 0)) (i_wbits (m_s m) <? len)) then IBrk (set_bad m M_wsize) else
  let m := upd_s m (fun s => set_i_wbits s (if i_wbits s =? 0 then len else i_wbits s)) in
  let mode := if Z.land (m_hold m) 512 =? 0 then Zlib.proof.inflate.Model.TYPE else DICTID in
  let m := upd_s m (fun s => set_i_check (set_i_flags (set_i_dmax s (2 ^ len)) 0) 1) in
  IBrk (set_mode (initbits (set_m_adler m 1)) mode).

Lemma c_HEAD_split: forall m,
  i_wrap (m_s m) <> 0 -> m_leave (needbits 16 m) = 0 ->
  c_HEAD2 m =
  (if andb (negb (Z.land (i_wrap (m_s (needbits 16 m))) 2 =? 0)) (m_hold (needbits 16 m) =? 35615)
   then IBrk (head_gzip_m (needbits 16 m)) else head_zlib_out (needbits 16 m)).
Proof.
  intros m Hw HL. unfold c_HEAD2. rewrite (proj2 (Z.eqb_neq _ _) Hw). cbv zeta. rewrite HL.
  reflexivity.
Qed.
