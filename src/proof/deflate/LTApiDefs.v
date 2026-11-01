(** * The model theory of the deflate laws, deflate_api part: the invariants

    [Iapi W HI dict wrap D O fin s tin tout adler]: a live stream between two calls of the API, in one of four
    phases:
    - [ph0] fresh: status INIT (raw / zlib) or GZIP, nothing consumed or produced, nothing pending, the
      dictionary (if any) in the window: strstart = block_start, <> 0 exactly with a dictionary;
    - [ph1] in the middle of a gzip header ([HI]): the first [k] bytes of the header [H] are [O ++ pend s];
    - [ph2] BUSY: [O ++ pend s] is the header [H] (see [hdr_good]) followed by any bytes; strm->adler is the
      check value of the data [D];
    - [ph3] FINISH: as BUSY, lookahead 0, and once the trailer was put (wrap negated) [O ++ pend s] ends with it.
    Outside [ph0] last_flush <> -2.  As long as no data was consumed ([D = []]), everything read is in blocks
    (lookahead 0, strstart = block_start: deflateSetDictionary on a raw stream needs it).  [Iend s]: after Z_STREAM_END.

    Inside a call ([z] the running stream of the call offered [inb] and [aout] bytes of output space):
    [zrun inb aout tin tout z] and [Mid] = [Iapi] of the data consumed and output produced so far. *)
From Coq Require Import ZArith List Lia Bool.
Require Import VST.zlist.sublist.
Require Export Zlib.proof.deflate.LTIface.
Require Zlib.proof.crc32.Combine.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope cmodel_scope.

Notation radler := Zlib.proof.adler32.Model.ref_adler32.
Notation rcrc := Zlib.proof.crc32.Model.ref_crc32.

(** ** The header and the trailer *)

(** What final_ok needs of the header [H] at the start of the output. *)
Definition hdr_good (dict : list Z) (wrap : Z) (H : list Z) : Prop :=
  bytes H /\
  (wrap = 0 -> H = []) /\
  (wrap = 1 ->
     Zlength H = (match dict with [] => 2 | _ => 6 end) /\
     Z.land (Znth 0 H) 15 = 8 /\ Z.shiftr (Znth 0 H) 4 <= 7 /\ (Znth 0 H * 256 + Znth 1 H) mod 31 = 0 /\
     (Z.land (Znth 1 H) 32 <> 0 <-> dict <> []) /\
     (dict <> [] -> be32 (sublist 2 6 H) = radler 1 dict)) /\
  (wrap = 2 -> 10 <= Zlength H /\ sublist 0 3 H = [31; 139; 8]).

(** The trailer deflate() puts: the big-endian Adler-32 (zlib), the little-endian CRC-32 and total_in (gzip). *)
Definition trailer (wrap a t : Z) : list Z :=
  if wrap =? 1 then msb2 (u32 (Z.shiftr a 16)) ++ msb2 (u32 (Z.land a 65535))
  else if wrap =? 2 then
    map u8 [Z.land a 255; Z.land (Z.shiftr a 8) 255; Z.land (Z.shiftr a 16) 255; Z.land (Z.shiftr a 24) 255;
            Z.land t 255; Z.land (Z.shiftr t 8) 255; Z.land (Z.shiftr t 16) 255; Z.land (Z.shiftr t 24) 255]
  else [].

(** strm->adler once the header is done: the check value of the data (raw: anything). *)
Definition chk_ok (wrap : Z) (D : list Z) (adler : Z) : Prop :=
  (wrap = 1 -> adler = radler 1 D) /\ (wrap = 2 -> adler = rcrc 0 D).

(** ** The phases *)
Section Inv.
Variable W : dstate -> Prop.
Variable HI : hdr_inv.

Definition ph0 (dict : list Z) (wrap : Z) (D O : list Z) (s : dstate) (tin adler : Z) : Prop :=
  ((d_status s = INIT_STATE /\ wrap <= 1) \/ (d_status s = GZIP_STATE /\ wrap = 2)) /\
  d_wrap s = wrap /\ D = [] /\ O = [] /\
  d_pending s = 0 /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\ d_lookahead s = 0 /\
  d_strstart s = d_block_start s /\ (d_strstart s = 0 <-> dict = []) /\
  (wrap = 1 -> adler = radler 1 dict).

Definition ph1 (dict : list Z) (wrap : Z) (D O : list Z) (s : dstate) (tin adler : Z) : Prop :=
  wrap = 2 /\ D = [] /\ O <> [] /\ d_bi_valid s = 0 /\ d_sym_next s = 0 /\
  exists H k, HI s adler H k /\ O ++ pend s = sublist 0 k H.

Definition ph2 (dict : list Z) (wrap : Z) (D O : list Z) (s : dstate) (tin adler : Z) : Prop :=
  d_status s = BUSY_STATE /\ d_wrap s = wrap /\ d_bi_valid s <= 7 /\ (wrap <> 0 -> O <> []) /\
  chk_ok wrap D adler /\
  exists H body, hdr_good dict wrap H /\ O ++ pend s = H ++ body.

Definition ph3 (dict : list Z) (wrap : Z) (D O : list Z) (s : dstate) (tin adler : Z) : Prop :=
  d_status s = FINISH_STATE /\ d_lookahead s = 0 /\ d_sym_next s = 0 /\ d_bi_valid s <= 7 /\
  (wrap <> 0 -> O <> []) /\ chk_ok wrap D adler /\
  exists H body, hdr_good dict wrap H /\
    ((d_wrap s = wrap /\ O ++ pend s = H ++ body) \/
     (0 < wrap /\ d_wrap s = - wrap /\ O ++ pend s = H ++ body ++ trailer wrap adler tin)).

Definition Iapi : api_inv := fun dict wrap D O fin s tin tout adler =>
  W s /\ outok s /\ 0 <= wrap <= 2 /\ (wrap = 2 -> dict = []) /\ bytes dict /\ Zlength dict <= 32768 /\
  -2 <= d_last_flush s <= 5 /\ (forall h, d_gzhead s = Some h -> hdr_ok h) /\
  tout = Zlength O /\ bytes O /\ bytes D /\ Zlength D <= tin <= Zlength D + Zlength dict /\
  (d_status s = FINISH_STATE -> fin = Some []) /\
  (D = [] -> d_lookahead s = 0 /\ d_strstart s = d_block_start s /\ (dict = [] -> d_strstart s = 0)) /\
  (ph0 dict wrap D O s tin adler \/
   (d_last_flush s <> -2 /\
    (ph1 dict wrap D O s tin adler \/ ph2 dict wrap D O s tin adler \/ ph3 dict wrap D O s tin adler))).

End Inv.

Definition Iend (s : dstate) : Prop :=
  d_status s = FINISH_STATE /\ d_wrap s <= 0 /\ d_pending s = 0 /\ d_lookahead s = 0 /\
  -2 <= d_last_flush s <= 5.

(** ** Inside a call *)

(** The running stream of a call offered the whole object [inb] and [aout] bytes of output space. *)
Definition zrun (inb : list Z) (aout tin tout : Z) (z : strm) : Prop :=
  z_in z = inb /\ 0 <= z_next_in z <= Zlength inb /\ z_avail_in z = Zlength inb - z_next_in z /\
  z_total_in z = tin + z_next_in z /\
  0 <= z_avail_out z /\ Zlength (z_out z) = aout - z_avail_out z /\ z_total_out z = tout + Zlength (z_out z) /\
  bytes (z_out z).

(** [fin] at the end of a call with [flush] whose input not yet consumed is [inb] from [z_next_in z] on. *)
Definition fin_of (flush : Z) (inb : list Z) (z : strm) : option (list Z) :=
  if flush =? Z_FINISH then Some (sublist (z_next_in z) (Zlength inb) inb) else None.

(** The invariant in the middle of a call: [Iapi] of all the data consumed and the output produced so far. *)
Definition Mid (W : dstate -> Prop) (HI : hdr_inv) (dict : list Z) (wrap : Z) (D O : list Z)
    (inb : list Z) (aout tin tout flush : Z) (s : dstate) (z : strm) : Prop :=
  zrun inb aout tin tout z /\ Zlength D + Zlength inb <= 1048576 /\ Zlength O + aout <= 4194304 /\
  Iapi W HI dict wrap (D ++ sublist 0 (z_next_in z) inb) (O ++ z_out z) (fin_of flush inb z) s
       (z_total_in z) (z_total_out z) (z_adler z).

(** The block_done branch of the compression stage ([c_deflate_compress], verbatim). *)
Definition bd_tail (s : dstate) (z : strm) (flush : Z) : option dres :=
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
  if z_avail_out z =? 0 then Some (set_d_last_flush s (-1), z, Some Z_OK) else Some (s, z, None).
