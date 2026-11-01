(* What inflate.c's functions do with a caller-supplied allocator (src/proof/zutil/ZAlloc.v), as the events of
   its trace: the specifications of the allocator-generic port (src/proof/za/inflate_api/Spec5.v, generated
   with docs/port-za/cfg_inflate.py) append these lists to the allocator's trace.

   inflate.c allocates two blocks: the struct inflate_state (inflateInit2_, 7160 bytes) and the window
   (2^wbits bytes, allocated lazily by updatewindow when inflate() has output to keep or
   inflateSetDictionary has a dictionary); inflateReset2 frees the window when the window size changes,
   inflateReset when the window size comes from each header (bit 3 of wrap, patch F8),
   inflateInit2_ frees the state when inflateReset2 rejects windowBits, inflateEnd frees the window (if
   allocated) and then the state.  An allocation that fails is the event ZFail: inflateInit2_ then returns
   Z_MEM_ERROR, and updatewindow returns 1, after which inflate() and inflateSetDictionary set the mode MEM
   and return Z_MEM_ERROR (inflate() in mode MEM returns Z_MEM_ERROR again, allocating nothing;
   inflateSetDictionary on a raw stream in mode MEM tries again). *)
Require Import VST.floyd.proofauto.
Require Import Zlib.proof.zutil.ZAlloc.
Require Import Zlib.proof.inflate.Model.
Require Import Zlib.proof.inflate_api.ApiModel.

(* sizeof(struct inflate_state) (Spec5.state_pad: the last member ends at 7156, 4 bytes of padding) *)
Definition state_size : Z := 7160.

(* updatewindow on a state s that returned r: the window allocated when there was none and r = 0, a failed
   allocation when there was none and r <> 0 *)
Definition uw_ev (s : istate) (r : Z) : list zev :=
  if i_win s then [] else if r =? 0 then [ZAlloc (2 ^ i_wbits s)] else [ZFail].

(* a call of inflate() that took the state s to s': the window allocated in between, or the allocation of
   the window that failed (the call entered the mode MEM) *)
Definition win_ev (s s' : istate) : list zev :=
  if andb (negb (i_win s)) (i_win s') then [ZAlloc (2 ^ i_wbits s')]
  else if andb (negb (i_win s)) (andb (i_mode s' =? MEM) (negb (i_mode s =? MEM))) then [ZFail]
  else [].

(* inflateSetDictionary with the dictionary dict on the state s, alloc_ok the outcome of the window's allocation:
   only a state that takes the dictionary (setdict_check = SDUpdate, also a raw stream in mode MEM) and has no
   window allocates one, which succeeds or fails *)
Definition dict_ev (s : istate) (dict : list Z) (alloc_ok : bool) : list zev :=
  match setdict_check s dict with
  | SDUpdate => if i_win s then [] else if alloc_ok then [ZAlloc (2 ^ i_wbits s)] else [ZFail]
  | _ => []
  end.

(* inflateInit2_(strm, w, version, stream_size) returning init_ret: the state allocated when the version and
   the stream are accepted and the allocation succeeds (alloc_ok), freed again when w is rejected; the failed
   allocation when it does not *)
Definition init_ev (strm_null : bool) (c ssize w : Z) (alloc_ok : bool) : list zev :=
  if orb (negb (c =? 49)) (negb (ssize =? 112)) then []
  else if strm_null then []
  else if negb alloc_ok then [ZFail]
  else if wbits_ok w then [ZAlloc state_size] else [ZAlloc state_size; ZFree state_size].

(* inflateReset on the state s: the window freed when allocated and bit 3 of wrap is set (patch F8) *)
Definition reset_ev (s : istate) : list zev :=
  if andb (negb (Z.land (i_wrap s) 8 =? 0)) (i_win s) then [ZFree (2 ^ i_wbits s)] else [].

(* inflateReset2 on the state s with windowBits w: the window freed when allocated and its size changes, or by
   its inflateReset call when windowBits asks for the size of the header (wb = 0: bit 3 set, patch F8) *)
Definition reset2_ev (s : istate) (w : Z) : list zev :=
  match reset2_wb w with
  | Some (_, wb) =>
      if andb (i_win s) (orb (negb (i_wbits s =? wb)) (wb =? 0)) then [ZFree (2 ^ i_wbits s)] else []
  | None => []
  end.

(* inflateEnd on a live state s: the window (when allocated), then the state *)
Definition end_ev (s : istate) : list zev :=
  (if i_win s then [ZFree (2 ^ i_wbits s)] else []) ++ [ZFree state_size].
