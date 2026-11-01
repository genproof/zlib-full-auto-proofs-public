From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "trees.c".
  Definition normalized := true.
End Info.

Definition __anon_2c403fe6f6d2 : ident := $"_anon_2c403fe6f6d2".
Definition __anon_7a8a915e1e8b : ident := $"_anon_7a8a915e1e8b".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition __dist_code : ident := $"_dist_code".
Definition __length_code : ident := $"_length_code".
Definition __tr_align : ident := $"_tr_align".
Definition __tr_flush_bits : ident := $"_tr_flush_bits".
Definition __tr_flush_block : ident := $"_tr_flush_block".
Definition __tr_init : ident := $"_tr_init".
Definition __tr_stored_block : ident := $"_tr_stored_block".
Definition __tr_tally : ident := $"_tr_tally".
Definition _adler : ident := $"adler".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _base : ident := $"base".
Definition _base_dist : ident := $"base_dist".
Definition _base_length : ident := $"base_length".
Definition _bi_buf : ident := $"bi_buf".
Definition _bi_flush : ident := $"bi_flush".
Definition _bi_reverse : ident := $"bi_reverse".
Definition _bi_used : ident := $"bi_used".
Definition _bi_valid : ident := $"bi_valid".
Definition _bi_windup : ident := $"bi_windup".
Definition _bits : ident := $"bits".
Definition _bl_count : ident := $"bl_count".
Definition _bl_desc : ident := $"bl_desc".
Definition _bl_order : ident := $"bl_order".
Definition _bl_tree : ident := $"bl_tree".
Definition _blcodes : ident := $"blcodes".
Definition _block_mask : ident := $"block_mask".
Definition _block_start : ident := $"block_start".
Definition _buf : ident := $"buf".
Definition _build_bl_tree : ident := $"build_bl_tree".
Definition _build_tree : ident := $"build_tree".
Definition _code : ident := $"code".
Definition _comm_max : ident := $"comm_max".
Definition _comment : ident := $"comment".
Definition _compress_block : ident := $"compress_block".
Definition _count : ident := $"count".
Definition _ct_data_s : ident := $"ct_data_s".
Definition _curlen : ident := $"curlen".
Definition _d_desc : ident := $"d_desc".
Definition _dad : ident := $"dad".
Definition _data_type : ident := $"data_type".
Definition _dcodes : ident := $"dcodes".
Definition _depth : ident := $"depth".
Definition _desc : ident := $"desc".
Definition _detect_data_type : ident := $"detect_data_type".
Definition _dist : ident := $"dist".
Definition _dl : ident := $"dl".
Definition _done : ident := $"done".
Definition _dtree : ident := $"dtree".
Definition _dyn_dtree : ident := $"dyn_dtree".
Definition _dyn_ltree : ident := $"dyn_ltree".
Definition _dyn_tree : ident := $"dyn_tree".
Definition _elems : ident := $"elems".
Definition _extra : ident := $"extra".
Definition _extra_base : ident := $"extra_base".
Definition _extra_bits : ident := $"extra_bits".
Definition _extra_blbits : ident := $"extra_blbits".
Definition _extra_dbits : ident := $"extra_dbits".
Definition _extra_lbits : ident := $"extra_lbits".
Definition _extra_len : ident := $"extra_len".
Definition _extra_max : ident := $"extra_max".
Definition _f : ident := $"f".
Definition _fc : ident := $"fc".
Definition _freq : ident := $"freq".
Definition _gen_bitlen : ident := $"gen_bitlen".
Definition _gen_codes : ident := $"gen_codes".
Definition _good_match : ident := $"good_match".
Definition _gz_header_s : ident := $"gz_header_s".
Definition _gzhead : ident := $"gzhead".
Definition _gzindex : ident := $"gzindex".
Definition _h : ident := $"h".
Definition _hash_bits : ident := $"hash_bits".
Definition _hash_mask : ident := $"hash_mask".
Definition _hash_shift : ident := $"hash_shift".
Definition _hash_size : ident := $"hash_size".
Definition _hcrc : ident := $"hcrc".
Definition _head : ident := $"head".
Definition _heap : ident := $"heap".
Definition _heap_len : ident := $"heap_len".
Definition _heap_max : ident := $"heap_max".
Definition _high_water : ident := $"high_water".
Definition _init_block : ident := $"init_block".
Definition _ins_h : ident := $"ins_h".
Definition _insert : ident := $"insert".
Definition _internal_state : ident := $"internal_state".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _l_desc : ident := $"l_desc".
Definition _last : ident := $"last".
Definition _last_flush : ident := $"last_flush".
Definition _lc : ident := $"lc".
Definition _lcodes : ident := $"lcodes".
Definition _len : ident := $"len".
Definition _len__1 : ident := $"len__1".
Definition _len__2 : ident := $"len__2".
Definition _len__3 : ident := $"len__3".
Definition _len__4 : ident := $"len__4".
Definition _len__5 : ident := $"len__5".
Definition _len__6 : ident := $"len__6".
Definition _len__7 : ident := $"len__7".
Definition _level : ident := $"level".
Definition _lit_bufsize : ident := $"lit_bufsize".
Definition _lookahead : ident := $"lookahead".
Definition _ltree : ident := $"ltree".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _match_available : ident := $"match_available".
Definition _match_length : ident := $"match_length".
Definition _match_start : ident := $"match_start".
Definition _matches : ident := $"matches".
Definition _max_blindex : ident := $"max_blindex".
Definition _max_chain_length : ident := $"max_chain_length".
Definition _max_code : ident := $"max_code".
Definition _max_count : ident := $"max_count".
Definition _max_lazy_match : ident := $"max_lazy_match".
Definition _max_length : ident := $"max_length".
Definition _memcpy : ident := $"memcpy".
Definition _method : ident := $"method".
Definition _min_count : ident := $"min_count".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _name : ident := $"name".
Definition _name_max : ident := $"name_max".
Definition _next_code : ident := $"next_code".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nextlen : ident := $"nextlen".
Definition _nice_match : ident := $"nice_match".
Definition _node : ident := $"node".
Definition _opaque : ident := $"opaque".
Definition _opt_len : ident := $"opt_len".
Definition _opt_lenb : ident := $"opt_lenb".
Definition _os : ident := $"os".
Definition _overflow : ident := $"overflow".
Definition _pending : ident := $"pending".
Definition _pending_buf : ident := $"pending_buf".
Definition _pending_buf_size : ident := $"pending_buf_size".
Definition _pending_out : ident := $"pending_out".
Definition _pqdownheap : ident := $"pqdownheap".
Definition _prev : ident := $"prev".
Definition _prev_length : ident := $"prev_length".
Definition _prev_match : ident := $"prev_match".
Definition _prevlen : ident := $"prevlen".
Definition _rank : ident := $"rank".
Definition _res : ident := $"res".
Definition _reserved : ident := $"reserved".
Definition _s : ident := $"s".
Definition _scan_tree : ident := $"scan_tree".
Definition _send_all_trees : ident := $"send_all_trees".
Definition _send_tree : ident := $"send_tree".
Definition _slid : ident := $"slid".
Definition _stat_desc : ident := $"stat_desc".
Definition _state : ident := $"state".
Definition _static_bl_desc : ident := $"static_bl_desc".
Definition _static_d_desc : ident := $"static_d_desc".
Definition _static_dtree : ident := $"static_dtree".
Definition _static_l_desc : ident := $"static_l_desc".
Definition _static_len : ident := $"static_len".
Definition _static_lenb : ident := $"static_lenb".
Definition _static_ltree : ident := $"static_ltree".
Definition _static_tree : ident := $"static_tree".
Definition _static_tree_desc_s : ident := $"static_tree_desc_s".
Definition _status : ident := $"status".
Definition _stored_len : ident := $"stored_len".
Definition _strategy : ident := $"strategy".
Definition _stree : ident := $"stree".
Definition _strm : ident := $"strm".
Definition _strstart : ident := $"strstart".
Definition _sx : ident := $"sx".
Definition _sym_buf : ident := $"sym_buf".
Definition _sym_end : ident := $"sym_end".
Definition _sym_next : ident := $"sym_next".
Definition _text : ident := $"text".
Definition _time : ident := $"time".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _tr_static_init : ident := $"tr_static_init".
Definition _tree : ident := $"tree".
Definition _tree_desc_s : ident := $"tree_desc_s".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _val__1 : ident := $"val__1".
Definition _val__2 : ident := $"val__2".
Definition _val__3 : ident := $"val__3".
Definition _val__4 : ident := $"val__4".
Definition _val__5 : ident := $"val__5".
Definition _val__6 : ident := $"val__6".
Definition _val__7 : ident := $"val__7".
Definition _w_bits : ident := $"w_bits".
Definition _w_mask : ident := $"w_mask".
Definition _w_size : ident := $"w_size".
Definition _window : ident := $"window".
Definition _window_size : ident := $"window_size".
Definition _wrap : ident := $"wrap".
Definition _xbits : ident := $"xbits".
Definition _xflags : ident := $"xflags".
Definition _z_stream_s : ident := $"z_stream_s".
Definition _zalloc : ident := $"zalloc".
Definition _zfree : ident := $"zfree".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'100 : ident := 227%positive.
Definition _t'101 : ident := 228%positive.
Definition _t'102 : ident := 229%positive.
Definition _t'103 : ident := 230%positive.
Definition _t'104 : ident := 231%positive.
Definition _t'105 : ident := 232%positive.
Definition _t'106 : ident := 233%positive.
Definition _t'107 : ident := 234%positive.
Definition _t'108 : ident := 235%positive.
Definition _t'109 : ident := 236%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'110 : ident := 237%positive.
Definition _t'111 : ident := 238%positive.
Definition _t'112 : ident := 239%positive.
Definition _t'113 : ident := 240%positive.
Definition _t'114 : ident := 241%positive.
Definition _t'115 : ident := 242%positive.
Definition _t'116 : ident := 243%positive.
Definition _t'117 : ident := 244%positive.
Definition _t'118 : ident := 245%positive.
Definition _t'119 : ident := 246%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'120 : ident := 247%positive.
Definition _t'121 : ident := 248%positive.
Definition _t'122 : ident := 249%positive.
Definition _t'123 : ident := 250%positive.
Definition _t'124 : ident := 251%positive.
Definition _t'125 : ident := 252%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
Definition _t'75 : ident := 202%positive.
Definition _t'76 : ident := 203%positive.
Definition _t'77 : ident := 204%positive.
Definition _t'78 : ident := 205%positive.
Definition _t'79 : ident := 206%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'80 : ident := 207%positive.
Definition _t'81 : ident := 208%positive.
Definition _t'82 : ident := 209%positive.
Definition _t'83 : ident := 210%positive.
Definition _t'84 : ident := 211%positive.
Definition _t'85 : ident := 212%positive.
Definition _t'86 : ident := 213%positive.
Definition _t'87 : ident := 214%positive.
Definition _t'88 : ident := 215%positive.
Definition _t'89 : ident := 216%positive.
Definition _t'9 : ident := 136%positive.
Definition _t'90 : ident := 217%positive.
Definition _t'91 : ident := 218%positive.
Definition _t'92 : ident := 219%positive.
Definition _t'93 : ident := 220%positive.
Definition _t'94 : ident := 221%positive.
Definition _t'95 : ident := 222%positive.
Definition _t'96 : ident := 223%positive.
Definition _t'97 : ident := 224%positive.
Definition _t'98 : ident := 225%positive.
Definition _t'99 : ident := 226%positive.

Definition v_extra_lbits := {|
  gvar_info := (tarray tint 29);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 2) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 2) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 4) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 4) ::
                Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 5) ::
                Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 5) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_extra_dbits := {|
  gvar_info := (tarray tint 30);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 2) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 4) ::
                Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 5) ::
                Init_int32 (Int.repr 6) :: Init_int32 (Int.repr 6) ::
                Init_int32 (Int.repr 7) :: Init_int32 (Int.repr 7) ::
                Init_int32 (Int.repr 8) :: Init_int32 (Int.repr 8) ::
                Init_int32 (Int.repr 9) :: Init_int32 (Int.repr 9) ::
                Init_int32 (Int.repr 10) :: Init_int32 (Int.repr 10) ::
                Init_int32 (Int.repr 11) :: Init_int32 (Int.repr 11) ::
                Init_int32 (Int.repr 12) :: Init_int32 (Int.repr 12) ::
                Init_int32 (Int.repr 13) :: Init_int32 (Int.repr 13) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_extra_blbits := {|
  gvar_info := (tarray tint 19);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 7) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_bl_order := {|
  gvar_info := (tarray tuchar 19);
  gvar_init := (Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 15) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_static_ltree := {|
  gvar_info := (tarray (Tstruct _ct_data_s noattr) 288);
  gvar_init := (Init_int16 (Int.repr 12) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 140) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 76) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 204) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 44) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 172) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 108) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 236) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 28) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 156) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 92) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 220) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 60) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 188) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 124) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 252) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 130) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 66) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 194) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 34) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 162) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 98) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 226) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 146) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 82) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 210) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 50) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 178) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 114) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 242) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 10) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 138) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 74) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 202) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 42) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 170) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 106) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 234) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 26) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 154) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 90) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 218) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 58) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 186) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 122) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 250) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 6) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 134) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 70) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 198) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 38) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 166) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 102) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 230) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 22) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 150) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 86) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 214) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 54) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 182) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 118) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 246) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 14) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 142) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 78) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 206) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 46) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 174) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 110) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 238) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 30) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 158) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 94) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 222) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 62) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 190) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 126) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 254) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 129) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 65) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 193) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 33) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 161) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 97) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 225) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 145) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 81) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 209) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 49) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 177) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 113) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 241) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 9) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 137) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 73) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 201) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 41) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 169) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 105) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 233) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 25) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 153) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 89) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 217) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 57) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 185) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 121) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 249) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 5) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 133) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 69) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 197) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 37) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 165) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 101) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 229) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 21) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 149) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 85) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 213) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 53) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 181) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 117) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 245) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 13) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 141) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 77) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 205) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 45) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 173) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 109) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 237) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 29) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 157) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 93) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 221) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 61) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 189) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 125) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 253) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 275) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 147) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 403) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 83) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 339) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 211) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 467) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 51) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 307) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 179) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 435) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 115) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 371) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 243) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 499) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 11) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 267) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 139) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 395) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 75) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 331) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 203) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 459) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 43) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 299) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 171) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 427) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 107) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 363) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 235) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 491) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 27) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 283) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 155) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 411) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 91) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 347) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 219) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 475) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 59) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 315) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 187) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 443) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 123) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 379) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 251) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 507) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 7) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 263) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 135) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 391) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 71) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 327) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 199) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 455) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 39) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 295) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 167) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 423) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 103) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 359) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 231) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 487) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 23) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 279) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 151) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 407) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 87) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 343) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 215) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 471) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 55) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 311) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 183) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 439) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 119) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 375) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 247) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 503) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 15) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 271) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 143) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 399) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 79) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 335) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 207) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 463) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 47) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 303) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 175) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 431) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 111) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 367) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 239) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 495) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 31) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 287) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 159) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 415) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 95) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 351) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 223) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 479) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 63) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 319) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 191) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 447) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 127) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 383) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 255) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 511) :: Init_int16 (Int.repr 9) ::
                Init_int16 (Int.repr 0) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 64) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 32) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 96) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 80) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 48) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 112) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 8) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 72) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 40) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 104) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 24) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 88) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 56) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 120) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 4) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 68) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 36) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 100) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 20) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 84) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 52) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 116) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 3) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 131) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 67) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 195) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 35) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 163) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 99) :: Init_int16 (Int.repr 8) ::
                Init_int16 (Int.repr 227) :: Init_int16 (Int.repr 8) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_static_dtree := {|
  gvar_info := (tarray (Tstruct _ct_data_s noattr) 30);
  gvar_init := (Init_int16 (Int.repr 0) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 8) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 24) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 4) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 20) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 12) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 28) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 2) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 10) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 26) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 6) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 22) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 14) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 30) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 1) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 17) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 9) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 25) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 5) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 21) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 13) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 29) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 3) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 19) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 11) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 27) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 7) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 23) :: Init_int16 (Int.repr 5) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v__dist_code := {|
  gvar_info := (tarray tuchar 512);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 0) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 28) :: Init_int8 (Int.repr 28) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 29) :: Init_int8 (Int.repr 29) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v__length_code := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 9) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 11) :: Init_int8 (Int.repr 11) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 12) :: Init_int8 (Int.repr 12) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 13) :: Init_int8 (Int.repr 13) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 14) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 15) :: Init_int8 (Int.repr 15) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 16) :: Init_int8 (Int.repr 16) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 17) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 18) :: Init_int8 (Int.repr 18) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 19) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 20) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 21) :: Init_int8 (Int.repr 21) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 22) :: Init_int8 (Int.repr 22) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 23) :: Init_int8 (Int.repr 23) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 24) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 26) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 27) ::
                Init_int8 (Int.repr 27) :: Init_int8 (Int.repr 28) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_base_length := {|
  gvar_info := (tarray tint 29);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 5) ::
                Init_int32 (Int.repr 6) :: Init_int32 (Int.repr 7) ::
                Init_int32 (Int.repr 8) :: Init_int32 (Int.repr 10) ::
                Init_int32 (Int.repr 12) :: Init_int32 (Int.repr 14) ::
                Init_int32 (Int.repr 16) :: Init_int32 (Int.repr 20) ::
                Init_int32 (Int.repr 24) :: Init_int32 (Int.repr 28) ::
                Init_int32 (Int.repr 32) :: Init_int32 (Int.repr 40) ::
                Init_int32 (Int.repr 48) :: Init_int32 (Int.repr 56) ::
                Init_int32 (Int.repr 64) :: Init_int32 (Int.repr 80) ::
                Init_int32 (Int.repr 96) :: Init_int32 (Int.repr 112) ::
                Init_int32 (Int.repr 128) :: Init_int32 (Int.repr 160) ::
                Init_int32 (Int.repr 192) :: Init_int32 (Int.repr 224) ::
                Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_base_dist := {|
  gvar_info := (tarray tint 30);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 2) :: Init_int32 (Int.repr 3) ::
                Init_int32 (Int.repr 4) :: Init_int32 (Int.repr 6) ::
                Init_int32 (Int.repr 8) :: Init_int32 (Int.repr 12) ::
                Init_int32 (Int.repr 16) :: Init_int32 (Int.repr 24) ::
                Init_int32 (Int.repr 32) :: Init_int32 (Int.repr 48) ::
                Init_int32 (Int.repr 64) :: Init_int32 (Int.repr 96) ::
                Init_int32 (Int.repr 128) :: Init_int32 (Int.repr 192) ::
                Init_int32 (Int.repr 256) :: Init_int32 (Int.repr 384) ::
                Init_int32 (Int.repr 512) :: Init_int32 (Int.repr 768) ::
                Init_int32 (Int.repr 1024) :: Init_int32 (Int.repr 1536) ::
                Init_int32 (Int.repr 2048) :: Init_int32 (Int.repr 3072) ::
                Init_int32 (Int.repr 4096) :: Init_int32 (Int.repr 6144) ::
                Init_int32 (Int.repr 8192) :: Init_int32 (Int.repr 12288) ::
                Init_int32 (Int.repr 16384) :: Init_int32 (Int.repr 24576) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_static_l_desc := {|
  gvar_info := (Tstruct _static_tree_desc_s noattr);
  gvar_init := (Init_addrof _static_ltree (Ptrofs.repr 0) ::
                Init_addrof _extra_lbits (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 257) :: Init_int32 (Int.repr 286) ::
                Init_int32 (Int.repr 15) :: Init_space 4 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_static_d_desc := {|
  gvar_info := (Tstruct _static_tree_desc_s noattr);
  gvar_init := (Init_addrof _static_dtree (Ptrofs.repr 0) ::
                Init_addrof _extra_dbits (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 30) ::
                Init_int32 (Int.repr 15) :: Init_space 4 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_static_bl_desc := {|
  gvar_info := (Tstruct _static_tree_desc_s noattr);
  gvar_init := (Init_int64 (Int64.repr 0) ::
                Init_addrof _extra_blbits (Ptrofs.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 19) ::
                Init_int32 (Int.repr 7) :: Init_space 4 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_bi_reverse := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_code, tuint) :: (_len, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_res, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _res (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sloop
      (Ssequence
        (Sset _res
          (Ebinop Oor (Etempvar _res tuint)
            (Ebinop Oand (Etempvar _code tuint)
              (Econst_int (Int.repr 1) tint) tuint) tuint))
        (Ssequence
          (Sset _code
            (Ebinop Oshr (Etempvar _code tuint)
              (Econst_int (Int.repr 1) tint) tuint))
          (Sset _res
            (Ebinop Oshl (Etempvar _res tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ecast
              (Ebinop Osub (Etempvar _len tint)
                (Econst_int (Int.repr 1) tint) tint) tint))
          (Sset _len (Etempvar _t'1 tint)))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          Sskip
          Sbreak)))
    (Sreturn (Some (Ebinop Oshr (Etempvar _res tuint)
                     (Econst_int (Int.repr 1) tint) tuint)))))
|}.

Definition f_bi_flush := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) ::
               (_t'13, tushort) :: (_t'12, (tptr tuchar)) ::
               (_t'11, tushort) :: (_t'10, (tptr tuchar)) ::
               (_t'9, tushort) :: (_t'8, (tptr tuchar)) :: (_t'7, tushort) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'4
    (Efield
      (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
        (Tstruct _internal_state noattr)) _bi_valid tint))
  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                 (Econst_int (Int.repr 16) tint) tint)
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'1 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Ssequence
              (Sset _t'13
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'12 (tptr tuchar))
                    (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oand (Etempvar _t'13 tushort)
                      (Econst_int (Int.repr 255) tint) tint) tuchar) tuchar)))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'2 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'10 (tptr tuchar))
                    (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oshr (Ecast (Etempvar _t'11 tushort) tushort)
                      (Econst_int (Int.repr 8) tint) tint) tuchar) tuchar))))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_buf tushort)
          (Econst_int (Int.repr 0) tint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_valid tint)
          (Econst_int (Int.repr 0) tint))))
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint))
      (Sifthenelse (Ebinop Oge (Etempvar _t'5 tint)
                     (Econst_int (Int.repr 8) tint) tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong)
                (Ebinop Oadd (Etempvar _t'3 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending_buf
                  (tptr tuchar)))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'8 (tptr tuchar))
                      (Etempvar _t'3 tulong) (tptr tuchar)) tuchar)
                  (Ecast (Ecast (Etempvar _t'9 tushort) tuchar) tuchar)))))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort)
                (Ebinop Oshr (Etempvar _t'7 tushort)
                  (Econst_int (Int.repr 8) tint) tint)))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint)
                (Ebinop Osub (Etempvar _t'6 tint)
                  (Econst_int (Int.repr 8) tint) tint)))))
        Sskip))))
|}.

Definition f_bi_windup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) ::
               (_t'12, tushort) :: (_t'11, (tptr tuchar)) ::
               (_t'10, tushort) :: (_t'9, (tptr tuchar)) ::
               (_t'8, tushort) :: (_t'7, (tptr tuchar)) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
          (Tstruct _internal_state noattr)) _bi_valid tint))
    (Sifthenelse (Ebinop Ogt (Etempvar _t'5 tint)
                   (Econst_int (Int.repr 8) tint) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'1 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'11 (tptr tuchar))
                    (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oand (Etempvar _t'12 tushort)
                      (Econst_int (Int.repr 255) tint) tint) tuchar) tuchar)))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'2 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'9 (tptr tuchar))
                    (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oshr (Ecast (Etempvar _t'10 tushort) tushort)
                      (Econst_int (Int.repr 8) tint) tint) tuchar) tuchar))))))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_valid tint))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'6 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong)
                (Ebinop Oadd (Etempvar _t'3 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending_buf
                  (tptr tuchar)))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _t'7 (tptr tuchar))
                      (Etempvar _t'3 tulong) (tptr tuchar)) tuchar)
                  (Ecast (Ecast (Etempvar _t'8 tushort) tuchar) tuchar)))))
          Sskip))))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_used tint)
        (Ebinop Oadd
          (Ebinop Oand
            (Ebinop Osub (Etempvar _t'4 tint) (Econst_int (Int.repr 1) tint)
              tint) (Econst_int (Int.repr 7) tint) tint)
          (Econst_int (Int.repr 1) tint) tint)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_buf tushort)
        (Econst_int (Int.repr 0) tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_gen_codes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tree, (tptr (Tstruct _ct_data_s noattr))) ::
                (_max_code, tint) :: (_bl_count, (tptr tushort)) :: nil);
  fn_vars := ((_next_code, (tarray tushort 16)) :: nil);
  fn_temps := ((_code, tuint) :: (_bits, tint) :: (_n, tint) ::
               (_len, tint) :: (_t'2, tuint) :: (_t'1, tushort) ::
               (_t'3, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _code (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _bits (Econst_int (Int.repr 1) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _bits tint)
                         (Econst_int (Int.repr 15) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _bl_count (tptr tushort))
                    (Ebinop Osub (Etempvar _bits tint)
                      (Econst_int (Int.repr 1) tint) tint) (tptr tushort))
                  tushort))
              (Sset _code
                (Ebinop Oshl
                  (Ebinop Oadd (Etempvar _code tuint) (Etempvar _t'3 tushort)
                    tuint) (Econst_int (Int.repr 1) tint) tuint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _next_code (tarray tushort 16))
                  (Etempvar _bits tint) (tptr tushort)) tushort)
              (Ecast (Etempvar _code tuint) tushort))))
        (Sset _bits
          (Ebinop Oadd (Etempvar _bits tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _n (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _n tint)
                         (Etempvar _max_code tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _len
              (Efield
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                      (Etempvar _n tint) (tptr (Tstruct _ct_data_s noattr)))
                    (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr))
                _len tushort))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _len tint)
                             (Econst_int (Int.repr 0) tint) tint)
                Scontinue
                Sskip)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Ederef
                        (Ebinop Oadd (Evar _next_code (tarray tushort 16))
                          (Etempvar _len tint) (tptr tushort)) tushort))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _next_code (tarray tushort 16))
                          (Etempvar _len tint) (tptr tushort)) tushort)
                      (Ebinop Oadd (Etempvar _t'1 tushort)
                        (Econst_int (Int.repr 1) tint) tint)))
                  (Scall (Some _t'2)
                    (Evar _bi_reverse (Tfunction (tuint :: tint :: nil) tuint
                                        cc_default))
                    ((Etempvar _t'1 tushort) :: (Etempvar _len tint) :: nil)))
                (Sassign
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                          (Etempvar _n tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort)
                  (Ecast (Etempvar _t'2 tuint) tushort))))))
        (Sset _n
          (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_tr_static_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
Sskip
|}.

Definition f_init_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tint) :: (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _n (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                       (Ebinop Oadd
                         (Ebinop Oadd (Econst_int (Int.repr 256) tint)
                           (Econst_int (Int.repr 1) tint) tint)
                         (Econst_int (Int.repr 29) tint) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Efield
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _dyn_ltree
                    (tarray (Tstruct _ct_data_s noattr) 573))
                  (Etempvar _n tint) (tptr (Tstruct _ct_data_s noattr)))
                (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
            tushort) (Econst_int (Int.repr 0) tint)))
      (Sset _n
        (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _n (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                         (Econst_int (Int.repr 30) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Efield
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _dyn_dtree
                      (tarray (Tstruct _ct_data_s noattr) 61))
                    (Etempvar _n tint) (tptr (Tstruct _ct_data_s noattr)))
                  (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
              _freq tushort) (Econst_int (Int.repr 0) tint)))
        (Sset _n
          (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _n (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                           (Econst_int (Int.repr 19) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Efield
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bl_tree
                        (tarray (Tstruct _ct_data_s noattr) 39))
                      (Etempvar _n tint) (tptr (Tstruct _ct_data_s noattr)))
                    (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                _freq tushort) (Econst_int (Int.repr 0) tint)))
          (Sset _n
            (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _dyn_ltree
                    (tarray (Tstruct _ct_data_s noattr) 573))
                  (Econst_int (Int.repr 256) tint)
                  (tptr (Tstruct _ct_data_s noattr)))
                (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
            tushort) (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'1 (Ecast (Econst_long (Int64.repr 0) tlong) tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _static_len tulong)
                (Etempvar _t'1 tulong)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _opt_len tulong)
              (Etempvar _t'1 tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _matches tuint)
                (Etempvar _t'2 tuint)))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _sym_next tuint)
              (Etempvar _t'2 tuint))))))))
|}.

Definition f__tr_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None (Evar _tr_static_init (Tfunction nil tvoid cc_default)) nil)
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _l_desc
          (Tstruct _tree_desc_s noattr)) _dyn_tree
        (tptr (Tstruct _ct_data_s noattr)))
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
          (Tstruct _internal_state noattr)) _dyn_ltree
        (tarray (Tstruct _ct_data_s noattr) 573)))
    (Ssequence
      (Sassign
        (Efield
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _l_desc
            (Tstruct _tree_desc_s noattr)) _stat_desc
          (tptr (Tstruct _static_tree_desc_s noattr)))
        (Eaddrof (Evar _static_l_desc (Tstruct _static_tree_desc_s noattr))
          (tptr (Tstruct _static_tree_desc_s noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _d_desc
              (Tstruct _tree_desc_s noattr)) _dyn_tree
            (tptr (Tstruct _ct_data_s noattr)))
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _dyn_dtree
            (tarray (Tstruct _ct_data_s noattr) 61)))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _d_desc
                (Tstruct _tree_desc_s noattr)) _stat_desc
              (tptr (Tstruct _static_tree_desc_s noattr)))
            (Eaddrof
              (Evar _static_d_desc (Tstruct _static_tree_desc_s noattr))
              (tptr (Tstruct _static_tree_desc_s noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bl_desc
                  (Tstruct _tree_desc_s noattr)) _dyn_tree
                (tptr (Tstruct _ct_data_s noattr)))
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bl_tree
                (tarray (Tstruct _ct_data_s noattr) 39)))
            (Ssequence
              (Sassign
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bl_desc
                    (Tstruct _tree_desc_s noattr)) _stat_desc
                  (tptr (Tstruct _static_tree_desc_s noattr)))
                (Eaddrof
                  (Evar _static_bl_desc (Tstruct _static_tree_desc_s noattr))
                  (tptr (Tstruct _static_tree_desc_s noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_used tint)
                      (Econst_int (Int.repr 0) tint))
                    (Scall None
                      (Evar _init_block (Tfunction
                                          ((tptr (Tstruct _internal_state noattr)) ::
                                           nil) tvoid cc_default))
                      ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                       nil))))))))))))
|}.

Definition f_pqdownheap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_tree, (tptr (Tstruct _ct_data_s noattr))) :: (_k, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_v, tint) :: (_j, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'26, tint) :: (_t'25, tuchar) :: (_t'24, tint) ::
               (_t'23, tuchar) :: (_t'22, tint) :: (_t'21, tushort) ::
               (_t'20, tint) :: (_t'19, tushort) :: (_t'18, tint) ::
               (_t'17, tushort) :: (_t'16, tint) :: (_t'15, tushort) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tuchar) ::
               (_t'11, tint) :: (_t'10, tuchar) :: (_t'9, tushort) ::
               (_t'8, tint) :: (_t'7, tushort) :: (_t'6, tushort) ::
               (_t'5, tint) :: (_t'4, tushort) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _v
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _heap (tarray tint 573))
        (Etempvar _k tint) (tptr tint)) tint))
  (Ssequence
    (Sset _j
      (Ebinop Oshl (Etempvar _k tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'26
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _heap_len tint))
            (Sifthenelse (Ebinop Ole (Etempvar _j tint) (Etempvar _t'26 tint)
                           tint)
              Sskip
              Sbreak))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _heap_len tint))
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Etempvar _t'13 tint) tint)
                  (Ssequence
                    (Sset _t'14
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _heap
                            (tarray tint 573))
                          (Ebinop Oadd (Etempvar _j tint)
                            (Econst_int (Int.repr 1) tint) tint) (tptr tint))
                        tint))
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Etempvar _t'14 tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _fc
                            (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                      (Ssequence
                        (Sset _t'16
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _heap
                                (tarray tint 573)) (Etempvar _j tint)
                              (tptr tint)) tint))
                        (Ssequence
                          (Sset _t'17
                            (Efield
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                    (Etempvar _t'16 tint)
                                    (tptr (Tstruct _ct_data_s noattr)))
                                  (Tstruct _ct_data_s noattr)) _fc
                                (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                          (Sifthenelse (Ebinop Olt (Etempvar _t'15 tushort)
                                         (Etempvar _t'17 tushort) tint)
                            (Sset _t'1
                              (Ecast (Econst_int (Int.repr 1) tint) tbool))
                            (Ssequence
                              (Sset _t'18
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _heap (tarray tint 573))
                                    (Ebinop Oadd (Etempvar _j tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr tint)) tint))
                              (Ssequence
                                (Sset _t'19
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                          (Etempvar _t'18 tint)
                                          (tptr (Tstruct _ct_data_s noattr)))
                                        (Tstruct _ct_data_s noattr)) _fc
                                      (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                                (Ssequence
                                  (Sset _t'20
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _heap (tarray tint 573))
                                        (Etempvar _j tint) (tptr tint)) tint))
                                  (Ssequence
                                    (Sset _t'21
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                              (Etempvar _t'20 tint)
                                              (tptr (Tstruct _ct_data_s noattr)))
                                            (Tstruct _ct_data_s noattr)) _fc
                                          (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                        tushort))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'19 tushort)
                                                   (Etempvar _t'21 tushort)
                                                   tint)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'22
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _heap (tarray tint 573))
                                                  (Ebinop Oadd
                                                    (Etempvar _j tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tint)) tint))
                                            (Ssequence
                                              (Sset _t'23
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _depth
                                                      (tarray tuchar 573))
                                                    (Etempvar _t'22 tint)
                                                    (tptr tuchar)) tuchar))
                                              (Ssequence
                                                (Sset _t'24
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _heap
                                                        (tarray tint 573))
                                                      (Etempvar _j tint)
                                                      (tptr tint)) tint))
                                                (Ssequence
                                                  (Sset _t'25
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _depth
                                                          (tarray tuchar 573))
                                                        (Etempvar _t'24 tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sset _t'1
                                                    (Ecast
                                                      (Ebinop Ole
                                                        (Etempvar _t'23 tuchar)
                                                        (Etempvar _t'25 tuchar)
                                                        tint) tbool))))))
                                          (Sset _t'1
                                            (Ecast (Etempvar _t'1 tint)
                                              tbool)))
                                        (Sset _t'1
                                          (Ecast (Etempvar _t'1 tint) tbool)))
                                      (Ssequence
                                        (Sset _t'1
                                          (Ecast
                                            (Econst_int (Int.repr 0) tint)
                                            tbool))
                                        (Sset _t'1
                                          (Ecast (Etempvar _t'1 tint) tbool)))))))))))))
                  (Sset _t'1 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'1 tint)
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tint)
                    (Econst_int (Int.repr 1) tint) tint))
                Sskip))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                            (Etempvar _v tint)
                            (tptr (Tstruct _ct_data_s noattr)))
                          (Tstruct _ct_data_s noattr)) _fc
                        (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _heap
                            (tarray tint 573)) (Etempvar _j tint)
                          (tptr tint)) tint))
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Etempvar _t'5 tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _fc
                            (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                      (Sifthenelse (Ebinop Olt (Etempvar _t'4 tushort)
                                     (Etempvar _t'6 tushort) tint)
                        (Sset _t'2 (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                    (Etempvar _v tint)
                                    (tptr (Tstruct _ct_data_s noattr)))
                                  (Tstruct _ct_data_s noattr)) _fc
                                (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                          (Ssequence
                            (Sset _t'8
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573)) (Etempvar _j tint)
                                  (tptr tint)) tint))
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                        (Etempvar _t'8 tint)
                                        (tptr (Tstruct _ct_data_s noattr)))
                                      (Tstruct _ct_data_s noattr)) _fc
                                    (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _t'7 tushort)
                                             (Etempvar _t'9 tushort) tint)
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'10
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _depth (tarray tuchar 573))
                                          (Etempvar _v tint) (tptr tuchar))
                                        tuchar))
                                    (Ssequence
                                      (Sset _t'11
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _heap (tarray tint 573))
                                            (Etempvar _j tint) (tptr tint))
                                          tint))
                                      (Ssequence
                                        (Sset _t'12
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _depth (tarray tuchar 573))
                                              (Etempvar _t'11 tint)
                                              (tptr tuchar)) tuchar))
                                        (Sset _t'2
                                          (Ecast
                                            (Ebinop Ole
                                              (Etempvar _t'10 tuchar)
                                              (Etempvar _t'12 tuchar) tint)
                                            tbool)))))
                                  (Sset _t'2
                                    (Ecast (Etempvar _t'2 tint) tbool)))
                                (Sset _t'2
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tbool))))))))))
                (Sifthenelse (Etempvar _t'2 tint) Sbreak Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _heap
                          (tarray tint 573)) (Etempvar _j tint) (tptr tint))
                      tint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _heap
                          (tarray tint 573)) (Etempvar _k tint) (tptr tint))
                      tint) (Etempvar _t'3 tint)))
                (Ssequence
                  (Sset _k (Etempvar _j tint))
                  (Sset _j
                    (Ebinop Oshl (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))
        Sskip)
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _heap (tarray tint 573))
            (Etempvar _k tint) (tptr tint)) tint) (Etempvar _v tint)))))
|}.

Definition f_gen_bitlen := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_desc, (tptr (Tstruct _tree_desc_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tree, (tptr (Tstruct _ct_data_s noattr))) ::
               (_max_code, tint) ::
               (_stree, (tptr (Tstruct _ct_data_s noattr))) ::
               (_extra, (tptr tint)) :: (_base, tint) ::
               (_max_length, tint) :: (_h, tint) :: (_n, tint) ::
               (_m, tint) :: (_bits, tint) :: (_xbits, tint) ::
               (_f, tushort) :: (_overflow, tint) :: (_t'1, tint) ::
               (_t'23, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'22, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'21, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'20, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'19, tint) :: (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, tushort) :: (_t'15, tushort) :: (_t'14, tushort) ::
               (_t'13, tushort) :: (_t'12, tulong) :: (_t'11, tushort) ::
               (_t'10, tulong) :: (_t'9, tushort) :: (_t'8, tushort) ::
               (_t'7, tushort) :: (_t'6, tushort) :: (_t'5, tushort) ::
               (_t'4, tushort) :: (_t'3, tulong) :: (_t'2, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _tree
    (Efield
      (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
        (Tstruct _tree_desc_s noattr)) _dyn_tree
      (tptr (Tstruct _ct_data_s noattr))))
  (Ssequence
    (Sset _max_code
      (Efield
        (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
          (Tstruct _tree_desc_s noattr)) _max_code tint))
    (Ssequence
      (Ssequence
        (Sset _t'23
          (Efield
            (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
              (Tstruct _tree_desc_s noattr)) _stat_desc
            (tptr (Tstruct _static_tree_desc_s noattr))))
        (Sset _stree
          (Efield
            (Ederef
              (Etempvar _t'23 (tptr (Tstruct _static_tree_desc_s noattr)))
              (Tstruct _static_tree_desc_s noattr)) _static_tree
            (tptr (Tstruct _ct_data_s noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'22
            (Efield
              (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
                (Tstruct _tree_desc_s noattr)) _stat_desc
              (tptr (Tstruct _static_tree_desc_s noattr))))
          (Sset _extra
            (Efield
              (Ederef
                (Etempvar _t'22 (tptr (Tstruct _static_tree_desc_s noattr)))
                (Tstruct _static_tree_desc_s noattr)) _extra_bits
              (tptr tint))))
        (Ssequence
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
                  (Tstruct _tree_desc_s noattr)) _stat_desc
                (tptr (Tstruct _static_tree_desc_s noattr))))
            (Sset _base
              (Efield
                (Ederef
                  (Etempvar _t'21 (tptr (Tstruct _static_tree_desc_s noattr)))
                  (Tstruct _static_tree_desc_s noattr)) _extra_base tint)))
          (Ssequence
            (Ssequence
              (Sset _t'20
                (Efield
                  (Ederef
                    (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
                    (Tstruct _tree_desc_s noattr)) _stat_desc
                  (tptr (Tstruct _static_tree_desc_s noattr))))
              (Sset _max_length
                (Efield
                  (Ederef
                    (Etempvar _t'20 (tptr (Tstruct _static_tree_desc_s noattr)))
                    (Tstruct _static_tree_desc_s noattr)) _max_length tint)))
            (Ssequence
              (Sset _overflow (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Ssequence
                  (Sset _bits (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _bits tint)
                                     (Econst_int (Int.repr 15) tint) tint)
                        Sskip
                        Sbreak)
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bl_count
                              (tarray tushort 16)) (Etempvar _bits tint)
                            (tptr tushort)) tushort)
                        (Econst_int (Int.repr 0) tint)))
                    (Sset _bits
                      (Ebinop Oadd (Etempvar _bits tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Ssequence
                    (Sset _t'18
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _heap_max tint))
                    (Ssequence
                      (Sset _t'19
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _heap
                              (tarray tint 573)) (Etempvar _t'18 tint)
                            (tptr tint)) tint))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Etempvar _t'19 tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _dl
                            (Tunion __anon_7a8a915e1e8b noattr)) _len tushort)
                        (Econst_int (Int.repr 0) tint))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'17
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _heap_max
                            tint))
                        (Sset _h
                          (Ebinop Oadd (Etempvar _t'17 tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _h tint)
                                         (Ebinop Oadd
                                           (Ebinop Omul
                                             (Econst_int (Int.repr 2) tint)
                                             (Ebinop Oadd
                                               (Ebinop Oadd
                                                 (Econst_int (Int.repr 256) tint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)
                                               (Econst_int (Int.repr 29) tint)
                                               tint) tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _n
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573)) (Etempvar _h tint)
                                  (tptr tint)) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                          (Etempvar _n tint)
                                          (tptr (Tstruct _ct_data_s noattr)))
                                        (Tstruct _ct_data_s noattr)) _dl
                                      (Tunion __anon_7a8a915e1e8b noattr)) _dad tushort))
                                (Ssequence
                                  (Sset _t'16
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                            (Etempvar _t'15 tushort)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _dl
                                        (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                                  (Sset _bits
                                    (Ebinop Oadd (Etempvar _t'16 tushort)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _bits tint)
                                               (Etempvar _max_length tint)
                                               tint)
                                  (Ssequence
                                    (Sset _bits (Etempvar _max_length tint))
                                    (Sset _overflow
                                      (Ebinop Oadd (Etempvar _overflow tint)
                                        (Econst_int (Int.repr 1) tint) tint)))
                                  Sskip)
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                            (Etempvar _n tint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _dl
                                        (Tunion __anon_7a8a915e1e8b noattr)) _len tushort)
                                    (Ecast (Etempvar _bits tint) tushort))
                                  (Ssequence
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _n tint)
                                                   (Etempvar _max_code tint)
                                                   tint)
                                      Scontinue
                                      Sskip)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'14
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bl_count
                                                (tarray tushort 16))
                                              (Etempvar _bits tint)
                                              (tptr tushort)) tushort))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bl_count
                                                (tarray tushort 16))
                                              (Etempvar _bits tint)
                                              (tptr tushort)) tushort)
                                          (Ebinop Oadd
                                            (Etempvar _t'14 tushort)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))
                                      (Ssequence
                                        (Sset _xbits
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oge
                                                         (Etempvar _n tint)
                                                         (Etempvar _base tint)
                                                         tint)
                                            (Sset _xbits
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _extra (tptr tint))
                                                  (Ebinop Osub
                                                    (Etempvar _n tint)
                                                    (Etempvar _base tint)
                                                    tint) (tptr tint)) tint))
                                            Sskip)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'13
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                        (Etempvar _n tint)
                                                        (tptr (Tstruct _ct_data_s noattr)))
                                                      (Tstruct _ct_data_s noattr))
                                                    _fc
                                                    (Tunion __anon_2c403fe6f6d2 noattr))
                                                  _freq tushort))
                                              (Sset _f
                                                (Ecast
                                                  (Etempvar _t'13 tushort)
                                                  tushort)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'12
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _opt_len tulong))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _opt_len tulong)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'12 tulong)
                                                    (Ebinop Omul
                                                      (Ecast
                                                        (Etempvar _f tushort)
                                                        tulong)
                                                      (Ecast
                                                        (Ebinop Oadd
                                                          (Etempvar _bits tint)
                                                          (Etempvar _xbits tint)
                                                          tint) tuint)
                                                      tulong) tulong)))
                                              (Sifthenelse (Etempvar _stree (tptr (Tstruct _ct_data_s noattr)))
                                                (Ssequence
                                                  (Sset _t'10
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _static_len tulong))
                                                  (Ssequence
                                                    (Sset _t'11
                                                      (Efield
                                                        (Efield
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _stree (tptr (Tstruct _ct_data_s noattr)))
                                                              (Etempvar _n tint)
                                                              (tptr (Tstruct _ct_data_s noattr)))
                                                            (Tstruct _ct_data_s noattr))
                                                          _dl
                                                          (Tunion __anon_7a8a915e1e8b noattr))
                                                        _len tushort))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _static_len tulong)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'10 tulong)
                                                        (Ebinop Omul
                                                          (Ecast
                                                            (Etempvar _f tushort)
                                                            tulong)
                                                          (Ecast
                                                            (Ebinop Oadd
                                                              (Etempvar _t'11 tushort)
                                                              (Etempvar _xbits tint)
                                                              tint) tuint)
                                                          tulong) tulong))))
                                                Sskip))))))))))))
                        (Sset _h
                          (Ebinop Oadd (Etempvar _h tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _overflow tint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sreturn None)
                        Sskip)
                      (Ssequence
                        (Sloop
                          (Ssequence
                            (Sset _bits
                              (Ebinop Osub (Etempvar _max_length tint)
                                (Econst_int (Int.repr 1) tint) tint))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'9
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bl_count (tarray tushort 16))
                                          (Etempvar _bits tint)
                                          (tptr tushort)) tushort))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'9 tushort)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      Sskip
                                      Sbreak))
                                  (Sset _bits
                                    (Ebinop Osub (Etempvar _bits tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                Sskip)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'8
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bl_count (tarray tushort 16))
                                        (Etempvar _bits tint) (tptr tushort))
                                      tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bl_count (tarray tushort 16))
                                        (Etempvar _bits tint) (tptr tushort))
                                      tushort)
                                    (Ebinop Osub (Etempvar _t'8 tushort)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'7
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bl_count (tarray tushort 16))
                                          (Ebinop Oadd (Etempvar _bits tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (tptr tushort)) tushort))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bl_count (tarray tushort 16))
                                          (Ebinop Oadd (Etempvar _bits tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) (tptr tushort)) tushort)
                                      (Ebinop Oadd (Etempvar _t'7 tushort)
                                        (Econst_int (Int.repr 2) tint) tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'6
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bl_count (tarray tushort 16))
                                            (Etempvar _max_length tint)
                                            (tptr tushort)) tushort))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bl_count (tarray tushort 16))
                                            (Etempvar _max_length tint)
                                            (tptr tushort)) tushort)
                                        (Ebinop Osub (Etempvar _t'6 tushort)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Sset _overflow
                                      (Ebinop Osub (Etempvar _overflow tint)
                                        (Econst_int (Int.repr 2) tint) tint)))))))
                          (Sifthenelse (Ebinop Ogt (Etempvar _overflow tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            Sskip
                            Sbreak))
                        (Ssequence
                          (Sset _bits (Etempvar _max_length tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop One (Etempvar _bits tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _n
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bl_count (tarray tushort 16))
                                      (Etempvar _bits tint) (tptr tushort))
                                    tushort))
                                (Swhile
                                  (Ebinop One (Etempvar _n tint)
                                    (Econst_int (Int.repr 0) tint) tint)
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'1
                                          (Ecast
                                            (Ebinop Osub (Etempvar _h tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint) tint))
                                        (Sset _h (Etempvar _t'1 tint)))
                                      (Sset _m
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _heap (tarray tint 573))
                                            (Etempvar _t'1 tint) (tptr tint))
                                          tint)))
                                    (Ssequence
                                      (Sifthenelse (Ebinop Ogt
                                                     (Etempvar _m tint)
                                                     (Etempvar _max_code tint)
                                                     tint)
                                        Scontinue
                                        Sskip)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'2
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                    (Etempvar _m tint)
                                                    (tptr (Tstruct _ct_data_s noattr)))
                                                  (Tstruct _ct_data_s noattr))
                                                _dl (Tunion __anon_7a8a915e1e8b noattr))
                                              _len tushort))
                                          (Sifthenelse (Ebinop One
                                                         (Ecast
                                                           (Etempvar _t'2 tushort)
                                                           tuint)
                                                         (Ecast
                                                           (Etempvar _bits tint)
                                                           tuint) tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'3
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _opt_len tulong))
                                                (Ssequence
                                                  (Sset _t'4
                                                    (Efield
                                                      (Efield
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                            (Etempvar _m tint)
                                                            (tptr (Tstruct _ct_data_s noattr)))
                                                          (Tstruct _ct_data_s noattr))
                                                        _dl
                                                        (Tunion __anon_7a8a915e1e8b noattr))
                                                      _len tushort))
                                                  (Ssequence
                                                    (Sset _t'5
                                                      (Efield
                                                        (Efield
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                              (Etempvar _m tint)
                                                              (tptr (Tstruct _ct_data_s noattr)))
                                                            (Tstruct _ct_data_s noattr))
                                                          _fc
                                                          (Tunion __anon_2c403fe6f6d2 noattr))
                                                        _freq tushort))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _opt_len tulong)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'3 tulong)
                                                        (Ebinop Omul
                                                          (Ebinop Osub
                                                            (Ecast
                                                              (Etempvar _bits tint)
                                                              tulong)
                                                            (Etempvar _t'4 tushort)
                                                            tulong)
                                                          (Etempvar _t'5 tushort)
                                                          tulong) tulong)))))
                                              (Sassign
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                        (Etempvar _m tint)
                                                        (tptr (Tstruct _ct_data_s noattr)))
                                                      (Tstruct _ct_data_s noattr))
                                                    _dl
                                                    (Tunion __anon_7a8a915e1e8b noattr))
                                                  _len tushort)
                                                (Ecast (Etempvar _bits tint)
                                                  tushort)))
                                            Sskip))
                                        (Sset _n
                                          (Ebinop Osub (Etempvar _n tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint))))))))
                            (Sset _bits
                              (Ebinop Osub (Etempvar _bits tint)
                                (Econst_int (Int.repr 1) tint) tint))))))))))))))))
|}.

Definition f_build_tree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_desc, (tptr (Tstruct _tree_desc_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tree, (tptr (Tstruct _ct_data_s noattr))) ::
               (_stree, (tptr (Tstruct _ct_data_s noattr))) ::
               (_elems, tint) :: (_n, tint) :: (_m, tint) ::
               (_max_code, tint) :: (_node, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tushort) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'35, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'34, (tptr (Tstruct _static_tree_desc_s noattr))) ::
               (_t'33, tint) :: (_t'32, tushort) :: (_t'31, tint) ::
               (_t'30, tint) :: (_t'29, tulong) :: (_t'28, tushort) ::
               (_t'27, tulong) :: (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, tint) :: (_t'23, tint) :: (_t'22, tushort) ::
               (_t'21, tushort) :: (_t'20, tuchar) :: (_t'19, tuchar) ::
               (_t'18, tuchar) :: (_t'17, tuchar) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _tree
    (Efield
      (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
        (Tstruct _tree_desc_s noattr)) _dyn_tree
      (tptr (Tstruct _ct_data_s noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'35
        (Efield
          (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
            (Tstruct _tree_desc_s noattr)) _stat_desc
          (tptr (Tstruct _static_tree_desc_s noattr))))
      (Sset _stree
        (Efield
          (Ederef
            (Etempvar _t'35 (tptr (Tstruct _static_tree_desc_s noattr)))
            (Tstruct _static_tree_desc_s noattr)) _static_tree
          (tptr (Tstruct _ct_data_s noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'34
          (Efield
            (Ederef (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
              (Tstruct _tree_desc_s noattr)) _stat_desc
            (tptr (Tstruct _static_tree_desc_s noattr))))
        (Sset _elems
          (Efield
            (Ederef
              (Etempvar _t'34 (tptr (Tstruct _static_tree_desc_s noattr)))
              (Tstruct _static_tree_desc_s noattr)) _elems tint)))
      (Ssequence
        (Sset _max_code (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
        (Ssequence
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _heap_len tint)
              (Econst_int (Int.repr 0) tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _heap_max tint)
              (Ebinop Oadd
                (Ebinop Omul (Econst_int (Int.repr 2) tint)
                  (Ebinop Oadd
                    (Ebinop Oadd (Econst_int (Int.repr 256) tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (Econst_int (Int.repr 29) tint) tint) tint)
                (Econst_int (Int.repr 1) tint) tint)))
          (Ssequence
            (Ssequence
              (Sset _n (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                                 (Etempvar _elems tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'32
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                              (Etempvar _n tint)
                              (tptr (Tstruct _ct_data_s noattr)))
                            (Tstruct _ct_data_s noattr)) _fc
                          (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                    (Sifthenelse (Ebinop One (Etempvar _t'32 tushort)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'33
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _heap_len tint))
                                  (Sset _t'1
                                    (Ecast
                                      (Ebinop Oadd (Etempvar _t'33 tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tint)))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _heap_len tint) (Etempvar _t'1 tint)))
                              (Sset _t'2 (Ecast (Etempvar _n tint) tint)))
                            (Sset _max_code (Etempvar _t'2 tint)))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _heap
                                  (tarray tint 573)) (Etempvar _t'1 tint)
                                (tptr tint)) tint) (Etempvar _t'2 tint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _depth
                                (tarray tuchar 573)) (Etempvar _n tint)
                              (tptr tuchar)) tuchar)
                          (Econst_int (Int.repr 0) tint)))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Etempvar _n tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _dl
                            (Tunion __anon_7a8a915e1e8b noattr)) _len tushort)
                        (Econst_int (Int.repr 0) tint)))))
                (Sset _n
                  (Ebinop Oadd (Etempvar _n tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sloop
                (Ssequence
                  (Ssequence
                    (Sset _t'31
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _heap_len tint))
                    (Sifthenelse (Ebinop Olt (Etempvar _t'31 tint)
                                   (Econst_int (Int.repr 2) tint) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'30
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _heap_len tint))
                                (Sset _t'3
                                  (Ecast
                                    (Ebinop Oadd (Etempvar _t'30 tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tint)))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _heap_len tint) (Etempvar _t'3 tint)))
                            (Sifthenelse (Ebinop Olt
                                           (Etempvar _max_code tint)
                                           (Econst_int (Int.repr 2) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5
                                    (Ecast
                                      (Ebinop Oadd (Etempvar _max_code tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tint))
                                  (Sset _max_code (Etempvar _t'5 tint)))
                                (Sset _t'4 (Ecast (Etempvar _t'5 tint) tint)))
                              (Sset _t'4
                                (Ecast (Econst_int (Int.repr 0) tint) tint))))
                          (Sset _t'6 (Ecast (Etempvar _t'4 tint) tint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _heap
                                (tarray tint 573)) (Etempvar _t'3 tint)
                              (tptr tint)) tint) (Etempvar _t'6 tint)))
                      (Sset _node (Etempvar _t'6 tint)))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Etempvar _node tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _fc
                            (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort)
                        (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _depth
                                (tarray tuchar 573)) (Etempvar _node tint)
                              (tptr tuchar)) tuchar)
                          (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Ssequence
                            (Sset _t'29
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _opt_len
                                tulong))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _opt_len
                                tulong)
                              (Ebinop Osub (Etempvar _t'29 tulong)
                                (Econst_int (Int.repr 1) tint) tulong)))
                          (Sifthenelse (Etempvar _stree (tptr (Tstruct _ct_data_s noattr)))
                            (Ssequence
                              (Sset _t'27
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _static_len tulong))
                              (Ssequence
                                (Sset _t'28
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _stree (tptr (Tstruct _ct_data_s noattr)))
                                          (Etempvar _node tint)
                                          (tptr (Tstruct _ct_data_s noattr)))
                                        (Tstruct _ct_data_s noattr)) _dl
                                      (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _static_len tulong)
                                  (Ebinop Osub (Etempvar _t'27 tulong)
                                    (Etempvar _t'28 tushort) tulong))))
                            Sskip))))))
                Sskip)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
                      (Tstruct _tree_desc_s noattr)) _max_code tint)
                  (Etempvar _max_code tint))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'26
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _heap_len tint))
                      (Sset _n
                        (Ebinop Odiv (Etempvar _t'26 tint)
                          (Econst_int (Int.repr 2) tint) tint)))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Oge (Etempvar _n tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          Sskip
                          Sbreak)
                        (Scall None
                          (Evar _pqdownheap (Tfunction
                                              ((tptr (Tstruct _internal_state noattr)) ::
                                               (tptr (Tstruct _ct_data_s noattr)) ::
                                               tint :: nil) tvoid cc_default))
                          ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                           (Etempvar _tree (tptr (Tstruct _ct_data_s noattr))) ::
                           (Etempvar _n tint) :: nil)))
                      (Sset _n
                        (Ebinop Osub (Etempvar _n tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Sset _node (Etempvar _elems tint))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Sset _n
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573))
                                  (Econst_int (Int.repr 1) tint) (tptr tint))
                                tint))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _heap_len tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _heap_len tint)
                                    (Ebinop Osub (Etempvar _t'7 tint)
                                      (Econst_int (Int.repr 1) tint) tint)))
                                (Ssequence
                                  (Sset _t'25
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _heap (tarray tint 573))
                                        (Etempvar _t'7 tint) (tptr tint))
                                      tint))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _heap (tarray tint 573))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tint)) tint)
                                    (Etempvar _t'25 tint))))
                              (Scall None
                                (Evar _pqdownheap (Tfunction
                                                    ((tptr (Tstruct _internal_state noattr)) ::
                                                     (tptr (Tstruct _ct_data_s noattr)) ::
                                                     tint :: nil) tvoid
                                                    cc_default))
                                ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                                 (Etempvar _tree (tptr (Tstruct _ct_data_s noattr))) ::
                                 (Econst_int (Int.repr 1) tint) :: nil))))
                          (Ssequence
                            (Sset _m
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573))
                                  (Econst_int (Int.repr 1) tint) (tptr tint))
                                tint))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'24
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _heap_max tint))
                                    (Sset _t'8
                                      (Ecast
                                        (Ebinop Osub (Etempvar _t'24 tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tint)))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _heap_max tint) (Etempvar _t'8 tint)))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _heap (tarray tint 573))
                                      (Etempvar _t'8 tint) (tptr tint)) tint)
                                  (Etempvar _n tint)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'23
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _heap_max tint))
                                      (Sset _t'9
                                        (Ecast
                                          (Ebinop Osub (Etempvar _t'23 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) tint)))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _heap_max tint) (Etempvar _t'9 tint)))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _heap (tarray tint 573))
                                        (Etempvar _t'9 tint) (tptr tint))
                                      tint) (Etempvar _m tint)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'21
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                              (Etempvar _n tint)
                                              (tptr (Tstruct _ct_data_s noattr)))
                                            (Tstruct _ct_data_s noattr)) _fc
                                          (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                        tushort))
                                    (Ssequence
                                      (Sset _t'22
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                (Etempvar _m tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort))
                                      (Sassign
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                (Etempvar _node tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort)
                                        (Ebinop Oadd (Etempvar _t'21 tushort)
                                          (Etempvar _t'22 tushort) tint))))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _depth (tarray tuchar 573))
                                              (Etempvar _n tint)
                                              (tptr tuchar)) tuchar))
                                        (Ssequence
                                          (Sset _t'18
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _depth (tarray tuchar 573))
                                                (Etempvar _m tint)
                                                (tptr tuchar)) tuchar))
                                          (Sifthenelse (Ebinop Oge
                                                         (Etempvar _t'17 tuchar)
                                                         (Etempvar _t'18 tuchar)
                                                         tint)
                                            (Ssequence
                                              (Sset _t'20
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _depth
                                                      (tarray tuchar 573))
                                                    (Etempvar _n tint)
                                                    (tptr tuchar)) tuchar))
                                              (Sset _t'10
                                                (Ecast
                                                  (Etempvar _t'20 tuchar)
                                                  tint)))
                                            (Ssequence
                                              (Sset _t'19
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _depth
                                                      (tarray tuchar 573))
                                                    (Etempvar _m tint)
                                                    (tptr tuchar)) tuchar))
                                              (Sset _t'10
                                                (Ecast
                                                  (Etempvar _t'19 tuchar)
                                                  tint))))))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _depth (tarray tuchar 573))
                                            (Etempvar _node tint)
                                            (tptr tuchar)) tuchar)
                                        (Ecast
                                          (Ebinop Oadd (Etempvar _t'10 tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint) tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'11
                                            (Ecast
                                              (Ecast (Etempvar _node tint)
                                                tushort) tushort))
                                          (Sassign
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                    (Etempvar _m tint)
                                                    (tptr (Tstruct _ct_data_s noattr)))
                                                  (Tstruct _ct_data_s noattr))
                                                _dl (Tunion __anon_7a8a915e1e8b noattr))
                                              _dad tushort)
                                            (Etempvar _t'11 tushort)))
                                        (Sassign
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                                  (Etempvar _n tint)
                                                  (tptr (Tstruct _ct_data_s noattr)))
                                                (Tstruct _ct_data_s noattr))
                                              _dl (Tunion __anon_7a8a915e1e8b noattr)) _dad
                                            tushort)
                                          (Etempvar _t'11 tushort)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'12
                                              (Etempvar _node tint))
                                            (Sset _node
                                              (Ebinop Oadd
                                                (Etempvar _t'12 tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _heap (tarray tint 573))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tint)) tint)
                                            (Etempvar _t'12 tint)))
                                        (Scall None
                                          (Evar _pqdownheap (Tfunction
                                                              ((tptr (Tstruct _internal_state noattr)) ::
                                                               (tptr (Tstruct _ct_data_s noattr)) ::
                                                               tint :: nil)
                                                              tvoid
                                                              cc_default))
                                          ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                                           (Etempvar _tree (tptr (Tstruct _ct_data_s noattr))) ::
                                           (Econst_int (Int.repr 1) tint) ::
                                           nil))))))))))
                        (Ssequence
                          (Sset _t'16
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _heap_len
                              tint))
                          (Sifthenelse (Ebinop Oge (Etempvar _t'16 tint)
                                         (Econst_int (Int.repr 2) tint) tint)
                            Sskip
                            Sbreak)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'15
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _heap_max tint))
                              (Sset _t'13
                                (Ecast
                                  (Ebinop Osub (Etempvar _t'15 tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint)))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _heap_max
                                tint) (Etempvar _t'13 tint)))
                          (Ssequence
                            (Sset _t'14
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573))
                                  (Econst_int (Int.repr 1) tint) (tptr tint))
                                tint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr)) _heap
                                    (tarray tint 573)) (Etempvar _t'13 tint)
                                  (tptr tint)) tint) (Etempvar _t'14 tint))))
                        (Ssequence
                          (Scall None
                            (Evar _gen_bitlen (Tfunction
                                                ((tptr (Tstruct _internal_state noattr)) ::
                                                 (tptr (Tstruct _tree_desc_s noattr)) ::
                                                 nil) tvoid cc_default))
                            ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                             (Ecast
                               (Etempvar _desc (tptr (Tstruct _tree_desc_s noattr)))
                               (tptr (Tstruct _tree_desc_s noattr))) :: nil))
                          (Scall None
                            (Evar _gen_codes (Tfunction
                                               ((tptr (Tstruct _ct_data_s noattr)) ::
                                                tint :: (tptr tushort) ::
                                                nil) tvoid cc_default))
                            ((Ecast
                               (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                               (tptr (Tstruct _ct_data_s noattr))) ::
                             (Etempvar _max_code tint) ::
                             (Efield
                               (Ederef
                                 (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                 (Tstruct _internal_state noattr)) _bl_count
                               (tarray tushort 16)) :: nil)))))))))))))))
|}.

Definition f_scan_tree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_tree, (tptr (Tstruct _ct_data_s noattr))) ::
                (_max_code, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tint) :: (_prevlen, tint) :: (_curlen, tint) ::
               (_nextlen, tint) :: (_count, tint) :: (_max_count, tint) ::
               (_min_count, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'7, tushort) :: (_t'6, tushort) :: (_t'5, tushort) ::
               (_t'4, tushort) :: (_t'3, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _prevlen (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _nextlen
      (Efield
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
              (Econst_int (Int.repr 0) tint)
              (tptr (Tstruct _ct_data_s noattr)))
            (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
        tushort))
    (Ssequence
      (Sset _count (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _max_count (Econst_int (Int.repr 7) tint))
        (Ssequence
          (Sset _min_count (Econst_int (Int.repr 4) tint))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _nextlen tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _max_count (Econst_int (Int.repr 138) tint))
                (Sset _min_count (Econst_int (Int.repr 3) tint)))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                        (Ebinop Oadd (Etempvar _max_code tint)
                          (Econst_int (Int.repr 1) tint) tint)
                        (tptr (Tstruct _ct_data_s noattr)))
                      (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr))
                  _len tushort)
                (Ecast (Econst_int (Int.repr 65535) tint) tushort))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Ole (Etempvar _n tint)
                                   (Etempvar _max_code tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _curlen (Etempvar _nextlen tint))
                      (Ssequence
                        (Sset _nextlen
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                  (Ebinop Oadd (Etempvar _n tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr (Tstruct _ct_data_s noattr)))
                                (Tstruct _ct_data_s noattr)) _dl
                              (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'1
                                  (Ecast
                                    (Ebinop Oadd (Etempvar _count tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tint))
                                (Sset _count (Etempvar _t'1 tint)))
                              (Sifthenelse (Ebinop Olt (Etempvar _t'1 tint)
                                             (Etempvar _max_count tint) tint)
                                (Sset _t'2
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _curlen tint)
                                      (Etempvar _nextlen tint) tint) tbool))
                                (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'2 tint)
                              Scontinue
                              (Sifthenelse (Ebinop Olt (Etempvar _count tint)
                                             (Etempvar _min_count tint) tint)
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bl_tree
                                              (tarray (Tstruct _ct_data_s noattr) 39))
                                            (Etempvar _curlen tint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _fc
                                        (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                                  (Sassign
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bl_tree
                                              (tarray (Tstruct _ct_data_s noattr) 39))
                                            (Etempvar _curlen tint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _fc
                                        (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort)
                                    (Ebinop Oadd (Etempvar _t'7 tushort)
                                      (Ecast (Etempvar _count tint) tushort)
                                      tint)))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _curlen tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _curlen tint)
                                                   (Etempvar _prevlen tint)
                                                   tint)
                                      (Ssequence
                                        (Sset _t'6
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bl_tree
                                                    (tarray (Tstruct _ct_data_s noattr) 39))
                                                  (Etempvar _curlen tint)
                                                  (tptr (Tstruct _ct_data_s noattr)))
                                                (Tstruct _ct_data_s noattr))
                                              _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                            _freq tushort))
                                        (Sassign
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bl_tree
                                                    (tarray (Tstruct _ct_data_s noattr) 39))
                                                  (Etempvar _curlen tint)
                                                  (tptr (Tstruct _ct_data_s noattr)))
                                                (Tstruct _ct_data_s noattr))
                                              _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                            _freq tushort)
                                          (Ebinop Oadd
                                            (Etempvar _t'6 tushort)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)))
                                      Sskip)
                                    (Ssequence
                                      (Sset _t'5
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 16) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort))
                                      (Sassign
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 16) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort)
                                        (Ebinop Oadd (Etempvar _t'5 tushort)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))))
                                  (Sifthenelse (Ebinop Ole
                                                 (Etempvar _count tint)
                                                 (Econst_int (Int.repr 10) tint)
                                                 tint)
                                    (Ssequence
                                      (Sset _t'4
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 17) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort))
                                      (Sassign
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 17) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort)
                                        (Ebinop Oadd (Etempvar _t'4 tushort)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Ssequence
                                      (Sset _t'3
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 18) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort))
                                      (Sassign
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 18) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _fc (Tunion __anon_2c403fe6f6d2 noattr)) _freq
                                          tushort)
                                        (Ebinop Oadd (Etempvar _t'3 tushort)
                                          (Econst_int (Int.repr 1) tint)
                                          tint))))))))
                          (Ssequence
                            (Sset _count (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sset _prevlen (Etempvar _curlen tint))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _nextlen tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _max_count
                                    (Econst_int (Int.repr 138) tint))
                                  (Sset _min_count
                                    (Econst_int (Int.repr 3) tint)))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _curlen tint)
                                               (Etempvar _nextlen tint) tint)
                                  (Ssequence
                                    (Sset _max_count
                                      (Econst_int (Int.repr 6) tint))
                                    (Sset _min_count
                                      (Econst_int (Int.repr 3) tint)))
                                  (Ssequence
                                    (Sset _max_count
                                      (Econst_int (Int.repr 7) tint))
                                    (Sset _min_count
                                      (Econst_int (Int.repr 4) tint)))))))))))
                  (Sset _n
                    (Ebinop Oadd (Etempvar _n tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))))))
|}.

Definition f_send_tree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_tree, (tptr (Tstruct _ct_data_s noattr))) ::
                (_max_code, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tint) :: (_prevlen, tint) :: (_curlen, tint) ::
               (_nextlen, tint) :: (_count, tint) :: (_max_count, tint) ::
               (_min_count, tint) :: (_len, tint) :: (_val, tint) ::
               (_len__1, tint) :: (_val__1, tint) :: (_len__2, tint) ::
               (_val__2, tint) :: (_len__3, tint) :: (_val__3, tint) ::
               (_len__4, tint) :: (_val__4, tint) :: (_len__5, tint) ::
               (_val__5, tint) :: (_len__6, tint) :: (_val__6, tint) ::
               (_len__7, tint) :: (_val__7, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tulong) :: (_t'16, tulong) ::
               (_t'15, tulong) :: (_t'14, tulong) :: (_t'13, tulong) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tulong) ::
               (_t'9, tulong) :: (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tint) ::
               (_t'125, tushort) :: (_t'124, tint) :: (_t'123, tushort) ::
               (_t'122, tushort) :: (_t'121, (tptr tuchar)) ::
               (_t'120, tushort) :: (_t'119, (tptr tuchar)) ::
               (_t'118, tint) :: (_t'117, tint) :: (_t'116, tint) ::
               (_t'115, tushort) :: (_t'114, tushort) :: (_t'113, tint) ::
               (_t'112, tint) :: (_t'111, tushort) :: (_t'110, tint) ::
               (_t'109, tushort) :: (_t'108, tushort) ::
               (_t'107, (tptr tuchar)) :: (_t'106, tushort) ::
               (_t'105, (tptr tuchar)) :: (_t'104, tint) :: (_t'103, tint) ::
               (_t'102, tint) :: (_t'101, tushort) :: (_t'100, tushort) ::
               (_t'99, tint) :: (_t'98, tint) :: (_t'97, tushort) ::
               (_t'96, tint) :: (_t'95, tushort) :: (_t'94, tushort) ::
               (_t'93, (tptr tuchar)) :: (_t'92, tushort) ::
               (_t'91, (tptr tuchar)) :: (_t'90, tint) :: (_t'89, tint) ::
               (_t'88, tint) :: (_t'87, tushort) :: (_t'86, tushort) ::
               (_t'85, tint) :: (_t'84, tint) :: (_t'83, tint) ::
               (_t'82, tushort) :: (_t'81, tushort) ::
               (_t'80, (tptr tuchar)) :: (_t'79, tushort) ::
               (_t'78, (tptr tuchar)) :: (_t'77, tint) :: (_t'76, tint) ::
               (_t'75, tint) :: (_t'74, tushort) :: (_t'73, tint) ::
               (_t'72, tint) :: (_t'71, tushort) :: (_t'70, tint) ::
               (_t'69, tushort) :: (_t'68, tushort) ::
               (_t'67, (tptr tuchar)) :: (_t'66, tushort) ::
               (_t'65, (tptr tuchar)) :: (_t'64, tint) :: (_t'63, tint) ::
               (_t'62, tint) :: (_t'61, tushort) :: (_t'60, tushort) ::
               (_t'59, tint) :: (_t'58, tint) :: (_t'57, tint) ::
               (_t'56, tushort) :: (_t'55, tushort) ::
               (_t'54, (tptr tuchar)) :: (_t'53, tushort) ::
               (_t'52, (tptr tuchar)) :: (_t'51, tint) :: (_t'50, tint) ::
               (_t'49, tint) :: (_t'48, tushort) :: (_t'47, tint) ::
               (_t'46, tint) :: (_t'45, tushort) :: (_t'44, tint) ::
               (_t'43, tushort) :: (_t'42, tushort) ::
               (_t'41, (tptr tuchar)) :: (_t'40, tushort) ::
               (_t'39, (tptr tuchar)) :: (_t'38, tint) :: (_t'37, tint) ::
               (_t'36, tint) :: (_t'35, tushort) :: (_t'34, tushort) ::
               (_t'33, tint) :: (_t'32, tint) :: (_t'31, tint) ::
               (_t'30, tushort) :: (_t'29, tushort) ::
               (_t'28, (tptr tuchar)) :: (_t'27, tushort) ::
               (_t'26, (tptr tuchar)) :: (_t'25, tint) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tushort) :: (_t'21, tint) ::
               (_t'20, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _prevlen (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sset _nextlen
      (Efield
        (Efield
          (Ederef
            (Ebinop Oadd (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
              (Econst_int (Int.repr 0) tint)
              (tptr (Tstruct _ct_data_s noattr)))
            (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
        tushort))
    (Ssequence
      (Sset _count (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _max_count (Econst_int (Int.repr 7) tint))
        (Ssequence
          (Sset _min_count (Econst_int (Int.repr 4) tint))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _nextlen tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Sset _max_count (Econst_int (Int.repr 138) tint))
                (Sset _min_count (Econst_int (Int.repr 3) tint)))
              Sskip)
            (Ssequence
              (Sset _n (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Ole (Etempvar _n tint)
                                 (Etempvar _max_code tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _curlen (Etempvar _nextlen tint))
                    (Ssequence
                      (Sset _nextlen
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Etempvar _tree (tptr (Tstruct _ct_data_s noattr)))
                                (Ebinop Oadd (Etempvar _n tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _dl
                            (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'18
                                (Ecast
                                  (Ebinop Oadd (Etempvar _count tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint))
                              (Sset _count (Etempvar _t'18 tint)))
                            (Sifthenelse (Ebinop Olt (Etempvar _t'18 tint)
                                           (Etempvar _max_count tint) tint)
                              (Sset _t'19
                                (Ecast
                                  (Ebinop Oeq (Etempvar _curlen tint)
                                    (Etempvar _nextlen tint) tint) tbool))
                              (Sset _t'19 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'19 tint)
                            Scontinue
                            (Sifthenelse (Ebinop Olt (Etempvar _count tint)
                                           (Etempvar _min_count tint) tint)
                              (Sloop
                                (Ssequence
                                  (Sset _len
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bl_tree
                                              (tarray (Tstruct _ct_data_s noattr) 39))
                                            (Etempvar _curlen tint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _dl
                                        (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                                  (Ssequence
                                    (Sset _t'112
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_valid tint))
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _t'112 tint)
                                                   (Ebinop Osub
                                                     (Ecast
                                                       (Econst_int (Int.repr 16) tint)
                                                       tint)
                                                     (Etempvar _len tint)
                                                     tint) tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'125
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bl_tree
                                                      (tarray (Tstruct _ct_data_s noattr) 39))
                                                    (Etempvar _curlen tint)
                                                    (tptr (Tstruct _ct_data_s noattr)))
                                                  (Tstruct _ct_data_s noattr))
                                                _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                              _code tushort))
                                          (Sset _val
                                            (Ecast (Etempvar _t'125 tushort)
                                              tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'123
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bi_buf tushort))
                                            (Ssequence
                                              (Sset _t'124
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort)
                                                (Ebinop Oor
                                                  (Etempvar _t'123 tushort)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _val tint)
                                                      tushort)
                                                    (Etempvar _t'124 tint)
                                                    tint) tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'2
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'2 tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong)))
                                                (Ssequence
                                                  (Sset _t'121
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending_buf
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'122
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'121 (tptr tuchar))
                                                          (Etempvar _t'2 tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ecast
                                                          (Ebinop Oand
                                                            (Etempvar _t'122 tushort)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tint) tuchar)
                                                        tuchar)))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'3
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'3 tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong)))
                                                (Ssequence
                                                  (Sset _t'119
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending_buf
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'120
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'119 (tptr tuchar))
                                                          (Etempvar _t'3 tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ecast
                                                          (Ebinop Oshr
                                                            (Ecast
                                                              (Etempvar _t'120 tushort)
                                                              tushort)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tint) tuchar)
                                                        tuchar))))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'118
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort)
                                                  (Ebinop Oshr
                                                    (Ecast
                                                      (Etempvar _val tint)
                                                      tushort)
                                                    (Ebinop Osub
                                                      (Econst_int (Int.repr 16) tint)
                                                      (Etempvar _t'118 tint)
                                                      tint) tint)))
                                              (Ssequence
                                                (Sset _t'117
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'117 tint)
                                                    (Ebinop Osub
                                                      (Etempvar _len tint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tint) tint)))))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'114
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort))
                                          (Ssequence
                                            (Sset _t'115
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bl_tree
                                                        (tarray (Tstruct _ct_data_s noattr) 39))
                                                      (Etempvar _curlen tint)
                                                      (tptr (Tstruct _ct_data_s noattr)))
                                                    (Tstruct _ct_data_s noattr))
                                                  _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                                _code tushort))
                                            (Ssequence
                                              (Sset _t'116
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort)
                                                (Ebinop Oor
                                                  (Etempvar _t'114 tushort)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _t'115 tushort)
                                                      tushort)
                                                    (Etempvar _t'116 tint)
                                                    tint) tint)))))
                                        (Ssequence
                                          (Sset _t'113
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint)
                                            (Ebinop Oadd
                                              (Etempvar _t'113 tint)
                                              (Etempvar _len tint) tint)))))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'1
                                      (Ecast
                                        (Ebinop Osub (Etempvar _count tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint) tint))
                                    (Sset _count (Etempvar _t'1 tint)))
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _t'1 tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)))
                              (Sifthenelse (Ebinop One
                                             (Etempvar _curlen tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _curlen tint)
                                                 (Etempvar _prevlen tint)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _len__1
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bl_tree
                                                    (tarray (Tstruct _ct_data_s noattr) 39))
                                                  (Etempvar _curlen tint)
                                                  (tptr (Tstruct _ct_data_s noattr)))
                                                (Tstruct _ct_data_s noattr))
                                              _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
                                            tushort))
                                        (Ssequence
                                          (Sset _t'98
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint))
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _t'98 tint)
                                                         (Ebinop Osub
                                                           (Ecast
                                                             (Econst_int (Int.repr 16) tint)
                                                             tint)
                                                           (Etempvar _len__1 tint)
                                                           tint) tint)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'111
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bl_tree
                                                            (tarray (Tstruct _ct_data_s noattr) 39))
                                                          (Etempvar _curlen tint)
                                                          (tptr (Tstruct _ct_data_s noattr)))
                                                        (Tstruct _ct_data_s noattr))
                                                      _fc
                                                      (Tunion __anon_2c403fe6f6d2 noattr))
                                                    _code tushort))
                                                (Sset _val__1
                                                  (Ecast
                                                    (Etempvar _t'111 tushort)
                                                    tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'109
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort))
                                                  (Ssequence
                                                    (Sset _t'110
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oor
                                                        (Etempvar _t'109 tushort)
                                                        (Ebinop Oshl
                                                          (Ecast
                                                            (Etempvar _val__1 tint)
                                                            tushort)
                                                          (Etempvar _t'110 tint)
                                                          tint) tint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'4
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'4 tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sset _t'107
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending_buf
                                                            (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _t'108
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                                (Tstruct _internal_state noattr))
                                                              _bi_buf
                                                              tushort))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _t'107 (tptr tuchar))
                                                                (Etempvar _t'4 tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ecast
                                                              (Ecast
                                                                (Ebinop Oand
                                                                  (Etempvar _t'108 tushort)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tint)
                                                                tuchar)
                                                              tuchar)))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'5
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'5 tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sset _t'105
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending_buf
                                                            (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _t'106
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                                (Tstruct _internal_state noattr))
                                                              _bi_buf
                                                              tushort))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _t'105 (tptr tuchar))
                                                                (Etempvar _t'5 tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ecast
                                                              (Ecast
                                                                (Ebinop Oshr
                                                                  (Ecast
                                                                    (Etempvar _t'106 tushort)
                                                                    tushort)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tint)
                                                                tuchar)
                                                              tuchar))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'104
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_buf tushort)
                                                        (Ebinop Oshr
                                                          (Ecast
                                                            (Etempvar _val__1 tint)
                                                            tushort)
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 16) tint)
                                                            (Etempvar _t'104 tint)
                                                            tint) tint)))
                                                    (Ssequence
                                                      (Sset _t'103
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'103 tint)
                                                          (Ebinop Osub
                                                            (Etempvar _len__1 tint)
                                                            (Econst_int (Int.repr 16) tint)
                                                            tint) tint)))))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'100
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'101
                                                    (Efield
                                                      (Efield
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                                (Tstruct _internal_state noattr))
                                                              _bl_tree
                                                              (tarray (Tstruct _ct_data_s noattr) 39))
                                                            (Etempvar _curlen tint)
                                                            (tptr (Tstruct _ct_data_s noattr)))
                                                          (Tstruct _ct_data_s noattr))
                                                        _fc
                                                        (Tunion __anon_2c403fe6f6d2 noattr))
                                                      _code tushort))
                                                  (Ssequence
                                                    (Sset _t'102
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oor
                                                        (Etempvar _t'100 tushort)
                                                        (Ebinop Oshl
                                                          (Ecast
                                                            (Etempvar _t'101 tushort)
                                                            tushort)
                                                          (Etempvar _t'102 tint)
                                                          tint) tint)))))
                                              (Ssequence
                                                (Sset _t'99
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'99 tint)
                                                    (Etempvar _len__1 tint)
                                                    tint)))))))
                                      (Sset _count
                                        (Ebinop Osub (Etempvar _count tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    Sskip)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _len__2
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 16) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
                                          tushort))
                                      (Ssequence
                                        (Sset _t'84
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'84 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__2 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'97
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bl_tree
                                                          (tarray (Tstruct _ct_data_s noattr) 39))
                                                        (Econst_int (Int.repr 16) tint)
                                                        (tptr (Tstruct _ct_data_s noattr)))
                                                      (Tstruct _ct_data_s noattr))
                                                    _fc
                                                    (Tunion __anon_2c403fe6f6d2 noattr))
                                                  _code tushort))
                                              (Sset _val__2
                                                (Ecast
                                                  (Etempvar _t'97 tushort)
                                                  tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'95
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'96
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'95 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__2 tint)
                                                          tushort)
                                                        (Etempvar _t'96 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'6
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'6 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'93
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'94
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'93 (tptr tuchar))
                                                              (Etempvar _t'6 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'94 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'7
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'7 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'91
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'92
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'91 (tptr tuchar))
                                                              (Etempvar _t'7 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'92 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'90
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__2 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'90 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'89
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'89 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__2 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'86
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'87
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bl_tree
                                                            (tarray (Tstruct _ct_data_s noattr) 39))
                                                          (Econst_int (Int.repr 16) tint)
                                                          (tptr (Tstruct _ct_data_s noattr)))
                                                        (Tstruct _ct_data_s noattr))
                                                      _fc
                                                      (Tunion __anon_2c403fe6f6d2 noattr))
                                                    _code tushort))
                                                (Ssequence
                                                  (Sset _t'88
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'86 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _t'87 tushort)
                                                          tushort)
                                                        (Etempvar _t'88 tint)
                                                        tint) tint)))))
                                            (Ssequence
                                              (Sset _t'85
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'85 tint)
                                                  (Etempvar _len__2 tint)
                                                  tint)))))))
                                    (Ssequence
                                      (Sset _len__3
                                        (Econst_int (Int.repr 2) tint))
                                      (Ssequence
                                        (Sset _t'72
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'72 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__3 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Sset _val__3
                                              (Ebinop Osub
                                                (Ecast (Etempvar _count tint)
                                                  tint)
                                                (Econst_int (Int.repr 3) tint)
                                                tint))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'82
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'83
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'82 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__3 tint)
                                                          tushort)
                                                        (Etempvar _t'83 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'8
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'8 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'80
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'81
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'80 (tptr tuchar))
                                                              (Etempvar _t'8 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'81 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'9
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'9 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'78
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'79
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'78 (tptr tuchar))
                                                              (Etempvar _t'9 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'79 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'77
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__3 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'77 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'76
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'76 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__3 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'74
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'75
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort)
                                                  (Ebinop Oor
                                                    (Etempvar _t'74 tushort)
                                                    (Ebinop Oshl
                                                      (Ecast
                                                        (Ebinop Osub
                                                          (Etempvar _count tint)
                                                          (Econst_int (Int.repr 3) tint)
                                                          tint) tushort)
                                                      (Etempvar _t'75 tint)
                                                      tint) tint))))
                                            (Ssequence
                                              (Sset _t'73
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'73 tint)
                                                  (Etempvar _len__3 tint)
                                                  tint)))))))))
                                (Sifthenelse (Ebinop Ole
                                               (Etempvar _count tint)
                                               (Econst_int (Int.repr 10) tint)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Sset _len__4
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 17) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
                                          tushort))
                                      (Ssequence
                                        (Sset _t'58
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'58 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__4 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'71
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bl_tree
                                                          (tarray (Tstruct _ct_data_s noattr) 39))
                                                        (Econst_int (Int.repr 17) tint)
                                                        (tptr (Tstruct _ct_data_s noattr)))
                                                      (Tstruct _ct_data_s noattr))
                                                    _fc
                                                    (Tunion __anon_2c403fe6f6d2 noattr))
                                                  _code tushort))
                                              (Sset _val__4
                                                (Ecast
                                                  (Etempvar _t'71 tushort)
                                                  tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'69
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'70
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'69 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__4 tint)
                                                          tushort)
                                                        (Etempvar _t'70 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'10
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'10 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'67
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'68
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'67 (tptr tuchar))
                                                              (Etempvar _t'10 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'68 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'11
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'11 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'65
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'66
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'65 (tptr tuchar))
                                                              (Etempvar _t'11 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'66 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'64
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__4 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'64 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'63
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'63 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__4 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'60
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'61
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bl_tree
                                                            (tarray (Tstruct _ct_data_s noattr) 39))
                                                          (Econst_int (Int.repr 17) tint)
                                                          (tptr (Tstruct _ct_data_s noattr)))
                                                        (Tstruct _ct_data_s noattr))
                                                      _fc
                                                      (Tunion __anon_2c403fe6f6d2 noattr))
                                                    _code tushort))
                                                (Ssequence
                                                  (Sset _t'62
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'60 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _t'61 tushort)
                                                          tushort)
                                                        (Etempvar _t'62 tint)
                                                        tint) tint)))))
                                            (Ssequence
                                              (Sset _t'59
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'59 tint)
                                                  (Etempvar _len__4 tint)
                                                  tint)))))))
                                    (Ssequence
                                      (Sset _len__5
                                        (Econst_int (Int.repr 3) tint))
                                      (Ssequence
                                        (Sset _t'46
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'46 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__5 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Sset _val__5
                                              (Ebinop Osub
                                                (Ecast (Etempvar _count tint)
                                                  tint)
                                                (Econst_int (Int.repr 3) tint)
                                                tint))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'56
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'57
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'56 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__5 tint)
                                                          tushort)
                                                        (Etempvar _t'57 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'12
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'12 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'54
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'55
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'54 (tptr tuchar))
                                                              (Etempvar _t'12 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'55 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'13
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'13 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'52
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'53
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'52 (tptr tuchar))
                                                              (Etempvar _t'13 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'53 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'51
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__5 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'51 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'50
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'50 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__5 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'48
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'49
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort)
                                                  (Ebinop Oor
                                                    (Etempvar _t'48 tushort)
                                                    (Ebinop Oshl
                                                      (Ecast
                                                        (Ebinop Osub
                                                          (Etempvar _count tint)
                                                          (Econst_int (Int.repr 3) tint)
                                                          tint) tushort)
                                                      (Etempvar _t'49 tint)
                                                      tint) tint))))
                                            (Ssequence
                                              (Sset _t'47
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'47 tint)
                                                  (Etempvar _len__5 tint)
                                                  tint))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _len__6
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bl_tree
                                                  (tarray (Tstruct _ct_data_s noattr) 39))
                                                (Econst_int (Int.repr 18) tint)
                                                (tptr (Tstruct _ct_data_s noattr)))
                                              (Tstruct _ct_data_s noattr))
                                            _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
                                          tushort))
                                      (Ssequence
                                        (Sset _t'32
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'32 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__6 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'45
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bl_tree
                                                          (tarray (Tstruct _ct_data_s noattr) 39))
                                                        (Econst_int (Int.repr 18) tint)
                                                        (tptr (Tstruct _ct_data_s noattr)))
                                                      (Tstruct _ct_data_s noattr))
                                                    _fc
                                                    (Tunion __anon_2c403fe6f6d2 noattr))
                                                  _code tushort))
                                              (Sset _val__6
                                                (Ecast
                                                  (Etempvar _t'45 tushort)
                                                  tint)))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'43
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'44
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'43 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__6 tint)
                                                          tushort)
                                                        (Etempvar _t'44 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'14
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'14 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'41
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'42
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'41 (tptr tuchar))
                                                              (Etempvar _t'14 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'42 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'15
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'15 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'39
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'40
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'39 (tptr tuchar))
                                                              (Etempvar _t'15 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'40 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'38
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__6 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'38 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'37
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'37 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__6 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'34
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'35
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bl_tree
                                                            (tarray (Tstruct _ct_data_s noattr) 39))
                                                          (Econst_int (Int.repr 18) tint)
                                                          (tptr (Tstruct _ct_data_s noattr)))
                                                        (Tstruct _ct_data_s noattr))
                                                      _fc
                                                      (Tunion __anon_2c403fe6f6d2 noattr))
                                                    _code tushort))
                                                (Ssequence
                                                  (Sset _t'36
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'34 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _t'35 tushort)
                                                          tushort)
                                                        (Etempvar _t'36 tint)
                                                        tint) tint)))))
                                            (Ssequence
                                              (Sset _t'33
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'33 tint)
                                                  (Etempvar _len__6 tint)
                                                  tint)))))))
                                    (Ssequence
                                      (Sset _len__7
                                        (Econst_int (Int.repr 7) tint))
                                      (Ssequence
                                        (Sset _t'20
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'20 tint)
                                                       (Ebinop Osub
                                                         (Ecast
                                                           (Econst_int (Int.repr 16) tint)
                                                           tint)
                                                         (Etempvar _len__7 tint)
                                                         tint) tint)
                                          (Ssequence
                                            (Sset _val__7
                                              (Ebinop Osub
                                                (Ecast (Etempvar _count tint)
                                                  tint)
                                                (Econst_int (Int.repr 11) tint)
                                                tint))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'30
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'31
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'30 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _val__7 tint)
                                                          tushort)
                                                        (Etempvar _t'31 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'16
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'16 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'28
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'29
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'28 (tptr tuchar))
                                                              (Etempvar _t'16 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oand
                                                                (Etempvar _t'29 tushort)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tint) tuchar)
                                                            tuchar)))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'17
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending tulong)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'17 tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong)))
                                                    (Ssequence
                                                      (Sset _t'26
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _pending_buf
                                                          (tptr tuchar)))
                                                      (Ssequence
                                                        (Sset _t'27
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _bi_buf tushort))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _t'26 (tptr tuchar))
                                                              (Etempvar _t'17 tulong)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ecast
                                                              (Ebinop Oshr
                                                                (Ecast
                                                                  (Etempvar _t'27 tushort)
                                                                  tushort)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tuchar)
                                                            tuchar))))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'25
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oshr
                                                        (Ecast
                                                          (Etempvar _val__7 tint)
                                                          tushort)
                                                        (Ebinop Osub
                                                          (Econst_int (Int.repr 16) tint)
                                                          (Etempvar _t'25 tint)
                                                          tint) tint)))
                                                  (Ssequence
                                                    (Sset _t'24
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'24 tint)
                                                        (Ebinop Osub
                                                          (Etempvar _len__7 tint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tint) tint)))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'22
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort))
                                              (Ssequence
                                                (Sset _t'23
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort)
                                                  (Ebinop Oor
                                                    (Etempvar _t'22 tushort)
                                                    (Ebinop Oshl
                                                      (Ecast
                                                        (Ebinop Osub
                                                          (Etempvar _count tint)
                                                          (Econst_int (Int.repr 11) tint)
                                                          tint) tushort)
                                                      (Etempvar _t'23 tint)
                                                      tint) tint))))
                                            (Ssequence
                                              (Sset _t'21
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'21 tint)
                                                  (Etempvar _len__7 tint)
                                                  tint)))))))))))))
                        (Ssequence
                          (Sset _count (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sset _prevlen (Etempvar _curlen tint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _nextlen tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Ssequence
                                (Sset _max_count
                                  (Econst_int (Int.repr 138) tint))
                                (Sset _min_count
                                  (Econst_int (Int.repr 3) tint)))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _curlen tint)
                                             (Etempvar _nextlen tint) tint)
                                (Ssequence
                                  (Sset _max_count
                                    (Econst_int (Int.repr 6) tint))
                                  (Sset _min_count
                                    (Econst_int (Int.repr 3) tint)))
                                (Ssequence
                                  (Sset _max_count
                                    (Econst_int (Int.repr 7) tint))
                                  (Sset _min_count
                                    (Econst_int (Int.repr 4) tint)))))))))))
                (Sset _n
                  (Ebinop Oadd (Etempvar _n tint)
                    (Econst_int (Int.repr 1) tint) tint))))))))))
|}.

Definition f_build_bl_tree := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_max_blindex, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tushort) :: (_t'2, tuchar) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _l_desc
          (Tstruct _tree_desc_s noattr)) _max_code tint))
    (Scall None
      (Evar _scan_tree (Tfunction
                         ((tptr (Tstruct _internal_state noattr)) ::
                          (tptr (Tstruct _ct_data_s noattr)) :: tint :: nil)
                         tvoid cc_default))
      ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
       (Ecast
         (Efield
           (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
             (Tstruct _internal_state noattr)) _dyn_ltree
           (tarray (Tstruct _ct_data_s noattr) 573))
         (tptr (Tstruct _ct_data_s noattr))) :: (Etempvar _t'5 tint) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _d_desc
            (Tstruct _tree_desc_s noattr)) _max_code tint))
      (Scall None
        (Evar _scan_tree (Tfunction
                           ((tptr (Tstruct _internal_state noattr)) ::
                            (tptr (Tstruct _ct_data_s noattr)) :: tint ::
                            nil) tvoid cc_default))
        ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
         (Ecast
           (Efield
             (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
               (Tstruct _internal_state noattr)) _dyn_dtree
             (tarray (Tstruct _ct_data_s noattr) 61))
           (tptr (Tstruct _ct_data_s noattr))) :: (Etempvar _t'4 tint) ::
         nil)))
    (Ssequence
      (Scall None
        (Evar _build_tree (Tfunction
                            ((tptr (Tstruct _internal_state noattr)) ::
                             (tptr (Tstruct _tree_desc_s noattr)) :: nil)
                            tvoid cc_default))
        ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
         (Ecast
           (Eaddrof
             (Efield
               (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                 (Tstruct _internal_state noattr)) _bl_desc
               (Tstruct _tree_desc_s noattr))
             (tptr (Tstruct _tree_desc_s noattr)))
           (tptr (Tstruct _tree_desc_s noattr))) :: nil))
      (Ssequence
        (Ssequence
          (Sset _max_blindex
            (Ebinop Osub (Econst_int (Int.repr 19) tint)
              (Econst_int (Int.repr 1) tint) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _max_blindex tint)
                             (Econst_int (Int.repr 3) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Evar _bl_order (tarray tuchar 19))
                      (Etempvar _max_blindex tint) (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bl_tree
                              (tarray (Tstruct _ct_data_s noattr) 39))
                            (Etempvar _t'2 tuchar)
                            (tptr (Tstruct _ct_data_s noattr)))
                          (Tstruct _ct_data_s noattr)) _dl
                        (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                  (Sifthenelse (Ebinop One (Etempvar _t'3 tushort)
                                 (Econst_int (Int.repr 0) tint) tint)
                    Sbreak
                    Sskip))))
            (Sset _max_blindex
              (Ebinop Osub (Etempvar _max_blindex tint)
                (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _opt_len tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _opt_len tulong)
              (Ebinop Oadd (Etempvar _t'1 tulong)
                (Ebinop Oadd
                  (Ebinop Oadd
                    (Ebinop Oadd
                      (Ebinop Omul (Econst_int (Int.repr 3) tint)
                        (Ebinop Oadd
                          (Ecast (Etempvar _max_blindex tint) tulong)
                          (Econst_int (Int.repr 1) tint) tulong) tulong)
                      (Econst_int (Int.repr 5) tint) tulong)
                    (Econst_int (Int.repr 5) tint) tulong)
                  (Econst_int (Int.repr 4) tint) tulong) tulong)))
          (Sreturn (Some (Etempvar _max_blindex tint))))))))
|}.

Definition f_send_all_trees := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_lcodes, tint) :: (_dcodes, tint) :: (_blcodes, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_rank, tint) :: (_len, tint) :: (_val, tint) ::
               (_len__1, tint) :: (_val__1, tint) :: (_len__2, tint) ::
               (_val__2, tint) :: (_len__3, tint) :: (_val__3, tint) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: (_t'60, tint) ::
               (_t'59, tushort) :: (_t'58, tushort) ::
               (_t'57, (tptr tuchar)) :: (_t'56, tushort) ::
               (_t'55, (tptr tuchar)) :: (_t'54, tint) :: (_t'53, tint) ::
               (_t'52, tint) :: (_t'51, tushort) :: (_t'50, tint) ::
               (_t'49, tint) :: (_t'48, tint) :: (_t'47, tushort) ::
               (_t'46, tushort) :: (_t'45, (tptr tuchar)) ::
               (_t'44, tushort) :: (_t'43, (tptr tuchar)) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tint) :: (_t'39, tushort) ::
               (_t'38, tint) :: (_t'37, tint) :: (_t'36, tint) ::
               (_t'35, tushort) :: (_t'34, tushort) ::
               (_t'33, (tptr tuchar)) :: (_t'32, tushort) ::
               (_t'31, (tptr tuchar)) :: (_t'30, tint) :: (_t'29, tint) ::
               (_t'28, tint) :: (_t'27, tushort) :: (_t'26, tint) ::
               (_t'25, tint) :: (_t'24, tushort) :: (_t'23, tuchar) ::
               (_t'22, tint) :: (_t'21, tushort) :: (_t'20, tushort) ::
               (_t'19, (tptr tuchar)) :: (_t'18, tushort) ::
               (_t'17, (tptr tuchar)) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tushort) :: (_t'12, tuchar) ::
               (_t'11, tushort) :: (_t'10, tint) :: (_t'9, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _len (Econst_int (Int.repr 5) tint))
    (Ssequence
      (Sset _t'49
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'49 tint)
                     (Ebinop Osub
                       (Ecast (Econst_int (Int.repr 16) tint) tint)
                       (Etempvar _len tint) tint) tint)
        (Ssequence
          (Sset _val
            (Ebinop Osub (Ecast (Etempvar _lcodes tint) tint)
              (Econst_int (Int.repr 257) tint) tint))
          (Ssequence
            (Ssequence
              (Sset _t'59
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'60
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort)
                  (Ebinop Oor (Etempvar _t'59 tushort)
                    (Ebinop Oshl (Ecast (Etempvar _val tint) tushort)
                      (Etempvar _t'60 tint) tint) tint))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'1 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'57
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'58
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'57 (tptr tuchar))
                            (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oand (Etempvar _t'58 tushort)
                              (Econst_int (Int.repr 255) tint) tint) tuchar)
                          tuchar)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'2 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'55
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'56
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'55 (tptr tuchar))
                            (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oshr
                              (Ecast (Etempvar _t'56 tushort) tushort)
                              (Econst_int (Int.repr 8) tint) tint) tuchar)
                          tuchar))))))
              (Ssequence
                (Ssequence
                  (Sset _t'54
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oshr (Ecast (Etempvar _val tint) tushort)
                      (Ebinop Osub (Econst_int (Int.repr 16) tint)
                        (Etempvar _t'54 tint) tint) tint)))
                (Ssequence
                  (Sset _t'53
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint)
                    (Ebinop Oadd (Etempvar _t'53 tint)
                      (Ebinop Osub (Etempvar _len tint)
                        (Econst_int (Int.repr 16) tint) tint) tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'51
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_buf tushort))
            (Ssequence
              (Sset _t'52
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort)
                (Ebinop Oor (Etempvar _t'51 tushort)
                  (Ebinop Oshl
                    (Ecast
                      (Ebinop Osub (Etempvar _lcodes tint)
                        (Econst_int (Int.repr 257) tint) tint) tushort)
                    (Etempvar _t'52 tint) tint) tint))))
          (Ssequence
            (Sset _t'50
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint)
              (Ebinop Oadd (Etempvar _t'50 tint) (Etempvar _len tint) tint)))))))
  (Ssequence
    (Ssequence
      (Sset _len__1 (Econst_int (Int.repr 5) tint))
      (Ssequence
        (Sset _t'37
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_valid tint))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'37 tint)
                       (Ebinop Osub
                         (Ecast (Econst_int (Int.repr 16) tint) tint)
                         (Etempvar _len__1 tint) tint) tint)
          (Ssequence
            (Sset _val__1
              (Ebinop Osub (Ecast (Etempvar _dcodes tint) tint)
                (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Ssequence
                (Sset _t'47
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Ssequence
                  (Sset _t'48
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'47 tushort)
                      (Ebinop Oshl (Ecast (Etempvar _val__1 tint) tushort)
                        (Etempvar _t'48 tint) tint) tint))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'3 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'45
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'46
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'45 (tptr tuchar))
                              (Etempvar _t'3 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oand (Etempvar _t'46 tushort)
                                (Econst_int (Int.repr 255) tint) tint)
                              tuchar) tuchar)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'4 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'43
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'44
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'43 (tptr tuchar))
                              (Etempvar _t'4 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oshr
                                (Ecast (Etempvar _t'44 tushort) tushort)
                                (Econst_int (Int.repr 8) tint) tint) tuchar)
                            tuchar))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'42
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_buf tushort)
                      (Ebinop Oshr (Ecast (Etempvar _val__1 tint) tushort)
                        (Ebinop Osub (Econst_int (Int.repr 16) tint)
                          (Etempvar _t'42 tint) tint) tint)))
                  (Ssequence
                    (Sset _t'41
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint)
                      (Ebinop Oadd (Etempvar _t'41 tint)
                        (Ebinop Osub (Etempvar _len__1 tint)
                          (Econst_int (Int.repr 16) tint) tint) tint)))))))
          (Ssequence
            (Ssequence
              (Sset _t'39
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'40
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort)
                  (Ebinop Oor (Etempvar _t'39 tushort)
                    (Ebinop Oshl
                      (Ecast
                        (Ebinop Osub (Etempvar _dcodes tint)
                          (Econst_int (Int.repr 1) tint) tint) tushort)
                      (Etempvar _t'40 tint) tint) tint))))
            (Ssequence
              (Sset _t'38
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint)
                (Ebinop Oadd (Etempvar _t'38 tint) (Etempvar _len__1 tint)
                  tint)))))))
    (Ssequence
      (Ssequence
        (Sset _len__2 (Econst_int (Int.repr 4) tint))
        (Ssequence
          (Sset _t'25
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _bi_valid tint))
          (Sifthenelse (Ebinop Ogt (Etempvar _t'25 tint)
                         (Ebinop Osub
                           (Ecast (Econst_int (Int.repr 16) tint) tint)
                           (Etempvar _len__2 tint) tint) tint)
            (Ssequence
              (Sset _val__2
                (Ebinop Osub (Ecast (Etempvar _blcodes tint) tint)
                  (Econst_int (Int.repr 4) tint) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'35
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort))
                  (Ssequence
                    (Sset _t'36
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_buf tushort)
                      (Ebinop Oor (Etempvar _t'35 tushort)
                        (Ebinop Oshl (Ecast (Etempvar _val__2 tint) tushort)
                          (Etempvar _t'36 tint) tint) tint))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending
                            tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending
                            tulong)
                          (Ebinop Oadd (Etempvar _t'5 tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))
                      (Ssequence
                        (Sset _t'33
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending_buf
                            (tptr tuchar)))
                        (Ssequence
                          (Sset _t'34
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _t'33 (tptr tuchar))
                                (Etempvar _t'5 tulong) (tptr tuchar)) tuchar)
                            (Ecast
                              (Ecast
                                (Ebinop Oand (Etempvar _t'34 tushort)
                                  (Econst_int (Int.repr 255) tint) tint)
                                tuchar) tuchar)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending
                            tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending
                            tulong)
                          (Ebinop Oadd (Etempvar _t'6 tulong)
                            (Econst_int (Int.repr 1) tint) tulong)))
                      (Ssequence
                        (Sset _t'31
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _pending_buf
                            (tptr tuchar)))
                        (Ssequence
                          (Sset _t'32
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _t'31 (tptr tuchar))
                                (Etempvar _t'6 tulong) (tptr tuchar)) tuchar)
                            (Ecast
                              (Ecast
                                (Ebinop Oshr
                                  (Ecast (Etempvar _t'32 tushort) tushort)
                                  (Econst_int (Int.repr 8) tint) tint)
                                tuchar) tuchar))))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'30
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_valid tint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort)
                        (Ebinop Oshr (Ecast (Etempvar _val__2 tint) tushort)
                          (Ebinop Osub (Econst_int (Int.repr 16) tint)
                            (Etempvar _t'30 tint) tint) tint)))
                    (Ssequence
                      (Sset _t'29
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_valid tint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_valid tint)
                        (Ebinop Oadd (Etempvar _t'29 tint)
                          (Ebinop Osub (Etempvar _len__2 tint)
                            (Econst_int (Int.repr 16) tint) tint) tint)))))))
            (Ssequence
              (Ssequence
                (Sset _t'27
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Ssequence
                  (Sset _t'28
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'27 tushort)
                      (Ebinop Oshl
                        (Ecast
                          (Ebinop Osub (Etempvar _blcodes tint)
                            (Econst_int (Int.repr 4) tint) tint) tushort)
                        (Etempvar _t'28 tint) tint) tint))))
              (Ssequence
                (Sset _t'26
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint)
                  (Ebinop Oadd (Etempvar _t'26 tint) (Etempvar _len__2 tint)
                    tint)))))))
      (Ssequence
        (Ssequence
          (Sset _rank (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _rank tint)
                             (Etempvar _blcodes tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _len__3 (Econst_int (Int.repr 3) tint))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sifthenelse (Ebinop Ogt (Etempvar _t'9 tint)
                                 (Ebinop Osub
                                   (Ecast (Econst_int (Int.repr 16) tint)
                                     tint) (Etempvar _len__3 tint) tint)
                                 tint)
                    (Ssequence
                      (Ssequence
                        (Sset _t'23
                          (Ederef
                            (Ebinop Oadd (Evar _bl_order (tarray tuchar 19))
                              (Etempvar _rank tint) (tptr tuchar)) tuchar))
                        (Ssequence
                          (Sset _t'24
                            (Efield
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bl_tree
                                      (tarray (Tstruct _ct_data_s noattr) 39))
                                    (Etempvar _t'23 tuchar)
                                    (tptr (Tstruct _ct_data_s noattr)))
                                  (Tstruct _ct_data_s noattr)) _dl
                                (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                          (Sset _val__3
                            (Ecast (Etempvar _t'24 tushort) tint))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'21
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort))
                          (Ssequence
                            (Sset _t'22
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_valid
                                tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_buf
                                tushort)
                              (Ebinop Oor (Etempvar _t'21 tushort)
                                (Ebinop Oshl
                                  (Ecast (Etempvar _val__3 tint) tushort)
                                  (Etempvar _t'22 tint) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'7 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'19
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'20
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'19 (tptr tuchar))
                                        (Etempvar _t'7 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oand (Etempvar _t'20 tushort)
                                          (Econst_int (Int.repr 255) tint)
                                          tint) tuchar) tuchar)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'8
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'8 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'17
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'18
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'17 (tptr tuchar))
                                        (Etempvar _t'8 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oshr
                                          (Ecast (Etempvar _t'18 tushort)
                                            tushort)
                                          (Econst_int (Int.repr 8) tint)
                                          tint) tuchar) tuchar))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'16
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _bi_buf
                                  tushort)
                                (Ebinop Oshr
                                  (Ecast (Etempvar _val__3 tint) tushort)
                                  (Ebinop Osub
                                    (Econst_int (Int.repr 16) tint)
                                    (Etempvar _t'16 tint) tint) tint)))
                            (Ssequence
                              (Sset _t'15
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint)
                                (Ebinop Oadd (Etempvar _t'15 tint)
                                  (Ebinop Osub (Etempvar _len__3 tint)
                                    (Econst_int (Int.repr 16) tint) tint)
                                  tint)))))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Ssequence
                          (Sset _t'12
                            (Ederef
                              (Ebinop Oadd
                                (Evar _bl_order (tarray tuchar 19))
                                (Etempvar _rank tint) (tptr tuchar)) tuchar))
                          (Ssequence
                            (Sset _t'13
                              (Efield
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bl_tree
                                        (tarray (Tstruct _ct_data_s noattr) 39))
                                      (Etempvar _t'12 tuchar)
                                      (tptr (Tstruct _ct_data_s noattr)))
                                    (Tstruct _ct_data_s noattr)) _dl
                                  (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                            (Ssequence
                              (Sset _t'14
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _bi_buf
                                  tushort)
                                (Ebinop Oor (Etempvar _t'11 tushort)
                                  (Ebinop Oshl
                                    (Ecast (Etempvar _t'13 tushort) tushort)
                                    (Etempvar _t'14 tint) tint) tint))))))
                      (Ssequence
                        (Sset _t'10
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint)
                          (Ebinop Oadd (Etempvar _t'10 tint)
                            (Etempvar _len__3 tint) tint))))))))
            (Sset _rank
              (Ebinop Oadd (Etempvar _rank tint)
                (Econst_int (Int.repr 1) tint) tint))))
        (Ssequence
          (Scall None
            (Evar _send_tree (Tfunction
                               ((tptr (Tstruct _internal_state noattr)) ::
                                (tptr (Tstruct _ct_data_s noattr)) :: tint ::
                                nil) tvoid cc_default))
            ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
             (Ecast
               (Efield
                 (Ederef
                   (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                   (Tstruct _internal_state noattr)) _dyn_ltree
                 (tarray (Tstruct _ct_data_s noattr) 573))
               (tptr (Tstruct _ct_data_s noattr))) ::
             (Ebinop Osub (Etempvar _lcodes tint)
               (Econst_int (Int.repr 1) tint) tint) :: nil))
          (Scall None
            (Evar _send_tree (Tfunction
                               ((tptr (Tstruct _internal_state noattr)) ::
                                (tptr (Tstruct _ct_data_s noattr)) :: tint ::
                                nil) tvoid cc_default))
            ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
             (Ecast
               (Efield
                 (Ederef
                   (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                   (Tstruct _internal_state noattr)) _dyn_dtree
                 (tarray (Tstruct _ct_data_s noattr) 61))
               (tptr (Tstruct _ct_data_s noattr))) ::
             (Ebinop Osub (Etempvar _dcodes tint)
               (Econst_int (Int.repr 1) tint) tint) :: nil)))))))
|}.

Definition f__tr_stored_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_buf, (tptr tschar)) :: (_stored_len, tulong) ::
                (_last, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tint) :: (_val, tint) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: (_t'25, tint) ::
               (_t'24, tushort) :: (_t'23, tushort) ::
               (_t'22, (tptr tuchar)) :: (_t'21, tushort) ::
               (_t'20, (tptr tuchar)) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tushort) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, (tptr tuchar)) ::
               (_t'12, (tptr tuchar)) :: (_t'11, (tptr tuchar)) ::
               (_t'10, (tptr tuchar)) :: (_t'9, tulong) ::
               (_t'8, (tptr tuchar)) :: (_t'7, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _len (Econst_int (Int.repr 3) tint))
    (Ssequence
      (Sset _t'14
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'14 tint)
                     (Ebinop Osub
                       (Ecast (Econst_int (Int.repr 16) tint) tint)
                       (Etempvar _len tint) tint) tint)
        (Ssequence
          (Sset _val
            (Ebinop Oadd
              (Ecast
                (Ebinop Oshl (Econst_int (Int.repr 0) tint)
                  (Econst_int (Int.repr 1) tint) tint) tint)
              (Etempvar _last tint) tint))
          (Ssequence
            (Ssequence
              (Sset _t'24
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'25
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort)
                  (Ebinop Oor (Etempvar _t'24 tushort)
                    (Ebinop Oshl (Ecast (Etempvar _val tint) tushort)
                      (Etempvar _t'25 tint) tint) tint))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'1 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'22
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'23
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'22 (tptr tuchar))
                            (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oand (Etempvar _t'23 tushort)
                              (Econst_int (Int.repr 255) tint) tint) tuchar)
                          tuchar)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'2 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'20
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'21
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'20 (tptr tuchar))
                            (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oshr
                              (Ecast (Etempvar _t'21 tushort) tushort)
                              (Econst_int (Int.repr 8) tint) tint) tuchar)
                          tuchar))))))
              (Ssequence
                (Ssequence
                  (Sset _t'19
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oshr (Ecast (Etempvar _val tint) tushort)
                      (Ebinop Osub (Econst_int (Int.repr 16) tint)
                        (Etempvar _t'19 tint) tint) tint)))
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint)
                    (Ebinop Oadd (Etempvar _t'18 tint)
                      (Ebinop Osub (Etempvar _len tint)
                        (Econst_int (Int.repr 16) tint) tint) tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'16
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_buf tushort))
            (Ssequence
              (Sset _t'17
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort)
                (Ebinop Oor (Etempvar _t'16 tushort)
                  (Ebinop Oshl
                    (Ecast
                      (Ebinop Oadd
                        (Ebinop Oshl (Econst_int (Int.repr 0) tint)
                          (Econst_int (Int.repr 1) tint) tint)
                        (Etempvar _last tint) tint) tushort)
                    (Etempvar _t'17 tint) tint) tint))))
          (Ssequence
            (Sset _t'15
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint)
              (Ebinop Oadd (Etempvar _t'15 tint) (Etempvar _len tint) tint)))))))
  (Ssequence
    (Scall None
      (Evar _bi_windup (Tfunction
                         ((tptr (Tstruct _internal_state noattr)) :: nil)
                         tvoid cc_default))
      ((Etempvar _s (tptr (Tstruct _internal_state noattr))) :: nil))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'3 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'13 (tptr tuchar))
                  (Etempvar _t'3 tulong) (tptr tuchar)) tuchar)
              (Ecast
                (Ecast
                  (Ebinop Oand (Ecast (Etempvar _stored_len tulong) tushort)
                    (Econst_int (Int.repr 255) tint) tint) tuchar) tuchar))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'4 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending_buf
                (tptr tuchar)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _t'12 (tptr tuchar))
                  (Etempvar _t'4 tulong) (tptr tuchar)) tuchar)
              (Ecast
                (Ecast
                  (Ebinop Oshr
                    (Ecast (Ecast (Etempvar _stored_len tulong) tushort)
                      tushort) (Econst_int (Int.repr 8) tint) tint) tuchar)
                tuchar)))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong)
                (Ebinop Oadd (Etempvar _t'5 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending_buf
                  (tptr tuchar)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'11 (tptr tuchar))
                    (Etempvar _t'5 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oand
                      (Ecast
                        (Eunop Onotint (Etempvar _stored_len tulong) tulong)
                        tushort) (Econst_int (Int.repr 255) tint) tint)
                    tuchar) tuchar))))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending tulong)
                (Ebinop Oadd (Etempvar _t'6 tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending_buf
                  (tptr tuchar)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _t'10 (tptr tuchar))
                    (Etempvar _t'6 tulong) (tptr tuchar)) tuchar)
                (Ecast
                  (Ecast
                    (Ebinop Oshr
                      (Ecast
                        (Ecast
                          (Eunop Onotint (Etempvar _stored_len tulong)
                            tulong) tushort) tushort)
                      (Econst_int (Int.repr 8) tint) tint) tuchar) tuchar)))))
        (Ssequence
          (Sifthenelse (Etempvar _stored_len tulong)
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _pending_buf
                  (tptr tuchar)))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _pending tulong))
                (Scall None
                  (Evar _memcpy (Tfunction
                                  ((tptr tvoid) :: (tptr tvoid) :: tulong ::
                                   nil) (tptr tvoid) cc_default))
                  ((Ebinop Oadd (Etempvar _t'8 (tptr tuchar))
                     (Etempvar _t'9 tulong) (tptr tuchar)) ::
                   (Ecast (Etempvar _buf (tptr tschar)) (tptr tuchar)) ::
                   (Etempvar _stored_len tulong) :: nil))))
            Sskip)
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _pending tulong)
              (Ebinop Oadd (Etempvar _t'7 tulong)
                (Etempvar _stored_len tulong) tulong))))))))
|}.

Definition f__tr_flush_bits := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _bi_flush (Tfunction ((tptr (Tstruct _internal_state noattr)) :: nil)
                    tvoid cc_default))
  ((Etempvar _s (tptr (Tstruct _internal_state noattr))) :: nil))
|}.

Definition f__tr_align := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tint) :: (_val, tint) :: (_len__1, tint) ::
               (_val__1, tint) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: (_t'30, tint) ::
               (_t'29, tushort) :: (_t'28, tushort) ::
               (_t'27, (tptr tuchar)) :: (_t'26, tushort) ::
               (_t'25, (tptr tuchar)) :: (_t'24, tint) :: (_t'23, tint) ::
               (_t'22, tint) :: (_t'21, tushort) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, tushort) :: (_t'17, tint) ::
               (_t'16, tushort) :: (_t'15, tushort) ::
               (_t'14, (tptr tuchar)) :: (_t'13, tushort) ::
               (_t'12, (tptr tuchar)) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tushort) :: (_t'7, tushort) ::
               (_t'6, tint) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _len (Econst_int (Int.repr 3) tint))
    (Ssequence
      (Sset _t'19
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _bi_valid tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'19 tint)
                     (Ebinop Osub
                       (Ecast (Econst_int (Int.repr 16) tint) tint)
                       (Etempvar _len tint) tint) tint)
        (Ssequence
          (Sset _val
            (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tint)
              (Econst_int (Int.repr 1) tint) tint))
          (Ssequence
            (Ssequence
              (Sset _t'29
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'30
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_valid tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort)
                  (Ebinop Oor (Etempvar _t'29 tushort)
                    (Ebinop Oshl (Ecast (Etempvar _val tint) tushort)
                      (Etempvar _t'30 tint) tint) tint))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'1
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'1 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'27
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'28
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'27 (tptr tuchar))
                            (Etempvar _t'1 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oand (Etempvar _t'28 tushort)
                              (Econst_int (Int.repr 255) tint) tint) tuchar)
                          tuchar)))))
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending tulong)
                      (Ebinop Oadd (Etempvar _t'2 tulong)
                        (Econst_int (Int.repr 1) tint) tulong)))
                  (Ssequence
                    (Sset _t'25
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _pending_buf
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'26
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_buf
                          tushort))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'25 (tptr tuchar))
                            (Etempvar _t'2 tulong) (tptr tuchar)) tuchar)
                        (Ecast
                          (Ecast
                            (Ebinop Oshr
                              (Ecast (Etempvar _t'26 tushort) tushort)
                              (Econst_int (Int.repr 8) tint) tint) tuchar)
                          tuchar))))))
              (Ssequence
                (Ssequence
                  (Sset _t'24
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oshr (Ecast (Etempvar _val tint) tushort)
                      (Ebinop Osub (Econst_int (Int.repr 16) tint)
                        (Etempvar _t'24 tint) tint) tint)))
                (Ssequence
                  (Sset _t'23
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint)
                    (Ebinop Oadd (Etempvar _t'23 tint)
                      (Ebinop Osub (Etempvar _len tint)
                        (Econst_int (Int.repr 16) tint) tint) tint)))))))
        (Ssequence
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_buf tushort))
            (Ssequence
              (Sset _t'22
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort)
                (Ebinop Oor (Etempvar _t'21 tushort)
                  (Ebinop Oshl
                    (Ecast
                      (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                        (Econst_int (Int.repr 1) tint) tint) tushort)
                    (Etempvar _t'22 tint) tint) tint))))
          (Ssequence
            (Sset _t'20
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _bi_valid tint)
              (Ebinop Oadd (Etempvar _t'20 tint) (Etempvar _len tint) tint)))))))
  (Ssequence
    (Ssequence
      (Sset _len__1
        (Efield
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar _static_ltree (tarray (Tstruct _ct_data_s noattr) 288))
                (Econst_int (Int.repr 256) tint)
                (tptr (Tstruct _ct_data_s noattr)))
              (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
          tushort))
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_valid tint))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'5 tint)
                       (Ebinop Osub
                         (Ecast (Econst_int (Int.repr 16) tint) tint)
                         (Etempvar _len__1 tint) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'18
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _static_ltree (tarray (Tstruct _ct_data_s noattr) 288))
                        (Econst_int (Int.repr 256) tint)
                        (tptr (Tstruct _ct_data_s noattr)))
                      (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                  _code tushort))
              (Sset _val__1 (Ecast (Etempvar _t'18 tushort) tint)))
            (Ssequence
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Ssequence
                  (Sset _t'17
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'16 tushort)
                      (Ebinop Oshl (Ecast (Etempvar _val__1 tint) tushort)
                        (Etempvar _t'17 tint) tint) tint))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'3
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'3 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'14
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'15
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'14 (tptr tuchar))
                              (Etempvar _t'3 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oand (Etempvar _t'15 tushort)
                                (Econst_int (Int.repr 255) tint) tint)
                              tuchar) tuchar)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'4 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'12
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'13
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'12 (tptr tuchar))
                              (Etempvar _t'4 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oshr
                                (Ecast (Etempvar _t'13 tushort) tushort)
                                (Econst_int (Int.repr 8) tint) tint) tuchar)
                            tuchar))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_buf tushort)
                      (Ebinop Oshr (Ecast (Etempvar _val__1 tint) tushort)
                        (Ebinop Osub (Econst_int (Int.repr 16) tint)
                          (Etempvar _t'11 tint) tint) tint)))
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint)
                      (Ebinop Oadd (Etempvar _t'10 tint)
                        (Ebinop Osub (Etempvar _len__1 tint)
                          (Econst_int (Int.repr 16) tint) tint) tint)))))))
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _static_ltree (tarray (Tstruct _ct_data_s noattr) 288))
                          (Econst_int (Int.repr 256) tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'7 tushort)
                      (Ebinop Oshl (Ecast (Etempvar _t'8 tushort) tushort)
                        (Etempvar _t'9 tint) tint) tint)))))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint)
                (Ebinop Oadd (Etempvar _t'6 tint) (Etempvar _len__1 tint)
                  tint)))))))
    (Scall None
      (Evar _bi_flush (Tfunction
                        ((tptr (Tstruct _internal_state noattr)) :: nil)
                        tvoid cc_default))
      ((Etempvar _s (tptr (Tstruct _internal_state noattr))) :: nil))))
|}.

Definition f_compress_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_ltree, (tptr (Tstruct _ct_data_s noattr))) ::
                (_dtree, (tptr (Tstruct _ct_data_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_dist, tuint) :: (_lc, tint) :: (_sx, tuint) ::
               (_code, tuint) :: (_extra, tint) :: (_len, tint) ::
               (_val, tint) :: (_len__1, tint) :: (_val__1, tint) ::
               (_len__2, tint) :: (_val__2, tint) :: (_len__3, tint) ::
               (_val__3, tint) :: (_len__4, tint) :: (_val__4, tint) ::
               (_len__5, tint) :: (_val__5, tint) :: (_t'16, tulong) ::
               (_t'15, tulong) :: (_t'14, tulong) :: (_t'13, tulong) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tint) ::
               (_t'9, tulong) :: (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'107, tuchar) :: (_t'106, (tptr tuchar)) ::
               (_t'105, tuchar) :: (_t'104, (tptr tuchar)) ::
               (_t'103, (tptr tuchar)) :: (_t'102, tushort) ::
               (_t'101, tint) :: (_t'100, tushort) :: (_t'99, tushort) ::
               (_t'98, (tptr tuchar)) :: (_t'97, tushort) ::
               (_t'96, (tptr tuchar)) :: (_t'95, tint) :: (_t'94, tint) ::
               (_t'93, tint) :: (_t'92, tushort) :: (_t'91, tushort) ::
               (_t'90, tint) :: (_t'89, tint) :: (_t'88, tushort) ::
               (_t'87, tint) :: (_t'86, tushort) :: (_t'85, tushort) ::
               (_t'84, (tptr tuchar)) :: (_t'83, tushort) ::
               (_t'82, (tptr tuchar)) :: (_t'81, tint) :: (_t'80, tint) ::
               (_t'79, tint) :: (_t'78, tushort) :: (_t'77, tushort) ::
               (_t'76, tint) :: (_t'75, tint) :: (_t'74, tint) ::
               (_t'73, tint) :: (_t'72, tushort) :: (_t'71, tushort) ::
               (_t'70, (tptr tuchar)) :: (_t'69, tushort) ::
               (_t'68, (tptr tuchar)) :: (_t'67, tint) :: (_t'66, tint) ::
               (_t'65, tint) :: (_t'64, tushort) :: (_t'63, tint) ::
               (_t'62, tint) :: (_t'61, tuchar) :: (_t'60, tuchar) ::
               (_t'59, tushort) :: (_t'58, tint) :: (_t'57, tushort) ::
               (_t'56, tushort) :: (_t'55, (tptr tuchar)) ::
               (_t'54, tushort) :: (_t'53, (tptr tuchar)) :: (_t'52, tint) ::
               (_t'51, tint) :: (_t'50, tint) :: (_t'49, tushort) ::
               (_t'48, tushort) :: (_t'47, tint) :: (_t'46, tint) ::
               (_t'45, tint) :: (_t'44, tint) :: (_t'43, tushort) ::
               (_t'42, tushort) :: (_t'41, (tptr tuchar)) ::
               (_t'40, tushort) :: (_t'39, (tptr tuchar)) :: (_t'38, tint) ::
               (_t'37, tint) :: (_t'36, tint) :: (_t'35, tushort) ::
               (_t'34, tint) :: (_t'33, tint) :: (_t'32, tuint) ::
               (_t'31, tuint) :: (_t'30, tushort) :: (_t'29, tint) ::
               (_t'28, tushort) :: (_t'27, tushort) ::
               (_t'26, (tptr tuchar)) :: (_t'25, tushort) ::
               (_t'24, (tptr tuchar)) :: (_t'23, tint) :: (_t'22, tint) ::
               (_t'21, tint) :: (_t'20, tushort) :: (_t'19, tushort) ::
               (_t'18, tint) :: (_t'17, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _sx (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _t'31
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _sym_next tuint))
      (Sifthenelse (Ebinop One (Etempvar _t'31 tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Sloop
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1 (Etempvar _sx tuint))
                (Sset _sx
                  (Ebinop Oadd (Etempvar _t'1 tuint)
                    (Econst_int (Int.repr 1) tint) tuint)))
              (Ssequence
                (Sset _t'106
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _sym_buf
                    (tptr tuchar)))
                (Ssequence
                  (Sset _t'107
                    (Ederef
                      (Ebinop Oadd (Etempvar _t'106 (tptr tuchar))
                        (Etempvar _t'1 tuint) (tptr tuchar)) tuchar))
                  (Sset _dist
                    (Ebinop Oand (Etempvar _t'107 tuchar)
                      (Econst_int (Int.repr 255) tint) tint)))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'2 (Etempvar _sx tuint))
                  (Sset _sx
                    (Ebinop Oadd (Etempvar _t'2 tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))
                (Ssequence
                  (Sset _t'104
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _sym_buf
                      (tptr tuchar)))
                  (Ssequence
                    (Sset _t'105
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'104 (tptr tuchar))
                          (Etempvar _t'2 tuint) (tptr tuchar)) tuchar))
                    (Sset _dist
                      (Ebinop Oadd (Etempvar _dist tuint)
                        (Ebinop Oshl
                          (Ecast
                            (Ebinop Oand (Etempvar _t'105 tuchar)
                              (Econst_int (Int.repr 255) tint) tint) tuint)
                          (Econst_int (Int.repr 8) tint) tuint) tuint)))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'3 (Etempvar _sx tuint))
                    (Sset _sx
                      (Ebinop Oadd (Etempvar _t'3 tuint)
                        (Econst_int (Int.repr 1) tint) tuint)))
                  (Ssequence
                    (Sset _t'103
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _sym_buf
                        (tptr tuchar)))
                    (Sset _lc
                      (Ederef
                        (Ebinop Oadd (Etempvar _t'103 (tptr tuchar))
                          (Etempvar _t'3 tuint) (tptr tuchar)) tuchar))))
                (Sifthenelse (Ebinop Oeq (Etempvar _dist tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Ssequence
                    (Sset _len
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                              (Etempvar _lc tint)
                              (tptr (Tstruct _ct_data_s noattr)))
                            (Tstruct _ct_data_s noattr)) _dl
                          (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                    (Ssequence
                      (Sset _t'89
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _bi_valid tint))
                      (Sifthenelse (Ebinop Ogt (Etempvar _t'89 tint)
                                     (Ebinop Osub
                                       (Ecast (Econst_int (Int.repr 16) tint)
                                         tint) (Etempvar _len tint) tint)
                                     tint)
                        (Ssequence
                          (Ssequence
                            (Sset _t'102
                              (Efield
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                                      (Etempvar _lc tint)
                                      (tptr (Tstruct _ct_data_s noattr)))
                                    (Tstruct _ct_data_s noattr)) _fc
                                  (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                            (Sset _val
                              (Ecast (Etempvar _t'102 tushort) tint)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'100
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _bi_buf
                                  tushort))
                              (Ssequence
                                (Sset _t'101
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_valid tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_buf tushort)
                                  (Ebinop Oor (Etempvar _t'100 tushort)
                                    (Ebinop Oshl
                                      (Ecast (Etempvar _val tint) tushort)
                                      (Etempvar _t'101 tint) tint) tint))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'4
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending tulong)
                                      (Ebinop Oadd (Etempvar _t'4 tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong)))
                                  (Ssequence
                                    (Sset _t'98
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending_buf (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'99
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_buf tushort))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'98 (tptr tuchar))
                                            (Etempvar _t'4 tulong)
                                            (tptr tuchar)) tuchar)
                                        (Ecast
                                          (Ecast
                                            (Ebinop Oand
                                              (Etempvar _t'99 tushort)
                                              (Econst_int (Int.repr 255) tint)
                                              tint) tuchar) tuchar)))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'5
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending tulong))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending tulong)
                                      (Ebinop Oadd (Etempvar _t'5 tulong)
                                        (Econst_int (Int.repr 1) tint)
                                        tulong)))
                                  (Ssequence
                                    (Sset _t'96
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _pending_buf (tptr tuchar)))
                                    (Ssequence
                                      (Sset _t'97
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_buf tushort))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'96 (tptr tuchar))
                                            (Etempvar _t'5 tulong)
                                            (tptr tuchar)) tuchar)
                                        (Ecast
                                          (Ecast
                                            (Ebinop Oshr
                                              (Ecast (Etempvar _t'97 tushort)
                                                tushort)
                                              (Econst_int (Int.repr 8) tint)
                                              tint) tuchar) tuchar))))))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'95
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_valid tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort)
                                    (Ebinop Oshr
                                      (Ecast (Etempvar _val tint) tushort)
                                      (Ebinop Osub
                                        (Econst_int (Int.repr 16) tint)
                                        (Etempvar _t'95 tint) tint) tint)))
                                (Ssequence
                                  (Sset _t'94
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_valid tint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_valid tint)
                                    (Ebinop Oadd (Etempvar _t'94 tint)
                                      (Ebinop Osub (Etempvar _len tint)
                                        (Econst_int (Int.repr 16) tint) tint)
                                      tint)))))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'91
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_buf
                                tushort))
                            (Ssequence
                              (Sset _t'92
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                                        (Etempvar _lc tint)
                                        (tptr (Tstruct _ct_data_s noattr)))
                                      (Tstruct _ct_data_s noattr)) _fc
                                    (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                              (Ssequence
                                (Sset _t'93
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_valid tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_buf tushort)
                                  (Ebinop Oor (Etempvar _t'91 tushort)
                                    (Ebinop Oshl
                                      (Ecast (Etempvar _t'92 tushort)
                                        tushort) (Etempvar _t'93 tint) tint)
                                    tint)))))
                          (Ssequence
                            (Sset _t'90
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_valid
                                tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_valid
                                tint)
                              (Ebinop Oadd (Etempvar _t'90 tint)
                                (Etempvar _len tint) tint)))))))
                  (Ssequence
                    (Sset _code
                      (Ederef
                        (Ebinop Oadd (Evar __length_code (tarray tuchar 256))
                          (Etempvar _lc tint) (tptr tuchar)) tuchar))
                    (Ssequence
                      (Ssequence
                        (Sset _len__1
                          (Efield
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                                  (Ebinop Oadd
                                    (Ebinop Oadd (Etempvar _code tuint)
                                      (Econst_int (Int.repr 256) tint) tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)
                                  (tptr (Tstruct _ct_data_s noattr)))
                                (Tstruct _ct_data_s noattr)) _dl
                              (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                        (Ssequence
                          (Sset _t'75
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_valid
                              tint))
                          (Sifthenelse (Ebinop Ogt (Etempvar _t'75 tint)
                                         (Ebinop Osub
                                           (Ecast
                                             (Econst_int (Int.repr 16) tint)
                                             tint) (Etempvar _len__1 tint)
                                           tint) tint)
                            (Ssequence
                              (Ssequence
                                (Sset _t'88
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Etempvar _code tuint)
                                              (Econst_int (Int.repr 256) tint)
                                              tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint)
                                          (tptr (Tstruct _ct_data_s noattr)))
                                        (Tstruct _ct_data_s noattr)) _fc
                                      (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                                (Sset _val__1
                                  (Ecast (Etempvar _t'88 tushort) tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'86
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Ssequence
                                    (Sset _t'87
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_valid tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_buf tushort)
                                      (Ebinop Oor (Etempvar _t'86 tushort)
                                        (Ebinop Oshl
                                          (Ecast (Etempvar _val__1 tint)
                                            tushort) (Etempvar _t'87 tint)
                                          tint) tint))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'6
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending tulong))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending tulong)
                                          (Ebinop Oadd (Etempvar _t'6 tulong)
                                            (Econst_int (Int.repr 1) tint)
                                            tulong)))
                                      (Ssequence
                                        (Sset _t'84
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending_buf (tptr tuchar)))
                                        (Ssequence
                                          (Sset _t'85
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'84 (tptr tuchar))
                                                (Etempvar _t'6 tulong)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ecast
                                                (Ebinop Oand
                                                  (Etempvar _t'85 tushort)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tint) tuchar) tuchar)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'7
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending tulong))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending tulong)
                                          (Ebinop Oadd (Etempvar _t'7 tulong)
                                            (Econst_int (Int.repr 1) tint)
                                            tulong)))
                                      (Ssequence
                                        (Sset _t'82
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _pending_buf (tptr tuchar)))
                                        (Ssequence
                                          (Sset _t'83
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _t'82 (tptr tuchar))
                                                (Etempvar _t'7 tulong)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ecast
                                                (Ebinop Oshr
                                                  (Ecast
                                                    (Etempvar _t'83 tushort)
                                                    tushort)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tint) tuchar) tuchar))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'81
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_valid tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_buf tushort)
                                        (Ebinop Oshr
                                          (Ecast (Etempvar _val__1 tint)
                                            tushort)
                                          (Ebinop Osub
                                            (Econst_int (Int.repr 16) tint)
                                            (Etempvar _t'81 tint) tint) tint)))
                                    (Ssequence
                                      (Sset _t'80
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_valid tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                            (Tstruct _internal_state noattr))
                                          _bi_valid tint)
                                        (Ebinop Oadd (Etempvar _t'80 tint)
                                          (Ebinop Osub
                                            (Etempvar _len__1 tint)
                                            (Econst_int (Int.repr 16) tint)
                                            tint) tint)))))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'77
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_buf tushort))
                                (Ssequence
                                  (Sset _t'78
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _code tuint)
                                                (Econst_int (Int.repr 256) tint)
                                                tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _fc
                                        (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                                  (Ssequence
                                    (Sset _t'79
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_valid tint))
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_buf tushort)
                                      (Ebinop Oor (Etempvar _t'77 tushort)
                                        (Ebinop Oshl
                                          (Ecast (Etempvar _t'78 tushort)
                                            tushort) (Etempvar _t'79 tint)
                                          tint) tint)))))
                              (Ssequence
                                (Sset _t'76
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_valid tint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _bi_valid tint)
                                  (Ebinop Oadd (Etempvar _t'76 tint)
                                    (Etempvar _len__1 tint) tint)))))))
                      (Ssequence
                        (Sset _extra
                          (Ederef
                            (Ebinop Oadd (Evar _extra_lbits (tarray tint 29))
                              (Etempvar _code tuint) (tptr tint)) tint))
                        (Ssequence
                          (Sifthenelse (Ebinop One (Etempvar _extra tint)
                                         (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Ssequence
                                (Sset _t'74
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _base_length (tarray tint 29))
                                      (Etempvar _code tuint) (tptr tint))
                                    tint))
                                (Sset _lc
                                  (Ebinop Osub (Etempvar _lc tint)
                                    (Etempvar _t'74 tint) tint)))
                              (Ssequence
                                (Sset _len__2 (Etempvar _extra tint))
                                (Ssequence
                                  (Sset _t'62
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_valid tint))
                                  (Sifthenelse (Ebinop Ogt
                                                 (Etempvar _t'62 tint)
                                                 (Ebinop Osub
                                                   (Ecast
                                                     (Econst_int (Int.repr 16) tint)
                                                     tint)
                                                   (Etempvar _len__2 tint)
                                                   tint) tint)
                                    (Ssequence
                                      (Sset _val__2
                                        (Ecast (Etempvar _lc tint) tint))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'72
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort))
                                          (Ssequence
                                            (Sset _t'73
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bi_valid tint))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bi_buf tushort)
                                              (Ebinop Oor
                                                (Etempvar _t'72 tushort)
                                                (Ebinop Oshl
                                                  (Ecast
                                                    (Etempvar _val__2 tint)
                                                    tushort)
                                                  (Etempvar _t'73 tint) tint)
                                                tint))))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'8
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending tulong))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending tulong)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'8 tulong)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tulong)))
                                              (Ssequence
                                                (Sset _t'70
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending_buf
                                                    (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'71
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'70 (tptr tuchar))
                                                        (Etempvar _t'8 tulong)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Ecast
                                                      (Ecast
                                                        (Ebinop Oand
                                                          (Etempvar _t'71 tushort)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tint) tuchar)
                                                      tuchar)))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'9
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending tulong))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending tulong)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'9 tulong)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tulong)))
                                              (Ssequence
                                                (Sset _t'68
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _pending_buf
                                                    (tptr tuchar)))
                                                (Ssequence
                                                  (Sset _t'69
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _t'68 (tptr tuchar))
                                                        (Etempvar _t'9 tulong)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Ecast
                                                      (Ecast
                                                        (Ebinop Oshr
                                                          (Ecast
                                                            (Etempvar _t'69 tushort)
                                                            tushort)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tint) tuchar)
                                                      tuchar))))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'67
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort)
                                                (Ebinop Oshr
                                                  (Ecast
                                                    (Etempvar _val__2 tint)
                                                    tushort)
                                                  (Ebinop Osub
                                                    (Econst_int (Int.repr 16) tint)
                                                    (Etempvar _t'67 tint)
                                                    tint) tint)))
                                            (Ssequence
                                              (Sset _t'66
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint)
                                                (Ebinop Oadd
                                                  (Etempvar _t'66 tint)
                                                  (Ebinop Osub
                                                    (Etempvar _len__2 tint)
                                                    (Econst_int (Int.repr 16) tint)
                                                    tint) tint)))))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'64
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_buf tushort))
                                        (Ssequence
                                          (Sset _t'65
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort)
                                            (Ebinop Oor
                                              (Etempvar _t'64 tushort)
                                              (Ebinop Oshl
                                                (Ecast (Etempvar _lc tint)
                                                  tushort)
                                                (Etempvar _t'65 tint) tint)
                                              tint))))
                                      (Ssequence
                                        (Sset _t'63
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                              (Tstruct _internal_state noattr))
                                            _bi_valid tint)
                                          (Ebinop Oadd (Etempvar _t'63 tint)
                                            (Etempvar _len__2 tint) tint))))))))
                            Sskip)
                          (Ssequence
                            (Sset _dist
                              (Ebinop Osub (Etempvar _dist tuint)
                                (Econst_int (Int.repr 1) tint) tuint))
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Olt
                                               (Etempvar _dist tuint)
                                               (Econst_int (Int.repr 256) tint)
                                               tint)
                                  (Ssequence
                                    (Sset _t'61
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar __dist_code (tarray tuchar 512))
                                          (Etempvar _dist tuint)
                                          (tptr tuchar)) tuchar))
                                    (Sset _t'10
                                      (Ecast (Etempvar _t'61 tuchar) tint)))
                                  (Ssequence
                                    (Sset _t'60
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar __dist_code (tarray tuchar 512))
                                          (Ebinop Oadd
                                            (Econst_int (Int.repr 256) tint)
                                            (Ebinop Oshr
                                              (Etempvar _dist tuint)
                                              (Econst_int (Int.repr 7) tint)
                                              tuint) tuint) (tptr tuchar))
                                        tuchar))
                                    (Sset _t'10
                                      (Ecast (Etempvar _t'60 tuchar) tint))))
                                (Sset _code (Etempvar _t'10 tint)))
                              (Ssequence
                                (Ssequence
                                  (Sset _len__3
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _dtree (tptr (Tstruct _ct_data_s noattr)))
                                            (Etempvar _code tuint)
                                            (tptr (Tstruct _ct_data_s noattr)))
                                          (Tstruct _ct_data_s noattr)) _dl
                                        (Tunion __anon_7a8a915e1e8b noattr)) _len tushort))
                                  (Ssequence
                                    (Sset _t'46
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                          (Tstruct _internal_state noattr))
                                        _bi_valid tint))
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _t'46 tint)
                                                   (Ebinop Osub
                                                     (Ecast
                                                       (Econst_int (Int.repr 16) tint)
                                                       tint)
                                                     (Etempvar _len__3 tint)
                                                     tint) tint)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'59
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _dtree (tptr (Tstruct _ct_data_s noattr)))
                                                    (Etempvar _code tuint)
                                                    (tptr (Tstruct _ct_data_s noattr)))
                                                  (Tstruct _ct_data_s noattr))
                                                _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                              _code tushort))
                                          (Sset _val__3
                                            (Ecast (Etempvar _t'59 tushort)
                                              tint)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'57
                                              (Efield
                                                (Ederef
                                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                  (Tstruct _internal_state noattr))
                                                _bi_buf tushort))
                                            (Ssequence
                                              (Sset _t'58
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort)
                                                (Ebinop Oor
                                                  (Etempvar _t'57 tushort)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _val__3 tint)
                                                      tushort)
                                                    (Etempvar _t'58 tint)
                                                    tint) tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'11
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'11 tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong)))
                                                (Ssequence
                                                  (Sset _t'55
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending_buf
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'56
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'55 (tptr tuchar))
                                                          (Etempvar _t'11 tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ecast
                                                          (Ebinop Oand
                                                            (Etempvar _t'56 tushort)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tint) tuchar)
                                                        tuchar)))))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'12
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending tulong)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'12 tulong)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tulong)))
                                                (Ssequence
                                                  (Sset _t'53
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _pending_buf
                                                      (tptr tuchar)))
                                                  (Ssequence
                                                    (Sset _t'54
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _t'53 (tptr tuchar))
                                                          (Etempvar _t'12 tulong)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ecast
                                                          (Ebinop Oshr
                                                            (Ecast
                                                              (Etempvar _t'54 tushort)
                                                              tushort)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tint) tuchar)
                                                        tuchar))))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'52
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort)
                                                  (Ebinop Oshr
                                                    (Ecast
                                                      (Etempvar _val__3 tint)
                                                      tushort)
                                                    (Ebinop Osub
                                                      (Econst_int (Int.repr 16) tint)
                                                      (Etempvar _t'52 tint)
                                                      tint) tint)))
                                              (Ssequence
                                                (Sset _t'51
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'51 tint)
                                                    (Ebinop Osub
                                                      (Etempvar _len__3 tint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tint) tint)))))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'48
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_buf tushort))
                                          (Ssequence
                                            (Sset _t'49
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _dtree (tptr (Tstruct _ct_data_s noattr)))
                                                      (Etempvar _code tuint)
                                                      (tptr (Tstruct _ct_data_s noattr)))
                                                    (Tstruct _ct_data_s noattr))
                                                  _fc (Tunion __anon_2c403fe6f6d2 noattr))
                                                _code tushort))
                                            (Ssequence
                                              (Sset _t'50
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_valid tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                    (Tstruct _internal_state noattr))
                                                  _bi_buf tushort)
                                                (Ebinop Oor
                                                  (Etempvar _t'48 tushort)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _t'49 tushort)
                                                      tushort)
                                                    (Etempvar _t'50 tint)
                                                    tint) tint)))))
                                        (Ssequence
                                          (Sset _t'47
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint)
                                            (Ebinop Oadd
                                              (Etempvar _t'47 tint)
                                              (Etempvar _len__3 tint) tint)))))))
                                (Ssequence
                                  (Sset _extra
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _extra_dbits (tarray tint 30))
                                        (Etempvar _code tuint) (tptr tint))
                                      tint))
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _extra tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'45
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _base_dist (tarray tint 30))
                                              (Etempvar _code tuint)
                                              (tptr tint)) tint))
                                        (Sset _dist
                                          (Ebinop Osub (Etempvar _dist tuint)
                                            (Ecast (Etempvar _t'45 tint)
                                              tuint) tuint)))
                                      (Ssequence
                                        (Sset _len__4 (Etempvar _extra tint))
                                        (Ssequence
                                          (Sset _t'33
                                            (Efield
                                              (Ederef
                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                (Tstruct _internal_state noattr))
                                              _bi_valid tint))
                                          (Sifthenelse (Ebinop Ogt
                                                         (Etempvar _t'33 tint)
                                                         (Ebinop Osub
                                                           (Ecast
                                                             (Econst_int (Int.repr 16) tint)
                                                             tint)
                                                           (Etempvar _len__4 tint)
                                                           tint) tint)
                                            (Ssequence
                                              (Sset _val__4
                                                (Ecast
                                                  (Ecast
                                                    (Etempvar _dist tuint)
                                                    tint) tint))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'43
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort))
                                                  (Ssequence
                                                    (Sset _t'44
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_valid tint))
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                          (Tstruct _internal_state noattr))
                                                        _bi_buf tushort)
                                                      (Ebinop Oor
                                                        (Etempvar _t'43 tushort)
                                                        (Ebinop Oshl
                                                          (Ecast
                                                            (Etempvar _val__4 tint)
                                                            tushort)
                                                          (Etempvar _t'44 tint)
                                                          tint) tint))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'13
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'13 tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sset _t'41
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending_buf
                                                            (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _t'42
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                                (Tstruct _internal_state noattr))
                                                              _bi_buf
                                                              tushort))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _t'41 (tptr tuchar))
                                                                (Etempvar _t'13 tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ecast
                                                              (Ecast
                                                                (Ebinop Oand
                                                                  (Etempvar _t'42 tushort)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tint)
                                                                tuchar)
                                                              tuchar)))))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'14
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending tulong)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'14 tulong)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tulong)))
                                                      (Ssequence
                                                        (Sset _t'39
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                              (Tstruct _internal_state noattr))
                                                            _pending_buf
                                                            (tptr tuchar)))
                                                        (Ssequence
                                                          (Sset _t'40
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                                (Tstruct _internal_state noattr))
                                                              _bi_buf
                                                              tushort))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Etempvar _t'39 (tptr tuchar))
                                                                (Etempvar _t'14 tulong)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Ecast
                                                              (Ecast
                                                                (Ebinop Oshr
                                                                  (Ecast
                                                                    (Etempvar _t'40 tushort)
                                                                    tushort)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tint)
                                                                tuchar)
                                                              tuchar))))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'38
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_buf tushort)
                                                        (Ebinop Oshr
                                                          (Ecast
                                                            (Etempvar _val__4 tint)
                                                            tushort)
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 16) tint)
                                                            (Etempvar _t'38 tint)
                                                            tint) tint)))
                                                    (Ssequence
                                                      (Sset _t'37
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                            (Tstruct _internal_state noattr))
                                                          _bi_valid tint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t'37 tint)
                                                          (Ebinop Osub
                                                            (Etempvar _len__4 tint)
                                                            (Econst_int (Int.repr 16) tint)
                                                            tint) tint)))))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'35
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_buf tushort))
                                                (Ssequence
                                                  (Sset _t'36
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_valid tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                        (Tstruct _internal_state noattr))
                                                      _bi_buf tushort)
                                                    (Ebinop Oor
                                                      (Etempvar _t'35 tushort)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Ecast
                                                            (Etempvar _dist tuint)
                                                            tint) tushort)
                                                        (Etempvar _t'36 tint)
                                                        tint) tint))))
                                              (Ssequence
                                                (Sset _t'34
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                                      (Tstruct _internal_state noattr))
                                                    _bi_valid tint)
                                                  (Ebinop Oadd
                                                    (Etempvar _t'34 tint)
                                                    (Etempvar _len__4 tint)
                                                    tint))))))))
                                    Sskip)))))))))))))
          (Ssequence
            (Sset _t'32
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _sym_next tuint))
            (Sifthenelse (Ebinop Olt (Etempvar _sx tuint)
                           (Etempvar _t'32 tuint) tint)
              Sskip
              Sbreak)))
        Sskip))
    (Ssequence
      (Sset _len__5
        (Efield
          (Efield
            (Ederef
              (Ebinop Oadd
                (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                (Econst_int (Int.repr 256) tint)
                (tptr (Tstruct _ct_data_s noattr)))
              (Tstruct _ct_data_s noattr)) _dl (Tunion __anon_7a8a915e1e8b noattr)) _len
          tushort))
      (Ssequence
        (Sset _t'17
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _bi_valid tint))
        (Sifthenelse (Ebinop Ogt (Etempvar _t'17 tint)
                       (Ebinop Osub
                         (Ecast (Econst_int (Int.repr 16) tint) tint)
                         (Etempvar _len__5 tint) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'30
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                        (Econst_int (Int.repr 256) tint)
                        (tptr (Tstruct _ct_data_s noattr)))
                      (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                  _code tushort))
              (Sset _val__5 (Ecast (Etempvar _t'30 tushort) tint)))
            (Ssequence
              (Ssequence
                (Sset _t'28
                  (Efield
                    (Ederef
                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                      (Tstruct _internal_state noattr)) _bi_buf tushort))
                (Ssequence
                  (Sset _t'29
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'28 tushort)
                      (Ebinop Oshl (Ecast (Etempvar _val__5 tint) tushort)
                        (Etempvar _t'29 tint) tint) tint))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'15
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'15 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'26
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'27
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'26 (tptr tuchar))
                              (Etempvar _t'15 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oand (Etempvar _t'27 tushort)
                                (Econst_int (Int.repr 255) tint) tint)
                              tuchar) tuchar)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'16
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending
                          tulong)
                        (Ebinop Oadd (Etempvar _t'16 tulong)
                          (Econst_int (Int.repr 1) tint) tulong)))
                    (Ssequence
                      (Sset _t'24
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _pending_buf
                          (tptr tuchar)))
                      (Ssequence
                        (Sset _t'25
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'24 (tptr tuchar))
                              (Etempvar _t'16 tulong) (tptr tuchar)) tuchar)
                          (Ecast
                            (Ecast
                              (Ebinop Oshr
                                (Ecast (Etempvar _t'25 tushort) tushort)
                                (Econst_int (Int.repr 8) tint) tint) tuchar)
                            tuchar))))))
                (Ssequence
                  (Ssequence
                    (Sset _t'23
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_buf tushort)
                      (Ebinop Oshr (Ecast (Etempvar _val__5 tint) tushort)
                        (Ebinop Osub (Econst_int (Int.repr 16) tint)
                          (Etempvar _t'23 tint) tint) tint)))
                  (Ssequence
                    (Sset _t'22
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _bi_valid tint)
                      (Ebinop Oadd (Etempvar _t'22 tint)
                        (Ebinop Osub (Etempvar _len__5 tint)
                          (Econst_int (Int.repr 16) tint) tint) tint)))))))
          (Ssequence
            (Ssequence
              (Sset _t'19
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_buf tushort))
              (Ssequence
                (Sset _t'20
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Etempvar _ltree (tptr (Tstruct _ct_data_s noattr)))
                          (Econst_int (Int.repr 256) tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _code tushort))
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_buf tushort)
                    (Ebinop Oor (Etempvar _t'19 tushort)
                      (Ebinop Oshl (Ecast (Etempvar _t'20 tushort) tushort)
                        (Etempvar _t'21 tint) tint) tint)))))
            (Ssequence
              (Sset _t'18
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _bi_valid tint)
                (Ebinop Oadd (Etempvar _t'18 tint) (Etempvar _len__5 tint)
                  tint)))))))))
|}.

Definition f_detect_data_type := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_block_mask, tulong) :: (_n, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'8, tushort) ::
               (_t'7, tushort) :: (_t'6, tushort) :: (_t'5, tushort) ::
               (_t'4, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _block_mask (Econst_long (Int64.repr 4093624447) tulong))
  (Ssequence
    (Ssequence
      (Sset _n (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ole (Etempvar _n tint)
                         (Econst_int (Int.repr 31) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sifthenelse (Ebinop Oand (Etempvar _block_mask tulong)
                           (Econst_int (Int.repr 1) tint) tulong)
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _dyn_ltree
                            (tarray (Tstruct _ct_data_s noattr) 573))
                          (Etempvar _n tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                (Sset _t'1
                  (Ecast
                    (Ebinop One (Etempvar _t'8 tushort)
                      (Econst_int (Int.repr 0) tint) tint) tbool)))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'1 tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip)))
        (Ssequence
          (Sset _n
            (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
              tint))
          (Sset _block_mask
            (Ebinop Oshr (Etempvar _block_mask tulong)
              (Econst_int (Int.repr 1) tint) tulong)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _dyn_ltree
                        (tarray (Tstruct _ct_data_s noattr) 573))
                      (Econst_int (Int.repr 9) tint)
                      (tptr (Tstruct _ct_data_s noattr)))
                    (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                _freq tushort))
            (Sifthenelse (Ebinop One (Etempvar _t'6 tushort)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _t'2 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _dyn_ltree
                            (tarray (Tstruct _ct_data_s noattr) 573))
                          (Econst_int (Int.repr 10) tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                (Sset _t'2
                  (Ecast
                    (Ebinop One (Etempvar _t'7 tushort)
                      (Econst_int (Int.repr 0) tint) tint) tbool)))))
          (Sifthenelse (Etempvar _t'2 tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _dyn_ltree
                          (tarray (Tstruct _ct_data_s noattr) 573))
                        (Econst_int (Int.repr 13) tint)
                        (tptr (Tstruct _ct_data_s noattr)))
                      (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                  _freq tushort))
              (Sset _t'3
                (Ecast
                  (Ebinop One (Etempvar _t'5 tushort)
                    (Econst_int (Int.repr 0) tint) tint) tbool)))))
        (Sifthenelse (Etempvar _t'3 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _n (Econst_int (Int.repr 32) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _n tint)
                             (Econst_int (Int.repr 256) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _dyn_ltree
                            (tarray (Tstruct _ct_data_s noattr) 573))
                          (Etempvar _n tint)
                          (tptr (Tstruct _ct_data_s noattr)))
                        (Tstruct _ct_data_s noattr)) _fc
                      (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                (Sifthenelse (Ebinop One (Etempvar _t'4 tushort)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                  Sskip)))
            (Sset _n
              (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f__tr_flush_block := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_buf, (tptr tschar)) :: (_stored_len, tulong) ::
                (_last, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_opt_lenb, tulong) :: (_static_lenb, tulong) ::
               (_max_blindex, tint) :: (_len, tint) :: (_val, tint) ::
               (_len__1, tint) :: (_val__1, tint) :: (_t'9, tint) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'42, (tptr (Tstruct _z_stream_s noattr))) ::
               (_t'41, tint) ::
               (_t'40, (tptr (Tstruct _z_stream_s noattr))) ::
               (_t'39, tulong) :: (_t'38, tulong) :: (_t'37, tint) ::
               (_t'36, tint) :: (_t'35, tint) :: (_t'34, tushort) ::
               (_t'33, tushort) :: (_t'32, (tptr tuchar)) ::
               (_t'31, tushort) :: (_t'30, (tptr tuchar)) :: (_t'29, tint) ::
               (_t'28, tint) :: (_t'27, tint) :: (_t'26, tushort) ::
               (_t'25, tint) :: (_t'24, tint) :: (_t'23, tint) ::
               (_t'22, tushort) :: (_t'21, tushort) ::
               (_t'20, (tptr tuchar)) :: (_t'19, tushort) ::
               (_t'18, (tptr tuchar)) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tushort) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _max_blindex (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _t'36
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _level tint))
      (Sifthenelse (Ebinop Ogt (Etempvar _t'36 tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'40
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _strm
                (tptr (Tstruct _z_stream_s noattr))))
            (Ssequence
              (Sset _t'41
                (Efield
                  (Ederef
                    (Etempvar _t'40 (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _data_type tint))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'41 tint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _detect_data_type (Tfunction
                                              ((tptr (Tstruct _internal_state noattr)) ::
                                               nil) tint cc_default))
                    ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                     nil))
                  (Ssequence
                    (Sset _t'42
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _strm
                        (tptr (Tstruct _z_stream_s noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _t'42 (tptr (Tstruct _z_stream_s noattr)))
                          (Tstruct _z_stream_s noattr)) _data_type tint)
                      (Etempvar _t'1 tint))))
                Sskip)))
          (Ssequence
            (Scall None
              (Evar _build_tree (Tfunction
                                  ((tptr (Tstruct _internal_state noattr)) ::
                                   (tptr (Tstruct _tree_desc_s noattr)) ::
                                   nil) tvoid cc_default))
              ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
               (Ecast
                 (Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                       (Tstruct _internal_state noattr)) _l_desc
                     (Tstruct _tree_desc_s noattr))
                   (tptr (Tstruct _tree_desc_s noattr)))
                 (tptr (Tstruct _tree_desc_s noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _build_tree (Tfunction
                                    ((tptr (Tstruct _internal_state noattr)) ::
                                     (tptr (Tstruct _tree_desc_s noattr)) ::
                                     nil) tvoid cc_default))
                ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                 (Ecast
                   (Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                         (Tstruct _internal_state noattr)) _d_desc
                       (Tstruct _tree_desc_s noattr))
                     (tptr (Tstruct _tree_desc_s noattr)))
                   (tptr (Tstruct _tree_desc_s noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _build_bl_tree (Tfunction
                                           ((tptr (Tstruct _internal_state noattr)) ::
                                            nil) tint cc_default))
                    ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                     nil))
                  (Sset _max_blindex (Etempvar _t'2 tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'39
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _opt_len tulong))
                    (Sset _opt_lenb
                      (Ebinop Oshr
                        (Ebinop Oadd
                          (Ebinop Oadd (Etempvar _t'39 tulong)
                            (Econst_int (Int.repr 3) tint) tulong)
                          (Econst_int (Int.repr 7) tint) tulong)
                        (Econst_int (Int.repr 3) tint) tulong)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'38
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _static_len
                          tulong))
                      (Sset _static_lenb
                        (Ebinop Oshr
                          (Ebinop Oadd
                            (Ebinop Oadd (Etempvar _t'38 tulong)
                              (Econst_int (Int.repr 3) tint) tulong)
                            (Econst_int (Int.repr 7) tint) tulong)
                          (Econst_int (Int.repr 3) tint) tulong)))
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _static_lenb tulong)
                                     (Etempvar _opt_lenb tulong) tint)
                        (Sset _t'3 (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Sset _t'37
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _strategy
                              tint))
                          (Sset _t'3
                            (Ecast
                              (Ebinop Oeq (Etempvar _t'37 tint)
                                (Econst_int (Int.repr 4) tint) tint) tbool))))
                      (Sifthenelse (Etempvar _t'3 tint)
                        (Sset _opt_lenb (Etempvar _static_lenb tulong))
                        Sskip))))))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ecast
                (Ebinop Oadd (Etempvar _stored_len tulong)
                  (Econst_int (Int.repr 5) tint) tulong) tulong))
            (Sset _static_lenb (Etempvar _t'4 tulong)))
          (Sset _opt_lenb (Etempvar _t'4 tulong)))))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Ole
                       (Ebinop Oadd (Etempvar _stored_len tulong)
                         (Econst_int (Int.repr 4) tint) tulong)
                       (Etempvar _opt_lenb tulong) tint)
          (Sset _t'9
            (Ecast
              (Ebinop One (Etempvar _buf (tptr tschar))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tschar)) tint)
              tbool))
          (Sset _t'9 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'9 tint)
          (Scall None
            (Evar __tr_stored_block (Tfunction
                                      ((tptr (Tstruct _internal_state noattr)) ::
                                       (tptr tschar) :: tulong :: tint ::
                                       nil) tvoid cc_default))
            ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
             (Etempvar _buf (tptr tschar)) ::
             (Etempvar _stored_len tulong) :: (Etempvar _last tint) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _static_lenb tulong)
                         (Etempvar _opt_lenb tulong) tint)
            (Ssequence
              (Ssequence
                (Sset _len (Econst_int (Int.repr 3) tint))
                (Ssequence
                  (Sset _t'24
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sifthenelse (Ebinop Ogt (Etempvar _t'24 tint)
                                 (Ebinop Osub
                                   (Ecast (Econst_int (Int.repr 16) tint)
                                     tint) (Etempvar _len tint) tint) tint)
                    (Ssequence
                      (Sset _val
                        (Ebinop Oadd
                          (Ecast
                            (Ebinop Oshl (Econst_int (Int.repr 1) tint)
                              (Econst_int (Int.repr 1) tint) tint) tint)
                          (Etempvar _last tint) tint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'34
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort))
                          (Ssequence
                            (Sset _t'35
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_valid
                                tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_buf
                                tushort)
                              (Ebinop Oor (Etempvar _t'34 tushort)
                                (Ebinop Oshl
                                  (Ecast (Etempvar _val tint) tushort)
                                  (Etempvar _t'35 tint) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'5 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'32
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'33
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'32 (tptr tuchar))
                                        (Etempvar _t'5 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oand (Etempvar _t'33 tushort)
                                          (Econst_int (Int.repr 255) tint)
                                          tint) tuchar) tuchar)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'6
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'6 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'30
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'31
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'30 (tptr tuchar))
                                        (Etempvar _t'6 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oshr
                                          (Ecast (Etempvar _t'31 tushort)
                                            tushort)
                                          (Econst_int (Int.repr 8) tint)
                                          tint) tuchar) tuchar))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'29
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _bi_buf
                                  tushort)
                                (Ebinop Oshr
                                  (Ecast (Etempvar _val tint) tushort)
                                  (Ebinop Osub
                                    (Econst_int (Int.repr 16) tint)
                                    (Etempvar _t'29 tint) tint) tint)))
                            (Ssequence
                              (Sset _t'28
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint)
                                (Ebinop Oadd (Etempvar _t'28 tint)
                                  (Ebinop Osub (Etempvar _len tint)
                                    (Econst_int (Int.repr 16) tint) tint)
                                  tint)))))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'26
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Ssequence
                          (Sset _t'27
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_valid
                              tint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort)
                            (Ebinop Oor (Etempvar _t'26 tushort)
                              (Ebinop Oshl
                                (Ecast
                                  (Ebinop Oadd
                                    (Ebinop Oshl
                                      (Econst_int (Int.repr 1) tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (Etempvar _last tint) tint) tushort)
                                (Etempvar _t'27 tint) tint) tint))))
                      (Ssequence
                        (Sset _t'25
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint)
                          (Ebinop Oadd (Etempvar _t'25 tint)
                            (Etempvar _len tint) tint)))))))
              (Scall None
                (Evar _compress_block (Tfunction
                                        ((tptr (Tstruct _internal_state noattr)) ::
                                         (tptr (Tstruct _ct_data_s noattr)) ::
                                         (tptr (Tstruct _ct_data_s noattr)) ::
                                         nil) tvoid cc_default))
                ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                 (Ecast
                   (Evar _static_ltree (tarray (Tstruct _ct_data_s noattr) 288))
                   (tptr (Tstruct _ct_data_s noattr))) ::
                 (Ecast
                   (Evar _static_dtree (tarray (Tstruct _ct_data_s noattr) 30))
                   (tptr (Tstruct _ct_data_s noattr))) :: nil)))
            (Ssequence
              (Ssequence
                (Sset _len__1 (Econst_int (Int.repr 3) tint))
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef
                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                        (Tstruct _internal_state noattr)) _bi_valid tint))
                  (Sifthenelse (Ebinop Ogt (Etempvar _t'12 tint)
                                 (Ebinop Osub
                                   (Ecast (Econst_int (Int.repr 16) tint)
                                     tint) (Etempvar _len__1 tint) tint)
                                 tint)
                    (Ssequence
                      (Sset _val__1
                        (Ebinop Oadd
                          (Ecast
                            (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                              (Econst_int (Int.repr 1) tint) tint) tint)
                          (Etempvar _last tint) tint))
                      (Ssequence
                        (Ssequence
                          (Sset _t'22
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort))
                          (Ssequence
                            (Sset _t'23
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_valid
                                tint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr)) _bi_buf
                                tushort)
                              (Ebinop Oor (Etempvar _t'22 tushort)
                                (Ebinop Oshl
                                  (Ecast (Etempvar _val__1 tint) tushort)
                                  (Etempvar _t'23 tint) tint) tint))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'7 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'20
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'21
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'20 (tptr tuchar))
                                        (Etempvar _t'7 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oand (Etempvar _t'21 tushort)
                                          (Econst_int (Int.repr 255) tint)
                                          tint) tuchar) tuchar)))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'8
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending tulong)
                                  (Ebinop Oadd (Etempvar _t'8 tulong)
                                    (Econst_int (Int.repr 1) tint) tulong)))
                              (Ssequence
                                (Sset _t'18
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                      (Tstruct _internal_state noattr))
                                    _pending_buf (tptr tuchar)))
                                (Ssequence
                                  (Sset _t'19
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                        (Tstruct _internal_state noattr))
                                      _bi_buf tushort))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _t'18 (tptr tuchar))
                                        (Etempvar _t'8 tulong) (tptr tuchar))
                                      tuchar)
                                    (Ecast
                                      (Ecast
                                        (Ebinop Oshr
                                          (Ecast (Etempvar _t'19 tushort)
                                            tushort)
                                          (Econst_int (Int.repr 8) tint)
                                          tint) tuchar) tuchar))))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'17
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr)) _bi_buf
                                  tushort)
                                (Ebinop Oshr
                                  (Ecast (Etempvar _val__1 tint) tushort)
                                  (Ebinop Osub
                                    (Econst_int (Int.repr 16) tint)
                                    (Etempvar _t'17 tint) tint) tint)))
                            (Ssequence
                              (Sset _t'16
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _bi_valid tint)
                                (Ebinop Oadd (Etempvar _t'16 tint)
                                  (Ebinop Osub (Etempvar _len__1 tint)
                                    (Econst_int (Int.repr 16) tint) tint)
                                  tint)))))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_buf
                            tushort))
                        (Ssequence
                          (Sset _t'15
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_valid
                              tint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                (Tstruct _internal_state noattr)) _bi_buf
                              tushort)
                            (Ebinop Oor (Etempvar _t'14 tushort)
                              (Ebinop Oshl
                                (Ecast
                                  (Ebinop Oadd
                                    (Ebinop Oshl
                                      (Econst_int (Int.repr 2) tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (Etempvar _last tint) tint) tushort)
                                (Etempvar _t'15 tint) tint) tint))))
                      (Ssequence
                        (Sset _t'13
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                              (Tstruct _internal_state noattr)) _bi_valid
                            tint)
                          (Ebinop Oadd (Etempvar _t'13 tint)
                            (Etempvar _len__1 tint) tint)))))))
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _l_desc
                        (Tstruct _tree_desc_s noattr)) _max_code tint))
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                            (Tstruct _internal_state noattr)) _d_desc
                          (Tstruct _tree_desc_s noattr)) _max_code tint))
                    (Scall None
                      (Evar _send_all_trees (Tfunction
                                              ((tptr (Tstruct _internal_state noattr)) ::
                                               tint :: tint :: tint :: nil)
                                              tvoid cc_default))
                      ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                       (Ebinop Oadd (Etempvar _t'10 tint)
                         (Econst_int (Int.repr 1) tint) tint) ::
                       (Ebinop Oadd (Etempvar _t'11 tint)
                         (Econst_int (Int.repr 1) tint) tint) ::
                       (Ebinop Oadd (Etempvar _max_blindex tint)
                         (Econst_int (Int.repr 1) tint) tint) :: nil))))
                (Scall None
                  (Evar _compress_block (Tfunction
                                          ((tptr (Tstruct _internal_state noattr)) ::
                                           (tptr (Tstruct _ct_data_s noattr)) ::
                                           (tptr (Tstruct _ct_data_s noattr)) ::
                                           nil) tvoid cc_default))
                  ((Etempvar _s (tptr (Tstruct _internal_state noattr))) ::
                   (Ecast
                     (Efield
                       (Ederef
                         (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                         (Tstruct _internal_state noattr)) _dyn_ltree
                       (tarray (Tstruct _ct_data_s noattr) 573))
                     (tptr (Tstruct _ct_data_s noattr))) ::
                   (Ecast
                     (Efield
                       (Ederef
                         (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                         (Tstruct _internal_state noattr)) _dyn_dtree
                       (tarray (Tstruct _ct_data_s noattr) 61))
                     (tptr (Tstruct _ct_data_s noattr))) :: nil)))))))
      (Ssequence
        (Scall None
          (Evar _init_block (Tfunction
                              ((tptr (Tstruct _internal_state noattr)) ::
                               nil) tvoid cc_default))
          ((Etempvar _s (tptr (Tstruct _internal_state noattr))) :: nil))
        (Sifthenelse (Etempvar _last tint)
          (Scall None
            (Evar _bi_windup (Tfunction
                               ((tptr (Tstruct _internal_state noattr)) ::
                                nil) tvoid cc_default))
            ((Etempvar _s (tptr (Tstruct _internal_state noattr))) :: nil))
          Sskip)))))
|}.

Definition f__tr_tally := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _internal_state noattr))) ::
                (_dist, tuint) :: (_lc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: (_t'17, (tptr tuchar)) ::
               (_t'16, (tptr tuchar)) :: (_t'15, (tptr tuchar)) ::
               (_t'14, tushort) :: (_t'13, tuint) :: (_t'12, tushort) ::
               (_t'11, tuchar) :: (_t'10, tuchar) :: (_t'9, tuchar) ::
               (_t'8, tuchar) :: (_t'7, tushort) :: (_t'6, tuint) ::
               (_t'5, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _sym_next tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _sym_next tuint)
        (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    (Ssequence
      (Sset _t'17
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
            (Tstruct _internal_state noattr)) _sym_buf (tptr tuchar)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _t'17 (tptr tuchar)) (Etempvar _t'1 tuint)
            (tptr tuchar)) tuchar) (Ecast (Etempvar _dist tuint) tuchar))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _sym_next tuint))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _sym_next tuint)
          (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
            tuint)))
      (Ssequence
        (Sset _t'16
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
              (Tstruct _internal_state noattr)) _sym_buf (tptr tuchar)))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _t'16 (tptr tuchar)) (Etempvar _t'2 tuint)
              (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _dist tuint)
              (Econst_int (Int.repr 8) tint) tuint) tuchar))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _sym_next tuint))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _sym_next tuint)
            (Ebinop Oadd (Etempvar _t'3 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _sym_buf (tptr tuchar)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _t'15 (tptr tuchar))
                (Etempvar _t'3 tuint) (tptr tuchar)) tuchar)
            (Ecast (Etempvar _lc tuint) tuchar))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _dist tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sset _t'14
              (Efield
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _dyn_ltree
                        (tarray (Tstruct _ct_data_s noattr) 573))
                      (Etempvar _lc tuint)
                      (tptr (Tstruct _ct_data_s noattr)))
                    (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                _freq tushort))
            (Sassign
              (Efield
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                          (Tstruct _internal_state noattr)) _dyn_ltree
                        (tarray (Tstruct _ct_data_s noattr) 573))
                      (Etempvar _lc tuint)
                      (tptr (Tstruct _ct_data_s noattr)))
                    (Tstruct _ct_data_s noattr)) _fc (Tunion __anon_2c403fe6f6d2 noattr))
                _freq tushort)
              (Ebinop Oadd (Etempvar _t'14 tushort)
                (Econst_int (Int.repr 1) tint) tint)))
          (Ssequence
            (Ssequence
              (Sset _t'13
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _matches tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                    (Tstruct _internal_state noattr)) _matches tuint)
                (Ebinop Oadd (Etempvar _t'13 tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))
            (Ssequence
              (Sset _dist
                (Ebinop Osub (Etempvar _dist tuint)
                  (Econst_int (Int.repr 1) tint) tuint))
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Ederef
                      (Ebinop Oadd (Evar __length_code (tarray tuchar 256))
                        (Etempvar _lc tuint) (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _t'11
                      (Ederef
                        (Ebinop Oadd (Evar __length_code (tarray tuchar 256))
                          (Etempvar _lc tuint) (tptr tuchar)) tuchar))
                    (Ssequence
                      (Sset _t'12
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _dyn_ltree
                                  (tarray (Tstruct _ct_data_s noattr) 573))
                                (Ebinop Oadd
                                  (Ebinop Oadd (Etempvar _t'11 tuchar)
                                    (Econst_int (Int.repr 256) tint) tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _fc
                            (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                    (Tstruct _internal_state noattr))
                                  _dyn_ltree
                                  (tarray (Tstruct _ct_data_s noattr) 573))
                                (Ebinop Oadd
                                  (Ebinop Oadd (Etempvar _t'10 tuchar)
                                    (Econst_int (Int.repr 256) tint) tint)
                                  (Econst_int (Int.repr 1) tint) tint)
                                (tptr (Tstruct _ct_data_s noattr)))
                              (Tstruct _ct_data_s noattr)) _fc
                            (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort)
                        (Ebinop Oadd (Etempvar _t'12 tushort)
                          (Econst_int (Int.repr 1) tint) tint)))))
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _dist tuint)
                                 (Econst_int (Int.repr 256) tint) tint)
                    (Ssequence
                      (Sset _t'9
                        (Ederef
                          (Ebinop Oadd (Evar __dist_code (tarray tuchar 512))
                            (Etempvar _dist tuint) (tptr tuchar)) tuchar))
                      (Sset _t'4 (Ecast (Etempvar _t'9 tuchar) tint)))
                    (Ssequence
                      (Sset _t'8
                        (Ederef
                          (Ebinop Oadd (Evar __dist_code (tarray tuchar 512))
                            (Ebinop Oadd (Econst_int (Int.repr 256) tint)
                              (Ebinop Oshr (Etempvar _dist tuint)
                                (Econst_int (Int.repr 7) tint) tuint) tuint)
                            (tptr tuchar)) tuchar))
                      (Sset _t'4 (Ecast (Etempvar _t'8 tuchar) tint))))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr))
                                _dyn_dtree
                                (tarray (Tstruct _ct_data_s noattr) 61))
                              (Etempvar _t'4 tint)
                              (tptr (Tstruct _ct_data_s noattr)))
                            (Tstruct _ct_data_s noattr)) _fc
                          (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                                  (Tstruct _internal_state noattr))
                                _dyn_dtree
                                (tarray (Tstruct _ct_data_s noattr) 61))
                              (Etempvar _t'4 tint)
                              (tptr (Tstruct _ct_data_s noattr)))
                            (Tstruct _ct_data_s noattr)) _fc
                          (Tunion __anon_2c403fe6f6d2 noattr)) _freq tushort)
                      (Ebinop Oadd (Etempvar _t'7 tushort)
                        (Econst_int (Int.repr 1) tint) tint))))))))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                (Tstruct _internal_state noattr)) _sym_next tuint))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _internal_state noattr)))
                  (Tstruct _internal_state noattr)) _sym_end tuint))
            (Sreturn (Some (Ebinop Oeq (Etempvar _t'5 tuint)
                             (Etempvar _t'6 tuint) tint)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _z_stream_s Struct
   (Member_plain _next_in (tptr tuchar) :: Member_plain _avail_in tuint ::
    Member_plain _total_in tulong :: Member_plain _next_out (tptr tuchar) ::
    Member_plain _avail_out tuint :: Member_plain _total_out tulong ::
    Member_plain _msg (tptr tschar) ::
    Member_plain _state (tptr (Tstruct _internal_state noattr)) ::
    Member_plain _zalloc
      (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil) (tptr tvoid)
              cc_default)) ::
    Member_plain _zfree
      (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
              cc_default)) :: Member_plain _opaque (tptr tvoid) ::
    Member_plain _data_type tint :: Member_plain _adler tulong ::
    Member_plain _reserved tulong :: nil)
   noattr ::
 Composite _gz_header_s Struct
   (Member_plain _text tint :: Member_plain _time tulong ::
    Member_plain _xflags tint :: Member_plain _os tint ::
    Member_plain _extra (tptr tuchar) :: Member_plain _extra_len tuint ::
    Member_plain _extra_max tuint :: Member_plain _name (tptr tuchar) ::
    Member_plain _name_max tuint :: Member_plain _comment (tptr tuchar) ::
    Member_plain _comm_max tuint :: Member_plain _hcrc tint ::
    Member_plain _done tint :: nil)
   noattr ::
 Composite __anon_2c403fe6f6d2 Union
   (Member_plain _freq tushort :: Member_plain _code tushort :: nil)
   noattr ::
 Composite __anon_7a8a915e1e8b Union
   (Member_plain _dad tushort :: Member_plain _len tushort :: nil)
   noattr ::
 Composite _ct_data_s Struct
   (Member_plain _fc (Tunion __anon_2c403fe6f6d2 noattr) ::
    Member_plain _dl (Tunion __anon_7a8a915e1e8b noattr) :: nil)
   noattr ::
 Composite _tree_desc_s Struct
   (Member_plain _dyn_tree (tptr (Tstruct _ct_data_s noattr)) ::
    Member_plain _max_code tint ::
    Member_plain _stat_desc (tptr (Tstruct _static_tree_desc_s noattr)) ::
    nil)
   noattr ::
 Composite _internal_state Struct
   (Member_plain _strm (tptr (Tstruct _z_stream_s noattr)) ::
    Member_plain _status tint :: Member_plain _pending_buf (tptr tuchar) ::
    Member_plain _pending_buf_size tulong ::
    Member_plain _pending_out (tptr tuchar) ::
    Member_plain _pending tulong :: Member_plain _wrap tint ::
    Member_plain _gzhead (tptr (Tstruct _gz_header_s noattr)) ::
    Member_plain _gzindex tulong :: Member_plain _method tuchar ::
    Member_plain _last_flush tint :: Member_plain _w_size tuint ::
    Member_plain _w_bits tuint :: Member_plain _w_mask tuint ::
    Member_plain _window (tptr tuchar) :: Member_plain _window_size tulong ::
    Member_plain _prev (tptr tushort) :: Member_plain _head (tptr tushort) ::
    Member_plain _ins_h tuint :: Member_plain _hash_size tuint ::
    Member_plain _hash_bits tuint :: Member_plain _hash_mask tuint ::
    Member_plain _hash_shift tuint :: Member_plain _block_start tlong ::
    Member_plain _match_length tuint :: Member_plain _prev_match tuint ::
    Member_plain _match_available tint :: Member_plain _strstart tuint ::
    Member_plain _match_start tuint :: Member_plain _lookahead tuint ::
    Member_plain _prev_length tuint ::
    Member_plain _max_chain_length tuint ::
    Member_plain _max_lazy_match tuint :: Member_plain _level tint ::
    Member_plain _strategy tint :: Member_plain _good_match tuint ::
    Member_plain _nice_match tint ::
    Member_plain _dyn_ltree (tarray (Tstruct _ct_data_s noattr) 573) ::
    Member_plain _dyn_dtree (tarray (Tstruct _ct_data_s noattr) 61) ::
    Member_plain _bl_tree (tarray (Tstruct _ct_data_s noattr) 39) ::
    Member_plain _l_desc (Tstruct _tree_desc_s noattr) ::
    Member_plain _d_desc (Tstruct _tree_desc_s noattr) ::
    Member_plain _bl_desc (Tstruct _tree_desc_s noattr) ::
    Member_plain _bl_count (tarray tushort 16) ::
    Member_plain _heap (tarray tint 573) :: Member_plain _heap_len tint ::
    Member_plain _heap_max tint :: Member_plain _depth (tarray tuchar 573) ::
    Member_plain _sym_buf (tptr tuchar) :: Member_plain _lit_bufsize tuint ::
    Member_plain _sym_next tuint :: Member_plain _sym_end tuint ::
    Member_plain _opt_len tulong :: Member_plain _static_len tulong ::
    Member_plain _matches tuint :: Member_plain _insert tuint ::
    Member_plain _bi_buf tushort :: Member_plain _bi_valid tint ::
    Member_plain _bi_used tint :: Member_plain _high_water tulong ::
    Member_plain _slid tint :: nil)
   noattr ::
 Composite _static_tree_desc_s Struct
   (Member_plain _static_tree (tptr (Tstruct _ct_data_s noattr)) ::
    Member_plain _extra_bits (tptr tint) :: Member_plain _extra_base tint ::
    Member_plain _elems tint :: Member_plain _max_length tint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) :: (_extra_lbits, Gvar v_extra_lbits) ::
 (_extra_dbits, Gvar v_extra_dbits) ::
 (_extra_blbits, Gvar v_extra_blbits) :: (_bl_order, Gvar v_bl_order) ::
 (_static_ltree, Gvar v_static_ltree) ::
 (_static_dtree, Gvar v_static_dtree) :: (__dist_code, Gvar v__dist_code) ::
 (__length_code, Gvar v__length_code) ::
 (_base_length, Gvar v_base_length) :: (_base_dist, Gvar v_base_dist) ::
 (_static_l_desc, Gvar v_static_l_desc) ::
 (_static_d_desc, Gvar v_static_d_desc) ::
 (_static_bl_desc, Gvar v_static_bl_desc) ::
 (_bi_reverse, Gfun(Internal f_bi_reverse)) ::
 (_bi_flush, Gfun(Internal f_bi_flush)) ::
 (_bi_windup, Gfun(Internal f_bi_windup)) ::
 (_gen_codes, Gfun(Internal f_gen_codes)) ::
 (_tr_static_init, Gfun(Internal f_tr_static_init)) ::
 (_init_block, Gfun(Internal f_init_block)) ::
 (__tr_init, Gfun(Internal f__tr_init)) ::
 (_pqdownheap, Gfun(Internal f_pqdownheap)) ::
 (_gen_bitlen, Gfun(Internal f_gen_bitlen)) ::
 (_build_tree, Gfun(Internal f_build_tree)) ::
 (_scan_tree, Gfun(Internal f_scan_tree)) ::
 (_send_tree, Gfun(Internal f_send_tree)) ::
 (_build_bl_tree, Gfun(Internal f_build_bl_tree)) ::
 (_send_all_trees, Gfun(Internal f_send_all_trees)) ::
 (__tr_stored_block, Gfun(Internal f__tr_stored_block)) ::
 (__tr_flush_bits, Gfun(Internal f__tr_flush_bits)) ::
 (__tr_align, Gfun(Internal f__tr_align)) ::
 (_compress_block, Gfun(Internal f_compress_block)) ::
 (_detect_data_type, Gfun(Internal f_detect_data_type)) ::
 (__tr_flush_block, Gfun(Internal f__tr_flush_block)) ::
 (__tr_tally, Gfun(Internal f__tr_tally)) :: nil).

Definition public_idents : list ident :=
(__tr_tally :: __tr_flush_block :: __tr_align :: __tr_flush_bits ::
 __tr_stored_block :: __tr_init :: __length_code :: __dist_code :: _memcpy ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


