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
  Definition source_file := "inflate.c".
  Definition normalized := true.
End Info.

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
Definition ___gp_code : ident := $"__gp_code".
Definition ___stringlit_inflate_1 : ident := $"__stringlit_inflate_1".
Definition ___stringlit_inflate_10 : ident := $"__stringlit_inflate_10".
Definition ___stringlit_inflate_11 : ident := $"__stringlit_inflate_11".
Definition ___stringlit_inflate_12 : ident := $"__stringlit_inflate_12".
Definition ___stringlit_inflate_13 : ident := $"__stringlit_inflate_13".
Definition ___stringlit_inflate_14 : ident := $"__stringlit_inflate_14".
Definition ___stringlit_inflate_15 : ident := $"__stringlit_inflate_15".
Definition ___stringlit_inflate_16 : ident := $"__stringlit_inflate_16".
Definition ___stringlit_inflate_17 : ident := $"__stringlit_inflate_17".
Definition ___stringlit_inflate_18 : ident := $"__stringlit_inflate_18".
Definition ___stringlit_inflate_19 : ident := $"__stringlit_inflate_19".
Definition ___stringlit_inflate_2 : ident := $"__stringlit_inflate_2".
Definition ___stringlit_inflate_3 : ident := $"__stringlit_inflate_3".
Definition ___stringlit_inflate_4 : ident := $"__stringlit_inflate_4".
Definition ___stringlit_inflate_5 : ident := $"__stringlit_inflate_5".
Definition ___stringlit_inflate_6 : ident := $"__stringlit_inflate_6".
Definition ___stringlit_inflate_7 : ident := $"__stringlit_inflate_7".
Definition ___stringlit_inflate_8 : ident := $"__stringlit_inflate_8".
Definition ___stringlit_inflate_9 : ident := $"__stringlit_inflate_9".
Definition _adler : ident := $"adler".
Definition _adler32 : ident := $"adler32".
Definition _avail_in : ident := $"avail_in".
Definition _avail_out : ident := $"avail_out".
Definition _back : ident := $"back".
Definition _bits : ident := $"bits".
Definition _buf : ident := $"buf".
Definition _check : ident := $"check".
Definition _codes : ident := $"codes".
Definition _comm_max : ident := $"comm_max".
Definition _comment : ident := $"comment".
Definition _copy : ident := $"copy".
Definition _crc32 : ident := $"crc32".
Definition _data_type : ident := $"data_type".
Definition _dest : ident := $"dest".
Definition _dictLength : ident := $"dictLength".
Definition _dictid : ident := $"dictid".
Definition _dictionary : ident := $"dictionary".
Definition _dist : ident := $"dist".
Definition _distbits : ident := $"distbits".
Definition _distcode : ident := $"distcode".
Definition _dmax : ident := $"dmax".
Definition _done : ident := $"done".
Definition _end : ident := $"end".
Definition _extra : ident := $"extra".
Definition _extra_len : ident := $"extra_len".
Definition _extra_max : ident := $"extra_max".
Definition _flags : ident := $"flags".
Definition _flush : ident := $"flush".
Definition _from : ident := $"from".
Definition _got : ident := $"got".
Definition _gz_header_s : ident := $"gz_header_s".
Definition _have : ident := $"have".
Definition _havedict : ident := $"havedict".
Definition _hbuf : ident := $"hbuf".
Definition _hcrc : ident := $"hcrc".
Definition _head : ident := $"head".
Definition _here : ident := $"here".
Definition _hold : ident := $"hold".
Definition _in : ident := $"in".
Definition _inflate : ident := $"inflate".
Definition _inflateCodesUsed : ident := $"inflateCodesUsed".
Definition _inflateCopy : ident := $"inflateCopy".
Definition _inflateEnd : ident := $"inflateEnd".
Definition _inflateGetDictionary : ident := $"inflateGetDictionary".
Definition _inflateGetHeader : ident := $"inflateGetHeader".
Definition _inflateInit2_ : ident := $"inflateInit2_".
Definition _inflateInit_ : ident := $"inflateInit_".
Definition _inflateMark : ident := $"inflateMark".
Definition _inflatePrime : ident := $"inflatePrime".
Definition _inflateReset : ident := $"inflateReset".
Definition _inflateReset2 : ident := $"inflateReset2".
Definition _inflateResetKeep : ident := $"inflateResetKeep".
Definition _inflateSetDictionary : ident := $"inflateSetDictionary".
Definition _inflateStateCheck : ident := $"inflateStateCheck".
Definition _inflateSync : ident := $"inflateSync".
Definition _inflateSyncPoint : ident := $"inflateSyncPoint".
Definition _inflateUndermine : ident := $"inflateUndermine".
Definition _inflateValidate : ident := $"inflateValidate".
Definition _inflate_fast : ident := $"inflate_fast".
Definition _inflate_fixed : ident := $"inflate_fixed".
Definition _inflate_state : ident := $"inflate_state".
Definition _inflate_table : ident := $"inflate_table".
Definition _internal_state : ident := $"internal_state".
Definition _last : ident := $"last".
Definition _leave : ident := $"leave".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _lenbits : ident := $"lenbits".
Definition _lencode : ident := $"lencode".
Definition _length : ident := $"length".
Definition _lens : ident := $"lens".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _mode : ident := $"mode".
Definition _msg : ident := $"msg".
Definition _name : ident := $"name".
Definition _name_max : ident := $"name_max".
Definition _ncode : ident := $"ncode".
Definition _ndist : ident := $"ndist".
Definition _next : ident := $"next".
Definition _next_in : ident := $"next_in".
Definition _next_out : ident := $"next_out".
Definition _nlen : ident := $"nlen".
Definition _offset : ident := $"offset".
Definition _op : ident := $"op".
Definition _opaque : ident := $"opaque".
Definition _order : ident := $"order".
Definition _os : ident := $"os".
Definition _out : ident := $"out".
Definition _put : ident := $"put".
Definition _reserved : ident := $"reserved".
Definition _ret : ident := $"ret".
Definition _sane : ident := $"sane".
Definition _source : ident := $"source".
Definition _state : ident := $"state".
Definition _stream_size : ident := $"stream_size".
Definition _strm : ident := $"strm".
Definition _subvert : ident := $"subvert".
Definition _syncsearch : ident := $"syncsearch".
Definition _text : ident := $"text".
Definition _time : ident := $"time".
Definition _total : ident := $"total".
Definition _total_in : ident := $"total_in".
Definition _total_out : ident := $"total_out".
Definition _updatewindow : ident := $"updatewindow".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _version : ident := $"version".
Definition _was : ident := $"was".
Definition _wbits : ident := $"wbits".
Definition _whave : ident := $"whave".
Definition _window : ident := $"window".
Definition _windowBits : ident := $"windowBits".
Definition _wnext : ident := $"wnext".
Definition _work : ident := $"work".
Definition _wrap : ident := $"wrap".
Definition _wsize : ident := $"wsize".
Definition _xflags : ident := $"xflags".
Definition _z_stream_s : ident := $"z_stream_s".
Definition _zalloc : ident := $"zalloc".
Definition _zcalloc : ident := $"zcalloc".
Definition _zcfree : ident := $"zcfree".
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
Definition _t'126 : ident := 253%positive.
Definition _t'127 : ident := 254%positive.
Definition _t'128 : ident := 255%positive.
Definition _t'129 : ident := 256%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'130 : ident := 257%positive.
Definition _t'131 : ident := 258%positive.
Definition _t'132 : ident := 259%positive.
Definition _t'133 : ident := 260%positive.
Definition _t'134 : ident := 261%positive.
Definition _t'135 : ident := 262%positive.
Definition _t'136 : ident := 263%positive.
Definition _t'137 : ident := 264%positive.
Definition _t'138 : ident := 265%positive.
Definition _t'139 : ident := 266%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'140 : ident := 267%positive.
Definition _t'141 : ident := 268%positive.
Definition _t'142 : ident := 269%positive.
Definition _t'143 : ident := 270%positive.
Definition _t'144 : ident := 271%positive.
Definition _t'145 : ident := 272%positive.
Definition _t'146 : ident := 273%positive.
Definition _t'147 : ident := 274%positive.
Definition _t'148 : ident := 275%positive.
Definition _t'149 : ident := 276%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'150 : ident := 277%positive.
Definition _t'151 : ident := 278%positive.
Definition _t'152 : ident := 279%positive.
Definition _t'153 : ident := 280%positive.
Definition _t'154 : ident := 281%positive.
Definition _t'155 : ident := 282%positive.
Definition _t'156 : ident := 283%positive.
Definition _t'157 : ident := 284%positive.
Definition _t'158 : ident := 285%positive.
Definition _t'159 : ident := 286%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'160 : ident := 287%positive.
Definition _t'161 : ident := 288%positive.
Definition _t'162 : ident := 289%positive.
Definition _t'163 : ident := 290%positive.
Definition _t'164 : ident := 291%positive.
Definition _t'165 : ident := 292%positive.
Definition _t'166 : ident := 293%positive.
Definition _t'167 : ident := 294%positive.
Definition _t'168 : ident := 295%positive.
Definition _t'169 : ident := 296%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'170 : ident := 297%positive.
Definition _t'171 : ident := 298%positive.
Definition _t'172 : ident := 299%positive.
Definition _t'173 : ident := 300%positive.
Definition _t'174 : ident := 301%positive.
Definition _t'175 : ident := 302%positive.
Definition _t'176 : ident := 303%positive.
Definition _t'177 : ident := 304%positive.
Definition _t'178 : ident := 305%positive.
Definition _t'179 : ident := 306%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'180 : ident := 307%positive.
Definition _t'181 : ident := 308%positive.
Definition _t'182 : ident := 309%positive.
Definition _t'183 : ident := 310%positive.
Definition _t'184 : ident := 311%positive.
Definition _t'185 : ident := 312%positive.
Definition _t'186 : ident := 313%positive.
Definition _t'187 : ident := 314%positive.
Definition _t'188 : ident := 315%positive.
Definition _t'189 : ident := 316%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'190 : ident := 317%positive.
Definition _t'191 : ident := 318%positive.
Definition _t'192 : ident := 319%positive.
Definition _t'193 : ident := 320%positive.
Definition _t'194 : ident := 321%positive.
Definition _t'195 : ident := 322%positive.
Definition _t'196 : ident := 323%positive.
Definition _t'197 : ident := 324%positive.
Definition _t'198 : ident := 325%positive.
Definition _t'199 : ident := 326%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'200 : ident := 327%positive.
Definition _t'201 : ident := 328%positive.
Definition _t'202 : ident := 329%positive.
Definition _t'203 : ident := 330%positive.
Definition _t'204 : ident := 331%positive.
Definition _t'205 : ident := 332%positive.
Definition _t'206 : ident := 333%positive.
Definition _t'207 : ident := 334%positive.
Definition _t'208 : ident := 335%positive.
Definition _t'209 : ident := 336%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'210 : ident := 337%positive.
Definition _t'211 : ident := 338%positive.
Definition _t'212 : ident := 339%positive.
Definition _t'213 : ident := 340%positive.
Definition _t'214 : ident := 341%positive.
Definition _t'215 : ident := 342%positive.
Definition _t'216 : ident := 343%positive.
Definition _t'217 : ident := 344%positive.
Definition _t'218 : ident := 345%positive.
Definition _t'219 : ident := 346%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'220 : ident := 347%positive.
Definition _t'221 : ident := 348%positive.
Definition _t'222 : ident := 349%positive.
Definition _t'223 : ident := 350%positive.
Definition _t'224 : ident := 351%positive.
Definition _t'225 : ident := 352%positive.
Definition _t'226 : ident := 353%positive.
Definition _t'227 : ident := 354%positive.
Definition _t'228 : ident := 355%positive.
Definition _t'229 : ident := 356%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'230 : ident := 357%positive.
Definition _t'231 : ident := 358%positive.
Definition _t'232 : ident := 359%positive.
Definition _t'233 : ident := 360%positive.
Definition _t'234 : ident := 361%positive.
Definition _t'235 : ident := 362%positive.
Definition _t'236 : ident := 363%positive.
Definition _t'237 : ident := 364%positive.
Definition _t'238 : ident := 365%positive.
Definition _t'239 : ident := 366%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'240 : ident := 367%positive.
Definition _t'241 : ident := 368%positive.
Definition _t'242 : ident := 369%positive.
Definition _t'243 : ident := 370%positive.
Definition _t'244 : ident := 371%positive.
Definition _t'245 : ident := 372%positive.
Definition _t'246 : ident := 373%positive.
Definition _t'247 : ident := 374%positive.
Definition _t'248 : ident := 375%positive.
Definition _t'249 : ident := 376%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'250 : ident := 377%positive.
Definition _t'251 : ident := 378%positive.
Definition _t'252 : ident := 379%positive.
Definition _t'253 : ident := 380%positive.
Definition _t'254 : ident := 381%positive.
Definition _t'255 : ident := 382%positive.
Definition _t'256 : ident := 383%positive.
Definition _t'257 : ident := 384%positive.
Definition _t'258 : ident := 385%positive.
Definition _t'259 : ident := 386%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'260 : ident := 387%positive.
Definition _t'261 : ident := 388%positive.
Definition _t'262 : ident := 389%positive.
Definition _t'263 : ident := 390%positive.
Definition _t'264 : ident := 391%positive.
Definition _t'265 : ident := 392%positive.
Definition _t'266 : ident := 393%positive.
Definition _t'267 : ident := 394%positive.
Definition _t'268 : ident := 395%positive.
Definition _t'269 : ident := 396%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'270 : ident := 397%positive.
Definition _t'271 : ident := 398%positive.
Definition _t'272 : ident := 399%positive.
Definition _t'273 : ident := 400%positive.
Definition _t'274 : ident := 401%positive.
Definition _t'275 : ident := 402%positive.
Definition _t'276 : ident := 403%positive.
Definition _t'277 : ident := 404%positive.
Definition _t'278 : ident := 405%positive.
Definition _t'279 : ident := 406%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'280 : ident := 407%positive.
Definition _t'281 : ident := 408%positive.
Definition _t'282 : ident := 409%positive.
Definition _t'283 : ident := 410%positive.
Definition _t'284 : ident := 411%positive.
Definition _t'285 : ident := 412%positive.
Definition _t'286 : ident := 413%positive.
Definition _t'287 : ident := 414%positive.
Definition _t'288 : ident := 415%positive.
Definition _t'289 : ident := 416%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'290 : ident := 417%positive.
Definition _t'291 : ident := 418%positive.
Definition _t'292 : ident := 419%positive.
Definition _t'293 : ident := 420%positive.
Definition _t'294 : ident := 421%positive.
Definition _t'295 : ident := 422%positive.
Definition _t'296 : ident := 423%positive.
Definition _t'297 : ident := 424%positive.
Definition _t'298 : ident := 425%positive.
Definition _t'299 : ident := 426%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'300 : ident := 427%positive.
Definition _t'301 : ident := 428%positive.
Definition _t'302 : ident := 429%positive.
Definition _t'303 : ident := 430%positive.
Definition _t'304 : ident := 431%positive.
Definition _t'305 : ident := 432%positive.
Definition _t'306 : ident := 433%positive.
Definition _t'307 : ident := 434%positive.
Definition _t'308 : ident := 435%positive.
Definition _t'309 : ident := 436%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'310 : ident := 437%positive.
Definition _t'311 : ident := 438%positive.
Definition _t'312 : ident := 439%positive.
Definition _t'313 : ident := 440%positive.
Definition _t'314 : ident := 441%positive.
Definition _t'315 : ident := 442%positive.
Definition _t'316 : ident := 443%positive.
Definition _t'317 : ident := 444%positive.
Definition _t'318 : ident := 445%positive.
Definition _t'319 : ident := 446%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'320 : ident := 447%positive.
Definition _t'321 : ident := 448%positive.
Definition _t'322 : ident := 449%positive.
Definition _t'323 : ident := 450%positive.
Definition _t'324 : ident := 451%positive.
Definition _t'325 : ident := 452%positive.
Definition _t'326 : ident := 453%positive.
Definition _t'327 : ident := 454%positive.
Definition _t'328 : ident := 455%positive.
Definition _t'329 : ident := 456%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'330 : ident := 457%positive.
Definition _t'331 : ident := 458%positive.
Definition _t'332 : ident := 459%positive.
Definition _t'333 : ident := 460%positive.
Definition _t'334 : ident := 461%positive.
Definition _t'335 : ident := 462%positive.
Definition _t'336 : ident := 463%positive.
Definition _t'337 : ident := 464%positive.
Definition _t'338 : ident := 465%positive.
Definition _t'339 : ident := 466%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'340 : ident := 467%positive.
Definition _t'341 : ident := 468%positive.
Definition _t'342 : ident := 469%positive.
Definition _t'343 : ident := 470%positive.
Definition _t'344 : ident := 471%positive.
Definition _t'345 : ident := 472%positive.
Definition _t'346 : ident := 473%positive.
Definition _t'347 : ident := 474%positive.
Definition _t'348 : ident := 475%positive.
Definition _t'349 : ident := 476%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'350 : ident := 477%positive.
Definition _t'351 : ident := 478%positive.
Definition _t'352 : ident := 479%positive.
Definition _t'353 : ident := 480%positive.
Definition _t'354 : ident := 481%positive.
Definition _t'355 : ident := 482%positive.
Definition _t'356 : ident := 483%positive.
Definition _t'357 : ident := 484%positive.
Definition _t'358 : ident := 485%positive.
Definition _t'359 : ident := 486%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'360 : ident := 487%positive.
Definition _t'361 : ident := 488%positive.
Definition _t'362 : ident := 489%positive.
Definition _t'363 : ident := 490%positive.
Definition _t'364 : ident := 491%positive.
Definition _t'365 : ident := 492%positive.
Definition _t'366 : ident := 493%positive.
Definition _t'367 : ident := 494%positive.
Definition _t'368 : ident := 495%positive.
Definition _t'369 : ident := 496%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'370 : ident := 497%positive.
Definition _t'371 : ident := 498%positive.
Definition _t'372 : ident := 499%positive.
Definition _t'373 : ident := 500%positive.
Definition _t'374 : ident := 501%positive.
Definition _t'375 : ident := 502%positive.
Definition _t'376 : ident := 503%positive.
Definition _t'377 : ident := 504%positive.
Definition _t'378 : ident := 505%positive.
Definition _t'379 : ident := 506%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'380 : ident := 507%positive.
Definition _t'381 : ident := 508%positive.
Definition _t'382 : ident := 509%positive.
Definition _t'383 : ident := 510%positive.
Definition _t'384 : ident := 511%positive.
Definition _t'385 : ident := 512%positive.
Definition _t'386 : ident := 513%positive.
Definition _t'387 : ident := 514%positive.
Definition _t'388 : ident := 515%positive.
Definition _t'389 : ident := 516%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'390 : ident := 517%positive.
Definition _t'391 : ident := 518%positive.
Definition _t'392 : ident := 519%positive.
Definition _t'393 : ident := 520%positive.
Definition _t'394 : ident := 521%positive.
Definition _t'395 : ident := 522%positive.
Definition _t'396 : ident := 523%positive.
Definition _t'397 : ident := 524%positive.
Definition _t'398 : ident := 525%positive.
Definition _t'399 : ident := 526%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'400 : ident := 527%positive.
Definition _t'401 : ident := 528%positive.
Definition _t'402 : ident := 529%positive.
Definition _t'403 : ident := 530%positive.
Definition _t'404 : ident := 531%positive.
Definition _t'405 : ident := 532%positive.
Definition _t'406 : ident := 533%positive.
Definition _t'407 : ident := 534%positive.
Definition _t'408 : ident := 535%positive.
Definition _t'409 : ident := 536%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'410 : ident := 537%positive.
Definition _t'411 : ident := 538%positive.
Definition _t'412 : ident := 539%positive.
Definition _t'413 : ident := 540%positive.
Definition _t'414 : ident := 541%positive.
Definition _t'415 : ident := 542%positive.
Definition _t'416 : ident := 543%positive.
Definition _t'417 : ident := 544%positive.
Definition _t'418 : ident := 545%positive.
Definition _t'419 : ident := 546%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'420 : ident := 547%positive.
Definition _t'421 : ident := 548%positive.
Definition _t'422 : ident := 549%positive.
Definition _t'423 : ident := 550%positive.
Definition _t'424 : ident := 551%positive.
Definition _t'425 : ident := 552%positive.
Definition _t'426 : ident := 553%positive.
Definition _t'427 : ident := 554%positive.
Definition _t'428 : ident := 555%positive.
Definition _t'429 : ident := 556%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'430 : ident := 557%positive.
Definition _t'431 : ident := 558%positive.
Definition _t'432 : ident := 559%positive.
Definition _t'433 : ident := 560%positive.
Definition _t'434 : ident := 561%positive.
Definition _t'435 : ident := 562%positive.
Definition _t'436 : ident := 563%positive.
Definition _t'437 : ident := 564%positive.
Definition _t'438 : ident := 565%positive.
Definition _t'439 : ident := 566%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'440 : ident := 567%positive.
Definition _t'441 : ident := 568%positive.
Definition _t'442 : ident := 569%positive.
Definition _t'443 : ident := 570%positive.
Definition _t'444 : ident := 571%positive.
Definition _t'445 : ident := 572%positive.
Definition _t'446 : ident := 573%positive.
Definition _t'447 : ident := 574%positive.
Definition _t'448 : ident := 575%positive.
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

Definition v___stringlit_inflate_5 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_10 := {|
  gvar_info := (tarray tschar 22);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_15 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_7 := {|
  gvar_info := (tarray tschar 26);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_14 := {|
  gvar_info := (tarray tschar 19);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_6 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_8 := {|
  gvar_info := (tarray tschar 37);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_2 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_13 := {|
  gvar_info := (tarray tschar 29);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_17 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_12 := {|
  gvar_info := (tarray tschar 36);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_18 := {|
  gvar_info := (tarray tschar 23);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_3 := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_9 := {|
  gvar_info := (tarray tschar 28);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_16 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 112) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_4 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_19 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 119) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_inflate_11 := {|
  gvar_info := (tarray tschar 25);
  gvar_init := (Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_inflateStateCheck := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'11,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) ::
               (_t'10,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) ::
               (_t'9, (tptr (Tstruct _internal_state noattr))) ::
               (_t'8, (tptr (Tstruct _z_stream_s noattr))) :: (_t'7, tint) ::
               (_t'6, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zalloc
              (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                      (tptr tvoid) cc_default))))
          (Sset _t'1
            (Ecast
              (Ebinop Oeq
                (Etempvar _t'11 (tptr (Tfunction
                                        ((tptr tvoid) :: tuint :: tuint ::
                                         nil) (tptr tvoid) cc_default)))
                (Ecast (Econst_int (Int.repr 0) tint)
                  (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                          (tptr tvoid) cc_default))) tint) tbool))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zfree
              (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                      cc_default))))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq
                (Etempvar _t'10 (tptr (Tfunction
                                        ((tptr tvoid) :: (tptr tvoid) :: nil)
                                        tvoid cc_default)))
                (Ecast (Econst_int (Int.repr 0) tint)
                  (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                          tvoid cc_default))) tint) tbool)))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'9 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sset _t'3 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _strm
                    (tptr (Tstruct _z_stream_s noattr))))
                (Sset _t'3
                  (Ecast
                    (Ebinop One
                      (Etempvar _t'8 (tptr (Tstruct _z_stream_s noattr)))
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      tint) tbool))))
            (Sifthenelse (Etempvar _t'3 tint)
              (Sset _t'4 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _mode tint))
                (Sset _t'4
                  (Ecast
                    (Ebinop Olt (Etempvar _t'7 tint)
                      (Econst_int (Int.repr 16180) tint) tint) tbool)))))
          (Sifthenelse (Etempvar _t'4 tint)
            (Sset _t'5 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _mode tint))
              (Sset _t'5
                (Ecast
                  (Ebinop Ogt (Etempvar _t'6 tint)
                    (Econst_int (Int.repr 16211) tint) tint) tbool)))))
        (Sifthenelse (Etempvar _t'5 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_inflateResetKeep := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'5, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'4, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tint) ::
               (_t'8, (tptr (Tstruct _internal_state noattr))) ::
               (_t'7, tint) :: (_t'6, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'8 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tulong))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _total tulong)
                (Etempvar _t'2 tulong)))
            (Sset _t'3 (Ecast (Etempvar _t'2 tulong) tulong)))
          (Sassign
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _total_out tulong)
            (Etempvar _t'3 tulong)))
        (Sassign
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _total_in tulong)
          (Etempvar _t'3 tulong)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _msg (tptr tschar))
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _data_type tint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wrap tint))
              (Sifthenelse (Etempvar _t'6 tint)
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wrap tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _adler tulong)
                    (Ebinop Oand (Etempvar _t'7 tint)
                      (Econst_int (Int.repr 1) tint) tint)))
                Sskip))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _mode tint)
                (Econst_int (Int.repr 16180) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _last tint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _havedict tint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _flags tint)
                      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _dmax tuint)
                        (Econst_int (Int.repr 32768) tuint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _head
                            (tptr (Tstruct _gz_header_s noattr)))
                          (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _hold
                              tulong) (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _bits
                                tuint) (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'4
                                        (Ecast
                                          (Efield
                                            (Ederef
                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                              (Tstruct _inflate_state noattr))
                                            _codes
                                            (tarray (Tstruct ___gp_code noattr) 1444))
                                          (tptr (Tstruct ___gp_code noattr))))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _next
                                          (tptr (Tstruct ___gp_code noattr)))
                                        (Etempvar _t'4 (tptr (Tstruct ___gp_code noattr)))))
                                    (Sset _t'5
                                      (Ecast
                                        (Etempvar _t'4 (tptr (Tstruct ___gp_code noattr)))
                                        (tptr (Tstruct ___gp_code noattr)))))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _distcode
                                      (tptr (Tstruct ___gp_code noattr)))
                                    (Etempvar _t'5 (tptr (Tstruct ___gp_code noattr)))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr))
                                    _lencode
                                    (tptr (Tstruct ___gp_code noattr)))
                                  (Etempvar _t'5 (tptr (Tstruct ___gp_code noattr)))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _sane
                                    tint) (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _back tint)
                                    (Eunop Oneg
                                      (Econst_int (Int.repr 1) tint) tint))
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))
|}.

Definition f_inflateReset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'8, (tptr (Tstruct _internal_state noattr))) ::
               (_t'7, (tptr tuchar)) :: (_t'6, (tptr tvoid)) ::
               (_t'5,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: (_t'4, (tptr tuchar)) ::
               (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'8 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _wrap tint))
        (Sifthenelse (Ebinop Oand (Etempvar _t'3 tint)
                       (Econst_int (Int.repr 8) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
              (Sifthenelse (Ebinop One (Etempvar _t'4 (tptr tuchar))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                          (Tstruct _z_stream_s noattr)) _zfree
                        (tptr (Tfunction
                                ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                                cc_default))))
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                            (Tstruct _z_stream_s noattr)) _opaque
                          (tptr tvoid)))
                      (Ssequence
                        (Sset _t'7
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _window
                            (tptr tuchar)))
                        (Scall None
                          (Ederef
                            (Etempvar _t'5 (tptr (Tfunction
                                                   ((tptr tvoid) ::
                                                    (tptr tvoid) :: nil)
                                                   tvoid cc_default)))
                            (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                              tvoid cc_default))
                          ((Etempvar _t'6 (tptr tvoid)) ::
                           (Ecast (Etempvar _t'7 (tptr tuchar)) (tptr tvoid)) ::
                           nil)))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _window
                      (tptr tuchar)) (Econst_int (Int.repr 0) tint)))
                Sskip))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wbits tuint)
              (Econst_int (Int.repr 0) tint)))
          Sskip))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _wsize tuint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _whave tuint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wnext tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Scall (Some _t'2)
                (Evar _inflateResetKeep (Tfunction
                                          ((tptr (Tstruct _z_stream_s noattr)) ::
                                           nil) tint cc_default))
                ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
              (Sreturn (Some (Etempvar _t'2 tint))))))))))
|}.

Definition f_inflateReset2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_windowBits, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_wrap, tint) ::
               (_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) ::
               (_t'10, (tptr (Tstruct _internal_state noattr))) ::
               (_t'9, tuint) :: (_t'8, (tptr tuchar)) ::
               (_t'7, (tptr tuchar)) :: (_t'6, (tptr tvoid)) ::
               (_t'5,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'10 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _windowBits tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _windowBits tint)
                         (Eunop Oneg (Econst_int (Int.repr 15) tint) tint)
                         tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
            Sskip)
          (Ssequence
            (Sset _wrap (Econst_int (Int.repr 0) tint))
            (Sset _windowBits (Eunop Oneg (Etempvar _windowBits tint) tint))))
        (Ssequence
          (Sset _wrap
            (Ebinop Oadd
              (Ebinop Oshr (Etempvar _windowBits tint)
                (Econst_int (Int.repr 4) tint) tint)
              (Econst_int (Int.repr 5) tint) tint))
          (Sifthenelse (Ebinop Olt (Etempvar _windowBits tint)
                         (Econst_int (Int.repr 48) tint) tint)
            (Sset _windowBits
              (Ebinop Oand (Etempvar _windowBits tint)
                (Econst_int (Int.repr 15) tint) tint))
            Sskip)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Etempvar _windowBits tint)
            (Sifthenelse (Ebinop Olt (Etempvar _windowBits tint)
                           (Econst_int (Int.repr 8) tint) tint)
              (Sset _t'2 (Ecast (Econst_int (Int.repr 1) tint) tbool))
              (Ssequence
                (Sset _t'2
                  (Ecast
                    (Ebinop Ogt (Etempvar _windowBits tint)
                      (Econst_int (Int.repr 15) tint) tint) tbool))
                (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool))))
            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'2 tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
            Sskip))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
              (Sifthenelse (Ebinop One (Etempvar _t'8 (tptr tuchar))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wbits tuint))
                  (Sset _t'3
                    (Ecast
                      (Ebinop One (Etempvar _t'9 tuint)
                        (Ecast (Etempvar _windowBits tint) tuint) tint)
                      tbool)))
                (Sset _t'3 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'3 tint)
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _zfree
                      (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                              tvoid cc_default))))
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                          (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _window
                          (tptr tuchar)))
                      (Scall None
                        (Ederef
                          (Etempvar _t'5 (tptr (Tfunction
                                                 ((tptr tvoid) ::
                                                  (tptr tvoid) :: nil) tvoid
                                                 cc_default)))
                          (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                            tvoid cc_default))
                        ((Etempvar _t'6 (tptr tvoid)) ::
                         (Ecast (Etempvar _t'7 (tptr tuchar)) (tptr tvoid)) ::
                         nil)))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _window (tptr tuchar))
                  (Econst_int (Int.repr 0) tint)))
              Sskip))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _windowBits tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _wrap
                (Ebinop Oor (Etempvar _wrap tint)
                  (Econst_int (Int.repr 8) tint) tint))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wrap tint)
                (Etempvar _wrap tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _wbits tuint)
                  (Ecast (Etempvar _windowBits tint) tuint))
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _inflateReset (Tfunction
                                          ((tptr (Tstruct _z_stream_s noattr)) ::
                                           nil) tint cc_default))
                    ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
                     nil))
                  (Sreturn (Some (Etempvar _t'4 tint))))))))))))
|}.

Definition f_inflateInit2_ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_windowBits, tint) :: (_version, (tptr tschar)) ::
                (_stream_size, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'4, tint) :: (_t'3, (tptr tvoid)) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'12, tschar) :: (_t'11, tschar) ::
               (_t'10,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) ::
               (_t'9,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: (_t'8, (tptr tvoid)) ::
               (_t'7,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) :: (_t'6, (tptr tvoid)) ::
               (_t'5,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _version (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd (Etempvar _version (tptr tschar))
                (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
          (Ssequence
            (Sset _t'12
              (Ederef
                (Ebinop Oadd (Evar ___stringlit_inflate_1 (tarray tschar 6))
                  (Econst_int (Int.repr 0) tint) (tptr tschar)) tschar))
            (Sset _t'1
              (Ecast
                (Ebinop One (Etempvar _t'11 tschar) (Etempvar _t'12 tschar)
                  tint) tbool)))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Sset _t'2
          (Ecast
            (Ebinop One (Etempvar _stream_size tint)
              (Ecast (Esizeof (Tstruct _z_stream_s noattr) tulong) tint)
              tint) tbool))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 6) tint) tint)))
      Sskip))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _msg (tptr tschar))
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zalloc
              (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                      (tptr tvoid) cc_default))))
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _t'10 (tptr (Tfunction
                                                 ((tptr tvoid) :: tuint ::
                                                  tuint :: nil) (tptr tvoid)
                                                 cc_default)))
                         (Ecast (Econst_int (Int.repr 0) tint)
                           (tptr (Tfunction
                                   ((tptr tvoid) :: tuint :: tuint :: nil)
                                   (tptr tvoid) cc_default))) tint)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _zalloc
                  (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                          (tptr tvoid) cc_default)))
                (Evar _zcalloc (Tfunction
                                 ((tptr tvoid) :: tuint :: tuint :: nil)
                                 (tptr tvoid) cc_default)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
            Sskip))
        (Ssequence
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _zfree
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'9 (tptr (Tfunction
                                                  ((tptr tvoid) ::
                                                   (tptr tvoid) :: nil) tvoid
                                                  cc_default)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr (Tfunction
                                     ((tptr tvoid) :: (tptr tvoid) :: nil)
                                     tvoid cc_default))) tint)
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _zfree
                  (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil)
                          tvoid cc_default)))
                (Evar _zcfree (Tfunction
                                ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                                cc_default)))
              Sskip))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'7
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _zalloc
                    (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                            (tptr tvoid) cc_default))))
                (Ssequence
                  (Sset _t'8
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
                  (Scall (Some _t'3)
                    (Ederef
                      (Etempvar _t'7 (tptr (Tfunction
                                             ((tptr tvoid) :: tuint ::
                                              tuint :: nil) (tptr tvoid)
                                             cc_default)))
                      (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))
                    ((Etempvar _t'8 (tptr tvoid)) ::
                     (Econst_int (Int.repr 1) tint) ::
                     (Esizeof (Tstruct _inflate_state noattr) tulong) :: nil))))
              (Sset _state
                (Ecast (Etempvar _t'3 (tptr tvoid))
                  (tptr (Tstruct _inflate_state noattr)))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 4) tint)
                                 tint)))
                Sskip)
              (Ssequence
                (Scall None
                  (Evar _memset (Tfunction
                                  ((tptr tvoid) :: tint :: tulong :: nil)
                                  (tptr tvoid) cc_default))
                  ((Etempvar _state (tptr (Tstruct _inflate_state noattr))) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Esizeof (Tstruct _inflate_state noattr) tulong) :: nil))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _state
                      (tptr (Tstruct _internal_state noattr)))
                    (Ecast
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (tptr (Tstruct _internal_state noattr))))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _strm
                        (tptr (Tstruct _z_stream_s noattr)))
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _window
                          (tptr tuchar)) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _mode tint)
                          (Econst_int (Int.repr 16180) tint))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _inflateReset2 (Tfunction
                                                     ((tptr (Tstruct _z_stream_s noattr)) ::
                                                      tint :: nil) tint
                                                     cc_default))
                              ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
                               (Etempvar _windowBits tint) :: nil))
                            (Sset _ret (Etempvar _t'4 tint)))
                          (Ssequence
                            (Sifthenelse (Ebinop One (Etempvar _ret tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5
                                    (Efield
                                      (Ederef
                                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                        (Tstruct _z_stream_s noattr)) _zfree
                                      (tptr (Tfunction
                                              ((tptr tvoid) ::
                                               (tptr tvoid) :: nil) tvoid
                                              cc_default))))
                                  (Ssequence
                                    (Sset _t'6
                                      (Efield
                                        (Ederef
                                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                          (Tstruct _z_stream_s noattr))
                                        _opaque (tptr tvoid)))
                                    (Scall None
                                      (Ederef
                                        (Etempvar _t'5 (tptr (Tfunction
                                                               ((tptr tvoid) ::
                                                                (tptr tvoid) ::
                                                                nil) tvoid
                                                               cc_default)))
                                        (Tfunction
                                          ((tptr tvoid) :: (tptr tvoid) ::
                                           nil) tvoid cc_default))
                                      ((Etempvar _t'6 (tptr tvoid)) ::
                                       (Ecast
                                         (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                         (tptr tvoid)) :: nil))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                      (Tstruct _z_stream_s noattr)) _state
                                    (tptr (Tstruct _internal_state noattr)))
                                  (Econst_int (Int.repr 0) tint)))
                              Sskip)
                            (Sreturn (Some (Etempvar _ret tint)))))))))))))))))
|}.

Definition f_inflateInit_ := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_version, (tptr tschar)) :: (_stream_size, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _inflateInit2_ (Tfunction
                           ((tptr (Tstruct _z_stream_s noattr)) :: tint ::
                            (tptr tschar) :: tint :: nil) tint cc_default))
    ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
     (Econst_int (Int.repr 15) tint) :: (Etempvar _version (tptr tschar)) ::
     (Etempvar _stream_size tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_inflatePrime := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_bits, tint) :: (_value, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'7, (tptr (Tstruct _internal_state noattr))) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tulong) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _bits tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _state
            (tptr (Tstruct _internal_state noattr))))
        (Sset _state
          (Ecast (Etempvar _t'7 (tptr (Tstruct _internal_state noattr)))
            (tptr (Tstruct _inflate_state noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _bits tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _hold tulong)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _bits tuint)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
          Sskip)
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _bits tint)
                           (Econst_int (Int.repr 16) tint) tint)
              (Sset _t'2 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _bits tuint))
                (Sset _t'2
                  (Ecast
                    (Ebinop Ogt
                      (Ebinop Oadd (Etempvar _t'6 tuint)
                        (Ecast (Etempvar _bits tint) tuint) tuint)
                      (Econst_int (Int.repr 32) tint) tint) tbool))))
            (Sifthenelse (Etempvar _t'2 tint)
              (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
              Sskip))
          (Ssequence
            (Sset _value
              (Ecast
                (Ebinop Oand (Etempvar _value tint)
                  (Ebinop Osub
                    (Ebinop Oshl (Econst_long (Int64.repr 1) tlong)
                      (Etempvar _bits tint) tlong)
                    (Econst_int (Int.repr 1) tint) tlong) tlong) tint))
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _hold tulong))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _bits tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _hold tulong)
                    (Ebinop Oadd (Etempvar _t'4 tulong)
                      (Ebinop Oshl (Ecast (Etempvar _value tint) tulong)
                        (Etempvar _t'5 tuint) tulong) tulong))))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _bits tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _bits tuint)
                    (Ebinop Oadd (Etempvar _t'3 tuint)
                      (Ecast (Etempvar _bits tint) tuint) tuint)))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_updatewindow := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_end, (tptr tuchar)) :: (_copy, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_dist, tuint) :: (_t'1, (tptr tvoid)) ::
               (_t'26, (tptr (Tstruct _internal_state noattr))) ::
               (_t'25, tuint) :: (_t'24, (tptr tvoid)) ::
               (_t'23,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) ::
               (_t'22, (tptr tuchar)) :: (_t'21, (tptr tuchar)) ::
               (_t'20, tuint) :: (_t'19, tuint) :: (_t'18, tuint) ::
               (_t'17, tuint) :: (_t'16, (tptr tuchar)) :: (_t'15, tuint) ::
               (_t'14, tuint) :: (_t'13, tuint) :: (_t'12, tuint) ::
               (_t'11, (tptr tuchar)) :: (_t'10, (tptr tuchar)) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'26
      (Efield
        (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
          (Tstruct _z_stream_s noattr)) _state
        (tptr (Tstruct _internal_state noattr))))
    (Sset _state
      (Ecast (Etempvar _t'26 (tptr (Tstruct _internal_state noattr)))
        (tptr (Tstruct _inflate_state noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'21
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
            (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'21 (tptr tuchar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'23
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _zalloc
                  (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                          (tptr tvoid) cc_default))))
              (Ssequence
                (Sset _t'24
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
                (Ssequence
                  (Sset _t'25
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wbits tuint))
                  (Scall (Some _t'1)
                    (Ederef
                      (Etempvar _t'23 (tptr (Tfunction
                                              ((tptr tvoid) :: tuint ::
                                               tuint :: nil) (tptr tvoid)
                                              cc_default)))
                      (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))
                    ((Etempvar _t'24 (tptr tvoid)) ::
                     (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                       (Etempvar _t'25 tuint) tuint) ::
                     (Esizeof tuchar tulong) :: nil)))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _window (tptr tuchar))
              (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tuchar))))
          (Ssequence
            (Sset _t'22
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'22 (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Sreturn (Some (Econst_int (Int.repr 1) tint)))
              Sskip)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'19
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _wsize tuint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'19 tuint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Ssequence
              (Sset _t'20
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wbits tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wsize tuint)
                (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                  (Etempvar _t'20 tuint) tuint)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _wnext tuint)
                (Econst_int (Int.repr 0) tint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _whave tuint)
                (Econst_int (Int.repr 0) tint))))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _wsize tuint))
          (Sifthenelse (Ebinop Oge (Etempvar _copy tuint)
                         (Etempvar _t'2 tuint) tint)
            (Ssequence
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
                (Ssequence
                  (Sset _t'17
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wsize tuint))
                  (Ssequence
                    (Sset _t'18
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _wsize tuint))
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      ((tptr tvoid) :: (tptr tvoid) ::
                                       tulong :: nil) (tptr tvoid)
                                      cc_default))
                      ((Etempvar _t'16 (tptr tuchar)) ::
                       (Ebinop Osub (Etempvar _end (tptr tuchar))
                         (Etempvar _t'17 tuint) (tptr tuchar)) ::
                       (Etempvar _t'18 tuint) :: nil)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _wnext tuint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wsize tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _whave tuint)
                    (Etempvar _t'15 tuint)))))
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _wsize tuint))
                (Ssequence
                  (Sset _t'14
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _wnext tuint))
                  (Sset _dist
                    (Ebinop Osub (Etempvar _t'13 tuint)
                      (Etempvar _t'14 tuint) tuint))))
              (Ssequence
                (Sifthenelse (Ebinop Ogt (Etempvar _dist tuint)
                               (Etempvar _copy tuint) tint)
                  (Sset _dist (Etempvar _copy tuint))
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _window
                        (tptr tuchar)))
                    (Ssequence
                      (Sset _t'12
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _wnext tuint))
                      (Scall None
                        (Evar _memcpy (Tfunction
                                        ((tptr tvoid) :: (tptr tvoid) ::
                                         tulong :: nil) (tptr tvoid)
                                        cc_default))
                        ((Ebinop Oadd (Etempvar _t'11 (tptr tuchar))
                           (Etempvar _t'12 tuint) (tptr tuchar)) ::
                         (Ebinop Osub (Etempvar _end (tptr tuchar))
                           (Etempvar _copy tuint) (tptr tuchar)) ::
                         (Etempvar _dist tuint) :: nil))))
                  (Ssequence
                    (Sset _copy
                      (Ebinop Osub (Etempvar _copy tuint)
                        (Etempvar _dist tuint) tuint))
                    (Sifthenelse (Etempvar _copy tuint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _window
                              (tptr tuchar)))
                          (Scall None
                            (Evar _memcpy (Tfunction
                                            ((tptr tvoid) :: (tptr tvoid) ::
                                             tulong :: nil) (tptr tvoid)
                                            cc_default))
                            ((Etempvar _t'10 (tptr tuchar)) ::
                             (Ebinop Osub (Etempvar _end (tptr tuchar))
                               (Etempvar _copy tuint) (tptr tuchar)) ::
                             (Etempvar _copy tuint) :: nil)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wnext
                              tuint) (Etempvar _copy tuint))
                          (Ssequence
                            (Sset _t'9
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _wsize
                                tuint))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _whave
                                tuint) (Etempvar _t'9 tuint)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wnext
                              tuint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wnext
                              tuint)
                            (Ebinop Oadd (Etempvar _t'8 tuint)
                              (Etempvar _dist tuint) tuint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'6
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _wnext
                                tuint))
                            (Ssequence
                              (Sset _t'7
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _wsize
                                  tuint))
                              (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                                             (Etempvar _t'7 tuint) tint)
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _wnext
                                    tuint) (Econst_int (Int.repr 0) tint))
                                Sskip)))
                          (Ssequence
                            (Sset _t'3
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _whave
                                tuint))
                            (Ssequence
                              (Sset _t'4
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _wsize
                                  tuint))
                              (Sifthenelse (Ebinop Olt (Etempvar _t'3 tuint)
                                             (Etempvar _t'4 tuint) tint)
                                (Ssequence
                                  (Sset _t'5
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _whave tuint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _whave tuint)
                                    (Ebinop Oadd (Etempvar _t'5 tuint)
                                      (Etempvar _dist tuint) tuint)))
                                Sskip))))))))))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition v_order := {|
  gvar_info := (tarray tushort 19);
  gvar_init := (Init_int16 (Int.repr 16) :: Init_int16 (Int.repr 17) ::
                Init_int16 (Int.repr 18) :: Init_int16 (Int.repr 0) ::
                Init_int16 (Int.repr 8) :: Init_int16 (Int.repr 7) ::
                Init_int16 (Int.repr 9) :: Init_int16 (Int.repr 6) ::
                Init_int16 (Int.repr 10) :: Init_int16 (Int.repr 5) ::
                Init_int16 (Int.repr 11) :: Init_int16 (Int.repr 4) ::
                Init_int16 (Int.repr 12) :: Init_int16 (Int.repr 3) ::
                Init_int16 (Int.repr 13) :: Init_int16 (Int.repr 2) ::
                Init_int16 (Int.repr 14) :: Init_int16 (Int.repr 1) ::
                Init_int16 (Int.repr 15) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_inflate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_flush, tint) :: nil);
  fn_vars := ((_here, (Tstruct ___gp_code noattr)) ::
              (_last, (Tstruct ___gp_code noattr)) ::
              (_hbuf, (tarray tuchar 4)) :: nil);
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_next, (tptr tuchar)) :: (_put, (tptr tuchar)) ::
               (_have, tuint) :: (_left, tuint) :: (_hold, tulong) ::
               (_bits, tuint) :: (_in, tuint) :: (_out, tuint) ::
               (_copy, tuint) :: (_from, (tptr tuchar)) :: (_len, tuint) ::
               (_ret, tint) :: (_leave, tint) :: (_t'110, tint) ::
               (_t'109, tint) :: (_t'108, tint) :: (_t'107, tint) ::
               (_t'106, tint) :: (_t'105, tint) :: (_t'104, tint) ::
               (_t'103, tint) :: (_t'102, tulong) :: (_t'101, tulong) ::
               (_t'100, tulong) :: (_t'99, tulong) :: (_t'98, tint) ::
               (_t'97, tint) :: (_t'96, tint) :: (_t'95, tint) ::
               (_t'94, tint) :: (_t'93, (tptr tuchar)) :: (_t'92, tulong) ::
               (_t'91, tint) :: (_t'90, tint) :: (_t'89, tulong) ::
               (_t'88, tulong) :: (_t'87, tulong) :: (_t'86, tulong) ::
               (_t'85, (tptr tuchar)) :: (_t'84, (tptr tuchar)) ::
               (_t'83, (tptr tuchar)) :: (_t'82, (tptr tuchar)) ::
               (_t'81, tuint) :: (_t'80, (tptr tuchar)) ::
               (_t'79, (tptr tuchar)) :: (_t'78, (tptr tuchar)) ::
               (_t'77, (tptr tuchar)) :: (_t'76, tint) ::
               (_t'75, (tptr tuchar)) :: (_t'74, (tptr tuchar)) ::
               (_t'73, tint) :: (_t'72, tint) :: (_t'71, tint) ::
               (_t'70, tint) :: (_t'69, tuint) :: (_t'68, tuint) ::
               (_t'67, (tptr tuchar)) :: (_t'66, (tptr tuchar)) ::
               (_t'65, (tptr tuchar)) :: (_t'64, tuint) ::
               (_t'63, (tptr tuchar)) :: (_t'62, tint) ::
               (_t'61, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'60, tuint) :: (_t'59, tuint) :: (_t'58, (tptr tuchar)) ::
               (_t'57, tint) :: (_t'56, (tptr tuchar)) ::
               (_t'55, (tptr tuchar)) :: (_t'54, (tptr tuchar)) ::
               (_t'53, tint) :: (_t'52, tulong) :: (_t'51, tulong) ::
               (_t'50, tulong) :: (_t'49, (tptr tuchar)) ::
               (_t'48, tulong) :: (_t'47, tulong) :: (_t'46, tint) ::
               (_t'45, (tptr tuchar)) :: (_t'44, tint) :: (_t'43, tulong) ::
               (_t'42, tint) :: (_t'41, tint) :: (_t'40, tuint) ::
               (_t'39, tuint) :: (_t'38, tint) :: (_t'37, tint) ::
               (_t'36, tulong) :: (_t'35, tint) :: (_t'34, tint) ::
               (_t'33, tuint) :: (_t'32, tuint) :: (_t'31, tint) ::
               (_t'30, tint) :: (_t'29, tulong) :: (_t'28, tuint) ::
               (_t'27, tint) :: (_t'26, tint) :: (_t'25, tuint) ::
               (_t'24, tint) :: (_t'23, tulong) :: (_t'22, (tptr tuchar)) ::
               (_t'21, tint) :: (_t'20, tulong) :: (_t'19, (tptr tuchar)) ::
               (_t'18, tint) :: (_t'17, tulong) :: (_t'16, (tptr tuchar)) ::
               (_t'15, tint) :: (_t'14, tulong) :: (_t'13, (tptr tuchar)) ::
               (_t'12, tint) :: (_t'11, tulong) :: (_t'10, tulong) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, (tptr tuchar)) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'448, (tptr tuchar)) :: (_t'447, tuint) ::
               (_t'446, (tptr tuchar)) ::
               (_t'445, (tptr (Tstruct _internal_state noattr))) ::
               (_t'444, tint) :: (_t'443, tint) :: (_t'442, tuchar) ::
               (_t'441, tint) :: (_t'440, tuint) :: (_t'439, tulong) ::
               (_t'438, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'437, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'436, tint) :: (_t'435, tuint) :: (_t'434, tuint) ::
               (_t'433, tuint) :: (_t'432, tuchar) :: (_t'431, tint) ::
               (_t'430, tint) ::
               (_t'429, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'428, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'427, tint) :: (_t'426, tint) :: (_t'425, tulong) ::
               (_t'424, tuchar) ::
               (_t'423, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'422, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'421, tint) :: (_t'420, tint) :: (_t'419, tulong) ::
               (_t'418, tuchar) ::
               (_t'417, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'416, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'415, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'414, tint) :: (_t'413, tint) :: (_t'412, tulong) ::
               (_t'411, tuchar) ::
               (_t'410, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'409, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'408, tint) :: (_t'407, tint) :: (_t'406, tulong) ::
               (_t'405, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'404, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'403, tint) :: (_t'402, (tptr tuchar)) ::
               (_t'401, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'400, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'399, tuint) :: (_t'398, tuint) ::
               (_t'397, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'396, tuint) ::
               (_t'395, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'394, tuint) ::
               (_t'393, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'392, tuint) ::
               (_t'391, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'390, (tptr tuchar)) ::
               (_t'389, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'388, tint) :: (_t'387, tint) :: (_t'386, tulong) ::
               (_t'385, tuint) :: (_t'384, tuint) :: (_t'383, tint) ::
               (_t'382, tuchar) :: (_t'381, (tptr tuchar)) ::
               (_t'380, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'379, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'378, tuint) ::
               (_t'377, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'376, tuint) :: (_t'375, (tptr tuchar)) ::
               (_t'374, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'373, tint) :: (_t'372, tint) :: (_t'371, tulong) ::
               (_t'370, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'369, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'368, tint) :: (_t'367, tuchar) ::
               (_t'366, (tptr tuchar)) ::
               (_t'365, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'364, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'363, tuint) ::
               (_t'362, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'361, tuint) :: (_t'360, (tptr tuchar)) ::
               (_t'359, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'358, tint) :: (_t'357, tint) :: (_t'356, tulong) ::
               (_t'355, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'354, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'353, tint) :: (_t'352, tuchar) :: (_t'351, tulong) ::
               (_t'350, tint) :: (_t'349, tint) :: (_t'348, tint) ::
               (_t'347, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'346, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'345, (tptr (Tstruct _gz_header_s noattr))) ::
               (_t'344, tuchar) :: (_t'343, tuint) :: (_t'342, tulong) ::
               (_t'341, tint) :: (_t'340, tint) :: (_t'339, tuchar) ::
               (_t'338, tuchar) :: (_t'337, tuint) :: (_t'336, tuchar) ::
               (_t'335, tuint) :: (_t'334, tuint) :: (_t'333, tuint) ::
               (_t'332, tuint) :: (_t'331, tuchar) :: (_t'330, tushort) ::
               (_t'329, tuint) :: (_t'328, tushort) ::
               (_t'327, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'326, tuint) :: (_t'325, tuint) :: (_t'324, tuint) ::
               (_t'323, tuchar) :: (_t'322, tuint) ::
               (_t'321, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'320, tuchar) :: (_t'319, tuint) ::
               (_t'318, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'317, tushort) :: (_t'316, tuint) ::
               (_t'315, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'314, tuchar) :: (_t'313, tuchar) :: (_t'312, tuchar) ::
               (_t'311, tuchar) :: (_t'310, tushort) :: (_t'309, tuchar) ::
               (_t'308, tuchar) :: (_t'307, tuchar) :: (_t'306, tuchar) ::
               (_t'305, tuint) :: (_t'304, tuint) :: (_t'303, tuchar) ::
               (_t'302, tuchar) :: (_t'301, tuchar) :: (_t'300, tuchar) ::
               (_t'299, tuchar) :: (_t'298, tuchar) :: (_t'297, tuchar) ::
               (_t'296, tuchar) :: (_t'295, tushort) :: (_t'294, tushort) ::
               (_t'293, tuint) :: (_t'292, tuint) :: (_t'291, tuint) ::
               (_t'290, tushort) :: (_t'289, tint) :: (_t'288, tushort) ::
               (_t'287, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'286, tuint) ::
               (_t'285, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'284, tuint) :: (_t'283, tuint) :: (_t'282, tint) ::
               (_t'281, tuchar) :: (_t'280, tuint) ::
               (_t'279, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'278, tuchar) :: (_t'277, tuint) ::
               (_t'276, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'275, tushort) :: (_t'274, tuint) ::
               (_t'273, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'272, tuchar) :: (_t'271, tuchar) :: (_t'270, tuchar) ::
               (_t'269, tuchar) :: (_t'268, tuchar) :: (_t'267, tuchar) ::
               (_t'266, tushort) :: (_t'265, tuchar) :: (_t'264, tuchar) ::
               (_t'263, tuchar) :: (_t'262, tuchar) :: (_t'261, tushort) ::
               (_t'260, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'259, tuchar) :: (_t'258, tuchar) :: (_t'257, tuchar) ::
               (_t'256, tuchar) :: (_t'255, tushort) ::
               (_t'254, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'253, tushort) :: (_t'252, tuchar) :: (_t'251, tuchar) ::
               (_t'250, tuchar) :: (_t'249, tushort) ::
               (_t'248, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'247, tuchar) :: (_t'246, tuchar) :: (_t'245, tuchar) ::
               (_t'244, tuchar) :: (_t'243, tuchar) :: (_t'242, tuchar) ::
               (_t'241, tint) :: (_t'240, tuchar) :: (_t'239, tuchar) ::
               (_t'238, tuchar) :: (_t'237, tint) :: (_t'236, tushort) ::
               (_t'235, tuchar) :: (_t'234, tuchar) :: (_t'233, tuchar) ::
               (_t'232, tuchar) :: (_t'231, tuint) :: (_t'230, tuchar) ::
               (_t'229, tuint) :: (_t'228, tuint) :: (_t'227, tuint) ::
               (_t'226, tuint) :: (_t'225, tuint) :: (_t'224, tint) ::
               (_t'223, tuint) :: (_t'222, tuint) :: (_t'221, tuchar) ::
               (_t'220, tuint) ::
               (_t'219, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'218, tuchar) :: (_t'217, tuint) ::
               (_t'216, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'215, tushort) :: (_t'214, tuint) ::
               (_t'213, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'212, tuchar) :: (_t'211, tuchar) :: (_t'210, tuchar) ::
               (_t'209, tuchar) :: (_t'208, tushort) :: (_t'207, tuchar) ::
               (_t'206, tuchar) :: (_t'205, tuchar) :: (_t'204, tuchar) ::
               (_t'203, tushort) ::
               (_t'202, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'201, tuchar) :: (_t'200, tuchar) :: (_t'199, tuchar) ::
               (_t'198, tuchar) :: (_t'197, tushort) ::
               (_t'196, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'195, tushort) :: (_t'194, tuchar) :: (_t'193, tuchar) ::
               (_t'192, tuchar) :: (_t'191, tushort) ::
               (_t'190, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'189, tuchar) :: (_t'188, tuchar) :: (_t'187, tuchar) ::
               (_t'186, tuchar) :: (_t'185, tuchar) :: (_t'184, tuchar) ::
               (_t'183, tint) :: (_t'182, tuchar) :: (_t'181, tuchar) ::
               (_t'180, tuchar) :: (_t'179, tuchar) :: (_t'178, tint) ::
               (_t'177, tuchar) :: (_t'176, tushort) :: (_t'175, tuchar) ::
               (_t'174, tuint) :: (_t'173, tuchar) :: (_t'172, tuint) ::
               (_t'171, tuint) :: (_t'170, tuint) :: (_t'169, tuint) ::
               (_t'168, tuint) :: (_t'167, tint) :: (_t'166, tuint) ::
               (_t'165, tuint) :: (_t'164, tint) :: (_t'163, tuint) ::
               (_t'162, tuint) :: (_t'161, tuint) ::
               (_t'160, (tptr tuchar)) :: (_t'159, tuint) ::
               (_t'158, (tptr tuchar)) :: (_t'157, tuint) ::
               (_t'156, tuint) :: (_t'155, tuint) :: (_t'154, tuint) ::
               (_t'153, tuint) :: (_t'152, tuchar) :: (_t'151, tuint) ::
               (_t'150, tuint) :: (_t'149, tuchar) :: (_t'148, tulong) ::
               (_t'147, tulong) :: (_t'146, tint) :: (_t'145, tulong) ::
               (_t'144, tulong) :: (_t'143, tint) :: (_t'142, tint) ::
               (_t'141, tulong) :: (_t'140, tint) :: (_t'139, tint) ::
               (_t'138, tint) :: (_t'137, tint) :: (_t'136, tuchar) ::
               (_t'135, tulong) :: (_t'134, tint) :: (_t'133, tint) ::
               (_t'132, tint) :: (_t'131, tuint) :: (_t'130, tint) ::
               (_t'129, tuint) :: (_t'128, tuint) ::
               (_t'127, (tptr tuchar)) :: (_t'126, tuint) ::
               (_t'125, tuint) :: (_t'124, tulong) :: (_t'123, tulong) ::
               (_t'122, tulong) :: (_t'121, tint) ::
               (_t'120, (tptr tuchar)) :: (_t'119, tulong) ::
               (_t'118, (tptr tuchar)) :: (_t'117, tulong) ::
               (_t'116, tint) :: (_t'115, tint) :: (_t'114, tint) ::
               (_t'113, tint) :: (_t'112, tint) :: (_t'111, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _leave (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _inflateStateCheck (Tfunction
                                       ((tptr (Tstruct _z_stream_s noattr)) ::
                                        nil) tint cc_default))
            ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
          (Sifthenelse (Etempvar _t'1 tint)
            (Sset _t'2 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'448
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _next_out (tptr tuchar)))
              (Sset _t'2
                (Ecast
                  (Ebinop Oeq (Etempvar _t'448 (tptr tuchar))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                  tbool)))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sset _t'3 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'446
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'446 (tptr tuchar))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'447
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _avail_in tuint))
                  (Sset _t'3
                    (Ecast
                      (Ebinop One (Etempvar _t'447 tuint)
                        (Econst_int (Int.repr 0) tint) tint) tbool)))
                (Sset _t'3 (Ecast (Etempvar _t'3 tint) tbool)))
              (Sset _t'3 (Ecast (Econst_int (Int.repr 0) tint) tbool))))))
      (Sifthenelse (Etempvar _t'3 tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'445
          (Efield
            (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
              (Tstruct _z_stream_s noattr)) _state
            (tptr (Tstruct _internal_state noattr))))
        (Sset _state
          (Ecast (Etempvar _t'445 (tptr (Tstruct _internal_state noattr)))
            (tptr (Tstruct _inflate_state noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'444
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _mode tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'444 tint)
                         (Econst_int (Int.repr 16191) tint) tint)
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _mode tint)
              (Econst_int (Int.repr 16192) tint))
            Sskip))
        (Ssequence
          (Sloop
            (Ssequence
              (Sset _put
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _next_out (tptr tuchar)))
              (Ssequence
                (Sset _left
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _avail_out tuint))
                (Ssequence
                  (Sset _next
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar)))
                  (Ssequence
                    (Sset _have
                      (Efield
                        (Ederef
                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                          (Tstruct _z_stream_s noattr)) _avail_in tuint))
                    (Ssequence
                      (Sset _hold
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _hold tulong))
                      (Sset _bits
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _bits tuint)))))))
            Sbreak)
          (Ssequence
            (Sset _in (Etempvar _have tuint))
            (Ssequence
              (Sset _out (Etempvar _left tuint))
              (Ssequence
                (Sset _ret (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sloop
                    (Ssequence
                      Sskip
                      (Ssequence
                        (Ssequence
                          (Sset _t'133
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _mode tint))
                          (Sswitch (Etempvar _t'133 tint)
                            (LScons (Some 16180)
                              (Ssequence
                                (Ssequence
                                  (Sset _t'443
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _wrap tint))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _t'443 tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _mode tint)
                                        (Econst_int (Int.repr 16192) tint))
                                      Sbreak)
                                    Sskip))
                                (Ssequence
                                  (Swhile
                                    (Ebinop Olt (Etempvar _bits tuint)
                                      (Ecast (Econst_int (Int.repr 16) tint)
                                        tuint) tint)
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _have tuint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Ssequence
                                          (Sset _leave
                                            (Econst_int (Int.repr 1) tint))
                                          Sbreak)
                                        Sskip)
                                      (Ssequence
                                        (Sset _have
                                          (Ebinop Osub (Etempvar _have tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'4
                                                (Etempvar _next (tptr tuchar)))
                                              (Sset _next
                                                (Ebinop Oadd
                                                  (Etempvar _t'4 (tptr tuchar))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuchar))))
                                            (Ssequence
                                              (Sset _t'442
                                                (Ederef
                                                  (Etempvar _t'4 (tptr tuchar))
                                                  tuchar))
                                              (Sset _hold
                                                (Ebinop Oadd
                                                  (Etempvar _hold tulong)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _t'442 tuchar)
                                                      tulong)
                                                    (Etempvar _bits tuint)
                                                    tulong) tulong))))
                                          (Sset _bits
                                            (Ebinop Oadd
                                              (Etempvar _bits tuint)
                                              (Econst_int (Int.repr 8) tint)
                                              tuint))))))
                                  (Ssequence
                                    (Sifthenelse (Etempvar _leave tint)
                                      Sbreak
                                      Sskip)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'441
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _wrap tint))
                                          (Sifthenelse (Ebinop Oand
                                                         (Etempvar _t'441 tint)
                                                         (Econst_int (Int.repr 2) tint)
                                                         tint)
                                            (Sset _t'7
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _hold tulong)
                                                  (Econst_int (Int.repr 35615) tint)
                                                  tint) tbool))
                                            (Sset _t'7
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'7 tint)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'440
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _wbits tuint))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _t'440 tuint)
                                                             (Econst_int (Int.repr 0) tint)
                                                             tint)
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _wbits tuint)
                                                  (Econst_int (Int.repr 15) tint))
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'5)
                                                  (Evar _crc32 (Tfunction
                                                                 (tulong ::
                                                                  (tptr tuchar) ::
                                                                  tuint ::
                                                                  nil) tulong
                                                                 cc_default))
                                                  ((Econst_long (Int64.repr 0) tlong) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   (Econst_int (Int.repr 0) tint) ::
                                                   nil))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _check tulong)
                                                  (Etempvar _t'5 tulong)))
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _hbuf (tarray tuchar 4))
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Etempvar _hold tulong)
                                                        tuchar))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _hbuf (tarray tuchar 4))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Ecast
                                                          (Ebinop Oshr
                                                            (Etempvar _hold tulong)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tulong) tuchar))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'439
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong))
                                                          (Scall (Some _t'6)
                                                            (Evar _crc32 
                                                            (Tfunction
                                                              (tulong ::
                                                               (tptr tuchar) ::
                                                               tuint :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Etempvar _t'439 tulong) ::
                                                             (Evar _hbuf (tarray tuchar 4)) ::
                                                             (Econst_int (Int.repr 2) tint) ::
                                                             nil)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _check tulong)
                                                          (Etempvar _t'6 tulong)))))
                                                  Sbreak)
                                                (Ssequence
                                                  (Sloop
                                                    (Ssequence
                                                      (Sset _hold
                                                        (Ecast
                                                          (Econst_int (Int.repr 0) tint)
                                                          tulong))
                                                      (Sset _bits
                                                        (Econst_int (Int.repr 0) tint)))
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _mode tint)
                                                      (Econst_int (Int.repr 16181) tint))
                                                    Sbreak)))))
                                          Sskip))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'437
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _head
                                              (tptr (Tstruct _gz_header_s noattr))))
                                          (Sifthenelse (Ebinop One
                                                         (Etempvar _t'437 (tptr (Tstruct _gz_header_s noattr)))
                                                         (Ecast
                                                           (Econst_int (Int.repr 0) tint)
                                                           (tptr tvoid))
                                                         tint)
                                            (Ssequence
                                              (Sset _t'438
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _head
                                                  (tptr (Tstruct _gz_header_s noattr))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'438 (tptr (Tstruct _gz_header_s noattr)))
                                                    (Tstruct _gz_header_s noattr))
                                                  _done tint)
                                                (Eunop Oneg
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint)))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'436
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _wrap tint))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Ebinop Oand
                                                               (Etempvar _t'436 tint)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tint) tint)
                                                (Sset _t'8
                                                  (Econst_int (Int.repr 1) tint))
                                                (Sset _t'8
                                                  (Ecast
                                                    (Ebinop Omod
                                                      (Ebinop Oadd
                                                        (Ebinop Oshl
                                                          (Ebinop Oand
                                                            (Ecast
                                                              (Etempvar _hold tulong)
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Ebinop Oshl
                                                                (Econst_int (Int.repr 1) tuint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tuint) tuint)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tuint)
                                                        (Ebinop Oshr
                                                          (Etempvar _hold tulong)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tulong) tulong)
                                                      (Econst_int (Int.repr 31) tint)
                                                      tulong) tbool))))
                                            (Sifthenelse (Etempvar _t'8 tint)
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                      (Tstruct _z_stream_s noattr))
                                                    _msg (tptr tschar))
                                                  (Ecast
                                                    (Evar ___stringlit_inflate_18 (tarray tschar 23))
                                                    (tptr tschar)))
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _mode tint)
                                                    (Econst_int (Int.repr 16209) tint))
                                                  Sbreak))
                                              Sskip))
                                          (Ssequence
                                            (Sifthenelse (Ebinop One
                                                           (Ebinop Oand
                                                             (Ecast
                                                               (Etempvar _hold tulong)
                                                               tuint)
                                                             (Ebinop Osub
                                                               (Ebinop Oshl
                                                                 (Econst_int (Int.repr 1) tuint)
                                                                 (Econst_int (Int.repr 4) tint)
                                                                 tuint)
                                                               (Econst_int (Int.repr 1) tint)
                                                               tuint) tuint)
                                                           (Econst_int (Int.repr 8) tint)
                                                           tint)
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                      (Tstruct _z_stream_s noattr))
                                                    _msg (tptr tschar))
                                                  (Ecast
                                                    (Evar ___stringlit_inflate_16 (tarray tschar 27))
                                                    (tptr tschar)))
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _mode tint)
                                                    (Econst_int (Int.repr 16209) tint))
                                                  Sbreak))
                                              Sskip)
                                            (Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Sset _hold
                                                    (Ebinop Oshr
                                                      (Etempvar _hold tulong)
                                                      (Econst_int (Int.repr 4) tint)
                                                      tulong))
                                                  (Sset _bits
                                                    (Ebinop Osub
                                                      (Etempvar _bits tuint)
                                                      (Ecast
                                                        (Econst_int (Int.repr 4) tint)
                                                        tuint) tuint)))
                                                Sbreak)
                                              (Ssequence
                                                (Sset _len
                                                  (Ebinop Oadd
                                                    (Ebinop Oand
                                                      (Ecast
                                                        (Etempvar _hold tulong)
                                                        tuint)
                                                      (Ebinop Osub
                                                        (Ebinop Oshl
                                                          (Econst_int (Int.repr 1) tuint)
                                                          (Econst_int (Int.repr 4) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tuint) tuint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tuint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Ogt
                                                                   (Etempvar _len tuint)
                                                                   (Econst_int (Int.repr 15) tint)
                                                                   tint)
                                                      (Sset _t'9
                                                        (Econst_int (Int.repr 1) tint))
                                                      (Ssequence
                                                        (Sset _t'434
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _wbits tuint))
                                                        (Sifthenelse 
                                                          (Ebinop One
                                                            (Etempvar _t'434 tuint)
                                                            (Econst_int (Int.repr 0) tint)
                                                            tint)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'435
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _wbits
                                                                  tuint))
                                                              (Sset _t'9
                                                                (Ecast
                                                                  (Ebinop Ogt
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _t'435 tuint)
                                                                    tint)
                                                                  tbool)))
                                                            (Sset _t'9
                                                              (Ecast
                                                                (Etempvar _t'9 tint)
                                                                tbool)))
                                                          (Sset _t'9
                                                            (Ecast
                                                              (Econst_int (Int.repr 0) tint)
                                                              tbool)))))
                                                    (Sifthenelse (Etempvar _t'9 tint)
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                              (Tstruct _z_stream_s noattr))
                                                            _msg
                                                            (tptr tschar))
                                                          (Ecast
                                                            (Evar ___stringlit_inflate_19 (tarray tschar 20))
                                                            (tptr tschar)))
                                                        (Ssequence
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _mode tint)
                                                            (Econst_int (Int.repr 16209) tint))
                                                          Sbreak))
                                                      Sskip))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'433
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _wbits tuint))
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _t'433 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _wbits tuint)
                                                          (Etempvar _len tuint))
                                                        Sskip))
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _dmax tuint)
                                                        (Ebinop Oshl
                                                          (Econst_int (Int.repr 1) tuint)
                                                          (Etempvar _len tuint)
                                                          tuint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _flags tint)
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'10)
                                                                  (Evar _adler32 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Econst_long (Int64.repr 0) tlong) ::
                                                                   (Econst_int (Int.repr 0) tint) ::
                                                                   (Econst_int (Int.repr 0) tint) ::
                                                                   nil))
                                                                (Sset _t'11
                                                                  (Ecast
                                                                    (Etempvar _t'10 tulong)
                                                                    tulong)))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _check
                                                                  tulong)
                                                                (Etempvar _t'11 tulong)))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                  (Tstruct _z_stream_s noattr))
                                                                _adler
                                                                tulong)
                                                              (Etempvar _t'11 tulong)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Oand
                                                                  (Etempvar _hold tulong)
                                                                  (Econst_int (Int.repr 512) tint)
                                                                  tulong)
                                                                (Sset _t'12
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 16189) tint)
                                                                    tint))
                                                                (Sset _t'12
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 16191) tint)
                                                                    tint)))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _mode tint)
                                                                (Etempvar _t'12 tint)))
                                                            (Ssequence
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sset _hold
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                  (Sset _bits
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                Sbreak)
                                                              Sbreak))))))))))))))))
                              (LScons (Some 16181)
                                (Ssequence
                                  (Swhile
                                    (Ebinop Olt (Etempvar _bits tuint)
                                      (Ecast (Econst_int (Int.repr 16) tint)
                                        tuint) tint)
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _have tuint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Ssequence
                                          (Sset _leave
                                            (Econst_int (Int.repr 1) tint))
                                          Sbreak)
                                        Sskip)
                                      (Ssequence
                                        (Sset _have
                                          (Ebinop Osub (Etempvar _have tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'13
                                                (Etempvar _next (tptr tuchar)))
                                              (Sset _next
                                                (Ebinop Oadd
                                                  (Etempvar _t'13 (tptr tuchar))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuchar))))
                                            (Ssequence
                                              (Sset _t'432
                                                (Ederef
                                                  (Etempvar _t'13 (tptr tuchar))
                                                  tuchar))
                                              (Sset _hold
                                                (Ebinop Oadd
                                                  (Etempvar _hold tulong)
                                                  (Ebinop Oshl
                                                    (Ecast
                                                      (Etempvar _t'432 tuchar)
                                                      tulong)
                                                    (Etempvar _bits tuint)
                                                    tulong) tulong))))
                                          (Sset _bits
                                            (Ebinop Oadd
                                              (Etempvar _bits tuint)
                                              (Econst_int (Int.repr 8) tint)
                                              tuint))))))
                                  (Ssequence
                                    (Sifthenelse (Etempvar _leave tint)
                                      Sbreak
                                      Sskip)
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _flags tint)
                                        (Ecast (Etempvar _hold tulong) tint))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'431
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _flags tint))
                                          (Sifthenelse (Ebinop One
                                                         (Ebinop Oand
                                                           (Etempvar _t'431 tint)
                                                           (Econst_int (Int.repr 255) tint)
                                                           tint)
                                                         (Econst_int (Int.repr 8) tint)
                                                         tint)
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                    (Tstruct _z_stream_s noattr))
                                                  _msg (tptr tschar))
                                                (Ecast
                                                  (Evar ___stringlit_inflate_16 (tarray tschar 27))
                                                  (tptr tschar)))
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _mode tint)
                                                  (Econst_int (Int.repr 16209) tint))
                                                Sbreak))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'430
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _flags tint))
                                            (Sifthenelse (Ebinop Oand
                                                           (Etempvar _t'430 tint)
                                                           (Econst_int (Int.repr 57344) tint)
                                                           tint)
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                      (Tstruct _z_stream_s noattr))
                                                    _msg (tptr tschar))
                                                  (Ecast
                                                    (Evar ___stringlit_inflate_17 (tarray tschar 25))
                                                    (tptr tschar)))
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _mode tint)
                                                    (Econst_int (Int.repr 16209) tint))
                                                  Sbreak))
                                              Sskip))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'428
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _head
                                                  (tptr (Tstruct _gz_header_s noattr))))
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _t'428 (tptr (Tstruct _gz_header_s noattr)))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Ssequence
                                                  (Sset _t'429
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _head
                                                      (tptr (Tstruct _gz_header_s noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'429 (tptr (Tstruct _gz_header_s noattr)))
                                                        (Tstruct _gz_header_s noattr))
                                                      _text tint)
                                                    (Ecast
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _hold tulong)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tulong)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tulong) tint)))
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'426
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _flags tint))
                                                  (Sifthenelse (Ebinop Oand
                                                                 (Etempvar _t'426 tint)
                                                                 (Econst_int (Int.repr 512) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _t'427
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _wrap tint))
                                                      (Sset _t'15
                                                        (Ecast
                                                          (Ebinop Oand
                                                            (Etempvar _t'427 tint)
                                                            (Econst_int (Int.repr 4) tint)
                                                            tint) tbool)))
                                                    (Sset _t'15
                                                      (Econst_int (Int.repr 0) tint))))
                                                (Sifthenelse (Etempvar _t'15 tint)
                                                  (Sloop
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _hbuf (tarray tuchar 4))
                                                            (Econst_int (Int.repr 0) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Ecast
                                                          (Etempvar _hold tulong)
                                                          tuchar))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _hbuf (tarray tuchar 4))
                                                              (Econst_int (Int.repr 1) tint)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ebinop Oshr
                                                              (Etempvar _hold tulong)
                                                              (Econst_int (Int.repr 8) tint)
                                                              tulong) tuchar))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'425
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _check
                                                                tulong))
                                                            (Scall (Some _t'14)
                                                              (Evar _crc32 
                                                              (Tfunction
                                                                (tulong ::
                                                                 (tptr tuchar) ::
                                                                 tuint ::
                                                                 nil) tulong
                                                                cc_default))
                                                              ((Etempvar _t'425 tulong) ::
                                                               (Evar _hbuf (tarray tuchar 4)) ::
                                                               (Econst_int (Int.repr 2) tint) ::
                                                               nil)))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong)
                                                            (Etempvar _t'14 tulong)))))
                                                    Sbreak)
                                                  Sskip))
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Sset _hold
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        tulong))
                                                    (Sset _bits
                                                      (Econst_int (Int.repr 0) tint)))
                                                  Sbreak)
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _mode tint)
                                                  (Econst_int (Int.repr 16182) tint))))))))))
                                (LScons (Some 16182)
                                  (Ssequence
                                    (Swhile
                                      (Ebinop Olt (Etempvar _bits tuint)
                                        (Ecast
                                          (Econst_int (Int.repr 32) tint)
                                          tuint) tint)
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _have tuint)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _leave
                                              (Econst_int (Int.repr 1) tint))
                                            Sbreak)
                                          Sskip)
                                        (Ssequence
                                          (Sset _have
                                            (Ebinop Osub
                                              (Etempvar _have tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'16
                                                  (Etempvar _next (tptr tuchar)))
                                                (Sset _next
                                                  (Ebinop Oadd
                                                    (Etempvar _t'16 (tptr tuchar))
                                                    (Econst_int (Int.repr 1) tint)
                                                    (tptr tuchar))))
                                              (Ssequence
                                                (Sset _t'424
                                                  (Ederef
                                                    (Etempvar _t'16 (tptr tuchar))
                                                    tuchar))
                                                (Sset _hold
                                                  (Ebinop Oadd
                                                    (Etempvar _hold tulong)
                                                    (Ebinop Oshl
                                                      (Ecast
                                                        (Etempvar _t'424 tuchar)
                                                        tulong)
                                                      (Etempvar _bits tuint)
                                                      tulong) tulong))))
                                            (Sset _bits
                                              (Ebinop Oadd
                                                (Etempvar _bits tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint))))))
                                    (Ssequence
                                      (Sifthenelse (Etempvar _leave tint)
                                        Sbreak
                                        Sskip)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'422
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _head
                                              (tptr (Tstruct _gz_header_s noattr))))
                                          (Sifthenelse (Ebinop One
                                                         (Etempvar _t'422 (tptr (Tstruct _gz_header_s noattr)))
                                                         (Ecast
                                                           (Econst_int (Int.repr 0) tint)
                                                           (tptr tvoid))
                                                         tint)
                                            (Ssequence
                                              (Sset _t'423
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _head
                                                  (tptr (Tstruct _gz_header_s noattr))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _t'423 (tptr (Tstruct _gz_header_s noattr)))
                                                    (Tstruct _gz_header_s noattr))
                                                  _time tulong)
                                                (Etempvar _hold tulong)))
                                            Sskip))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'420
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _flags tint))
                                              (Sifthenelse (Ebinop Oand
                                                             (Etempvar _t'420 tint)
                                                             (Econst_int (Int.repr 512) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sset _t'421
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _wrap tint))
                                                  (Sset _t'18
                                                    (Ecast
                                                      (Ebinop Oand
                                                        (Etempvar _t'421 tint)
                                                        (Econst_int (Int.repr 4) tint)
                                                        tint) tbool)))
                                                (Sset _t'18
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Sifthenelse (Etempvar _t'18 tint)
                                              (Sloop
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _hbuf (tarray tuchar 4))
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Ecast
                                                      (Etempvar _hold tulong)
                                                      tuchar))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _hbuf (tarray tuchar 4))
                                                          (Econst_int (Int.repr 1) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Ebinop Oshr
                                                          (Etempvar _hold tulong)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tulong) tuchar))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _hbuf (tarray tuchar 4))
                                                            (Econst_int (Int.repr 2) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Ecast
                                                          (Ebinop Oshr
                                                            (Etempvar _hold tulong)
                                                            (Econst_int (Int.repr 16) tint)
                                                            tulong) tuchar))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _hbuf (tarray tuchar 4))
                                                              (Econst_int (Int.repr 3) tint)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Ecast
                                                            (Ebinop Oshr
                                                              (Etempvar _hold tulong)
                                                              (Econst_int (Int.repr 24) tint)
                                                              tulong) tuchar))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'419
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _check
                                                                tulong))
                                                            (Scall (Some _t'17)
                                                              (Evar _crc32 
                                                              (Tfunction
                                                                (tulong ::
                                                                 (tptr tuchar) ::
                                                                 tuint ::
                                                                 nil) tulong
                                                                cc_default))
                                                              ((Etempvar _t'419 tulong) ::
                                                               (Evar _hbuf (tarray tuchar 4)) ::
                                                               (Econst_int (Int.repr 4) tint) ::
                                                               nil)))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong)
                                                            (Etempvar _t'17 tulong)))))))
                                                Sbreak)
                                              Sskip))
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Sset _hold
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tulong))
                                                (Sset _bits
                                                  (Econst_int (Int.repr 0) tint)))
                                              Sbreak)
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _mode tint)
                                              (Econst_int (Int.repr 16183) tint)))))))
                                  (LScons (Some 16183)
                                    (Ssequence
                                      (Swhile
                                        (Ebinop Olt (Etempvar _bits tuint)
                                          (Ecast
                                            (Econst_int (Int.repr 16) tint)
                                            tuint) tint)
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _have tuint)
                                                         (Econst_int (Int.repr 0) tint)
                                                         tint)
                                            (Ssequence
                                              (Sset _leave
                                                (Econst_int (Int.repr 1) tint))
                                              Sbreak)
                                            Sskip)
                                          (Ssequence
                                            (Sset _have
                                              (Ebinop Osub
                                                (Etempvar _have tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'19
                                                    (Etempvar _next (tptr tuchar)))
                                                  (Sset _next
                                                    (Ebinop Oadd
                                                      (Etempvar _t'19 (tptr tuchar))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tuchar))))
                                                (Ssequence
                                                  (Sset _t'418
                                                    (Ederef
                                                      (Etempvar _t'19 (tptr tuchar))
                                                      tuchar))
                                                  (Sset _hold
                                                    (Ebinop Oadd
                                                      (Etempvar _hold tulong)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _t'418 tuchar)
                                                          tulong)
                                                        (Etempvar _bits tuint)
                                                        tulong) tulong))))
                                              (Sset _bits
                                                (Ebinop Oadd
                                                  (Etempvar _bits tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint))))))
                                      (Ssequence
                                        (Sifthenelse (Etempvar _leave tint)
                                          Sbreak
                                          Sskip)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'415
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _head
                                                (tptr (Tstruct _gz_header_s noattr))))
                                            (Sifthenelse (Ebinop One
                                                           (Etempvar _t'415 (tptr (Tstruct _gz_header_s noattr)))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'417
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _head
                                                      (tptr (Tstruct _gz_header_s noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'417 (tptr (Tstruct _gz_header_s noattr)))
                                                        (Tstruct _gz_header_s noattr))
                                                      _xflags tint)
                                                    (Ecast
                                                      (Ebinop Oand
                                                        (Etempvar _hold tulong)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tulong) tint)))
                                                (Ssequence
                                                  (Sset _t'416
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _head
                                                      (tptr (Tstruct _gz_header_s noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'416 (tptr (Tstruct _gz_header_s noattr)))
                                                        (Tstruct _gz_header_s noattr))
                                                      _os tint)
                                                    (Ecast
                                                      (Ebinop Oshr
                                                        (Etempvar _hold tulong)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tulong) tint))))
                                              Sskip))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'413
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _flags tint))
                                                (Sifthenelse (Ebinop Oand
                                                               (Etempvar _t'413 tint)
                                                               (Econst_int (Int.repr 512) tint)
                                                               tint)
                                                  (Ssequence
                                                    (Sset _t'414
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _wrap tint))
                                                    (Sset _t'21
                                                      (Ecast
                                                        (Ebinop Oand
                                                          (Etempvar _t'414 tint)
                                                          (Econst_int (Int.repr 4) tint)
                                                          tint) tbool)))
                                                  (Sset _t'21
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Sifthenelse (Etempvar _t'21 tint)
                                                (Sloop
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _hbuf (tarray tuchar 4))
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Ecast
                                                        (Etempvar _hold tulong)
                                                        tuchar))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _hbuf (tarray tuchar 4))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Ecast
                                                          (Ebinop Oshr
                                                            (Etempvar _hold tulong)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tulong) tuchar))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'412
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong))
                                                          (Scall (Some _t'20)
                                                            (Evar _crc32 
                                                            (Tfunction
                                                              (tulong ::
                                                               (tptr tuchar) ::
                                                               tuint :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Etempvar _t'412 tulong) ::
                                                             (Evar _hbuf (tarray tuchar 4)) ::
                                                             (Econst_int (Int.repr 2) tint) ::
                                                             nil)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _check tulong)
                                                          (Etempvar _t'20 tulong)))))
                                                  Sbreak)
                                                Sskip))
                                            (Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Sset _hold
                                                    (Ecast
                                                      (Econst_int (Int.repr 0) tint)
                                                      tulong))
                                                  (Sset _bits
                                                    (Econst_int (Int.repr 0) tint)))
                                                Sbreak)
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _mode tint)
                                                (Econst_int (Int.repr 16184) tint)))))))
                                    (LScons (Some 16184)
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'403
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _flags tint))
                                          (Sifthenelse (Ebinop Oand
                                                         (Etempvar _t'403 tint)
                                                         (Econst_int (Int.repr 1024) tint)
                                                         tint)
                                            (Ssequence
                                              (Ssequence
                                                (Swhile
                                                  (Ebinop Olt
                                                    (Etempvar _bits tuint)
                                                    (Ecast
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint) tint)
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _have tuint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _leave
                                                          (Econst_int (Int.repr 1) tint))
                                                        Sbreak)
                                                      Sskip)
                                                    (Ssequence
                                                      (Sset _have
                                                        (Ebinop Osub
                                                          (Etempvar _have tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'22
                                                              (Etempvar _next (tptr tuchar)))
                                                            (Sset _next
                                                              (Ebinop Oadd
                                                                (Etempvar _t'22 (tptr tuchar))
                                                                (Econst_int (Int.repr 1) tint)
                                                                (tptr tuchar))))
                                                          (Ssequence
                                                            (Sset _t'411
                                                              (Ederef
                                                                (Etempvar _t'22 (tptr tuchar))
                                                                tuchar))
                                                            (Sset _hold
                                                              (Ebinop Oadd
                                                                (Etempvar _hold tulong)
                                                                (Ebinop Oshl
                                                                  (Ecast
                                                                    (Etempvar _t'411 tuchar)
                                                                    tulong)
                                                                  (Etempvar _bits tuint)
                                                                  tulong)
                                                                tulong))))
                                                        (Sset _bits
                                                          (Ebinop Oadd
                                                            (Etempvar _bits tuint)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tuint))))))
                                                (Sifthenelse (Etempvar _leave tint)
                                                  Sbreak
                                                  Sskip))
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _length tuint)
                                                  (Ecast
                                                    (Etempvar _hold tulong)
                                                    tuint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'409
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _head
                                                        (tptr (Tstruct _gz_header_s noattr))))
                                                    (Sifthenelse (Ebinop One
                                                                   (Etempvar _t'409 (tptr (Tstruct _gz_header_s noattr)))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _t'410
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _head
                                                            (tptr (Tstruct _gz_header_s noattr))))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _t'410 (tptr (Tstruct _gz_header_s noattr)))
                                                              (Tstruct _gz_header_s noattr))
                                                            _extra_len tuint)
                                                          (Ecast
                                                            (Etempvar _hold tulong)
                                                            tuint)))
                                                      Sskip))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'407
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _flags tint))
                                                        (Sifthenelse 
                                                          (Ebinop Oand
                                                            (Etempvar _t'407 tint)
                                                            (Econst_int (Int.repr 512) tint)
                                                            tint)
                                                          (Ssequence
                                                            (Sset _t'408
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _wrap tint))
                                                            (Sset _t'24
                                                              (Ecast
                                                                (Ebinop Oand
                                                                  (Etempvar _t'408 tint)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tint)
                                                                tbool)))
                                                          (Sset _t'24
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Etempvar _t'24 tint)
                                                        (Sloop
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _hbuf (tarray tuchar 4))
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              (Ecast
                                                                (Etempvar _hold tulong)
                                                                tuchar))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _hbuf (tarray tuchar 4))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))
                                                                  tuchar)
                                                                (Ecast
                                                                  (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                  tuchar))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'406
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                  (Scall (Some _t'23)
                                                                    (Evar _crc32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'406 tulong) ::
                                                                    (Evar _hbuf (tarray tuchar 4)) ::
                                                                    (Econst_int (Int.repr 2) tint) ::
                                                                    nil)))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong)
                                                                  (Etempvar _t'23 tulong)))))
                                                          Sbreak)
                                                        Sskip))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sset _hold
                                                          (Ecast
                                                            (Econst_int (Int.repr 0) tint)
                                                            tulong))
                                                        (Sset _bits
                                                          (Econst_int (Int.repr 0) tint)))
                                                      Sbreak)))))
                                            (Ssequence
                                              (Sset _t'404
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _head
                                                  (tptr (Tstruct _gz_header_s noattr))))
                                              (Sifthenelse (Ebinop One
                                                             (Etempvar _t'404 (tptr (Tstruct _gz_header_s noattr)))
                                                             (Ecast
                                                               (Econst_int (Int.repr 0) tint)
                                                               (tptr tvoid))
                                                             tint)
                                                (Ssequence
                                                  (Sset _t'405
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _head
                                                      (tptr (Tstruct _gz_header_s noattr))))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'405 (tptr (Tstruct _gz_header_s noattr)))
                                                        (Tstruct _gz_header_s noattr))
                                                      _extra (tptr tuchar))
                                                    (Econst_int (Int.repr 0) tint)))
                                                Sskip))))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                              (Tstruct _inflate_state noattr))
                                            _mode tint)
                                          (Econst_int (Int.repr 16185) tint)))
                                      (LScons (Some 16185)
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'383
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _flags tint))
                                            (Sifthenelse (Ebinop Oand
                                                           (Etempvar _t'383 tint)
                                                           (Econst_int (Int.repr 1024) tint)
                                                           tint)
                                              (Ssequence
                                                (Sset _copy
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _length tuint))
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Ogt
                                                                 (Etempvar _copy tuint)
                                                                 (Etempvar _have tuint)
                                                                 tint)
                                                    (Sset _copy
                                                      (Etempvar _have tuint))
                                                    Sskip)
                                                  (Ssequence
                                                    (Sifthenelse (Etempvar _copy tuint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'400
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _head
                                                                  (tptr (Tstruct _gz_header_s noattr))))
                                                              (Sifthenelse 
                                                                (Ebinop One
                                                                  (Etempvar _t'400 (tptr (Tstruct _gz_header_s noattr)))
                                                                  (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'401
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                  (Ssequence
                                                                    (Sset _t'402
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'401 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra
                                                                    (tptr tuchar)))
                                                                    (Sset _t'26
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'402 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))))
                                                                (Sset _t'26
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'26 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'397
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'398
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'397 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_len
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'399
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'398 tuint)
                                                                    (Etempvar _t'399 tuint)
                                                                    tuint)
                                                                    tuint)))))
                                                                  (Sset _len
                                                                    (Etempvar _t'28 tuint)))
                                                                (Ssequence
                                                                  (Sset _t'395
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                  (Ssequence
                                                                    (Sset _t'396
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'395 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_max
                                                                    tuint))
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'28 tuint)
                                                                    (Etempvar _t'396 tuint)
                                                                    tint)
                                                                    tbool)))))
                                                              (Sset _t'27
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'27 tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'391
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                (Ssequence
                                                                  (Sset _t'392
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'391 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_max
                                                                    tuint))
                                                                  (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _len tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)
                                                                    (Etempvar _t'392 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'393
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'394
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'393 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra_max
                                                                    tuint))
                                                                    (Sset _t'25
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'394 tuint)
                                                                    (Etempvar _len tuint)
                                                                    tuint)
                                                                    tuint))))
                                                                    (Sset _t'25
                                                                    (Ecast
                                                                    (Etempvar _copy tuint)
                                                                    tuint)))))
                                                              (Ssequence
                                                                (Sset _t'389
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                (Ssequence
                                                                  (Sset _t'390
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'389 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _extra
                                                                    (tptr tuchar)))
                                                                  (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Etempvar _t'390 (tptr tuchar))
                                                                    (Etempvar _len tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _next (tptr tuchar)) ::
                                                                    (Etempvar _t'25 tuint) ::
                                                                    nil)))))
                                                            Sskip))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'387
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _flags
                                                                  tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oand
                                                                  (Etempvar _t'387 tint)
                                                                  (Econst_int (Int.repr 512) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'388
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                  (Sset _t'30
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'388 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tbool)))
                                                                (Sset _t'30
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'30 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'386
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                  (Scall (Some _t'29)
                                                                    (Evar _crc32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'386 tulong) ::
                                                                    (Etempvar _next (tptr tuchar)) ::
                                                                    (Etempvar _copy tuint) ::
                                                                    nil)))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong)
                                                                  (Etempvar _t'29 tulong)))
                                                              Sskip))
                                                          (Ssequence
                                                            (Sset _have
                                                              (Ebinop Osub
                                                                (Etempvar _have tuint)
                                                                (Etempvar _copy tuint)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _next
                                                                (Ebinop Oadd
                                                                  (Etempvar _next (tptr tuchar))
                                                                  (Etempvar _copy tuint)
                                                                  (tptr tuchar)))
                                                              (Ssequence
                                                                (Sset _t'385
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                  (Ebinop Osub
                                                                    (Etempvar _t'385 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)))))))
                                                      Sskip)
                                                    (Ssequence
                                                      (Sset _t'384
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _length tuint))
                                                      (Sifthenelse (Etempvar _t'384 tuint)
                                                        (Ssequence
                                                          (Sset _leave
                                                            (Econst_int (Int.repr 1) tint))
                                                          Sbreak)
                                                        Sskip)))))
                                              Sskip))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _length tuint)
                                              (Econst_int (Int.repr 0) tint))
                                            (Sassign
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _mode tint)
                                              (Econst_int (Int.repr 16186) tint))))
                                        (LScons (Some 16186)
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'368
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _flags tint))
                                              (Sifthenelse (Ebinop Oand
                                                             (Etempvar _t'368 tint)
                                                             (Econst_int (Int.repr 2048) tint)
                                                             tint)
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _have tuint)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _leave
                                                        (Econst_int (Int.repr 1) tint))
                                                      Sbreak)
                                                    Sskip)
                                                  (Ssequence
                                                    (Sset _copy
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Ssequence
                                                      (Sloop
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'32
                                                                (Etempvar _copy tuint))
                                                              (Sset _copy
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'32 tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)))
                                                            (Ssequence
                                                              (Sset _t'382
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Etempvar _next (tptr tuchar))
                                                                    (Etempvar _t'32 tuint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _len
                                                                (Ecast
                                                                  (Etempvar _t'382 tuchar)
                                                                  tuint))))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'379
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                (Sifthenelse 
                                                                  (Ebinop One
                                                                    (Etempvar _t'379 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _t'380
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'381
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'380 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _name
                                                                    (tptr tuchar)))
                                                                    (Sset _t'34
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'381 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))))
                                                                  (Sset _t'34
                                                                    (Econst_int (Int.repr 0) tint))))
                                                              (Sifthenelse (Etempvar _t'34 tint)
                                                                (Ssequence
                                                                  (Sset _t'376
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _t'377
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'378
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'377 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _name_max
                                                                    tuint))
                                                                    (Sset _t'35
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'376 tuint)
                                                                    (Etempvar _t'378 tuint)
                                                                    tint)
                                                                    tbool)))))
                                                                (Sset _t'35
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'35 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'33
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'33 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _t'374
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                  (Ssequence
                                                                    (Sset _t'375
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'374 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _name
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'375 (tptr tuchar))
                                                                    (Etempvar _t'33 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _len tuint)
                                                                    tuchar)))))
                                                              Sskip)))
                                                        (Ssequence
                                                          (Sifthenelse (Etempvar _len tuint)
                                                            (Sset _t'31
                                                              (Ecast
                                                                (Ebinop Olt
                                                                  (Etempvar _copy tuint)
                                                                  (Etempvar _have tuint)
                                                                  tint)
                                                                tbool))
                                                            (Sset _t'31
                                                              (Econst_int (Int.repr 0) tint)))
                                                          (Sifthenelse (Etempvar _t'31 tint)
                                                            Sskip
                                                            Sbreak)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'372
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _flags tint))
                                                            (Sifthenelse 
                                                              (Ebinop Oand
                                                                (Etempvar _t'372 tint)
                                                                (Econst_int (Int.repr 512) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'373
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                (Sset _t'37
                                                                  (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'373 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _t'37
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'37 tint)
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'371
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                (Scall (Some _t'36)
                                                                  (Evar _crc32 
                                                                  (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Etempvar _t'371 tulong) ::
                                                                   (Etempvar _next (tptr tuchar)) ::
                                                                   (Etempvar _copy tuint) ::
                                                                   nil)))
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _check
                                                                  tulong)
                                                                (Etempvar _t'36 tulong)))
                                                            Sskip))
                                                        (Ssequence
                                                          (Sset _have
                                                            (Ebinop Osub
                                                              (Etempvar _have tuint)
                                                              (Etempvar _copy tuint)
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _next
                                                              (Ebinop Oadd
                                                                (Etempvar _next (tptr tuchar))
                                                                (Etempvar _copy tuint)
                                                                (tptr tuchar)))
                                                            (Sifthenelse (Etempvar _len tuint)
                                                              (Ssequence
                                                                (Sset _leave
                                                                  (Econst_int (Int.repr 1) tint))
                                                                Sbreak)
                                                              Sskip)))))))
                                                (Ssequence
                                                  (Sset _t'369
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _head
                                                      (tptr (Tstruct _gz_header_s noattr))))
                                                  (Sifthenelse (Ebinop One
                                                                 (Etempvar _t'369 (tptr (Tstruct _gz_header_s noattr)))
                                                                 (Ecast
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   (tptr tvoid))
                                                                 tint)
                                                    (Ssequence
                                                      (Sset _t'370
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _head
                                                          (tptr (Tstruct _gz_header_s noattr))))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _t'370 (tptr (Tstruct _gz_header_s noattr)))
                                                            (Tstruct _gz_header_s noattr))
                                                          _name
                                                          (tptr tuchar))
                                                        (Econst_int (Int.repr 0) tint)))
                                                    Sskip))))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _length tuint)
                                                (Econst_int (Int.repr 0) tint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _mode tint)
                                                (Econst_int (Int.repr 16187) tint))))
                                          (LScons (Some 16187)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'353
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _flags tint))
                                                (Sifthenelse (Ebinop Oand
                                                               (Etempvar _t'353 tint)
                                                               (Econst_int (Int.repr 4096) tint)
                                                               tint)
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _have tuint)
                                                                   (Econst_int (Int.repr 0) tint)
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _leave
                                                          (Econst_int (Int.repr 1) tint))
                                                        Sbreak)
                                                      Sskip)
                                                    (Ssequence
                                                      (Sset _copy
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'39
                                                                  (Etempvar _copy tuint))
                                                                (Sset _copy
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'39 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                              (Ssequence
                                                                (Sset _t'367
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr tuchar))
                                                                    (Etempvar _t'39 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Sset _len
                                                                  (Ecast
                                                                    (Etempvar _t'367 tuchar)
                                                                    tuint))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'364
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                  (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'364 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'365
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'366
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'365 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _comment
                                                                    (tptr tuchar)))
                                                                    (Sset _t'41
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'366 (tptr tuchar))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'41
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                (Sifthenelse (Etempvar _t'41 tint)
                                                                  (Ssequence
                                                                    (Sset _t'361
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'362
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'363
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'362 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _comm_max
                                                                    tuint))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'361 tuint)
                                                                    (Etempvar _t'363 tuint)
                                                                    tint)
                                                                    tbool)))))
                                                                  (Sset _t'42
                                                                    (Econst_int (Int.repr 0) tint))))
                                                              (Sifthenelse (Etempvar _t'42 tint)
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'40 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                  (Ssequence
                                                                    (Sset _t'359
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _head
                                                                    (tptr (Tstruct _gz_header_s noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'360
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'359 (tptr (Tstruct _gz_header_s noattr)))
                                                                    (Tstruct _gz_header_s noattr))
                                                                    _comment
                                                                    (tptr tuchar)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'360 (tptr tuchar))
                                                                    (Etempvar _t'40 tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _len tuint)
                                                                    tuchar)))))
                                                                Sskip)))
                                                          (Ssequence
                                                            (Sifthenelse (Etempvar _len tuint)
                                                              (Sset _t'38
                                                                (Ecast
                                                                  (Ebinop Olt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _have tuint)
                                                                    tint)
                                                                  tbool))
                                                              (Sset _t'38
                                                                (Econst_int (Int.repr 0) tint)))
                                                            (Sifthenelse (Etempvar _t'38 tint)
                                                              Sskip
                                                              Sbreak)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'357
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _flags
                                                                  tint))
                                                              (Sifthenelse 
                                                                (Ebinop Oand
                                                                  (Etempvar _t'357 tint)
                                                                  (Econst_int (Int.repr 512) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _t'358
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                  (Sset _t'44
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'358 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    tbool)))
                                                                (Sset _t'44
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'44 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'356
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                  (Scall (Some _t'43)
                                                                    (Evar _crc32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'356 tulong) ::
                                                                    (Etempvar _next (tptr tuchar)) ::
                                                                    (Etempvar _copy tuint) ::
                                                                    nil)))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong)
                                                                  (Etempvar _t'43 tulong)))
                                                              Sskip))
                                                          (Ssequence
                                                            (Sset _have
                                                              (Ebinop Osub
                                                                (Etempvar _have tuint)
                                                                (Etempvar _copy tuint)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _next
                                                                (Ebinop Oadd
                                                                  (Etempvar _next (tptr tuchar))
                                                                  (Etempvar _copy tuint)
                                                                  (tptr tuchar)))
                                                              (Sifthenelse (Etempvar _len tuint)
                                                                (Ssequence
                                                                  (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                  Sbreak)
                                                                Sskip)))))))
                                                  (Ssequence
                                                    (Sset _t'354
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _head
                                                        (tptr (Tstruct _gz_header_s noattr))))
                                                    (Sifthenelse (Ebinop One
                                                                   (Etempvar _t'354 (tptr (Tstruct _gz_header_s noattr)))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _t'355
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _head
                                                            (tptr (Tstruct _gz_header_s noattr))))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _t'355 (tptr (Tstruct _gz_header_s noattr)))
                                                              (Tstruct _gz_header_s noattr))
                                                            _comment
                                                            (tptr tuchar))
                                                          (Econst_int (Int.repr 0) tint)))
                                                      Sskip))))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _mode tint)
                                                (Econst_int (Int.repr 16188) tint)))
                                            (LScons (Some 16188)
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'349
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                        (Tstruct _inflate_state noattr))
                                                      _flags tint))
                                                  (Sifthenelse (Ebinop Oand
                                                                 (Etempvar _t'349 tint)
                                                                 (Econst_int (Int.repr 512) tint)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Swhile
                                                          (Ebinop Olt
                                                            (Etempvar _bits tuint)
                                                            (Ecast
                                                              (Econst_int (Int.repr 16) tint)
                                                              tuint) tint)
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _have tuint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _leave
                                                                  (Econst_int (Int.repr 1) tint))
                                                                Sbreak)
                                                              Sskip)
                                                            (Ssequence
                                                              (Sset _have
                                                                (Ebinop Osub
                                                                  (Etempvar _have tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'45
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'45 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                  (Ssequence
                                                                    (Sset _t'352
                                                                    (Ederef
                                                                    (Etempvar _t'45 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'352 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                (Sset _bits
                                                                  (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                        (Sifthenelse (Etempvar _leave tint)
                                                          Sbreak
                                                          Sskip))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'350
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _wrap tint))
                                                            (Sifthenelse 
                                                              (Ebinop Oand
                                                                (Etempvar _t'350 tint)
                                                                (Econst_int (Int.repr 4) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Sset _t'351
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                (Sset _t'46
                                                                  (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'351 tulong)
                                                                    (Econst_int (Int.repr 65535) tint)
                                                                    tulong)
                                                                    tint)
                                                                    tbool)))
                                                              (Sset _t'46
                                                                (Econst_int (Int.repr 0) tint))))
                                                          (Sifthenelse (Etempvar _t'46 tint)
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                  _msg
                                                                  (tptr tschar))
                                                                (Ecast
                                                                  (Evar ___stringlit_inflate_15 (tarray tschar 20))
                                                                  (tptr tschar)))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                  (Econst_int (Int.repr 16209) tint))
                                                                Sbreak))
                                                            Sskip))
                                                        (Sloop
                                                          (Ssequence
                                                            (Sset _hold
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tulong))
                                                            (Sset _bits
                                                              (Econst_int (Int.repr 0) tint)))
                                                          Sbreak)))
                                                    Sskip))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'345
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _head
                                                        (tptr (Tstruct _gz_header_s noattr))))
                                                    (Sifthenelse (Ebinop One
                                                                   (Etempvar _t'345 (tptr (Tstruct _gz_header_s noattr)))
                                                                   (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                   tint)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'347
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _head
                                                              (tptr (Tstruct _gz_header_s noattr))))
                                                          (Ssequence
                                                            (Sset _t'348
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                  (Tstruct _inflate_state noattr))
                                                                _flags tint))
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _t'347 (tptr (Tstruct _gz_header_s noattr)))
                                                                  (Tstruct _gz_header_s noattr))
                                                                _hcrc tint)
                                                              (Ecast
                                                                (Ebinop Oand
                                                                  (Ebinop Oshr
                                                                    (Etempvar _t'348 tint)
                                                                    (Econst_int (Int.repr 9) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint) tint))))
                                                        (Ssequence
                                                          (Sset _t'346
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _head
                                                              (tptr (Tstruct _gz_header_s noattr))))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _t'346 (tptr (Tstruct _gz_header_s noattr)))
                                                                (Tstruct _gz_header_s noattr))
                                                              _done tint)
                                                            (Econst_int (Int.repr 1) tint))))
                                                      Sskip))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'47)
                                                            (Evar _crc32 
                                                            (Tfunction
                                                              (tulong ::
                                                               (tptr tuchar) ::
                                                               tuint :: nil)
                                                              tulong
                                                              cc_default))
                                                            ((Econst_long (Int64.repr 0) tlong) ::
                                                             (Econst_int (Int.repr 0) tint) ::
                                                             (Econst_int (Int.repr 0) tint) ::
                                                             nil))
                                                          (Sset _t'48
                                                            (Ecast
                                                              (Etempvar _t'47 tulong)
                                                              tulong)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _check tulong)
                                                          (Etempvar _t'48 tulong)))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                            (Tstruct _z_stream_s noattr))
                                                          _adler tulong)
                                                        (Etempvar _t'48 tulong)))
                                                    (Ssequence
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _mode tint)
                                                        (Econst_int (Int.repr 16191) tint))
                                                      Sbreak))))
                                              (LScons (Some 16189)
                                                (Ssequence
                                                  (Swhile
                                                    (Ebinop Olt
                                                      (Etempvar _bits tuint)
                                                      (Ecast
                                                        (Econst_int (Int.repr 32) tint)
                                                        tuint) tint)
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sset _leave
                                                            (Econst_int (Int.repr 1) tint))
                                                          Sbreak)
                                                        Sskip)
                                                      (Ssequence
                                                        (Sset _have
                                                          (Ebinop Osub
                                                            (Etempvar _have tuint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tuint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'49
                                                                (Etempvar _next (tptr tuchar)))
                                                              (Sset _next
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'49 (tptr tuchar))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuchar))))
                                                            (Ssequence
                                                              (Sset _t'344
                                                                (Ederef
                                                                  (Etempvar _t'49 (tptr tuchar))
                                                                  tuchar))
                                                              (Sset _hold
                                                                (Ebinop Oadd
                                                                  (Etempvar _hold tulong)
                                                                  (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'344 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                  tulong))))
                                                          (Sset _bits
                                                            (Ebinop Oadd
                                                              (Etempvar _bits tuint)
                                                              (Econst_int (Int.repr 8) tint)
                                                              tuint))))))
                                                  (Ssequence
                                                    (Sifthenelse (Etempvar _leave tint)
                                                      Sbreak
                                                      Sskip)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'50
                                                            (Ecast
                                                              (Ebinop Oadd
                                                                (Ebinop Oadd
                                                                  (Ebinop Oadd
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 65280) tint)
                                                                    tulong)
                                                                    tulong)
                                                                  (Ebinop Oshl
                                                                    (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 65280) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                  tulong)
                                                                (Ebinop Oshl
                                                                  (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                  (Econst_int (Int.repr 24) tint)
                                                                  tulong)
                                                                tulong)
                                                              tulong))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong)
                                                            (Etempvar _t'50 tulong)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                              (Tstruct _z_stream_s noattr))
                                                            _adler tulong)
                                                          (Etempvar _t'50 tulong)))
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Sset _hold
                                                              (Ecast
                                                                (Econst_int (Int.repr 0) tint)
                                                                tulong))
                                                            (Sset _bits
                                                              (Econst_int (Int.repr 0) tint)))
                                                          Sbreak)
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                              (Tstruct _inflate_state noattr))
                                                            _mode tint)
                                                          (Econst_int (Int.repr 16190) tint))))))
                                                (LScons (Some 16190)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'341
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _havedict tint))
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _t'341 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                  _next_out
                                                                  (tptr tuchar))
                                                                (Etempvar _put (tptr tuchar)))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint)
                                                                  (Etempvar _left tuint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar))
                                                                    (Etempvar _next (tptr tuchar)))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint)
                                                                    (Etempvar _have tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _hold
                                                                    tulong)
                                                                    (Etempvar _hold tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _bits
                                                                    tuint)
                                                                    (Etempvar _bits tuint)))))))
                                                            Sbreak)
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'342
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                  _total_in
                                                                  tulong))
                                                              (Ssequence
                                                                (Sset _t'343
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_in
                                                                    tulong)
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'342 tulong)
                                                                    (Ebinop Osub
                                                                    (Etempvar _in tuint)
                                                                    (Etempvar _t'343 tuint)
                                                                    tuint)
                                                                    tulong))))
                                                            (Sreturn (Some (Econst_int (Int.repr 2) tint)))))
                                                        Sskip))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'51)
                                                              (Evar _adler32 
                                                              (Tfunction
                                                                (tulong ::
                                                                 (tptr tuchar) ::
                                                                 tuint ::
                                                                 nil) tulong
                                                                cc_default))
                                                              ((Econst_long (Int64.repr 0) tlong) ::
                                                               (Econst_int (Int.repr 0) tint) ::
                                                               (Econst_int (Int.repr 0) tint) ::
                                                               nil))
                                                            (Sset _t'52
                                                              (Ecast
                                                                (Etempvar _t'51 tulong)
                                                                tulong)))
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _check tulong)
                                                            (Etempvar _t'52 tulong)))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                              (Tstruct _z_stream_s noattr))
                                                            _adler tulong)
                                                          (Etempvar _t'52 tulong)))
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                            (Tstruct _inflate_state noattr))
                                                          _mode tint)
                                                        (Econst_int (Int.repr 16191) tint))))
                                                  (LScons (Some 16191)
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                        (Sset _t'53
                                                          (Econst_int (Int.repr 1) tint))
                                                        (Sset _t'53
                                                          (Ecast
                                                            (Ebinop Oeq
                                                              (Etempvar _flush tint)
                                                              (Econst_int (Int.repr 6) tint)
                                                              tint) tbool)))
                                                      (Sifthenelse (Etempvar _t'53 tint)
                                                        (Ssequence
                                                          (Sset _leave
                                                            (Econst_int (Int.repr 1) tint))
                                                          Sbreak)
                                                        Sskip))
                                                    (LScons (Some 16192)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _t'340
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _last tint))
                                                          (Sifthenelse (Etempvar _t'340 tint)
                                                            (Ssequence
                                                              (Sloop
                                                                (Ssequence
                                                                  (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oand
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                    tulong))
                                                                  (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ebinop Oand
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                Sbreak)
                                                              (Ssequence
                                                                (Sassign
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                  (Econst_int (Int.repr 16206) tint))
                                                                Sbreak))
                                                            Sskip))
                                                        (Ssequence
                                                          (Swhile
                                                            (Ebinop Olt
                                                              (Etempvar _bits tuint)
                                                              (Ecast
                                                                (Econst_int (Int.repr 3) tint)
                                                                tuint) tint)
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _have tuint)
                                                                  (Econst_int (Int.repr 0) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                  Sbreak)
                                                                Sskip)
                                                              (Ssequence
                                                                (Sset _have
                                                                  (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'54
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'54 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'339
                                                                    (Ederef
                                                                    (Etempvar _t'54 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'339 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                  (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                          (Ssequence
                                                            (Sifthenelse (Etempvar _leave tint)
                                                              Sbreak
                                                              Sskip)
                                                            (Ssequence
                                                              (Sassign
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _last tint)
                                                                (Ebinop Oand
                                                                  (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                  (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                  Sbreak)
                                                                (Ssequence
                                                                  (Sswitch 
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (LScons (Some 0)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16193) tint))
                                                                    Sbreak)
                                                                    (LScons (Some 1)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _inflate_fixed 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _inflate_state noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _state (tptr (Tstruct _inflate_state noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16199) tint))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak))
                                                                    Sskip)
                                                                    Sbreak)))
                                                                    (LScons (Some 2)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16196) tint))
                                                                    Sbreak)
                                                                    (LScons None
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_14 (tarray tschar 19))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    LSnil)))))
                                                                  (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)
                                                                    Sbreak))))))))
                                                      (LScons (Some 16193)
                                                        (Ssequence
                                                          (Sloop
                                                            (Ssequence
                                                              (Sset _hold
                                                                (Ebinop Oshr
                                                                  (Etempvar _hold tulong)
                                                                  (Ebinop Oand
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                  tulong))
                                                              (Sset _bits
                                                                (Ebinop Osub
                                                                  (Etempvar _bits tuint)
                                                                  (Ebinop Oand
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                  tuint)))
                                                            Sbreak)
                                                          (Ssequence
                                                            (Swhile
                                                              (Ebinop Olt
                                                                (Etempvar _bits tuint)
                                                                (Ecast
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  tuint)
                                                                tint)
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                  Sskip)
                                                                (Ssequence
                                                                  (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'55
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'55 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'338
                                                                    (Ederef
                                                                    (Etempvar _t'55 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'338 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                            (Ssequence
                                                              (Sifthenelse (Etempvar _leave tint)
                                                                Sbreak
                                                                Sskip)
                                                              (Ssequence
                                                                (Sifthenelse 
                                                                  (Ebinop One
                                                                    (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 65535) tint)
                                                                    tulong)
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 65535) tint)
                                                                    tulong)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_13 (tarray tschar 29))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                  Sskip)
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 65535) tint)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16194) tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip))))))))
                                                        (LScons (Some 16194)
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                (Tstruct _inflate_state noattr))
                                                              _mode tint)
                                                            (Econst_int (Int.repr 16195) tint))
                                                          (LScons (Some 16195)
                                                            (Ssequence
                                                              (Sset _copy
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                  _length
                                                                  tuint))
                                                              (Ssequence
                                                                (Sifthenelse (Etempvar _copy tuint)
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _have tuint)
                                                                    tint)
                                                                    (Sset _copy
                                                                    (Etempvar _have tuint))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _left tuint)
                                                                    tint)
                                                                    (Sset _copy
                                                                    (Etempvar _left tuint))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _copy tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _put (tptr tuchar)) ::
                                                                    (Etempvar _next (tptr tuchar)) ::
                                                                    (Etempvar _copy tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _next (tptr tuchar))
                                                                    (Etempvar _copy tuint)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _put
                                                                    (Ebinop Oadd
                                                                    (Etempvar _put (tptr tuchar))
                                                                    (Etempvar _copy tuint)
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'337
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'337 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)))
                                                                    Sbreak)))))))))
                                                                  Sskip)
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16191) tint))
                                                                  Sbreak)))
                                                            (LScons (Some 16196)
                                                              (Ssequence
                                                                (Swhile
                                                                  (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    tuint)
                                                                    tint)
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'56
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'56 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'336
                                                                    (Ederef
                                                                    (Etempvar _t'56 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'336 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                (Ssequence
                                                                  (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 257) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ndist
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ncode
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'334
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'334 tuint)
                                                                    (Econst_int (Int.repr 286) tint)
                                                                    tint)
                                                                    (Sset _t'57
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _t'335
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ndist
                                                                    tuint))
                                                                    (Sset _t'57
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'335 tuint)
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'57 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_12 (tarray tschar 36))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16197) tint))))))))))))
                                                              (LScons (Some 16197)
                                                                (Ssequence
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'332
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'333
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ncode
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'332 tuint)
                                                                    (Etempvar _t'333 tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'58
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'58 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'331
                                                                    (Ederef
                                                                    (Etempvar _t'58 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'331 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'59
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'59 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'330
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _order (tarray tushort 19))
                                                                    (Etempvar _t'59 tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Etempvar _t'330 tushort)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tushort))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak))))
                                                                    Sskip)
                                                                  (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'329
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'329 tuint)
                                                                    (Econst_int (Int.repr 19) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'60
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'60 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'328
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _order (tarray tushort 19))
                                                                    (Etempvar _t'60 tuint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Etempvar _t'328 tushort)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _codes
                                                                    (tarray (Tstruct ___gp_code noattr) 1444)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'327
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sset _t'61
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Etempvar _t'327 (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (Tstruct ___gp_code noattr)))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _t'61 (tptr (Tstruct ___gp_code noattr)))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Etempvar _t'61 (tptr (Tstruct ___gp_code noattr)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint)
                                                                    (Econst_int (Int.repr 7) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'62)
                                                                    (Evar _inflate_table 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    (tptr tushort) ::
                                                                    tuint ::
                                                                    (tptr (tptr (Tstruct ___gp_code noattr))) ::
                                                                    (tptr tuint) ::
                                                                    (tptr tushort) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 0) tint) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320)) ::
                                                                    (Econst_int (Int.repr 19) tint) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (tptr (Tstruct ___gp_code noattr)))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint)
                                                                    (tptr tuint)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _work
                                                                    (tarray tushort 288)) ::
                                                                    nil))
                                                                    (Sset _ret
                                                                    (Etempvar _t'62 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _ret tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_11 (tarray tschar 25))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16198) tint)))))))))))
                                                                (LScons (Some 16198)
                                                                  (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'324
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'325
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'326
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ndist
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'324 tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'325 tuint)
                                                                    (Etempvar _t'326 tuint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'321
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'322
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'323
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'321 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'322 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'323 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'318
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'319
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'320
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'318 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'319 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'320 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'315
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'316
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'317
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'315 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'316 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'317 tushort)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'314
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Etempvar _t'314 tuchar)
                                                                    tuint)
                                                                    (Etempvar _bits tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'63
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'63 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'313
                                                                    (Ederef
                                                                    (Etempvar _t'63 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'313 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _t'290
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _t'290 tushort)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'312
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'312 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'311
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'311 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'64
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'64 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'310
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Etempvar _t'64 tuint)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Etempvar _t'310 tushort)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'294
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'294 tushort)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'309
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'309 tuchar)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'65
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'65 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'308
                                                                    (Ederef
                                                                    (Etempvar _t'65 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'308 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    Sskip)
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'307
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'307 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'306
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'306 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'305
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'305 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_7 (tarray tschar 26))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'304
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sset _len
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'304 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    (tptr tushort))
                                                                    tushort)))
                                                                    (Ssequence
                                                                    (Sset _copy
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak))))))
                                                                    (Ssequence
                                                                    (Sset _t'295
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'295 tushort)
                                                                    (Econst_int (Int.repr 17) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'303
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'303 tuchar)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'66
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'66 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'302
                                                                    (Ederef
                                                                    (Etempvar _t'66 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'302 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    Sskip)
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'301
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'301 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'300
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'300 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _copy
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'299
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'299 tuchar)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'67
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'67 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'298
                                                                    (Ederef
                                                                    (Etempvar _t'67 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'298 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    Sskip)
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'297
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'297 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'296
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'296 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _len
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sset _copy
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 11) tint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tuint)
                                                                    tuint)))
                                                                    Sbreak)))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'291
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'292
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'293
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ndist
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'291 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'292 tuint)
                                                                    (Etempvar _t'293 tuint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_7 (tarray tschar 26))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'68
                                                                    (Etempvar _copy tuint))
                                                                    (Sset _copy
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'68 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sifthenelse (Etempvar _t'68 tuint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'69
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _have
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'69 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Etempvar _t'69 tuint)
                                                                    (tptr tushort))
                                                                    tushort)
                                                                    (Ecast
                                                                    (Etempvar _len tuint)
                                                                    tushort))))
                                                                    Sskip))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'289
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'289 tint)
                                                                    (Econst_int (Int.repr 16209) tint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'288
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Econst_int (Int.repr 256) tint)
                                                                    (tptr tushort))
                                                                    tushort))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'288 tushort)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_8 (tarray tschar 37))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _codes
                                                                    (tarray (Tstruct ___gp_code noattr) 1444)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'287
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ecast
                                                                    (Etempvar _t'287 (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (Tstruct ___gp_code noattr)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint)
                                                                    (Econst_int (Int.repr 9) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'286
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint))
                                                                    (Scall (Some _t'70)
                                                                    (Evar _inflate_table 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    (tptr tushort) ::
                                                                    tuint ::
                                                                    (tptr (tptr (Tstruct ___gp_code noattr))) ::
                                                                    (tptr tuint) ::
                                                                    (tptr tushort) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 1) tint) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320)) ::
                                                                    (Etempvar _t'286 tuint) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (tptr (Tstruct ___gp_code noattr)))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint)
                                                                    (tptr tuint)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _work
                                                                    (tarray tushort 288)) ::
                                                                    nil)))
                                                                    (Sset _ret
                                                                    (Etempvar _t'70 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _ret tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_9 (tarray tschar 28))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'285
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ecast
                                                                    (Etempvar _t'285 (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (Tstruct ___gp_code noattr)))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distbits
                                                                    tuint)
                                                                    (Econst_int (Int.repr 6) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'283
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _nlen
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'284
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _ndist
                                                                    tuint))
                                                                    (Scall (Some _t'71)
                                                                    (Evar _inflate_table 
                                                                    (Tfunction
                                                                    (tint ::
                                                                    (tptr tushort) ::
                                                                    tuint ::
                                                                    (tptr (tptr (Tstruct ___gp_code noattr))) ::
                                                                    (tptr tuint) ::
                                                                    (tptr tushort) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Econst_int (Int.repr 2) tint) ::
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lens
                                                                    (tarray tushort 320))
                                                                    (Etempvar _t'283 tuint)
                                                                    (tptr tushort)) ::
                                                                    (Etempvar _t'284 tuint) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _next
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (tptr (tptr (Tstruct ___gp_code noattr)))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distbits
                                                                    tuint)
                                                                    (tptr tuint)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _work
                                                                    (tarray tushort 288)) ::
                                                                    nil))))
                                                                    (Sset _ret
                                                                    (Etempvar _t'71 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _ret tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_10 (tarray tschar 22))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16199) tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _flush tint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)))))))))))))))
                                                                  (LScons (Some 16199)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16200) tint))
                                                                    (LScons (Some 16200)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oge
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    tint)
                                                                    (Sset _t'72
                                                                    (Ecast
                                                                    (Ebinop Oge
                                                                    (Etempvar _left tuint)
                                                                    (Econst_int (Int.repr 258) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'72
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'72 tint)
                                                                    (Sset _t'73
                                                                    (Ecast
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'73
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'73 tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar))
                                                                    (Etempvar _put (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint)
                                                                    (Etempvar _left tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar))
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint)
                                                                    (Etempvar _have tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _hold
                                                                    tulong)
                                                                    (Etempvar _hold tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _bits
                                                                    tuint)
                                                                    (Etempvar _bits tuint)))))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _inflate_fast 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
                                                                    (Etempvar _out tuint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _put
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_out
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_out
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _next
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _next_in
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _avail_in
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _hold
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _bits
                                                                    tuint)))))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'282
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'282 tint)
                                                                    (Econst_int (Int.repr 16191) tint)
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    Sskip))
                                                                    Sbreak))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'279
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'280
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'281
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'279 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'280 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'281 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'276
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'277
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'278
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'276 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'277 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'278 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'273
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'274
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lenbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'275
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'273 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'274 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'275 tushort)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'272
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Etempvar _t'272 tuchar)
                                                                    tuint)
                                                                    (Etempvar _bits tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'74
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'74 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'271
                                                                    (Ederef
                                                                    (Etempvar _t'74 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'271 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'269
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse (Etempvar _t'269 tuchar)
                                                                    (Ssequence
                                                                    (Sset _t'270
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sset _t'76
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'270 tuchar)
                                                                    (Econst_int (Int.repr 240) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'76
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'76 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'268
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'268 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'267
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'267 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'266
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'266 tushort)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'260
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'261
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'262
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'263
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'264
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'265
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'260 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'261 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'262 tuchar)
                                                                    (Etempvar _t'263 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'264 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'265 tuchar))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'254
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'255
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'256
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'257
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'258
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'259
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'254 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'255 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'256 tuchar)
                                                                    (Etempvar _t'257 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'258 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'259 tuchar))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'248
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _lencode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'249
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'250
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'251
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'252
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'253
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'248 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'249 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'250 tuchar)
                                                                    (Etempvar _t'251 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'252 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'253 tushort))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'246
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'247
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'246 tuchar)
                                                                    (Etempvar _t'247 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Etempvar _bits tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'75
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'75 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'245
                                                                    (Ederef
                                                                    (Etempvar _t'75 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'245 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'244
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'244 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'243
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'243 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'241
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'242
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'241 tint)
                                                                    (Etempvar _t'242 tuchar)
                                                                    tint))))))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'240
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'240 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'239
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'239 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'237
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'238
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'237 tint)
                                                                    (Etempvar _t'238 tuchar)
                                                                    tint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'236
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'236 tushort)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'235
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ecast
                                                                    (Etempvar _t'235 tuchar)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16205) tint))
                                                                    Sbreak)
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'234
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'234 tuchar)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16191) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'233
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'233 tuchar)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_6 (tarray tschar 28))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'232
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _t'232 tuchar)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16201) tint))))))))))))))
                                                                    (LScons (Some 16201)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'223
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sifthenelse (Etempvar _t'223 tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'231
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'231 tuint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'77
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'77 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'230
                                                                    (Ederef
                                                                    (Etempvar _t'77 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'230 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    Sskip)
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'228
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'229
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'228 tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'229 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'227
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'227 tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'226
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'226 tuint)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'224
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'225
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'224 tint)
                                                                    (Etempvar _t'225 tuint)
                                                                    tuint)))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'222
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _was
                                                                    tuint)
                                                                    (Etempvar _t'222 tuint)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16202) tint))))
                                                                    (LScons (Some 16202)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'219
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'220
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'221
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'219 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'220 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'221 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'216
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'217
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'218
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'216 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'217 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'218 tuchar)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'213
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'214
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distbits
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'215
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'213 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'214 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'215 tushort)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'212
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Etempvar _t'212 tuchar)
                                                                    tuint)
                                                                    (Etempvar _bits tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'78
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'78 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'211
                                                                    (Ederef
                                                                    (Etempvar _t'78 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'211 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'182
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'182 tuchar)
                                                                    (Econst_int (Int.repr 240) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'210
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'210 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'209
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'209 tuchar)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'208
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'208 tushort)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    Sskip
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'202
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'203
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'204
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'205
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'206
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'207
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'202 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'203 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'204 tuchar)
                                                                    (Etempvar _t'205 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'206 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar)
                                                                    (Etempvar _t'207 tuchar))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'196
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'197
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'198
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'199
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'200
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'201
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'196 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'197 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'198 tuchar)
                                                                    (Etempvar _t'199 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'200 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar)
                                                                    (Etempvar _t'201 tuchar))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'190
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _distcode
                                                                    (tptr (Tstruct ___gp_code noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'191
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Ssequence
                                                                    (Sset _t'192
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'193
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'194
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'195
                                                                    (Efield
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'190 (tptr (Tstruct ___gp_code noattr)))
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'191 tushort)
                                                                    (Ebinop Oshr
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'192 tuchar)
                                                                    (Etempvar _t'193 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Etempvar _t'194 tuchar)
                                                                    tuint)
                                                                    tuint)
                                                                    (tptr (Tstruct ___gp_code noattr)))
                                                                    (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort)
                                                                    (Etempvar _t'195 tushort))))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'188
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _t'189
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ole
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'188 tuchar)
                                                                    (Etempvar _t'189 tuchar)
                                                                    tint)
                                                                    tuint)
                                                                    (Etempvar _bits tuint)
                                                                    tint)
                                                                    Sbreak
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'79
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'79 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'187
                                                                    (Ederef
                                                                    (Etempvar _t'79 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'187 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'186
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'186 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'185
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'185 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'183
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'184
                                                                    (Efield
                                                                    (Evar _last (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'183 tint)
                                                                    (Etempvar _t'184 tuchar)
                                                                    tint))))))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'181
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'181 tuchar)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'180
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'180 tuchar)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'178
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'179
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _bits
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'178 tint)
                                                                    (Etempvar _t'179 tuchar)
                                                                    tint))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'177
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'177 tuchar)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_5 (tarray tschar 22))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'176
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _val
                                                                    tushort))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'176 tushort)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'175
                                                                    (Efield
                                                                    (Evar _here (Tstruct ___gp_code noattr))
                                                                    _op
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _t'175 tuchar)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    tuint)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16203) tint))))))))))
                                                                    (LScons (Some 16203)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'166
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sifthenelse (Etempvar _t'166 tuint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'174
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'174 tuint)
                                                                    tuint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'80
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'80 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'173
                                                                    (Ederef
                                                                    (Etempvar _t'80 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'173 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    Sskip)
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'171
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'172
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'171 tuint)
                                                                    (Ebinop Oand
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_int (Int.repr 1) tuint)
                                                                    (Etempvar _t'172 tuint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    tuint))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'170
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sset _hold
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Etempvar _t'170 tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Sset _t'169
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sset _bits
                                                                    (Ebinop Osub
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Etempvar _t'169 tuint)
                                                                    tuint)
                                                                    tuint))))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'167
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _t'168
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _extra
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _back
                                                                    tint)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'167 tint)
                                                                    (Etempvar _t'168 tuint)
                                                                    tuint)))))))
                                                                    Sskip))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16204) tint)))
                                                                    (LScons (Some 16204)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _left tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _copy
                                                                    (Ebinop Osub
                                                                    (Etempvar _out tuint)
                                                                    (Etempvar _left tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'154
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _t'154 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'165
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint))
                                                                    (Sset _copy
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'165 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'163
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _whave
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _t'163 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'164
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _sane
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'164 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_4 (tarray tschar 30))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'157
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wnext
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _t'157 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'162
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wnext
                                                                    tuint))
                                                                    (Sset _copy
                                                                    (Ebinop Osub
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _t'162 tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _t'160
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _window
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'161
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wsize
                                                                    tuint))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'160 (tptr tuchar))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'161 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)
                                                                    (tptr tuchar))))))
                                                                    (Ssequence
                                                                    (Sset _t'158
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _window
                                                                    (tptr tuchar)))
                                                                    (Ssequence
                                                                    (Sset _t'159
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wnext
                                                                    tuint))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'158 (tptr tuchar))
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'159 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)
                                                                    (tptr tuchar)))))))
                                                                    (Ssequence
                                                                    (Sset _t'156
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _t'156 tuint)
                                                                    tint)
                                                                    (Sset _copy
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    Sskip)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'155
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _offset
                                                                    tuint))
                                                                    (Sset _from
                                                                    (Ebinop Osub
                                                                    (Etempvar _put (tptr tuchar))
                                                                    (Etempvar _t'155 tuint)
                                                                    (tptr tuchar))))
                                                                    (Sset _copy
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _copy tuint)
                                                                    (Etempvar _left tuint)
                                                                    tint)
                                                                    (Sset _copy
                                                                    (Etempvar _left tuint))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'153
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint)
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'153 tuint)
                                                                    (Etempvar _copy tuint)
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'82
                                                                    (Etempvar _put (tptr tuchar)))
                                                                    (Sset _put
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'82 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Sset _t'83
                                                                    (Etempvar _from (tptr tuchar))))
                                                                    (Sset _from
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'83 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'152
                                                                    (Ederef
                                                                    (Etempvar _t'83 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'82 (tptr tuchar))
                                                                    tuchar)
                                                                    (Etempvar _t'152 tuchar))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'81
                                                                    (Ecast
                                                                    (Ebinop Osub
                                                                    (Etempvar _copy tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Sset _copy
                                                                    (Etempvar _t'81 tuint)))
                                                                    (Sifthenelse (Etempvar _t'81 tuint)
                                                                    Sskip
                                                                    Sbreak)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'151
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'151 tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16200) tint))
                                                                    Sskip))
                                                                    Sbreak))))))))
                                                                    (LScons (Some 16205)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _left tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'84
                                                                    (Etempvar _put (tptr tuchar)))
                                                                    (Sset _put
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'84 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'150
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _length
                                                                    tuint))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Etempvar _t'84 (tptr tuchar))
                                                                    tuchar)
                                                                    (Ecast
                                                                    (Etempvar _t'150 tuint)
                                                                    tuchar))))
                                                                    (Ssequence
                                                                    (Sset _left
                                                                    (Ebinop Osub
                                                                    (Etempvar _left tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16200) tint))
                                                                    Sbreak))))
                                                                    (LScons (Some 16206)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'139
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'139 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'85
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'85 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'149
                                                                    (Ederef
                                                                    (Etempvar _t'85 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'149 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sset _out
                                                                    (Ebinop Osub
                                                                    (Etempvar _out tuint)
                                                                    (Etempvar _left tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'148
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _total_out
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'148 tulong)
                                                                    (Etempvar _out tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'147
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _total
                                                                    tulong))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _total
                                                                    tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'147 tulong)
                                                                    (Etempvar _out tuint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'146
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'146 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Sset _t'90
                                                                    (Ecast
                                                                    (Etempvar _out tuint)
                                                                    tbool))
                                                                    (Sset _t'90
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'90 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'143
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _flags
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'143 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'145
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                    (Scall (Some _t'87)
                                                                    (Evar _crc32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'145 tulong) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _put (tptr tuchar))
                                                                    (Etempvar _out tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _out tuint) ::
                                                                    nil)))
                                                                    (Sset _t'86
                                                                    (Ecast
                                                                    (Etempvar _t'87 tulong)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'144
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                    (Scall (Some _t'88)
                                                                    (Evar _adler32 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    (tptr tuchar) ::
                                                                    tuint ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'144 tulong) ::
                                                                    (Ebinop Osub
                                                                    (Etempvar _put (tptr tuchar))
                                                                    (Etempvar _out tuint)
                                                                    (tptr tuchar)) ::
                                                                    (Etempvar _out tuint) ::
                                                                    nil)))
                                                                    (Sset _t'86
                                                                    (Ecast
                                                                    (Etempvar _t'88 tulong)
                                                                    tulong)))))
                                                                    (Sset _t'89
                                                                    (Ecast
                                                                    (Etempvar _t'86 tulong)
                                                                    tulong)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong)
                                                                    (Etempvar _t'89 tulong)))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _adler
                                                                    tulong)
                                                                    (Etempvar _t'89 tulong)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sset _out
                                                                    (Etempvar _left tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'140
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'140 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'142
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _flags
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'142 tint)
                                                                    (Sset _t'92
                                                                    (Ecast
                                                                    (Etempvar _hold tulong)
                                                                    tulong))
                                                                    (Sset _t'92
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oadd
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 65280) tint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Oshl
                                                                    (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 65280) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    tulong)
                                                                    (Ebinop Oshl
                                                                    (Ebinop Oand
                                                                    (Etempvar _hold tulong)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tulong)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Sset _t'141
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _check
                                                                    tulong))
                                                                    (Sset _t'91
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'92 tulong)
                                                                    (Etempvar _t'141 tulong)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'91
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'91 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_3 (tarray tschar 21))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    Sbreak))))))))
                                                                    Sskip))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16207) tint)))
                                                                    (LScons (Some 16207)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'137
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse (Etempvar _t'137 tint)
                                                                    (Ssequence
                                                                    (Sset _t'138
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _flags
                                                                    tint))
                                                                    (Sset _t'95
                                                                    (Ecast
                                                                    (Etempvar _t'138 tint)
                                                                    tbool)))
                                                                    (Sset _t'95
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'95 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Ebinop Olt
                                                                    (Etempvar _bits tuint)
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sset _have
                                                                    (Ebinop Osub
                                                                    (Etempvar _have tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'93
                                                                    (Etempvar _next (tptr tuchar)))
                                                                    (Sset _next
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'93 (tptr tuchar))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuchar))))
                                                                    (Ssequence
                                                                    (Sset _t'136
                                                                    (Ederef
                                                                    (Etempvar _t'93 (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _hold
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oshl
                                                                    (Ecast
                                                                    (Etempvar _t'136 tuchar)
                                                                    tulong)
                                                                    (Etempvar _bits tuint)
                                                                    tulong)
                                                                    tulong))))
                                                                    (Sset _bits
                                                                    (Ebinop Oadd
                                                                    (Etempvar _bits tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint))))))
                                                                    (Sifthenelse (Etempvar _leave tint)
                                                                    Sbreak
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'134
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _wrap
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'134 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'135
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _total
                                                                    tulong))
                                                                    (Sset _t'94
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _hold tulong)
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'135 tulong)
                                                                    (Econst_int (Int.repr (-1)) tuint)
                                                                    tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'94
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'94 tint)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                                    (Tstruct _z_stream_s noattr))
                                                                    _msg
                                                                    (tptr tschar))
                                                                    (Ecast
                                                                    (Evar ___stringlit_inflate_2 (tarray tschar 23))
                                                                    (tptr tschar)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16209) tint))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _hold
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sset _bits
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    Sbreak)))
                                                                    Sskip))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                                    (Tstruct _inflate_state noattr))
                                                                    _mode
                                                                    tint)
                                                                    (Econst_int (Int.repr 16208) tint)))
                                                                    (LScons (Some 16208)
                                                                    (Ssequence
                                                                    (Sset _ret
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak))
                                                                    (LScons (Some 16209)
                                                                    (Ssequence
                                                                    (Sset _ret
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint))
                                                                    (Ssequence
                                                                    (Sset _leave
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    Sbreak))
                                                                    (LScons (Some 16210)
                                                                    (Sreturn (Some 
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)))
                                                                    (LScons (Some 16211)
                                                                    Sskip
                                                                    (LScons None
                                                                    (Sreturn (Some 
                                                                    (Eunop Oneg
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)))
                                                                    LSnil)))))))))))))))))))))))))))))))))))
                        (Sifthenelse (Etempvar _leave tint) Sbreak Sskip)))
                    Sskip)
                  (Ssequence
                    (Sloop
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                              (Tstruct _z_stream_s noattr)) _next_out
                            (tptr tuchar)) (Etempvar _put (tptr tuchar)))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                (Tstruct _z_stream_s noattr)) _avail_out
                              tuint) (Etempvar _left tuint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                  (Tstruct _z_stream_s noattr)) _next_in
                                (tptr tuchar))
                              (Etempvar _next (tptr tuchar)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _avail_in
                                  tuint) (Etempvar _have tuint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _hold
                                    tulong) (Etempvar _hold tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _bits
                                    tuint) (Etempvar _bits tuint)))))))
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'129
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wsize
                              tuint))
                          (Sifthenelse (Etempvar _t'129 tuint)
                            (Sset _t'97 (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Ssequence
                                (Sset _t'131
                                  (Efield
                                    (Ederef
                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                      (Tstruct _z_stream_s noattr))
                                    _avail_out tuint))
                                (Sifthenelse (Ebinop One
                                               (Etempvar _out tuint)
                                               (Etempvar _t'131 tuint) tint)
                                  (Ssequence
                                    (Sset _t'132
                                      (Efield
                                        (Ederef
                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                          (Tstruct _inflate_state noattr))
                                        _mode tint))
                                    (Sset _t'98
                                      (Ecast
                                        (Ebinop Olt (Etempvar _t'132 tint)
                                          (Econst_int (Int.repr 16209) tint)
                                          tint) tbool)))
                                  (Sset _t'98 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'98 tint)
                                (Ssequence
                                  (Sset _t'130
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _mode tint))
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _t'130 tint)
                                                 (Econst_int (Int.repr 16206) tint)
                                                 tint)
                                    (Ssequence
                                      (Sset _t'97
                                        (Ecast (Econst_int (Int.repr 1) tint)
                                          tbool))
                                      (Sset _t'97
                                        (Ecast (Etempvar _t'97 tint) tbool)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'97
                                          (Ecast
                                            (Ebinop One
                                              (Etempvar _flush tint)
                                              (Econst_int (Int.repr 4) tint)
                                              tint) tbool))
                                        (Sset _t'97
                                          (Ecast (Etempvar _t'97 tint) tbool)))
                                      (Sset _t'97
                                        (Ecast (Etempvar _t'97 tint) tbool)))))
                                (Sset _t'97
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tbool))))))
                        (Sifthenelse (Etempvar _t'97 tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'127
                                (Efield
                                  (Ederef
                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _next_out
                                  (tptr tuchar)))
                              (Ssequence
                                (Sset _t'128
                                  (Efield
                                    (Ederef
                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                      (Tstruct _z_stream_s noattr))
                                    _avail_out tuint))
                                (Scall (Some _t'96)
                                  (Evar _updatewindow (Tfunction
                                                        ((tptr (Tstruct _z_stream_s noattr)) ::
                                                         (tptr tuchar) ::
                                                         tuint :: nil) tint
                                                        cc_default))
                                  ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
                                   (Etempvar _t'127 (tptr tuchar)) ::
                                   (Ebinop Osub (Etempvar _out tuint)
                                     (Etempvar _t'128 tuint) tuint) :: nil))))
                            (Sifthenelse (Etempvar _t'96 tint)
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _mode
                                    tint) (Econst_int (Int.repr 16210) tint))
                                (Sreturn (Some (Eunop Oneg
                                                 (Econst_int (Int.repr 4) tint)
                                                 tint))))
                              Sskip))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Sset _t'126
                            (Efield
                              (Ederef
                                (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                (Tstruct _z_stream_s noattr)) _avail_in
                              tuint))
                          (Sset _in
                            (Ebinop Osub (Etempvar _in tuint)
                              (Etempvar _t'126 tuint) tuint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'125
                              (Efield
                                (Ederef
                                  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                  (Tstruct _z_stream_s noattr)) _avail_out
                                tuint))
                            (Sset _out
                              (Ebinop Osub (Etempvar _out tuint)
                                (Etempvar _t'125 tuint) tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'124
                                (Efield
                                  (Ederef
                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _total_in
                                  tulong))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _total_in
                                  tulong)
                                (Ebinop Oadd (Etempvar _t'124 tulong)
                                  (Etempvar _in tuint) tulong)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'123
                                  (Efield
                                    (Ederef
                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                      (Tstruct _z_stream_s noattr))
                                    _total_out tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                      (Tstruct _z_stream_s noattr))
                                    _total_out tulong)
                                  (Ebinop Oadd (Etempvar _t'123 tulong)
                                    (Etempvar _out tuint) tulong)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'122
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _total tulong))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _total tulong)
                                    (Ebinop Oadd (Etempvar _t'122 tulong)
                                      (Etempvar _out tuint) tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'121
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _wrap tint))
                                      (Sifthenelse (Ebinop Oand
                                                     (Etempvar _t'121 tint)
                                                     (Econst_int (Int.repr 4) tint)
                                                     tint)
                                        (Sset _t'103
                                          (Ecast (Etempvar _out tuint) tbool))
                                        (Sset _t'103
                                          (Econst_int (Int.repr 0) tint))))
                                    (Sifthenelse (Etempvar _t'103 tint)
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'116
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _flags tint))
                                              (Sifthenelse (Etempvar _t'116 tint)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'119
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _check tulong))
                                                    (Ssequence
                                                      (Sset _t'120
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                            (Tstruct _z_stream_s noattr))
                                                          _next_out
                                                          (tptr tuchar)))
                                                      (Scall (Some _t'100)
                                                        (Evar _crc32 
                                                        (Tfunction
                                                          (tulong ::
                                                           (tptr tuchar) ::
                                                           tuint :: nil)
                                                          tulong cc_default))
                                                        ((Etempvar _t'119 tulong) ::
                                                         (Ebinop Osub
                                                           (Etempvar _t'120 (tptr tuchar))
                                                           (Etempvar _out tuint)
                                                           (tptr tuchar)) ::
                                                         (Etempvar _out tuint) ::
                                                         nil))))
                                                  (Sset _t'99
                                                    (Ecast
                                                      (Etempvar _t'100 tulong)
                                                      tulong)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'117
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                          (Tstruct _inflate_state noattr))
                                                        _check tulong))
                                                    (Ssequence
                                                      (Sset _t'118
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                                            (Tstruct _z_stream_s noattr))
                                                          _next_out
                                                          (tptr tuchar)))
                                                      (Scall (Some _t'101)
                                                        (Evar _adler32 
                                                        (Tfunction
                                                          (tulong ::
                                                           (tptr tuchar) ::
                                                           tuint :: nil)
                                                          tulong cc_default))
                                                        ((Etempvar _t'117 tulong) ::
                                                         (Ebinop Osub
                                                           (Etempvar _t'118 (tptr tuchar))
                                                           (Etempvar _out tuint)
                                                           (tptr tuchar)) ::
                                                         (Etempvar _out tuint) ::
                                                         nil))))
                                                  (Sset _t'99
                                                    (Ecast
                                                      (Etempvar _t'101 tulong)
                                                      tulong)))))
                                            (Sset _t'102
                                              (Ecast (Etempvar _t'99 tulong)
                                                tulong)))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _check tulong)
                                            (Etempvar _t'102 tulong)))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                              (Tstruct _z_stream_s noattr))
                                            _adler tulong)
                                          (Etempvar _t'102 tulong)))
                                      Sskip))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'115
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _last tint))
                                              (Sifthenelse (Etempvar _t'115 tint)
                                                (Sset _t'104
                                                  (Ecast
                                                    (Econst_int (Int.repr 64) tint)
                                                    tint))
                                                (Sset _t'104
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint))))
                                            (Ssequence
                                              (Sset _t'114
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                    (Tstruct _inflate_state noattr))
                                                  _mode tint))
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _t'114 tint)
                                                             (Econst_int (Int.repr 16191) tint)
                                                             tint)
                                                (Sset _t'105
                                                  (Ecast
                                                    (Econst_int (Int.repr 128) tint)
                                                    tint))
                                                (Sset _t'105
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint)))))
                                          (Ssequence
                                            (Sset _t'112
                                              (Efield
                                                (Ederef
                                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                  (Tstruct _inflate_state noattr))
                                                _mode tint))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _t'112 tint)
                                                           (Econst_int (Int.repr 16199) tint)
                                                           tint)
                                              (Sset _t'106
                                                (Econst_int (Int.repr 1) tint))
                                              (Ssequence
                                                (Sset _t'113
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                      (Tstruct _inflate_state noattr))
                                                    _mode tint))
                                                (Sset _t'106
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _t'113 tint)
                                                      (Econst_int (Int.repr 16194) tint)
                                                      tint) tbool))))))
                                        (Sifthenelse (Etempvar _t'106 tint)
                                          (Sset _t'107
                                            (Ecast
                                              (Econst_int (Int.repr 256) tint)
                                              tint))
                                          (Sset _t'107
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tint))))
                                      (Ssequence
                                        (Sset _t'111
                                          (Efield
                                            (Ederef
                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                              (Tstruct _inflate_state noattr))
                                            _bits tuint))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                              (Tstruct _z_stream_s noattr))
                                            _data_type tint)
                                          (Ebinop Oadd
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Ecast
                                                  (Etempvar _t'111 tuint)
                                                  tint)
                                                (Etempvar _t'104 tint) tint)
                                              (Etempvar _t'105 tint) tint)
                                            (Etempvar _t'107 tint) tint))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _in tuint)
                                                           (Econst_int (Int.repr 0) tint)
                                                           tint)
                                              (Sset _t'108
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _out tuint)
                                                    (Econst_int (Int.repr 0) tint)
                                                    tint) tbool))
                                              (Sset _t'108
                                                (Econst_int (Int.repr 0) tint)))
                                            (Sifthenelse (Etempvar _t'108 tint)
                                              (Sset _t'109
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'109
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _flush tint)
                                                    (Econst_int (Int.repr 4) tint)
                                                    tint) tbool))))
                                          (Sifthenelse (Etempvar _t'109 tint)
                                            (Sset _t'110
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _ret tint)
                                                  (Econst_int (Int.repr 0) tint)
                                                  tint) tbool))
                                            (Sset _t'110
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'110 tint)
                                          (Sset _ret
                                            (Eunop Oneg
                                              (Econst_int (Int.repr 5) tint)
                                              tint))
                                          Sskip))
                                      (Sreturn (Some (Etempvar _ret tint))))))))))))))))))))))
|}.

Definition f_inflateEnd := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'1, tint) ::
               (_t'9, (tptr (Tstruct _internal_state noattr))) ::
               (_t'8, (tptr tuchar)) :: (_t'7, (tptr tvoid)) ::
               (_t'6,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: (_t'5, (tptr tuchar)) ::
               (_t'4, (tptr (Tstruct _internal_state noattr))) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'9 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'5
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
        (Sifthenelse (Ebinop One (Etempvar _t'5 (tptr tuchar))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _zfree
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
              (Ssequence
                (Sset _t'8
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
                (Scall None
                  (Ederef
                    (Etempvar _t'6 (tptr (Tfunction
                                           ((tptr tvoid) :: (tptr tvoid) ::
                                            nil) tvoid cc_default)))
                    (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                      cc_default))
                  ((Etempvar _t'7 (tptr tvoid)) ::
                   (Ecast (Etempvar _t'8 (tptr tuchar)) (tptr tvoid)) :: nil)))))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zfree
              (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                      cc_default))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _state
                  (tptr (Tstruct _internal_state noattr))))
              (Scall None
                (Ederef
                  (Etempvar _t'2 (tptr (Tfunction
                                         ((tptr tvoid) :: (tptr tvoid) ::
                                          nil) tvoid cc_default)))
                  (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                    cc_default))
                ((Etempvar _t'3 (tptr tvoid)) ::
                 (Ecast
                   (Etempvar _t'4 (tptr (Tstruct _internal_state noattr)))
                   (tptr tvoid)) :: nil)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _state
              (tptr (Tstruct _internal_state noattr)))
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_inflateGetDictionary := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_dictionary, (tptr tuchar)) ::
                (_dictLength, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'13, (tptr (Tstruct _internal_state noattr))) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, (tptr tuchar)) :: (_t'7, tuint) ::
               (_t'6, (tptr tuchar)) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'13
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'13 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'12
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _whave tuint))
          (Sifthenelse (Etempvar _t'12 tuint)
            (Sset _t'2
              (Ecast
                (Ebinop One (Etempvar _dictionary (tptr tuchar))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                tbool))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _wnext tuint))
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _whave tuint))
                  (Ssequence
                    (Sset _t'11
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _wnext tuint))
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      ((tptr tvoid) :: (tptr tvoid) ::
                                       tulong :: nil) (tptr tvoid)
                                      cc_default))
                      ((Etempvar _dictionary (tptr tuchar)) ::
                       (Ebinop Oadd (Etempvar _t'8 (tptr tuchar))
                         (Etempvar _t'9 tuint) (tptr tuchar)) ::
                       (Ebinop Osub (Etempvar _t'10 tuint)
                         (Etempvar _t'11 tuint) tuint) :: nil))))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _whave tuint))
              (Ssequence
                (Sset _t'5
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _wnext tuint))
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _window
                      (tptr tuchar)))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _wnext tuint))
                    (Scall None
                      (Evar _memcpy (Tfunction
                                      ((tptr tvoid) :: (tptr tvoid) ::
                                       tulong :: nil) (tptr tvoid)
                                      cc_default))
                      ((Ebinop Osub
                         (Ebinop Oadd (Etempvar _dictionary (tptr tuchar))
                           (Etempvar _t'4 tuint) (tptr tuchar))
                         (Etempvar _t'5 tuint) (tptr tuchar)) ::
                       (Etempvar _t'6 (tptr tuchar)) ::
                       (Etempvar _t'7 tuint) :: nil)))))))
          Sskip))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _dictLength (tptr tuint))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _whave tuint))
            (Sassign (Ederef (Etempvar _dictLength (tptr tuint)) tuint)
              (Etempvar _t'3 tuint)))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_inflateSetDictionary := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_dictionary, (tptr tuchar)) :: (_dictLength, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_dictid, tulong) :: (_ret, tint) :: (_t'5, tint) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tint) ::
               (_t'1, tint) ::
               (_t'10, (tptr (Tstruct _internal_state noattr))) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tulong) ::
               (_t'6, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'10 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _wrap tint))
          (Sifthenelse (Ebinop One (Etempvar _t'8 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _mode tint))
              (Sset _t'2
                (Ecast
                  (Ebinop One (Etempvar _t'9 tint)
                    (Econst_int (Int.repr 16190) tint) tint) tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _mode tint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                         (Econst_int (Int.repr 16190) tint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _adler32 (Tfunction
                                   (tulong :: (tptr tuchar) :: tuint :: nil)
                                   tulong cc_default))
                  ((Econst_long (Int64.repr 0) tlong) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 0) tint) :: nil))
                (Sset _dictid (Etempvar _t'3 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _adler32 (Tfunction
                                     (tulong :: (tptr tuchar) :: tuint ::
                                      nil) tulong cc_default))
                    ((Etempvar _dictid tulong) ::
                     (Etempvar _dictionary (tptr tuchar)) ::
                     (Etempvar _dictLength tuint) :: nil))
                  (Sset _dictid (Etempvar _t'4 tulong)))
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _check tulong))
                  (Sifthenelse (Ebinop One (Etempvar _dictid tulong)
                                 (Etempvar _t'7 tulong) tint)
                    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 3) tint)
                                     tint)))
                    Sskip))))
            Sskip))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _updatewindow (Tfunction
                                    ((tptr (Tstruct _z_stream_s noattr)) ::
                                     (tptr tuchar) :: tuint :: nil) tint
                                    cc_default))
              ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
               (Ebinop Oadd (Etempvar _dictionary (tptr tuchar))
                 (Etempvar _dictLength tuint) (tptr tuchar)) ::
               (Etempvar _dictLength tuint) :: nil))
            (Sset _ret (Etempvar _t'5 tint)))
          (Ssequence
            (Sifthenelse (Etempvar _ret tint)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _mode tint)
                  (Econst_int (Int.repr 16210) tint))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 4) tint)
                                 tint))))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _havedict tint)
                (Econst_int (Int.repr 1) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_inflateGetHeader := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_head, (tptr (Tstruct _gz_header_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'1, tint) ::
               (_t'3, (tptr (Tstruct _internal_state noattr))) ::
               (_t'2, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'3 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _wrap tint))
        (Sifthenelse (Ebinop Oeq
                       (Ebinop Oand (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 2) tint) tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
          Sskip))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _head
            (tptr (Tstruct _gz_header_s noattr)))
          (Etempvar _head (tptr (Tstruct _gz_header_s noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _head (tptr (Tstruct _gz_header_s noattr)))
                (Tstruct _gz_header_s noattr)) _done tint)
            (Econst_int (Int.repr 0) tint))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_syncsearch := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_have, (tptr tuint)) :: (_buf, (tptr tuchar)) ::
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_got, tuint) :: (_next, tuint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tuchar) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _got (Ederef (Etempvar _have (tptr tuint)) tuint))
  (Ssequence
    (Sset _next (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _next tuint)
                           (Etempvar _len tuint) tint)
              (Sset _t'1
                (Ecast
                  (Ebinop Olt (Etempvar _got tuint)
                    (Econst_int (Int.repr 4) tint) tint) tbool))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _got tuint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))
                (Sset _t'2 (Ecast (Econst_int (Int.repr 255) tint) tint)))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                      (Etempvar _next tuint) (tptr tuchar)) tuchar))
                (Sifthenelse (Ebinop Oeq (Ecast (Etempvar _t'3 tuchar) tint)
                               (Etempvar _t'2 tint) tint)
                  (Sset _got
                    (Ebinop Oadd (Etempvar _got tuint)
                      (Econst_int (Int.repr 1) tint) tuint))
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                          (Etempvar _next tuint) (tptr tuchar)) tuchar))
                    (Sifthenelse (Etempvar _t'4 tuchar)
                      (Sset _got (Econst_int (Int.repr 0) tint))
                      (Sset _got
                        (Ebinop Osub (Econst_int (Int.repr 4) tint)
                          (Etempvar _got tuint) tuint)))))))
            (Sset _next
              (Ebinop Oadd (Etempvar _next tuint)
                (Econst_int (Int.repr 1) tint) tuint))))
        Sskip)
      (Ssequence
        (Sassign (Ederef (Etempvar _have (tptr tuint)) tuint)
          (Etempvar _got tuint))
        (Sreturn (Some (Etempvar _next tuint)))))))
|}.

Definition f_inflateSync := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := ((_buf, (tarray tuchar 4)) :: nil);
  fn_temps := ((_len, tuint) :: (_flags, tint) :: (_wrap, tint) ::
               (_in, tulong) :: (_out, tulong) ::
               (_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tint) ::
               (_t'1, tint) ::
               (_t'25, (tptr (Tstruct _internal_state noattr))) ::
               (_t'24, tuint) :: (_t'23, tuint) :: (_t'22, tuint) ::
               (_t'21, tulong) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, tuint) :: (_t'17, tulong) :: (_t'16, tulong) ::
               (_t'15, tuint) :: (_t'14, tint) :: (_t'13, tuint) ::
               (_t'12, (tptr tuchar)) :: (_t'11, tuint) ::
               (_t'10, (tptr tuchar)) :: (_t'9, tulong) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tint) :: (_t'5, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'25
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'25 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'23
            (Efield
              (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _avail_in tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'23 tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'24
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _bits tuint))
              (Sset _t'2
                (Ecast
                  (Ebinop Olt (Etempvar _t'24 tuint)
                    (Econst_int (Int.repr 8) tint) tint) tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 5) tint) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef
                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                (Tstruct _inflate_state noattr)) _mode tint))
          (Sifthenelse (Ebinop One (Etempvar _t'14 tint)
                         (Econst_int (Int.repr 16211) tint) tint)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                    (Tstruct _inflate_state noattr)) _mode tint)
                (Econst_int (Int.repr 16211) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _hold tulong))
                  (Ssequence
                    (Sset _t'22
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _bits tuint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _hold tulong)
                      (Ebinop Oshr (Etempvar _t'21 tulong)
                        (Ebinop Oand (Etempvar _t'22 tuint)
                          (Econst_int (Int.repr 7) tint) tuint) tulong))))
                (Ssequence
                  (Ssequence
                    (Sset _t'19
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _bits tuint))
                    (Ssequence
                      (Sset _t'20
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _bits tuint))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _bits tuint)
                        (Ebinop Osub (Etempvar _t'19 tuint)
                          (Ebinop Oand (Etempvar _t'20 tuint)
                            (Econst_int (Int.repr 7) tint) tuint) tuint))))
                  (Ssequence
                    (Sset _len (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Ssequence
                            (Sset _t'18
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _bits
                                tuint))
                            (Sifthenelse (Ebinop Oge (Etempvar _t'18 tuint)
                                           (Econst_int (Int.repr 8) tint)
                                           tint)
                              Sskip
                              Sbreak))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'3 (Etempvar _len tuint))
                                (Sset _len
                                  (Ebinop Oadd (Etempvar _t'3 tuint)
                                    (Econst_int (Int.repr 1) tint) tuint)))
                              (Ssequence
                                (Sset _t'17
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _hold
                                    tulong))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _buf (tarray tuchar 4))
                                      (Etempvar _t'3 tuint) (tptr tuchar))
                                    tuchar)
                                  (Ecast (Etempvar _t'17 tulong) tuchar))))
                            (Ssequence
                              (Ssequence
                                (Sset _t'16
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _hold
                                    tulong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _hold
                                    tulong)
                                  (Ebinop Oshr (Etempvar _t'16 tulong)
                                    (Econst_int (Int.repr 8) tint) tulong)))
                              (Ssequence
                                (Sset _t'15
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _bits
                                    tuint))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _bits
                                    tuint)
                                  (Ebinop Osub (Etempvar _t'15 tuint)
                                    (Econst_int (Int.repr 8) tint) tuint))))))
                        Sskip)
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _have tuint)
                          (Econst_int (Int.repr 0) tint))
                        (Scall None
                          (Evar _syncsearch (Tfunction
                                              ((tptr tuint) ::
                                               (tptr tuchar) :: tuint :: nil)
                                              tuint cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                 (Tstruct _inflate_state noattr)) _have
                               tuint) (tptr tuint)) ::
                           (Evar _buf (tarray tuchar 4)) ::
                           (Etempvar _len tuint) :: nil))))))))
            Sskip))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar)))
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _avail_in tuint))
                (Scall (Some _t'4)
                  (Evar _syncsearch (Tfunction
                                      ((tptr tuint) :: (tptr tuchar) ::
                                       tuint :: nil) tuint cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                         (Tstruct _inflate_state noattr)) _have tuint)
                     (tptr tuint)) :: (Etempvar _t'12 (tptr tuchar)) ::
                   (Etempvar _t'13 tuint) :: nil))))
            (Sset _len (Etempvar _t'4 tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _avail_in tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                    (Tstruct _z_stream_s noattr)) _avail_in tuint)
                (Ebinop Osub (Etempvar _t'11 tuint) (Etempvar _len tuint)
                  tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar)))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                      (Tstruct _z_stream_s noattr)) _next_in (tptr tuchar))
                  (Ebinop Oadd (Etempvar _t'10 (tptr tuchar))
                    (Etempvar _len tuint) (tptr tuchar))))
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _total_in tulong))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                        (Tstruct _z_stream_s noattr)) _total_in tulong)
                    (Ebinop Oadd (Etempvar _t'9 tulong) (Etempvar _len tuint)
                      tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _have tuint))
                    (Sifthenelse (Ebinop One (Etempvar _t'8 tuint)
                                   (Econst_int (Int.repr 4) tint) tint)
                      (Sreturn (Some (Eunop Oneg
                                       (Econst_int (Int.repr 3) tint) tint)))
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _flags tint))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                                     (Eunop Oneg
                                       (Econst_int (Int.repr 1) tint) tint)
                                     tint)
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wrap tint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sset _t'7
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _wbits
                                tuint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _wbits
                                  tuint) (Econst_int (Int.repr 15) tint))
                              Sskip)))
                        (Ssequence
                          (Sset _t'6
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wrap tint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wrap tint)
                            (Ebinop Oand (Etempvar _t'6 tint)
                              (Eunop Onotint (Econst_int (Int.repr 4) tint)
                                tint) tint)))))
                    (Ssequence
                      (Sset _flags
                        (Efield
                          (Ederef
                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                            (Tstruct _inflate_state noattr)) _flags tint))
                      (Ssequence
                        (Sset _wrap
                          (Efield
                            (Ederef
                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                              (Tstruct _inflate_state noattr)) _wrap tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _wrap tint)
                            (Ebinop Oand (Etempvar _wrap tint)
                              (Eunop Onotint (Econst_int (Int.repr 8) tint)
                                tint) tint))
                          (Ssequence
                            (Sset _in
                              (Efield
                                (Ederef
                                  (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                  (Tstruct _z_stream_s noattr)) _total_in
                                tulong))
                            (Ssequence
                              (Sset _out
                                (Efield
                                  (Ederef
                                    (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _total_out
                                  tulong))
                              (Ssequence
                                (Scall None
                                  (Evar _inflateReset (Tfunction
                                                        ((tptr (Tstruct _z_stream_s noattr)) ::
                                                         nil) tint
                                                        cc_default))
                                  ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) ::
                                   nil))
                                (Ssequence
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                        (Tstruct _z_stream_s noattr))
                                      _total_in tulong)
                                    (Etempvar _in tulong))
                                  (Ssequence
                                    (Sassign
                                      (Efield
                                        (Ederef
                                          (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
                                          (Tstruct _z_stream_s noattr))
                                        _total_out tulong)
                                      (Etempvar _out tulong))
                                    (Ssequence
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _flags tint)
                                        (Etempvar _flags tint))
                                      (Ssequence
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                              (Tstruct _inflate_state noattr))
                                            _wrap tint)
                                          (Etempvar _wrap tint))
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                                (Tstruct _inflate_state noattr))
                                              _mode tint)
                                            (Econst_int (Int.repr 16191) tint))
                                          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))
|}.

Definition f_inflateSyncPoint := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'5, (tptr (Tstruct _internal_state noattr))) ::
               (_t'4, tuint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'5 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _mode tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tint)
                       (Econst_int (Int.repr 16193) tint) tint)
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _bits tuint))
            (Sset _t'2
              (Ecast
                (Ebinop Oeq (Etempvar _t'4 tuint)
                  (Econst_int (Int.repr 0) tint) tint) tbool)))
          (Sset _t'2 (Econst_int (Int.repr 0) tint))))
      (Sreturn (Some (Etempvar _t'2 tint))))))
|}.

Definition f_inflateCopy := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr (Tstruct _z_stream_s noattr))) ::
                (_source, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_copy, (tptr (Tstruct _inflate_state noattr))) ::
               (_window, (tptr tuchar)) :: (_t'5, tint) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'21, (tptr (Tstruct _internal_state noattr))) ::
               (_t'20, (tptr tvoid)) ::
               (_t'19,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) :: (_t'18, tuint) ::
               (_t'17, (tptr tvoid)) ::
               (_t'16,
                (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                        (tptr tvoid) cc_default))) ::
               (_t'15, (tptr tvoid)) ::
               (_t'14,
                (tptr (Tfunction ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                        cc_default))) :: (_t'13, (tptr tuchar)) ::
               (_t'12, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'11, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'10, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'9, (tptr (Tstruct ___gp_code noattr))) ::
               (_t'8, (tptr (Tstruct ___gp_code noattr))) :: (_t'7, tuint) ::
               (_t'6, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _inflateStateCheck (Tfunction
                                   ((tptr (Tstruct _z_stream_s noattr)) ::
                                    nil) tint cc_default))
        ((Etempvar _source (tptr (Tstruct _z_stream_s noattr))) :: nil))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Sset _t'2
          (Ecast
            (Ebinop Oeq (Etempvar _dest (tptr (Tstruct _z_stream_s noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
            tbool))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'21
        (Efield
          (Ederef (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'21 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'19
            (Efield
              (Ederef (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                (Tstruct _z_stream_s noattr)) _zalloc
              (tptr (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                      (tptr tvoid) cc_default))))
          (Ssequence
            (Sset _t'20
              (Efield
                (Ederef
                  (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                  (Tstruct _z_stream_s noattr)) _opaque (tptr tvoid)))
            (Scall (Some _t'3)
              (Ederef
                (Etempvar _t'19 (tptr (Tfunction
                                        ((tptr tvoid) :: tuint :: tuint ::
                                         nil) (tptr tvoid) cc_default)))
                (Tfunction ((tptr tvoid) :: tuint :: tuint :: nil)
                  (tptr tvoid) cc_default))
              ((Etempvar _t'20 (tptr tvoid)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Esizeof (Tstruct _inflate_state noattr) tulong) :: nil))))
        (Sset _copy
          (Ecast (Etempvar _t'3 (tptr tvoid))
            (tptr (Tstruct _inflate_state noattr)))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq
                       (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 4) tint) tint)))
          Sskip)
        (Ssequence
          (Scall None
            (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                            (tptr tvoid) cc_default))
            ((Etempvar _copy (tptr (Tstruct _inflate_state noattr))) ::
             (Econst_int (Int.repr 0) tint) ::
             (Esizeof (Tstruct _inflate_state noattr) tulong) :: nil))
          (Ssequence
            (Sset _window
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tuchar)))
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                      (Tstruct _inflate_state noattr)) _window (tptr tuchar)))
                (Sifthenelse (Ebinop One (Etempvar _t'13 (tptr tuchar))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'16
                          (Efield
                            (Ederef
                              (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                              (Tstruct _z_stream_s noattr)) _zalloc
                            (tptr (Tfunction
                                    ((tptr tvoid) :: tuint :: tuint :: nil)
                                    (tptr tvoid) cc_default))))
                        (Ssequence
                          (Sset _t'17
                            (Efield
                              (Ederef
                                (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                                (Tstruct _z_stream_s noattr)) _opaque
                              (tptr tvoid)))
                          (Ssequence
                            (Sset _t'18
                              (Efield
                                (Ederef
                                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _wbits
                                tuint))
                            (Scall (Some _t'4)
                              (Ederef
                                (Etempvar _t'16 (tptr (Tfunction
                                                        ((tptr tvoid) ::
                                                         tuint :: tuint ::
                                                         nil) (tptr tvoid)
                                                        cc_default)))
                                (Tfunction
                                  ((tptr tvoid) :: tuint :: tuint :: nil)
                                  (tptr tvoid) cc_default))
                              ((Etempvar _t'17 (tptr tvoid)) ::
                               (Ebinop Oshl (Econst_int (Int.repr 1) tuint)
                                 (Etempvar _t'18 tuint) tuint) ::
                               (Esizeof tuchar tulong) :: nil)))))
                      (Sset _window
                        (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tuchar))))
                    (Sifthenelse (Ebinop Oeq (Etempvar _window (tptr tuchar))
                                   (Ecast (Econst_int (Int.repr 0) tint)
                                     (tptr tvoid)) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _t'14
                            (Efield
                              (Ederef
                                (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                                (Tstruct _z_stream_s noattr)) _zfree
                              (tptr (Tfunction
                                      ((tptr tvoid) :: (tptr tvoid) :: nil)
                                      tvoid cc_default))))
                          (Ssequence
                            (Sset _t'15
                              (Efield
                                (Ederef
                                  (Etempvar _source (tptr (Tstruct _z_stream_s noattr)))
                                  (Tstruct _z_stream_s noattr)) _opaque
                                (tptr tvoid)))
                            (Scall None
                              (Ederef
                                (Etempvar _t'14 (tptr (Tfunction
                                                        ((tptr tvoid) ::
                                                         (tptr tvoid) :: nil)
                                                        tvoid cc_default)))
                                (Tfunction
                                  ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
                                  cc_default))
                              ((Etempvar _t'15 (tptr tvoid)) ::
                               (Ecast
                                 (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                 (tptr tvoid)) :: nil))))
                        (Sreturn (Some (Eunop Oneg
                                         (Econst_int (Int.repr 4) tint) tint))))
                      Sskip))
                  Sskip))
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  ((tptr tvoid) :: (tptr tvoid) :: tulong ::
                                   nil) (tptr tvoid) cc_default))
                  ((Etempvar _dest (tptr (Tstruct _z_stream_s noattr))) ::
                   (Etempvar _source (tptr (Tstruct _z_stream_s noattr))) ::
                   (Esizeof (Tstruct _z_stream_s noattr) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) ::
                                     tulong :: nil) (tptr tvoid) cc_default))
                    ((Etempvar _copy (tptr (Tstruct _inflate_state noattr))) ::
                     (Etempvar _state (tptr (Tstruct _inflate_state noattr))) ::
                     (Esizeof (Tstruct _inflate_state noattr) tulong) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _strm
                        (tptr (Tstruct _z_stream_s noattr)))
                      (Etempvar _dest (tptr (Tstruct _z_stream_s noattr))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'11
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _lencode
                              (tptr (Tstruct ___gp_code noattr))))
                          (Sifthenelse (Ebinop Oge
                                         (Etempvar _t'11 (tptr (Tstruct ___gp_code noattr)))
                                         (Efield
                                           (Ederef
                                             (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                             (Tstruct _inflate_state noattr))
                                           _codes
                                           (tarray (Tstruct ___gp_code noattr) 1444))
                                         tint)
                            (Ssequence
                              (Sset _t'12
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _lencode
                                  (tptr (Tstruct ___gp_code noattr))))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Ole
                                    (Etempvar _t'12 (tptr (Tstruct ___gp_code noattr)))
                                    (Ebinop Osub
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                            (Tstruct _inflate_state noattr))
                                          _codes
                                          (tarray (Tstruct ___gp_code noattr) 1444))
                                        (Ebinop Oadd
                                          (Econst_int (Int.repr 852) tint)
                                          (Econst_int (Int.repr 592) tint)
                                          tint)
                                        (tptr (Tstruct ___gp_code noattr)))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr (Tstruct ___gp_code noattr)))
                                    tint) tbool)))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Ssequence
                              (Sset _t'10
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _lencode
                                  (tptr (Tstruct ___gp_code noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _lencode
                                  (tptr (Tstruct ___gp_code noattr)))
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _codes
                                    (tarray (Tstruct ___gp_code noattr) 1444))
                                  (Ebinop Osub
                                    (Etempvar _t'10 (tptr (Tstruct ___gp_code noattr)))
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _codes
                                      (tarray (Tstruct ___gp_code noattr) 1444))
                                    tlong)
                                  (tptr (Tstruct ___gp_code noattr)))))
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr))
                                  _distcode
                                  (tptr (Tstruct ___gp_code noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr))
                                  _distcode
                                  (tptr (Tstruct ___gp_code noattr)))
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _codes
                                    (tarray (Tstruct ___gp_code noattr) 1444))
                                  (Ebinop Osub
                                    (Etempvar _t'9 (tptr (Tstruct ___gp_code noattr)))
                                    (Efield
                                      (Ederef
                                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                        (Tstruct _inflate_state noattr))
                                      _codes
                                      (tarray (Tstruct ___gp_code noattr) 1444))
                                    tlong)
                                  (tptr (Tstruct ___gp_code noattr))))))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Sset _t'8
                            (Efield
                              (Ederef
                                (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _next
                              (tptr (Tstruct ___gp_code noattr))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                (Tstruct _inflate_state noattr)) _next
                              (tptr (Tstruct ___gp_code noattr)))
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _codes
                                (tarray (Tstruct ___gp_code noattr) 1444))
                              (Ebinop Osub
                                (Etempvar _t'8 (tptr (Tstruct ___gp_code noattr)))
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _codes
                                  (tarray (Tstruct ___gp_code noattr) 1444))
                                tlong) (tptr (Tstruct ___gp_code noattr)))))
                        (Ssequence
                          (Sifthenelse (Ebinop One
                                         (Etempvar _window (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Ssequence
                              (Sset _t'6
                                (Efield
                                  (Ederef
                                    (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                    (Tstruct _inflate_state noattr)) _window
                                  (tptr tuchar)))
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Ederef
                                      (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                                      (Tstruct _inflate_state noattr)) _whave
                                    tuint))
                                (Scall None
                                  (Evar _memcpy (Tfunction
                                                  ((tptr tvoid) ::
                                                   (tptr tvoid) :: tulong ::
                                                   nil) (tptr tvoid)
                                                  cc_default))
                                  ((Etempvar _window (tptr tuchar)) ::
                                   (Etempvar _t'6 (tptr tuchar)) ::
                                   (Etempvar _t'7 tuint) :: nil))))
                            Sskip)
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                  (Tstruct _inflate_state noattr)) _window
                                (tptr tuchar))
                              (Etempvar _window (tptr tuchar)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _dest (tptr (Tstruct _z_stream_s noattr)))
                                    (Tstruct _z_stream_s noattr)) _state
                                  (tptr (Tstruct _internal_state noattr)))
                                (Ecast
                                  (Etempvar _copy (tptr (Tstruct _inflate_state noattr)))
                                  (tptr (Tstruct _internal_state noattr))))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))
|}.

Definition f_inflateUndermine := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_subvert, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'1, tint) ::
               (_t'2, (tptr (Tstruct _internal_state noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'2 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
            (Tstruct _inflate_state noattr)) _sane tint)
        (Econst_int (Int.repr 1) tint))
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 3) tint) tint))))))
|}.

Definition f_inflateValidate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) ::
                (_check, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'6, (tptr (Tstruct _internal_state noattr))) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 2) tint) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'6
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'6 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _check tint)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wrap tint))
            (Sset _t'2 (Ecast (Etempvar _t'5 tint) tbool)))
          (Sset _t'2 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wrap tint))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wrap tint)
              (Ebinop Oor (Etempvar _t'4 tint) (Econst_int (Int.repr 4) tint)
                tint)))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wrap tint))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _wrap tint)
              (Ebinop Oand (Etempvar _t'3 tint)
                (Eunop Onotint (Econst_int (Int.repr 4) tint) tint) tint)))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_inflateMark := {|
  fn_return := tlong;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'2, tuint) :: (_t'1, tint) ::
               (_t'9, (tptr (Tstruct _internal_state noattr))) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Eunop Oneg
                       (Ebinop Oshl (Econst_long (Int64.repr 1) tlong)
                         (Econst_int (Int.repr 16) tint) tlong) tlong)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'9 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _mode tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tint)
                       (Econst_int (Int.repr 16195) tint) tint)
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _length tuint))
            (Sset _t'2 (Ecast (Etempvar _t'8 tuint) tuint)))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                  (Tstruct _inflate_state noattr)) _mode tint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tint)
                           (Econst_int (Int.repr 16204) tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                        (Tstruct _inflate_state noattr)) _was tuint))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef
                          (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                          (Tstruct _inflate_state noattr)) _length tuint))
                    (Sset _t'2
                      (Ecast
                        (Ebinop Osub (Etempvar _t'6 tuint)
                          (Etempvar _t'7 tuint) tuint) tuint))))
                (Sset _t'2 (Ecast (Etempvar _t'2 tuint) tuint)))
              (Ssequence
                (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tuint))
                (Sset _t'2 (Ecast (Etempvar _t'2 tuint) tuint)))))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
              (Tstruct _inflate_state noattr)) _back tint))
        (Sreturn (Some (Ebinop Oadd
                         (Ecast
                           (Ebinop Oshl
                             (Ecast (Ecast (Etempvar _t'3 tint) tlong)
                               tulong) (Econst_int (Int.repr 16) tint)
                             tulong) tlong) (Etempvar _t'2 tuint) tlong)))))))
|}.

Definition f_inflateCodesUsed := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_strm, (tptr (Tstruct _z_stream_s noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_state, (tptr (Tstruct _inflate_state noattr))) ::
               (_t'1, tint) ::
               (_t'3, (tptr (Tstruct _internal_state noattr))) ::
               (_t'2, (tptr (Tstruct ___gp_code noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _inflateStateCheck (Tfunction
                                 ((tptr (Tstruct _z_stream_s noattr)) :: nil)
                                 tint cc_default))
      ((Etempvar _strm (tptr (Tstruct _z_stream_s noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                       tulong)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _strm (tptr (Tstruct _z_stream_s noattr)))
            (Tstruct _z_stream_s noattr)) _state
          (tptr (Tstruct _internal_state noattr))))
      (Sset _state
        (Ecast (Etempvar _t'3 (tptr (Tstruct _internal_state noattr)))
          (tptr (Tstruct _inflate_state noattr)))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
            (Tstruct _inflate_state noattr)) _next
          (tptr (Tstruct ___gp_code noattr))))
      (Sreturn (Some (Ecast
                       (Ebinop Osub
                         (Etempvar _t'2 (tptr (Tstruct ___gp_code noattr)))
                         (Efield
                           (Ederef
                             (Etempvar _state (tptr (Tstruct _inflate_state noattr)))
                             (Tstruct _inflate_state noattr)) _codes
                           (tarray (Tstruct ___gp_code noattr) 1444)) tlong)
                       tulong))))))
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
 Composite ___gp_code Struct
   (Member_plain _op tuchar :: Member_plain _bits tuchar ::
    Member_plain _val tushort :: nil)
   noattr ::
 Composite _inflate_state Struct
   (Member_plain _strm (tptr (Tstruct _z_stream_s noattr)) ::
    Member_plain _mode tint :: Member_plain _last tint ::
    Member_plain _wrap tint :: Member_plain _havedict tint ::
    Member_plain _flags tint :: Member_plain _dmax tuint ::
    Member_plain _check tulong :: Member_plain _total tulong ::
    Member_plain _head (tptr (Tstruct _gz_header_s noattr)) ::
    Member_plain _wbits tuint :: Member_plain _wsize tuint ::
    Member_plain _whave tuint :: Member_plain _wnext tuint ::
    Member_plain _window (tptr tuchar) :: Member_plain _hold tulong ::
    Member_plain _bits tuint :: Member_plain _length tuint ::
    Member_plain _offset tuint :: Member_plain _extra tuint ::
    Member_plain _lencode (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _distcode (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _lenbits tuint :: Member_plain _distbits tuint ::
    Member_plain _ncode tuint :: Member_plain _nlen tuint ::
    Member_plain _ndist tuint :: Member_plain _have tuint ::
    Member_plain _next (tptr (Tstruct ___gp_code noattr)) ::
    Member_plain _lens (tarray tushort 320) ::
    Member_plain _work (tarray tushort 288) ::
    Member_plain _codes (tarray (Tstruct ___gp_code noattr) 1444) ::
    Member_plain _sane tint :: Member_plain _back tint ::
    Member_plain _was tuint :: nil)
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
     cc_default)) :: (___stringlit_inflate_5, Gvar v___stringlit_inflate_5) ::
 (___stringlit_inflate_10, Gvar v___stringlit_inflate_10) ::
 (___stringlit_inflate_15, Gvar v___stringlit_inflate_15) ::
 (___stringlit_inflate_7, Gvar v___stringlit_inflate_7) ::
 (___stringlit_inflate_14, Gvar v___stringlit_inflate_14) ::
 (___stringlit_inflate_6, Gvar v___stringlit_inflate_6) ::
 (___stringlit_inflate_8, Gvar v___stringlit_inflate_8) ::
 (___stringlit_inflate_2, Gvar v___stringlit_inflate_2) ::
 (___stringlit_inflate_13, Gvar v___stringlit_inflate_13) ::
 (___stringlit_inflate_17, Gvar v___stringlit_inflate_17) ::
 (___stringlit_inflate_12, Gvar v___stringlit_inflate_12) ::
 (___stringlit_inflate_18, Gvar v___stringlit_inflate_18) ::
 (___stringlit_inflate_3, Gvar v___stringlit_inflate_3) ::
 (___stringlit_inflate_9, Gvar v___stringlit_inflate_9) ::
 (___stringlit_inflate_16, Gvar v___stringlit_inflate_16) ::
 (___stringlit_inflate_4, Gvar v___stringlit_inflate_4) ::
 (___stringlit_inflate_19, Gvar v___stringlit_inflate_19) ::
 (___stringlit_inflate_1, Gvar v___stringlit_inflate_1) ::
 (___stringlit_inflate_11, Gvar v___stringlit_inflate_11) ::
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
 (_adler32,
   Gfun(External (EF_external "adler32"
                   (mksignature (AST.Xlong :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ::
 (_crc32,
   Gfun(External (EF_external "crc32"
                   (mksignature (AST.Xlong :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xlong cc_default))
     (tulong :: (tptr tuchar) :: tuint :: nil) tulong cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
 (_zcalloc,
   Gfun(External (EF_external "zcalloc"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tuint :: tuint :: nil) (tptr tvoid) cc_default)) ::
 (_zcfree,
   Gfun(External (EF_external "zcfree"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (_inflate_table,
   Gfun(External (EF_external "inflate_table"
                   (mksignature
                     (AST.Xint :: AST.Xptr :: AST.Xint :: AST.Xptr ::
                      AST.Xptr :: AST.Xptr :: nil) AST.Xint cc_default))
     (tint :: (tptr tushort) :: tuint ::
      (tptr (tptr (Tstruct ___gp_code noattr))) :: (tptr tuint) ::
      (tptr tushort) :: nil) tint cc_default)) ::
 (_inflate_fixed,
   Gfun(External (EF_external "inflate_fixed"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _inflate_state noattr)) :: nil) tvoid cc_default)) ::
 (_inflate_fast,
   Gfun(External (EF_external "inflate_fast"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _z_stream_s noattr)) :: tuint :: nil) tvoid cc_default)) ::
 (_inflateStateCheck, Gfun(Internal f_inflateStateCheck)) ::
 (_inflateResetKeep, Gfun(Internal f_inflateResetKeep)) ::
 (_inflateReset, Gfun(Internal f_inflateReset)) ::
 (_inflateReset2, Gfun(Internal f_inflateReset2)) ::
 (_inflateInit2_, Gfun(Internal f_inflateInit2_)) ::
 (_inflateInit_, Gfun(Internal f_inflateInit_)) ::
 (_inflatePrime, Gfun(Internal f_inflatePrime)) ::
 (_updatewindow, Gfun(Internal f_updatewindow)) :: (_order, Gvar v_order) ::
 (_inflate, Gfun(Internal f_inflate)) ::
 (_inflateEnd, Gfun(Internal f_inflateEnd)) ::
 (_inflateGetDictionary, Gfun(Internal f_inflateGetDictionary)) ::
 (_inflateSetDictionary, Gfun(Internal f_inflateSetDictionary)) ::
 (_inflateGetHeader, Gfun(Internal f_inflateGetHeader)) ::
 (_syncsearch, Gfun(Internal f_syncsearch)) ::
 (_inflateSync, Gfun(Internal f_inflateSync)) ::
 (_inflateSyncPoint, Gfun(Internal f_inflateSyncPoint)) ::
 (_inflateCopy, Gfun(Internal f_inflateCopy)) ::
 (_inflateUndermine, Gfun(Internal f_inflateUndermine)) ::
 (_inflateValidate, Gfun(Internal f_inflateValidate)) ::
 (_inflateMark, Gfun(Internal f_inflateMark)) ::
 (_inflateCodesUsed, Gfun(Internal f_inflateCodesUsed)) :: nil).

Definition public_idents : list ident :=
(_inflateCodesUsed :: _inflateMark :: _inflateValidate ::
 _inflateUndermine :: _inflateCopy :: _inflateSyncPoint :: _inflateSync ::
 _inflateGetHeader :: _inflateSetDictionary :: _inflateGetDictionary ::
 _inflateEnd :: _inflate :: _inflatePrime :: _inflateInit_ ::
 _inflateInit2_ :: _inflateReset2 :: _inflateReset :: _inflateResetKeep ::
 _inflate_fast :: _inflate_fixed :: _inflate_table :: _zcfree :: _zcalloc ::
 _memset :: _memcpy :: _crc32 :: _adler32 :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


