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
  Definition source_file := "crc32.c".
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
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _crc : ident := $"crc".
Definition _crc1 : ident := $"crc1".
Definition _crc2 : ident := $"crc2".
Definition _crc32 : ident := $"crc32".
Definition _crc32_combine : ident := $"crc32_combine".
Definition _crc32_combine64 : ident := $"crc32_combine64".
Definition _crc32_combine_gen : ident := $"crc32_combine_gen".
Definition _crc32_combine_gen64 : ident := $"crc32_combine_gen64".
Definition _crc32_combine_op : ident := $"crc32_combine_op".
Definition _crc32_z : ident := $"crc32_z".
Definition _crc_table : ident := $"crc_table".
Definition _get_crc_table : ident := $"get_crc_table".
Definition _k : ident := $"k".
Definition _len : ident := $"len".
Definition _len2 : ident := $"len2".
Definition _m : ident := $"m".
Definition _main : ident := $"main".
Definition _multmodp : ident := $"multmodp".
Definition _n : ident := $"n".
Definition _op : ident := $"op".
Definition _p : ident := $"p".
Definition _x2n_table : ident := $"x2n_table".
Definition _x2nmodp : ident := $"x2nmodp".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_crc_table := {|
  gvar_info := (tarray tuint 256);
  gvar_init := (Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 1996959894) ::
                Init_int32 (Int.repr (-301047508)) ::
                Init_int32 (Int.repr (-1727442502)) ::
                Init_int32 (Int.repr 124634137) ::
                Init_int32 (Int.repr 1886057615) ::
                Init_int32 (Int.repr (-379345611)) ::
                Init_int32 (Int.repr (-1637575261)) ::
                Init_int32 (Int.repr 249268274) ::
                Init_int32 (Int.repr 2044508324) ::
                Init_int32 (Int.repr (-522852066)) ::
                Init_int32 (Int.repr (-1747789432)) ::
                Init_int32 (Int.repr 162941995) ::
                Init_int32 (Int.repr 2125561021) ::
                Init_int32 (Int.repr (-407360249)) ::
                Init_int32 (Int.repr (-1866523247)) ::
                Init_int32 (Int.repr 498536548) ::
                Init_int32 (Int.repr 1789927666) ::
                Init_int32 (Int.repr (-205950648)) ::
                Init_int32 (Int.repr (-2067906082)) ::
                Init_int32 (Int.repr 450548861) ::
                Init_int32 (Int.repr 1843258603) ::
                Init_int32 (Int.repr (-187386543)) ::
                Init_int32 (Int.repr (-2083289657)) ::
                Init_int32 (Int.repr 325883990) ::
                Init_int32 (Int.repr 1684777152) ::
                Init_int32 (Int.repr (-43845254)) ::
                Init_int32 (Int.repr (-1973040660)) ::
                Init_int32 (Int.repr 335633487) ::
                Init_int32 (Int.repr 1661365465) ::
                Init_int32 (Int.repr (-99664541)) ::
                Init_int32 (Int.repr (-1928851979)) ::
                Init_int32 (Int.repr 997073096) ::
                Init_int32 (Int.repr 1281953886) ::
                Init_int32 (Int.repr (-715111964)) ::
                Init_int32 (Int.repr (-1570279054)) ::
                Init_int32 (Int.repr 1006888145) ::
                Init_int32 (Int.repr 1258607687) ::
                Init_int32 (Int.repr (-770865667)) ::
                Init_int32 (Int.repr (-1526024853)) ::
                Init_int32 (Int.repr 901097722) ::
                Init_int32 (Int.repr 1119000684) ::
                Init_int32 (Int.repr (-608450090)) ::
                Init_int32 (Int.repr (-1396901568)) ::
                Init_int32 (Int.repr 853044451) ::
                Init_int32 (Int.repr 1172266101) ::
                Init_int32 (Int.repr (-589951537)) ::
                Init_int32 (Int.repr (-1412350631)) ::
                Init_int32 (Int.repr 651767980) ::
                Init_int32 (Int.repr 1373503546) ::
                Init_int32 (Int.repr (-925412992)) ::
                Init_int32 (Int.repr (-1076862698)) ::
                Init_int32 (Int.repr 565507253) ::
                Init_int32 (Int.repr 1454621731) ::
                Init_int32 (Int.repr (-809855591)) ::
                Init_int32 (Int.repr (-1195530993)) ::
                Init_int32 (Int.repr 671266974) ::
                Init_int32 (Int.repr 1594198024) ::
                Init_int32 (Int.repr (-972236366)) ::
                Init_int32 (Int.repr (-1324619484)) ::
                Init_int32 (Int.repr 795835527) ::
                Init_int32 (Int.repr 1483230225) ::
                Init_int32 (Int.repr (-1050600021)) ::
                Init_int32 (Int.repr (-1234817731)) ::
                Init_int32 (Int.repr 1994146192) ::
                Init_int32 (Int.repr 31158534) ::
                Init_int32 (Int.repr (-1731059524)) ::
                Init_int32 (Int.repr (-271249366)) ::
                Init_int32 (Int.repr 1907459465) ::
                Init_int32 (Int.repr 112637215) ::
                Init_int32 (Int.repr (-1614814043)) ::
                Init_int32 (Int.repr (-390540237)) ::
                Init_int32 (Int.repr 2013776290) ::
                Init_int32 (Int.repr 251722036) ::
                Init_int32 (Int.repr (-1777751922)) ::
                Init_int32 (Int.repr (-519137256)) ::
                Init_int32 (Int.repr 2137656763) ::
                Init_int32 (Int.repr 141376813) ::
                Init_int32 (Int.repr (-1855689577)) ::
                Init_int32 (Int.repr (-429695999)) ::
                Init_int32 (Int.repr 1802195444) ::
                Init_int32 (Int.repr 476864866) ::
                Init_int32 (Int.repr (-2056965928)) ::
                Init_int32 (Int.repr (-228458418)) ::
                Init_int32 (Int.repr 1812370925) ::
                Init_int32 (Int.repr 453092731) ::
                Init_int32 (Int.repr (-2113342271)) ::
                Init_int32 (Int.repr (-183516073)) ::
                Init_int32 (Int.repr 1706088902) ::
                Init_int32 (Int.repr 314042704) ::
                Init_int32 (Int.repr (-1950435094)) ::
                Init_int32 (Int.repr (-54949764)) ::
                Init_int32 (Int.repr 1658658271) ::
                Init_int32 (Int.repr 366619977) ::
                Init_int32 (Int.repr (-1932296973)) ::
                Init_int32 (Int.repr (-69972891)) ::
                Init_int32 (Int.repr 1303535960) ::
                Init_int32 (Int.repr 984961486) ::
                Init_int32 (Int.repr (-1547960204)) ::
                Init_int32 (Int.repr (-725929758)) ::
                Init_int32 (Int.repr 1256170817) ::
                Init_int32 (Int.repr 1037604311) ::
                Init_int32 (Int.repr (-1529756563)) ::
                Init_int32 (Int.repr (-740887301)) ::
                Init_int32 (Int.repr 1131014506) ::
                Init_int32 (Int.repr 879679996) ::
                Init_int32 (Int.repr (-1385723834)) ::
                Init_int32 (Int.repr (-631195440)) ::
                Init_int32 (Int.repr 1141124467) ::
                Init_int32 (Int.repr 855842277) ::
                Init_int32 (Int.repr (-1442165665)) ::
                Init_int32 (Int.repr (-586318647)) ::
                Init_int32 (Int.repr 1342533948) ::
                Init_int32 (Int.repr 654459306) ::
                Init_int32 (Int.repr (-1106571248)) ::
                Init_int32 (Int.repr (-921952122)) ::
                Init_int32 (Int.repr 1466479909) ::
                Init_int32 (Int.repr 544179635) ::
                Init_int32 (Int.repr (-1184443383)) ::
                Init_int32 (Int.repr (-832445281)) ::
                Init_int32 (Int.repr 1591671054) ::
                Init_int32 (Int.repr 702138776) ::
                Init_int32 (Int.repr (-1328506846)) ::
                Init_int32 (Int.repr (-942167884)) ::
                Init_int32 (Int.repr 1504918807) ::
                Init_int32 (Int.repr 783551873) ::
                Init_int32 (Int.repr (-1212326853)) ::
                Init_int32 (Int.repr (-1061524307)) ::
                Init_int32 (Int.repr (-306674912)) ::
                Init_int32 (Int.repr (-1698712650)) ::
                Init_int32 (Int.repr 62317068) ::
                Init_int32 (Int.repr 1957810842) ::
                Init_int32 (Int.repr (-355121351)) ::
                Init_int32 (Int.repr (-1647151185)) ::
                Init_int32 (Int.repr 81470997) ::
                Init_int32 (Int.repr 1943803523) ::
                Init_int32 (Int.repr (-480048366)) ::
                Init_int32 (Int.repr (-1805370492)) ::
                Init_int32 (Int.repr 225274430) ::
                Init_int32 (Int.repr 2053790376) ::
                Init_int32 (Int.repr (-468791541)) ::
                Init_int32 (Int.repr (-1828061283)) ::
                Init_int32 (Int.repr 167816743) ::
                Init_int32 (Int.repr 2097651377) ::
                Init_int32 (Int.repr (-267414716)) ::
                Init_int32 (Int.repr (-2029476910)) ::
                Init_int32 (Int.repr 503444072) ::
                Init_int32 (Int.repr 1762050814) ::
                Init_int32 (Int.repr (-144550051)) ::
                Init_int32 (Int.repr (-2140837941)) ::
                Init_int32 (Int.repr 426522225) ::
                Init_int32 (Int.repr 1852507879) ::
                Init_int32 (Int.repr (-19653770)) ::
                Init_int32 (Int.repr (-1982649376)) ::
                Init_int32 (Int.repr 282753626) ::
                Init_int32 (Int.repr 1742555852) ::
                Init_int32 (Int.repr (-105259153)) ::
                Init_int32 (Int.repr (-1900089351)) ::
                Init_int32 (Int.repr 397917763) ::
                Init_int32 (Int.repr 1622183637) ::
                Init_int32 (Int.repr (-690576408)) ::
                Init_int32 (Int.repr (-1580100738)) ::
                Init_int32 (Int.repr 953729732) ::
                Init_int32 (Int.repr 1340076626) ::
                Init_int32 (Int.repr (-776247311)) ::
                Init_int32 (Int.repr (-1497606297)) ::
                Init_int32 (Int.repr 1068828381) ::
                Init_int32 (Int.repr 1219638859) ::
                Init_int32 (Int.repr (-670225446)) ::
                Init_int32 (Int.repr (-1358292148)) ::
                Init_int32 (Int.repr 906185462) ::
                Init_int32 (Int.repr 1090812512) ::
                Init_int32 (Int.repr (-547295293)) ::
                Init_int32 (Int.repr (-1469587627)) ::
                Init_int32 (Int.repr 829329135) ::
                Init_int32 (Int.repr 1181335161) ::
                Init_int32 (Int.repr (-882789492)) ::
                Init_int32 (Int.repr (-1134132454)) ::
                Init_int32 (Int.repr 628085408) ::
                Init_int32 (Int.repr 1382605366) ::
                Init_int32 (Int.repr (-871598187)) ::
                Init_int32 (Int.repr (-1156888829)) ::
                Init_int32 (Int.repr 570562233) ::
                Init_int32 (Int.repr 1426400815) ::
                Init_int32 (Int.repr (-977650754)) ::
                Init_int32 (Int.repr (-1296233688)) ::
                Init_int32 (Int.repr 733239954) ::
                Init_int32 (Int.repr 1555261956) ::
                Init_int32 (Int.repr (-1026031705)) ::
                Init_int32 (Int.repr (-1244606671)) ::
                Init_int32 (Int.repr 752459403) ::
                Init_int32 (Int.repr 1541320221) ::
                Init_int32 (Int.repr (-1687895376)) ::
                Init_int32 (Int.repr (-328994266)) ::
                Init_int32 (Int.repr 1969922972) ::
                Init_int32 (Int.repr 40735498) ::
                Init_int32 (Int.repr (-1677130071)) ::
                Init_int32 (Int.repr (-351390145)) ::
                Init_int32 (Int.repr 1913087877) ::
                Init_int32 (Int.repr 83908371) ::
                Init_int32 (Int.repr (-1782625662)) ::
                Init_int32 (Int.repr (-491226604)) ::
                Init_int32 (Int.repr 2075208622) ::
                Init_int32 (Int.repr 213261112) ::
                Init_int32 (Int.repr (-1831694693)) ::
                Init_int32 (Int.repr (-438977011)) ::
                Init_int32 (Int.repr 2094854071) ::
                Init_int32 (Int.repr 198958881) ::
                Init_int32 (Int.repr (-2032938284)) ::
                Init_int32 (Int.repr (-237706686)) ::
                Init_int32 (Int.repr 1759359992) ::
                Init_int32 (Int.repr 534414190) ::
                Init_int32 (Int.repr (-2118248755)) ::
                Init_int32 (Int.repr (-155638181)) ::
                Init_int32 (Int.repr 1873836001) ::
                Init_int32 (Int.repr 414664567) ::
                Init_int32 (Int.repr (-2012718362)) ::
                Init_int32 (Int.repr (-15766928)) ::
                Init_int32 (Int.repr 1711684554) ::
                Init_int32 (Int.repr 285281116) ::
                Init_int32 (Int.repr (-1889165569)) ::
                Init_int32 (Int.repr (-127750551)) ::
                Init_int32 (Int.repr 1634467795) ::
                Init_int32 (Int.repr 376229701) ::
                Init_int32 (Int.repr (-1609899400)) ::
                Init_int32 (Int.repr (-686959890)) ::
                Init_int32 (Int.repr 1308918612) ::
                Init_int32 (Int.repr 956543938) ::
                Init_int32 (Int.repr (-1486412191)) ::
                Init_int32 (Int.repr (-799009033)) ::
                Init_int32 (Int.repr 1231636301) ::
                Init_int32 (Int.repr 1047427035) ::
                Init_int32 (Int.repr (-1362007478)) ::
                Init_int32 (Int.repr (-640263460)) ::
                Init_int32 (Int.repr 1088359270) ::
                Init_int32 (Int.repr 936918000) ::
                Init_int32 (Int.repr (-1447252397)) ::
                Init_int32 (Int.repr (-558129467)) ::
                Init_int32 (Int.repr 1202900863) ::
                Init_int32 (Int.repr 817233897) ::
                Init_int32 (Int.repr (-1111625188)) ::
                Init_int32 (Int.repr (-893730166)) ::
                Init_int32 (Int.repr 1404277552) ::
                Init_int32 (Int.repr 615818150) ::
                Init_int32 (Int.repr (-1160759803)) ::
                Init_int32 (Int.repr (-841546093)) ::
                Init_int32 (Int.repr 1423857449) ::
                Init_int32 (Int.repr 601450431) ::
                Init_int32 (Int.repr (-1285129682)) ::
                Init_int32 (Int.repr (-1000256840)) ::
                Init_int32 (Int.repr 1567103746) ::
                Init_int32 (Int.repr 711928724) ::
                Init_int32 (Int.repr (-1274298825)) ::
                Init_int32 (Int.repr (-1022587231)) ::
                Init_int32 (Int.repr 1510334235) ::
                Init_int32 (Int.repr 755167117) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x2n_table := {|
  gvar_info := (tarray tuint 32);
  gvar_init := (Init_int32 (Int.repr 1073741824) ::
                Init_int32 (Int.repr 536870912) ::
                Init_int32 (Int.repr 134217728) ::
                Init_int32 (Int.repr 8388608) ::
                Init_int32 (Int.repr 32768) ::
                Init_int32 (Int.repr (-306674912)) ::
                Init_int32 (Int.repr (-1310281582)) ::
                Init_int32 (Int.repr (-1603656425)) ::
                Init_int32 (Int.repr (-312312402)) ::
                Init_int32 (Int.repr (-1999551385)) ::
                Init_int32 (Int.repr (-675545494)) ::
                Init_int32 (Int.repr (-331055343)) ::
                Init_int32 (Int.repr (-1904303760)) ::
                Init_int32 (Int.repr 1680310286) ::
                Init_int32 (Int.repr 1296546528) ::
                Init_int32 (Int.repr 167662735) ::
                Init_int32 (Int.repr (-2088424177)) ::
                Init_int32 (Int.repr 808857370) ::
                Init_int32 (Int.repr 2069535939) ::
                Init_int32 (Int.repr 838779241) ::
                Init_int32 (Int.repr (-1611922902)) ::
                Init_int32 (Int.repr 1821240772) ::
                Init_int32 (Int.repr 366380877) ::
                Init_int32 (Int.repr 1608415822) ::
                Init_int32 (Int.repr (-1160180169)) ::
                Init_int32 (Int.repr 776888047) ::
                Init_int32 (Int.repr 1319870996) ::
                Init_int32 (Int.repr (-1465617728)) ::
                Init_int32 (Int.repr 1117427358) ::
                Init_int32 (Int.repr 344797226) ::
                Init_int32 (Int.repr (-1005869360)) ::
                Init_int32 (Int.repr (-991810500)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_multmodp := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, tulong) :: (_b, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_m, tulong) :: (_p, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _m
    (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tulong)
      (Econst_int (Int.repr 31) tint) tulong))
  (Ssequence
    (Sset _p (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Sifthenelse (Ebinop Oand (Etempvar _a tulong)
                           (Etempvar _m tulong) tulong)
              (Ssequence
                (Sset _p
                  (Ebinop Oxor (Etempvar _p tulong) (Etempvar _b tulong)
                    tulong))
                (Sifthenelse (Ebinop Oeq
                               (Ebinop Oand (Etempvar _a tulong)
                                 (Ebinop Osub (Etempvar _m tulong)
                                   (Econst_int (Int.repr 1) tint) tulong)
                                 tulong) (Econst_int (Int.repr 0) tint) tint)
                  Sbreak
                  Sskip))
              Sskip)
            (Ssequence
              (Sset _m
                (Ebinop Oshr (Etempvar _m tulong)
                  (Econst_int (Int.repr 1) tint) tulong))
              (Ssequence
                (Sifthenelse (Ebinop Oand (Etempvar _b tulong)
                               (Econst_int (Int.repr 1) tint) tulong)
                  (Sset _t'1
                    (Ecast
                      (Ebinop Oxor
                        (Ebinop Oshr (Etempvar _b tulong)
                          (Econst_int (Int.repr 1) tint) tulong)
                        (Econst_int (Int.repr (-306674912)) tuint) tulong)
                      tulong))
                  (Sset _t'1
                    (Ecast
                      (Ebinop Oshr (Etempvar _b tulong)
                        (Econst_int (Int.repr 1) tint) tulong) tulong)))
                (Sset _b (Etempvar _t'1 tulong))))))
        Sskip)
      (Sreturn (Some (Etempvar _p tulong))))))
|}.

Definition f_x2nmodp := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_n, tlong) :: (_k, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, tulong) :: (_t'1, tulong) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tulong)
      (Econst_int (Int.repr 31) tint) tulong))
  (Ssequence
    (Swhile
      (Etempvar _n tlong)
      (Ssequence
        (Sifthenelse (Ebinop Oand (Etempvar _n tlong)
                       (Econst_int (Int.repr 1) tint) tlong)
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _x2n_table (tarray tuint 32))
                    (Ebinop Oand (Etempvar _k tuint)
                      (Econst_int (Int.repr 31) tint) tuint) (tptr tuint))
                  tuint))
              (Scall (Some _t'1)
                (Evar _multmodp (Tfunction (tulong :: tulong :: nil) tulong
                                  cc_default))
                ((Etempvar _t'2 tuint) :: (Etempvar _p tulong) :: nil)))
            (Sset _p (Etempvar _t'1 tulong)))
          Sskip)
        (Ssequence
          (Sset _n
            (Ebinop Oshr (Etempvar _n tlong) (Econst_int (Int.repr 1) tint)
              tlong))
          (Sset _k
            (Ebinop Oadd (Etempvar _k tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))
    (Sreturn (Some (Etempvar _p tulong)))))
|}.

Definition f_get_crc_table := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Evar _crc_table (tarray tuint 256)) (tptr tuint))))
|}.

Definition f_crc32_z := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_crc, tulong) :: (_buf, (tptr tuchar)) :: (_len, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'9, (tptr tuchar)) :: (_t'8, (tptr tuchar)) ::
               (_t'7, (tptr tuchar)) :: (_t'6, (tptr tuchar)) ::
               (_t'5, (tptr tuchar)) :: (_t'4, (tptr tuchar)) ::
               (_t'3, (tptr tuchar)) :: (_t'2, (tptr tuchar)) ::
               (_t'1, (tptr tuchar)) :: (_t'27, tuint) :: (_t'26, tuchar) ::
               (_t'25, tuint) :: (_t'24, tuchar) :: (_t'23, tuint) ::
               (_t'22, tuchar) :: (_t'21, tuint) :: (_t'20, tuchar) ::
               (_t'19, tuint) :: (_t'18, tuchar) :: (_t'17, tuint) ::
               (_t'16, tuchar) :: (_t'15, tuint) :: (_t'14, tuchar) ::
               (_t'13, tuint) :: (_t'12, tuchar) :: (_t'11, tuint) ::
               (_t'10, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _buf (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sset _crc
      (Ebinop Oand (Eunop Onotint (Etempvar _crc tulong) tulong)
        (Econst_int (Int.repr (-1)) tuint) tulong))
    (Ssequence
      (Swhile
        (Ebinop Oge (Etempvar _len tulong) (Econst_int (Int.repr 8) tint)
          tint)
        (Ssequence
          (Sset _len
            (Ebinop Osub (Etempvar _len tulong)
              (Econst_int (Int.repr 8) tint) tulong))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'1 (Etempvar _buf (tptr tuchar)))
                (Sset _buf
                  (Ebinop Oadd (Etempvar _t'1 (tptr tuchar))
                    (Econst_int (Int.repr 1) tint) (tptr tuchar))))
              (Ssequence
                (Sset _t'26 (Ederef (Etempvar _t'1 (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'27
                    (Ederef
                      (Ebinop Oadd (Evar _crc_table (tarray tuint 256))
                        (Ebinop Oand
                          (Ebinop Oxor (Etempvar _crc tulong)
                            (Etempvar _t'26 tuchar) tulong)
                          (Econst_int (Int.repr 255) tint) tulong)
                        (tptr tuint)) tuint))
                  (Sset _crc
                    (Ebinop Oxor
                      (Ebinop Oshr (Etempvar _crc tulong)
                        (Econst_int (Int.repr 8) tint) tulong)
                      (Etempvar _t'27 tuint) tulong)))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'2 (Etempvar _buf (tptr tuchar)))
                  (Sset _buf
                    (Ebinop Oadd (Etempvar _t'2 (tptr tuchar))
                      (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                (Ssequence
                  (Sset _t'24 (Ederef (Etempvar _t'2 (tptr tuchar)) tuchar))
                  (Ssequence
                    (Sset _t'25
                      (Ederef
                        (Ebinop Oadd (Evar _crc_table (tarray tuint 256))
                          (Ebinop Oand
                            (Ebinop Oxor (Etempvar _crc tulong)
                              (Etempvar _t'24 tuchar) tulong)
                            (Econst_int (Int.repr 255) tint) tulong)
                          (tptr tuint)) tuint))
                    (Sset _crc
                      (Ebinop Oxor
                        (Ebinop Oshr (Etempvar _crc tulong)
                          (Econst_int (Int.repr 8) tint) tulong)
                        (Etempvar _t'25 tuint) tulong)))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'3 (Etempvar _buf (tptr tuchar)))
                    (Sset _buf
                      (Ebinop Oadd (Etempvar _t'3 (tptr tuchar))
                        (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                  (Ssequence
                    (Sset _t'22
                      (Ederef (Etempvar _t'3 (tptr tuchar)) tuchar))
                    (Ssequence
                      (Sset _t'23
                        (Ederef
                          (Ebinop Oadd (Evar _crc_table (tarray tuint 256))
                            (Ebinop Oand
                              (Ebinop Oxor (Etempvar _crc tulong)
                                (Etempvar _t'22 tuchar) tulong)
                              (Econst_int (Int.repr 255) tint) tulong)
                            (tptr tuint)) tuint))
                      (Sset _crc
                        (Ebinop Oxor
                          (Ebinop Oshr (Etempvar _crc tulong)
                            (Econst_int (Int.repr 8) tint) tulong)
                          (Etempvar _t'23 tuint) tulong)))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'4 (Etempvar _buf (tptr tuchar)))
                      (Sset _buf
                        (Ebinop Oadd (Etempvar _t'4 (tptr tuchar))
                          (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                    (Ssequence
                      (Sset _t'20
                        (Ederef (Etempvar _t'4 (tptr tuchar)) tuchar))
                      (Ssequence
                        (Sset _t'21
                          (Ederef
                            (Ebinop Oadd (Evar _crc_table (tarray tuint 256))
                              (Ebinop Oand
                                (Ebinop Oxor (Etempvar _crc tulong)
                                  (Etempvar _t'20 tuchar) tulong)
                                (Econst_int (Int.repr 255) tint) tulong)
                              (tptr tuint)) tuint))
                        (Sset _crc
                          (Ebinop Oxor
                            (Ebinop Oshr (Etempvar _crc tulong)
                              (Econst_int (Int.repr 8) tint) tulong)
                            (Etempvar _t'21 tuint) tulong)))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'5 (Etempvar _buf (tptr tuchar)))
                        (Sset _buf
                          (Ebinop Oadd (Etempvar _t'5 (tptr tuchar))
                            (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                      (Ssequence
                        (Sset _t'18
                          (Ederef (Etempvar _t'5 (tptr tuchar)) tuchar))
                        (Ssequence
                          (Sset _t'19
                            (Ederef
                              (Ebinop Oadd
                                (Evar _crc_table (tarray tuint 256))
                                (Ebinop Oand
                                  (Ebinop Oxor (Etempvar _crc tulong)
                                    (Etempvar _t'18 tuchar) tulong)
                                  (Econst_int (Int.repr 255) tint) tulong)
                                (tptr tuint)) tuint))
                          (Sset _crc
                            (Ebinop Oxor
                              (Ebinop Oshr (Etempvar _crc tulong)
                                (Econst_int (Int.repr 8) tint) tulong)
                              (Etempvar _t'19 tuint) tulong)))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'6 (Etempvar _buf (tptr tuchar)))
                          (Sset _buf
                            (Ebinop Oadd (Etempvar _t'6 (tptr tuchar))
                              (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                        (Ssequence
                          (Sset _t'16
                            (Ederef (Etempvar _t'6 (tptr tuchar)) tuchar))
                          (Ssequence
                            (Sset _t'17
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _crc_table (tarray tuint 256))
                                  (Ebinop Oand
                                    (Ebinop Oxor (Etempvar _crc tulong)
                                      (Etempvar _t'16 tuchar) tulong)
                                    (Econst_int (Int.repr 255) tint) tulong)
                                  (tptr tuint)) tuint))
                            (Sset _crc
                              (Ebinop Oxor
                                (Ebinop Oshr (Etempvar _crc tulong)
                                  (Econst_int (Int.repr 8) tint) tulong)
                                (Etempvar _t'17 tuint) tulong)))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'7 (Etempvar _buf (tptr tuchar)))
                            (Sset _buf
                              (Ebinop Oadd (Etempvar _t'7 (tptr tuchar))
                                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                          (Ssequence
                            (Sset _t'14
                              (Ederef (Etempvar _t'7 (tptr tuchar)) tuchar))
                            (Ssequence
                              (Sset _t'15
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _crc_table (tarray tuint 256))
                                    (Ebinop Oand
                                      (Ebinop Oxor (Etempvar _crc tulong)
                                        (Etempvar _t'14 tuchar) tulong)
                                      (Econst_int (Int.repr 255) tint)
                                      tulong) (tptr tuint)) tuint))
                              (Sset _crc
                                (Ebinop Oxor
                                  (Ebinop Oshr (Etempvar _crc tulong)
                                    (Econst_int (Int.repr 8) tint) tulong)
                                  (Etempvar _t'15 tuint) tulong)))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'8 (Etempvar _buf (tptr tuchar)))
                            (Sset _buf
                              (Ebinop Oadd (Etempvar _t'8 (tptr tuchar))
                                (Econst_int (Int.repr 1) tint) (tptr tuchar))))
                          (Ssequence
                            (Sset _t'12
                              (Ederef (Etempvar _t'8 (tptr tuchar)) tuchar))
                            (Ssequence
                              (Sset _t'13
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _crc_table (tarray tuint 256))
                                    (Ebinop Oand
                                      (Ebinop Oxor (Etempvar _crc tulong)
                                        (Etempvar _t'12 tuchar) tulong)
                                      (Econst_int (Int.repr 255) tint)
                                      tulong) (tptr tuint)) tuint))
                              (Sset _crc
                                (Ebinop Oxor
                                  (Ebinop Oshr (Etempvar _crc tulong)
                                    (Econst_int (Int.repr 8) tint) tulong)
                                  (Etempvar _t'13 tuint) tulong))))))))))))))
      (Ssequence
        (Swhile
          (Etempvar _len tulong)
          (Ssequence
            (Sset _len
              (Ebinop Osub (Etempvar _len tulong)
                (Econst_int (Int.repr 1) tint) tulong))
            (Ssequence
              (Ssequence
                (Sset _t'9 (Etempvar _buf (tptr tuchar)))
                (Sset _buf
                  (Ebinop Oadd (Etempvar _t'9 (tptr tuchar))
                    (Econst_int (Int.repr 1) tint) (tptr tuchar))))
              (Ssequence
                (Sset _t'10 (Ederef (Etempvar _t'9 (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'11
                    (Ederef
                      (Ebinop Oadd (Evar _crc_table (tarray tuint 256))
                        (Ebinop Oand
                          (Ebinop Oxor (Etempvar _crc tulong)
                            (Etempvar _t'10 tuchar) tulong)
                          (Econst_int (Int.repr 255) tint) tulong)
                        (tptr tuint)) tuint))
                  (Sset _crc
                    (Ebinop Oxor
                      (Ebinop Oshr (Etempvar _crc tulong)
                        (Econst_int (Int.repr 8) tint) tulong)
                      (Etempvar _t'11 tuint) tulong)))))))
        (Sreturn (Some (Ebinop Oxor (Etempvar _crc tulong)
                         (Econst_int (Int.repr (-1)) tuint) tulong)))))))
|}.

Definition f_crc32 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_crc, tulong) :: (_buf, (tptr tuchar)) :: (_len, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crc32_z (Tfunction (tulong :: (tptr tuchar) :: tulong :: nil)
                     tulong cc_default))
    ((Etempvar _crc tulong) :: (Etempvar _buf (tptr tuchar)) ::
     (Etempvar _len tuint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_crc32_combine_gen64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_len2, tlong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _len2 tlong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _x2nmodp (Tfunction (tlong :: tuint :: nil) tulong cc_default))
      ((Etempvar _len2 tlong) :: (Econst_int (Int.repr 3) tint) :: nil))
    (Sreturn (Some (Etempvar _t'1 tulong)))))
|}.

Definition f_crc32_combine_gen := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_len2, tlong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crc32_combine_gen64 (Tfunction (tlong :: nil) tulong cc_default))
    ((Ecast (Etempvar _len2 tlong) tlong) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_crc32_combine_op := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_crc1, tulong) :: (_crc2, tulong) :: (_op, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _op tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _multmodp (Tfunction (tulong :: tulong :: nil) tulong cc_default))
      ((Etempvar _op tulong) ::
       (Ebinop Oand (Etempvar _crc1 tulong)
         (Econst_int (Int.repr (-1)) tuint) tulong) :: nil))
    (Sreturn (Some (Ebinop Oxor (Etempvar _t'1 tulong)
                     (Ebinop Oand (Etempvar _crc2 tulong)
                       (Econst_int (Int.repr (-1)) tuint) tulong) tulong)))))
|}.

Definition f_crc32_combine64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_crc1, tulong) :: (_crc2, tulong) :: (_len2, tlong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crc32_combine_gen64 (Tfunction (tlong :: nil) tulong cc_default))
      ((Etempvar _len2 tlong) :: nil))
    (Scall (Some _t'2)
      (Evar _crc32_combine_op (Tfunction (tulong :: tulong :: tulong :: nil)
                                tulong cc_default))
      ((Etempvar _crc1 tulong) :: (Etempvar _crc2 tulong) ::
       (Etempvar _t'1 tulong) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tulong))))
|}.

Definition f_crc32_combine := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_crc1, tulong) :: (_crc2, tulong) :: (_len2, tlong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crc32_combine64 (Tfunction (tulong :: tulong :: tlong :: nil)
                             tulong cc_default))
    ((Etempvar _crc1 tulong) :: (Etempvar _crc2 tulong) ::
     (Ecast (Etempvar _len2 tlong) tlong) :: nil))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_crc_table, Gvar v_crc_table) :: (_x2n_table, Gvar v_x2n_table) ::
 (_multmodp, Gfun(Internal f_multmodp)) ::
 (_x2nmodp, Gfun(Internal f_x2nmodp)) ::
 (_get_crc_table, Gfun(Internal f_get_crc_table)) ::
 (_crc32_z, Gfun(Internal f_crc32_z)) :: (_crc32, Gfun(Internal f_crc32)) ::
 (_crc32_combine_gen64, Gfun(Internal f_crc32_combine_gen64)) ::
 (_crc32_combine_gen, Gfun(Internal f_crc32_combine_gen)) ::
 (_crc32_combine_op, Gfun(Internal f_crc32_combine_op)) ::
 (_crc32_combine64, Gfun(Internal f_crc32_combine64)) ::
 (_crc32_combine, Gfun(Internal f_crc32_combine)) :: nil).

Definition public_idents : list ident :=
(_crc32_combine :: _crc32_combine64 :: _crc32_combine_op ::
 _crc32_combine_gen :: _crc32_combine_gen64 :: _crc32 :: _crc32_z ::
 _get_crc_table :: ___builtin_debug :: ___builtin_write32_reversed ::
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


