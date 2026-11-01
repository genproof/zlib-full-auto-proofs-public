(* CRC-32: the reference of the harnesses (harness/zlib_common.h ref_crc_byte, ref_crc32), transcribed.

   crc_step is one step of the bitwise register update with the reflected polynomial 0xedb88320
   (`if (c & 1) c = (c >> 1) ^ POLY; else c = c >> 1;`), ref_crc_byte(c, b) is eight steps of c ^ b, and
   ref_crc32(c, data) presets the register to ~c (32 low bits), updates it byte by byte and inverts it.
   crc_table_vals is the table of the CRC of every byte value from the register 0: what zlib's constant
   crc_table holds (Facts: crc_table_vals_code).  Bytes as in adler32/Bytes.v. *)
Require Import VST.floyd.proofauto.
Require Export Zlib.proof.adler32.Bytes.

Definition CRC_POLY : Z := 3988292384.  (* 0xedb88320 *)
Definition crc_mask : Z := 4294967295.  (* 0xffffffff *)

Definition crc_step (c: Z) : Z := if Z.odd c then Z.lxor (Z.shiftr c 1) CRC_POLY else Z.shiftr c 1.

Definition ref_crc_byte (c b: Z) : Z := Nat.iter 8 crc_step (Z.lxor c b).

Definition ref_crc32 (c: Z) (data: list Z) : Z :=
  Z.lxor (fold_left ref_crc_byte data (Z.lxor (c mod 2 ^ 32) crc_mask)) crc_mask.

Definition crc_table_vals : list Z := map (ref_crc_byte 0) (upto 256).
Definition crc_table_rep : list val := map (fun x => Vint (Int.repr x)) crc_table_vals.
