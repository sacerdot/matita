type alu_HC05 =
Mk_alu_HC05 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool
;;

let alu_HC05_rec =
(function f -> (function a -> 
(match a with 
   Mk_alu_HC05(b,b1,w,w1,w2,w3,w4,b2,b3,b4,b5,b6,b7) -> (f b b1 w w1 w2 w3 w4 b2 b3 b4 b5 b6 b7))
))
;;

let alu_HC05_rect =
(function f -> (function a -> 
(match a with 
   Mk_alu_HC05(b,b1,w,w1,w2,w3,w4,b2,b3,b4,b5,b6,b7) -> (f b b1 w w1 w2 w3 w4 b2 b3 b4 b5 b6 b7))
))
;;

let acc_low_reg_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> acc_low_reg_HC05)
)
;;

let indX_low_reg_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> indX_low_reg_HC05)
)
;;

let sp_reg_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> sp_reg_HC05)
)
;;

let sp_mask_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> sp_mask_HC05)
)
;;

let sp_fix_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> sp_fix_HC05)
)
;;

let pc_reg_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> pc_reg_HC05)
)
;;

let pc_mask_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> pc_mask_HC05)
)
;;

let h_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> h_flag_HC05)
)
;;

let i_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> i_flag_HC05)
)
;;

let n_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> n_flag_HC05)
)
;;

let z_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> z_flag_HC05)
)
;;

let c_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> c_flag_HC05)
)
;;

let irq_flag_HC05 =
(function w -> 
(match w with 
   Mk_alu_HC05(acc_low_reg_HC05,indX_low_reg_HC05,sp_reg_HC05,sp_mask_HC05,sp_fix_HC05,pc_reg_HC05,pc_mask_HC05,h_flag_HC05,i_flag_HC05,n_flag_HC05,z_flag_HC05,c_flag_HC05,irq_flag_HC05) -> irq_flag_HC05)
)
;;

type alu_HC08 =
Mk_alu_HC08 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool
;;

let alu_HC08_rec =
(function f -> (function a -> 
(match a with 
   Mk_alu_HC08(b,b1,b2,w,w1,b3,b4,b5,b6,b7,b8,b9) -> (f b b1 b2 w w1 b3 b4 b5 b6 b7 b8 b9))
))
;;

let alu_HC08_rect =
(function f -> (function a -> 
(match a with 
   Mk_alu_HC08(b,b1,b2,w,w1,b3,b4,b5,b6,b7,b8,b9) -> (f b b1 b2 w w1 b3 b4 b5 b6 b7 b8 b9))
))
;;

let acc_low_reg_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> acc_low_reg_HC08)
)
;;

let indX_low_reg_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> indX_low_reg_HC08)
)
;;

let indX_high_reg_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> indX_high_reg_HC08)
)
;;

let sp_reg_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> sp_reg_HC08)
)
;;

let pc_reg_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> pc_reg_HC08)
)
;;

let v_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> v_flag_HC08)
)
;;

let h_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> h_flag_HC08)
)
;;

let i_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> i_flag_HC08)
)
;;

let n_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> n_flag_HC08)
)
;;

let z_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> z_flag_HC08)
)
;;

let c_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> c_flag_HC08)
)
;;

let irq_flag_HC08 =
(function w -> 
(match w with 
   Mk_alu_HC08(acc_low_reg_HC08,indX_low_reg_HC08,indX_high_reg_HC08,sp_reg_HC08,pc_reg_HC08,v_flag_HC08,h_flag_HC08,i_flag_HC08,n_flag_HC08,z_flag_HC08,c_flag_HC08,irq_flag_HC08) -> irq_flag_HC08)
)
;;

type alu_RS08 =
Mk_alu_RS08 of Matita_freescale_byte8.byte8 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_freescale_word16.word16 * Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8 * Matita_datatypes_bool.bool * Matita_datatypes_bool.bool
;;

let alu_RS08_rec =
(function f -> (function a -> 
(match a with 
   Mk_alu_RS08(b,w,w1,w2,b1,b2,b3,b4) -> (f b w w1 w2 b1 b2 b3 b4))
))
;;

let alu_RS08_rect =
(function f -> (function a -> 
(match a with 
   Mk_alu_RS08(b,w,w1,w2,b1,b2,b3,b4) -> (f b w w1 w2 b1 b2 b3 b4))
))
;;

let acc_low_reg_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> acc_low_reg_RS08)
)
;;

let pc_reg_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> pc_reg_RS08)
)
;;

let pc_mask_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> pc_mask_RS08)
)
;;

let spc_reg_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> spc_reg_RS08)
)
;;

let x_map_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> x_map_RS08)
)
;;

let ps_map_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> ps_map_RS08)
)
;;

let z_flag_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> z_flag_RS08)
)
;;

let c_flag_RS08 =
(function w -> 
(match w with 
   Mk_alu_RS08(acc_low_reg_RS08,pc_reg_RS08,pc_mask_RS08,spc_reg_RS08,x_map_RS08,ps_map_RS08,z_flag_RS08,c_flag_RS08) -> c_flag_RS08)
)
;;

type any_status =
Mk_any_status of unit (* TOO POLYMORPHIC TYPE *) * Matita_freescale_memory_abs.aux_mem_type * Matita_freescale_memory_abs.aux_chk_type * ((Matita_freescale_byte8.byte8,Matita_freescale_opcode.any_opcode,Matita_freescale_opcode.instr_mode,Matita_freescale_byte8.byte8,Matita_freescale_word16.word16) Matita_freescale_extra.prod5T) Matita_datatypes_constructors.option
;;

let any_status_rec =
(function m -> (function m1 -> (function f -> (function a -> 
(match a with 
   Mk_any_status(x,a1,a2,o) -> (f x a1 a2 o))
))))
;;

let any_status_rect =
(function m -> (function m1 -> (function f -> (function a -> 
(match a with 
   Mk_any_status(x,a1,a2,o) -> (f x a1 a2 o))
))))
;;

let alu =
(function mcu -> (function t -> (function w -> 
(match w with 
   Mk_any_status(alu,mem_desc,chk_desc,clk_desc) -> alu)
)))
;;

let mem_desc =
(function mcu -> (function t -> (function w -> 
(match w with 
   Mk_any_status(alu,mem_desc,chk_desc,clk_desc) -> mem_desc)
)))
;;

let chk_desc =
(function mcu -> (function t -> (function w -> 
(match w with 
   Mk_any_status(alu,mem_desc,chk_desc,clk_desc) -> chk_desc)
)))
;;

let clk_desc =
(function mcu -> (function t -> (function w -> 
(match w with 
   Mk_any_status(alu,mem_desc,chk_desc,clk_desc) -> clk_desc)
)))
;;

type ('x) aux_get_typing = (unit (* TOO POLYMORPHIC TYPE *) -> 'x)
;;

let get_acc_8_low_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (acc_low_reg_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (acc_low_reg_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (acc_low_reg_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (acc_low_reg_RS08))
 (alu m t s)))))
;;

let get_indX_8_low_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((indX_low_reg_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((indX_low_reg_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((indX_low_reg_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_indX_8_high_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((indX_high_reg_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((indX_high_reg_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_indX_16_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((Matita_freescale_word16.Mk_word16((indX_high_reg_HC08 alu),(indX_low_reg_HC08 alu)))))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((Matita_freescale_word16.Mk_word16((indX_high_reg_HC08 alu),(indX_low_reg_HC08 alu)))))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_sp_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((sp_reg_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((sp_reg_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((sp_reg_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_pc_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (pc_reg_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (pc_reg_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (pc_reg_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (pc_reg_RS08))
 (alu m t s)))))
;;

let get_spc_reg =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((spc_reg_RS08 alu))))))
 (alu m t s)))))
;;

let get_x_map =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((x_map_RS08 alu))))))
 (alu m t s)))))
;;

let get_ps_map =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((ps_map_RS08 alu))))))
 (alu m t s)))))
;;

let get_v_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((v_flag_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((v_flag_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_h_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((h_flag_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((h_flag_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((h_flag_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_i_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((i_flag_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((i_flag_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((i_flag_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_n_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((n_flag_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((n_flag_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((n_flag_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_z_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (z_flag_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (z_flag_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (z_flag_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (z_flag_RS08))
 (alu m t s)))))
;;

let get_c_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (c_flag_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (c_flag_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (c_flag_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (c_flag_RS08))
 (alu m t s)))))
;;

let get_irq_flag =
(function m -> (function t -> (function s -> (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((irq_flag_HC05 alu)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((irq_flag_HC08 alu)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.Some((irq_flag_HC08 alu)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function alu -> (Matita_datatypes_constructors.None))))
 (alu m t s)))))
;;

let get_alu =
(function m -> (function t -> (function s -> (alu m t s))))
;;

let get_mem_desc =
(function m -> (function t -> (function s -> (mem_desc m t s))))
;;

let get_chk_desc =
(function m -> (function t -> (function s -> (chk_desc m t s))))
;;

let get_clk_desc =
(function m -> (function t -> (function s -> (clk_desc m t s))))
;;

type ('x) aux_set_typing = (unit (* TOO POLYMORPHIC TYPE *) -> ('x -> unit (* TOO POLYMORPHIC TYPE *)))
;;

type ('x) aux_set_typing_opt = ((unit (* TOO POLYMORPHIC TYPE *) -> ('x -> unit (* TOO POLYMORPHIC TYPE *)))) Matita_datatypes_constructors.option
;;

let set_alu =
(function m -> (function t -> (function s -> (function alu' -> 
(match s with 
   Mk_any_status(_,mem,chk,clk) -> (Mk_any_status(alu',mem,chk,clk)))
))))
;;

let set_mem_desc =
(function m -> (function t -> (function s -> (function mem' -> 
(match s with 
   Mk_any_status(alu,_,chk,clk) -> (Mk_any_status(alu,mem',chk,clk)))
))))
;;

let set_chk_desc =
(function m -> (function t -> (function s -> (function chk' -> 
(match s with 
   Mk_any_status(alu,mem,_,clk) -> (Mk_any_status(alu,mem,chk',clk)))
))))
;;

let set_clk_desc =
(function m -> (function t -> (function s -> (function clk' -> 
(match s with 
   Mk_any_status(alu,mem,chk,_) -> (Mk_any_status(alu,mem,chk,clk')))
))))
;;

let set_acc_8_low_reg_HC05 =
(function alu -> (function acclow' -> 
(match alu with 
   Mk_alu_HC05(_,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow',indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_acc_8_low_reg_HC08 =
(function alu -> (function acclow' -> 
(match alu with 
   Mk_alu_HC08(_,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow',indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_acc_8_low_reg_RS08 =
(function alu -> (function acclow' -> 
(match alu with 
   Mk_alu_RS08(_,pc,pcm,spc,xm,psm,zfl,cfl) -> (Mk_alu_RS08(acclow',pc,pcm,spc,xm,psm,zfl,cfl)))
))
;;

let set_acc_8_low_reg =
(function m -> (function t -> (function s -> (function acclow' -> (set_alu m t s (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (set_acc_8_low_reg_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (set_acc_8_low_reg_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (set_acc_8_low_reg_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (set_acc_8_low_reg_RS08))
 (alu m t s) acclow'))))))
;;

let set_indX_8_low_reg_HC05 =
(function alu -> (function indxlow' -> 
(match alu with 
   Mk_alu_HC05(acclow,_,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow',sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_indX_8_low_reg_HC08 =
(function alu -> (function indxlow' -> 
(match alu with 
   Mk_alu_HC08(acclow,_,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow',indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_indX_8_low_reg =
(function m -> (function t -> (function s -> (function indxlow' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_8_low_reg_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_8_low_reg_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_8_low_reg_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) indxlow'))))))))))
;;

let setweak_indX_8_low_reg =
(function m -> (function t -> (function s -> (function indxlow' -> 
(match (set_indX_8_low_reg m t s indxlow') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_indX_8_high_reg_HC08 =
(function alu -> (function indxhigh' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,_,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh',sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_indX_8_high_reg =
(function m -> (function t -> (function s -> (function indxhigh' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_8_high_reg_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_8_high_reg_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) indxhigh'))))))))))
;;

let setweak_indX_8_high_reg =
(function m -> (function t -> (function s -> (function indxhigh' -> 
(match (set_indX_8_high_reg m t s indxhigh') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_indX_16_reg_HC08 =
(function alu -> (function indx16 -> 
(match alu with 
   Mk_alu_HC08(acclow,_,_,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,(Matita_freescale_word16.w16l indx16),(Matita_freescale_word16.w16h indx16),sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_indX_16_reg =
(function m -> (function t -> (function s -> (function indx16 -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_16_reg_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_indX_16_reg_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) indx16))))))))))
;;

let setweak_indX_16_reg =
(function m -> (function t -> (function s -> (function indx16 -> 
(match (set_indX_16_reg m t s indx16) with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_sp_reg_HC05 =
(function alu -> (function sp' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,_,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,(Matita_freescale_word16.or_w16 (Matita_freescale_word16.and_w16 sp' spm) spf),spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_sp_reg_HC08 =
(function alu -> (function sp' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,_,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp',pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_sp_reg =
(function m -> (function t -> (function s -> (function sp' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_sp_reg_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_sp_reg_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_sp_reg_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) sp'))))))))))
;;

let setweak_sp_reg =
(function m -> (function t -> (function s -> (function sp' -> 
(match (set_sp_reg m t s sp') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_pc_reg_HC05 =
(function alu -> (function pc' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,_,pcm,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,(Matita_freescale_word16.and_w16 pc' pcm),pcm,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_pc_reg_HC08 =
(function alu -> (function pc' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,_,vfl,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc',vfl,hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_pc_reg_RS08 =
(function alu -> (function pc' -> 
(match alu with 
   Mk_alu_RS08(acclow,_,pcm,spc,xm,psm,zfl,cfl) -> (Mk_alu_RS08(acclow,(Matita_freescale_word16.and_w16 pc' pcm),pcm,spc,xm,psm,zfl,cfl)))
))
;;

let set_pc_reg =
(function m -> (function t -> (function s -> (function pc' -> (set_alu m t s (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (set_pc_reg_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (set_pc_reg_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (set_pc_reg_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (set_pc_reg_RS08))
 (alu m t s) pc'))))))
;;

let set_spc_reg_RS08 =
(function alu -> (function spc' -> 
(match alu with 
   Mk_alu_RS08(acclow,pc,pcm,_,xm,psm,zfl,cfl) -> (Mk_alu_RS08(acclow,pc,pcm,(Matita_freescale_word16.and_w16 spc' pcm),xm,psm,zfl,cfl)))
))
;;

let set_spc_reg =
(function m -> (function t -> (function s -> (function spc' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_spc_reg_RS08))))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) spc'))))))))))
;;

let setweak_spc_reg =
(function m -> (function t -> (function s -> (function spc' -> 
(match (set_spc_reg m t s spc') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_x_map_RS08 =
(function alu -> (function xm' -> 
(match alu with 
   Mk_alu_RS08(acclow,pc,pcm,spc,_,psm,zfl,cfl) -> (Mk_alu_RS08(acclow,pc,pcm,spc,xm',psm,zfl,cfl)))
))
;;

let set_x_map =
(function m -> (function t -> (function s -> (function xm' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_x_map_RS08))))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) xm'))))))))))
;;

let setweak_x_map =
(function m -> (function t -> (function s -> (function xm' -> 
(match (set_x_map m t s xm') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_ps_map_RS08 =
(function alu -> (function psm' -> 
(match alu with 
   Mk_alu_RS08(acclow,pc,pcm,spc,xm,_,zfl,cfl) -> (Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm',zfl,cfl)))
))
;;

let set_ps_map =
(function m -> (function t -> (function s -> (function psm' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_ps_map_RS08))))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) psm'))))))))))
;;

let setweak_ps_map =
(function m -> (function t -> (function s -> (function psm' -> 
(match (set_ps_map m t s psm') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_v_flag_HC08 =
(function alu -> (function vfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,_,hfl,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl',hfl,ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_v_flag =
(function m -> (function t -> (function s -> (function vfl' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.None))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_v_flag_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_v_flag_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) vfl'))))))))))
;;

let setweak_v_flag =
(function m -> (function t -> (function s -> (function vfl' -> 
(match (set_v_flag m t s vfl') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_h_flag_HC05 =
(function alu -> (function hfl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,_,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl',ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_h_flag_HC08 =
(function alu -> (function hfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,_,ifl,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl',ifl,nfl,zfl,cfl,irqfl)))
))
;;

let set_h_flag =
(function m -> (function t -> (function s -> (function hfl' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_h_flag_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_h_flag_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_h_flag_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) hfl'))))))))))
;;

let setweak_h_flag =
(function m -> (function t -> (function s -> (function hfl' -> 
(match (set_h_flag m t s hfl') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_i_flag_HC05 =
(function alu -> (function ifl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,_,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl',nfl,zfl,cfl,irqfl)))
))
;;

let set_i_flag_HC08 =
(function alu -> (function ifl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,_,nfl,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl',nfl,zfl,cfl,irqfl)))
))
;;

let set_i_flag =
(function m -> (function t -> (function s -> (function ifl' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_i_flag_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_i_flag_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_i_flag_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) ifl'))))))))))
;;

let setweak_i_flag =
(function m -> (function t -> (function s -> (function ifl' -> 
(match (set_i_flag m t s ifl') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_n_flag_HC05 =
(function alu -> (function nfl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,_,zfl,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl',zfl,cfl,irqfl)))
))
;;

let set_n_flag_HC08 =
(function alu -> (function nfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,_,zfl,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl',zfl,cfl,irqfl)))
))
;;

let set_n_flag =
(function m -> (function t -> (function s -> (function nfl' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_n_flag_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_n_flag_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_n_flag_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) nfl'))))))))))
;;

let setweak_n_flag =
(function m -> (function t -> (function s -> (function nfl' -> 
(match (set_n_flag m t s nfl') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let set_z_flag_HC05 =
(function alu -> (function zfl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,_,cfl,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl',cfl,irqfl)))
))
;;

let set_z_flag_HC08 =
(function alu -> (function zfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,_,cfl,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl',cfl,irqfl)))
))
;;

let set_z_flag_RS08 =
(function alu -> (function zfl' -> 
(match alu with 
   Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,_,cfl) -> (Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl',cfl)))
))
;;

let set_z_flag =
(function m -> (function t -> (function s -> (function zfl' -> (set_alu m t s (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (set_z_flag_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (set_z_flag_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (set_z_flag_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (set_z_flag_RS08))
 (alu m t s) zfl'))))))
;;

let set_c_flag_HC05 =
(function alu -> (function cfl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,_,irqfl) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl',irqfl)))
))
;;

let set_c_flag_HC08 =
(function alu -> (function cfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,_,irqfl) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl',irqfl)))
))
;;

let set_c_flag_RS08 =
(function alu -> (function cfl' -> 
(match alu with 
   Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,_) -> (Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,cfl')))
))
;;

let set_c_flag =
(function m -> (function t -> (function s -> (function cfl' -> (set_alu m t s (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (set_c_flag_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (set_c_flag_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (set_c_flag_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (set_c_flag_RS08))
 (alu m t s) cfl'))))))
;;

let set_irq_flag_HC05 =
(function alu -> (function irqfl' -> 
(match alu with 
   Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,_) -> (Mk_alu_HC05(acclow,indxlow,sp,spm,spf,pc,pcm,hfl,ifl,nfl,zfl,cfl,irqfl')))
))
;;

let set_irq_flag_HC08 =
(function alu -> (function irqfl' -> 
(match alu with 
   Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,_) -> (Mk_alu_HC08(acclow,indxlow,indxhigh,sp,pc,vfl,hfl,ifl,nfl,zfl,cfl,irqfl')))
))
;;

let set_irq_flag =
(function m -> (function t -> (function s -> (function irqfl' -> (Matita_freescale_extra.opt_map 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((Matita_datatypes_constructors.Some(set_irq_flag_HC05)))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_irq_flag_HC08)))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((Matita_datatypes_constructors.Some(set_irq_flag_HC08)))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((Matita_datatypes_constructors.None)))
 (function f -> (Matita_datatypes_constructors.Some((set_alu m t s (f (alu m t s) irqfl'))))))))))
;;

let setweak_irq_flag =
(function m -> (function t -> (function s -> (function irqfl' -> 
(match (set_irq_flag m t s irqfl') with 
   Matita_datatypes_constructors.None -> s
 | Matita_datatypes_constructors.Some(s') -> s')
))))
;;

let eq_alu_HC05 =
(function alu1 -> (function alu2 -> 
(match alu1 with 
   Mk_alu_HC05(acclow1,indxlow1,sp1,spm1,spf1,pc1,pcm1,hfl1,ifl1,nfl1,zfl1,cfl1,irqfl1) -> 
(match alu2 with 
   Mk_alu_HC05(acclow2,indxlow2,sp2,spm2,spf2,pc2,pcm2,hfl2,ifl2,nfl2,zfl2,cfl2,irqfl2) -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_byte8.eq_b8 acclow1 acclow2) (Matita_freescale_byte8.eq_b8 indxlow1 indxlow2)) (Matita_freescale_word16.eq_w16 sp1 sp2)) (Matita_freescale_word16.eq_w16 spm1 spm2)) (Matita_freescale_word16.eq_w16 spf1 spf2)) (Matita_freescale_word16.eq_w16 pc1 pc2)) (Matita_freescale_word16.eq_w16 pcm1 pcm2)) (Matita_freescale_extra.eq_bool hfl1 hfl2)) (Matita_freescale_extra.eq_bool ifl1 ifl2)) (Matita_freescale_extra.eq_bool nfl1 nfl2)) (Matita_freescale_extra.eq_bool zfl1 zfl2)) (Matita_freescale_extra.eq_bool cfl1 cfl2)) (Matita_freescale_extra.eq_bool irqfl1 irqfl2)))
)
))
;;

let eq_alu_HC08 =
(function alu1 -> (function alu2 -> 
(match alu1 with 
   Mk_alu_HC08(acclow1,indxlow1,indxhigh1,sp1,pc1,vfl1,hfl1,ifl1,nfl1,zfl1,cfl1,irqfl1) -> 
(match alu2 with 
   Mk_alu_HC08(acclow2,indxlow2,indxhigh2,sp2,pc2,vfl2,hfl2,ifl2,nfl2,zfl2,cfl2,irqfl2) -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_byte8.eq_b8 acclow1 acclow2) (Matita_freescale_byte8.eq_b8 indxlow1 indxlow2)) (Matita_freescale_byte8.eq_b8 indxhigh1 indxhigh2)) (Matita_freescale_word16.eq_w16 sp1 sp2)) (Matita_freescale_word16.eq_w16 pc1 pc2)) (Matita_freescale_extra.eq_bool vfl1 vfl2)) (Matita_freescale_extra.eq_bool hfl1 hfl2)) (Matita_freescale_extra.eq_bool ifl1 ifl2)) (Matita_freescale_extra.eq_bool nfl1 nfl2)) (Matita_freescale_extra.eq_bool zfl1 zfl2)) (Matita_freescale_extra.eq_bool cfl1 cfl2)) (Matita_freescale_extra.eq_bool irqfl1 irqfl2)))
)
))
;;

let eq_alu_RS08 =
(function alu1 -> (function alu2 -> 
(match alu1 with 
   Mk_alu_RS08(acclow1,pc1,pcm1,spc1,xm1,psm1,zfl1,cfl1) -> 
(match alu2 with 
   Mk_alu_RS08(acclow2,pc2,pcm2,spc2,xm2,psm2,zfl2,cfl2) -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_byte8.eq_b8 acclow1 acclow2) (Matita_freescale_word16.eq_w16 pc1 pc2)) (Matita_freescale_word16.eq_w16 pcm1 pcm2)) (Matita_freescale_word16.eq_w16 spc1 spc2)) (Matita_freescale_byte8.eq_b8 xm1 xm2)) (Matita_freescale_byte8.eq_b8 psm1 psm2)) (Matita_freescale_extra.eq_bool zfl1 zfl2)) (Matita_freescale_extra.eq_bool cfl1 cfl2)))
)
))
;;

let eq_b8_opt =
(function b1 -> (function b2 -> 
(match b1 with 
   Matita_datatypes_constructors.None -> 
(match b2 with 
   Matita_datatypes_constructors.None -> Matita_datatypes_bool.True
 | Matita_datatypes_constructors.Some(_) -> Matita_datatypes_bool.False)

 | Matita_datatypes_constructors.Some(b1') -> 
(match b2 with 
   Matita_datatypes_constructors.None -> Matita_datatypes_bool.False
 | Matita_datatypes_constructors.Some(b2') -> (Matita_freescale_byte8.eq_b8 b1' b2'))
)
))
;;

let forall_memory_ranged =
let rec forall_memory_ranged = 
(function t -> (function chk1 -> (function chk2 -> (function mem1 -> (function mem2 -> (function inf -> (function n -> 
(match n with 
   Matita_nat_nat.O -> (eq_b8_opt (Matita_freescale_memory_abs.mem_read t mem1 chk1 inf) (Matita_freescale_memory_abs.mem_read t mem2 chk2 inf))
 | Matita_nat_nat.S(n') -> (Matita_freescale_extra.and_bool (eq_b8_opt (Matita_freescale_memory_abs.mem_read t mem1 chk1 (Matita_freescale_word16.plus_w16nc inf (Matita_freescale_word16.word16_of_nat n))) (Matita_freescale_memory_abs.mem_read t mem2 chk2 (Matita_freescale_word16.plus_w16nc inf (Matita_freescale_word16.word16_of_nat n)))) (forall_memory_ranged t chk1 chk2 mem1 mem2 inf n')))
))))))) in forall_memory_ranged
;;

let eq_clk =
(function m -> (function c1 -> (function c2 -> 
(match c1 with 
   Matita_datatypes_constructors.None -> 
(match c2 with 
   Matita_datatypes_constructors.None -> Matita_datatypes_bool.True
 | Matita_datatypes_constructors.Some(_) -> Matita_datatypes_bool.False)

 | Matita_datatypes_constructors.Some(c1') -> 
(match c2 with 
   Matita_datatypes_constructors.None -> Matita_datatypes_bool.False
 | Matita_datatypes_constructors.Some(c2') -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (Matita_freescale_byte8.eq_b8 (Matita_freescale_extra.fst5T c1') (Matita_freescale_extra.fst5T c2')) (Matita_freescale_opcode.eqop m (Matita_freescale_extra.snd5T c1') (Matita_freescale_extra.snd5T c2'))) (Matita_freescale_opcode.eqim (Matita_freescale_extra.thd5T c1') (Matita_freescale_extra.thd5T c2'))) (Matita_freescale_byte8.eq_b8 (Matita_freescale_extra.frth5T c1') (Matita_freescale_extra.frth5T c2'))) (Matita_freescale_word16.eq_w16 (Matita_freescale_extra.ffth5T c1') (Matita_freescale_extra.ffth5T c2'))))
)
)))
;;

let eq_status =
(function m -> (function t -> (function s1 -> (function s2 -> (function inf -> (function n -> 
(match s1 with 
   Mk_any_status(alu1,mem1,chk1,clk1) -> 
(match s2 with 
   Mk_any_status(alu2,mem2,chk2,clk2) -> (Matita_freescale_extra.and_bool (Matita_freescale_extra.and_bool (
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (eq_alu_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (eq_alu_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (eq_alu_HC08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (eq_alu_RS08))
 alu1 alu2) (forall_memory_ranged t chk1 chk2 mem1 mem2 inf n)) (eq_clk m clk1 clk2)))
)
))))))
;;

