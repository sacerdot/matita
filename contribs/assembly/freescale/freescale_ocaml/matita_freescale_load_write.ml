type error_type =
ILL_OP
 | ILL_FETCH_AD
 | ILL_EX_AD
;;

let error_type_rec =
(function p -> (function p1 -> (function p2 -> (function e -> 
(match e with 
   ILL_OP -> p
 | ILL_FETCH_AD -> p1
 | ILL_EX_AD -> p2)
))))
;;

let error_type_rect =
(function p -> (function p1 -> (function p2 -> (function e -> 
(match e with 
   ILL_OP -> p
 | ILL_FETCH_AD -> p1
 | ILL_EX_AD -> p2)
))))
;;

type ('a) fetch_result =
FetchERR of error_type
 | FetchOK of 'a * Matita_freescale_word16.word16
;;

let fetch_result_rec =
(function f -> (function f1 -> (function f2 -> 
(match f2 with 
   FetchERR(e) -> (f e)
 | FetchOK(t,w) -> (f1 t w))
)))
;;

let fetch_result_rect =
(function f -> (function f1 -> (function f2 -> 
(match f2 with 
   FetchERR(e) -> (f e)
 | FetchOK(t,w) -> (f1 t w))
)))
;;

let rS08_memory_filter_read_aux =
(function t -> (function s -> (function addr -> (function fREG -> (function fMEM -> 
(match s with 
   Matita_freescale_status.Mk_any_status(alu,mem,chk,_) -> 
(match Obj.magic(alu) with 
   Matita_freescale_status.Mk_alu_RS08(_,_,_,_,xm,psm,_,_) -> 
(match (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_freescale_byte8.eq_b8 xm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.XF))))) (Matita_freescale_byte8.eq_b8 psm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (fREG xm)
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_freescale_byte8.eq_b8 xm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.XF))))) (Matita_freescale_byte8.eq_b8 psm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (fREG psm)
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) with 
   Matita_datatypes_bool.True -> (fMEM mem chk (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),xm)))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.in_range addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X0)))) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) with 
   Matita_datatypes_bool.True -> (fMEM mem chk (Matita_freescale_word16.or_w16 (Matita_datatypes_constructors.fst (Matita_freescale_word16.shr_w16 (Matita_datatypes_constructors.fst (Matita_freescale_word16.shr_w16 (Matita_freescale_word16.Mk_word16(psm,(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))))) (Matita_freescale_word16.and_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XF)))))))
 | Matita_datatypes_bool.False -> (fMEM mem chk addr))
)
)
)
)
)
)))))
;;

let rS08_memory_filter_read =
(function t -> (function s -> (function addr -> (rS08_memory_filter_read_aux t s addr (function b -> (Matita_datatypes_constructors.Some(b))) (function m -> (function c -> (function a -> (Matita_freescale_memory_abs.mem_read t m c a))))))))
;;

let rS08_memory_filter_read_bit =
(function t -> (function s -> (function addr -> (function sub -> (rS08_memory_filter_read_aux t s addr (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T sub (Matita_freescale_memory_struct.bits_of_byte8 b))))) (function m -> (function c -> (function a -> (Matita_freescale_memory_abs.mem_read_bit t m c a sub)))))))))
;;

let memory_filter_read =
(function m -> (function t -> 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function s -> (function addr -> (Matita_freescale_memory_abs.mem_read t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC05 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC05 t s) addr))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function s -> (function addr -> (Matita_freescale_memory_abs.mem_read t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC08 t s) addr))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function s -> (function addr -> (Matita_freescale_memory_abs.mem_read t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HCS08 t s) addr))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function s -> (function addr -> (rS08_memory_filter_read t s addr)))))
))
;;

let memory_filter_read_bit =
(function m -> (function t -> 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function s -> (function addr -> (function sub -> (Matita_freescale_memory_abs.mem_read_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC05 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC05 t s) addr sub)))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function s -> (function addr -> (function sub -> (Matita_freescale_memory_abs.mem_read_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC08 t s) addr sub)))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function s -> (function addr -> (function sub -> (Matita_freescale_memory_abs.mem_read_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HCS08 t s) addr sub)))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function s -> (function addr -> (function sub -> (rS08_memory_filter_read_bit t s addr sub))))))
))
;;

let rS08_memory_filter_write_aux =
(function t -> (function s -> (function addr -> (function fREG -> (function fMEM -> 
(match s with 
   Matita_freescale_status.Mk_any_status(alu,mem,chk,clk) -> 
(match Obj.magic(alu) with 
   Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,cfl) -> 
(match (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_freescale_byte8.eq_b8 xm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.XF))))) (Matita_freescale_byte8.eq_b8 psm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_freescale_status.Mk_any_status((Obj.magic(Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,(fREG xm),psm,zfl,cfl))),mem,chk,clk))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_extra.or_bool (Matita_freescale_extra.or_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) (Matita_freescale_byte8.eq_b8 xm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X1,Matita_freescale_exadecim.XF))))) (Matita_freescale_extra.and_bool (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XD,Matita_freescale_exadecim.XF))))) (Matita_freescale_byte8.eq_b8 psm (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0))))) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some((Matita_freescale_status.Mk_any_status((Obj.magic(Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,xm,(fREG psm),zfl,cfl))),mem,chk,clk))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.eq_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.XE))))) with 
   Matita_datatypes_bool.True -> (Matita_freescale_extra.opt_map (fMEM mem chk (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),xm))) (function mem' -> (Matita_datatypes_constructors.Some((Matita_freescale_status.Mk_any_status((Obj.magic(Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,cfl))),mem',chk,clk))))))
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.in_range addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XC,Matita_freescale_exadecim.X0)))) (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) with 
   Matita_datatypes_bool.True -> (Matita_freescale_extra.opt_map (fMEM mem chk (Matita_freescale_word16.or_w16 (Matita_datatypes_constructors.fst (Matita_freescale_word16.shr_w16 (Matita_datatypes_constructors.fst (Matita_freescale_word16.shr_w16 (Matita_freescale_word16.Mk_word16(psm,(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))))))) (Matita_freescale_word16.and_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X3,Matita_freescale_exadecim.XF))))))) (function mem' -> (Matita_datatypes_constructors.Some((Matita_freescale_status.Mk_any_status((Obj.magic(Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,cfl))),mem',chk,clk))))))
 | Matita_datatypes_bool.False -> (Matita_freescale_extra.opt_map (fMEM mem chk addr) (function mem' -> (Matita_datatypes_constructors.Some((Matita_freescale_status.Mk_any_status((Obj.magic(Matita_freescale_status.Mk_alu_RS08(acclow,pc,pcm,spc,xm,psm,zfl,cfl))),mem',chk,clk)))))))
)
)
)
)
)
)))))
;;

let rS08_memory_filter_write =
(function t -> (function s -> (function addr -> (function val_ -> (rS08_memory_filter_write_aux t s addr (function b -> val_) (function m -> (function c -> (function a -> (Matita_freescale_memory_abs.mem_update t m c a val_)))))))))
;;

let rS08_memory_filter_write_bit =
(function t -> (function s -> (function addr -> (function sub -> (function val_ -> (rS08_memory_filter_write_aux t s addr (function b -> (Matita_freescale_memory_struct.byte8_of_bits (Matita_freescale_memory_struct.setn_array8T sub (Matita_freescale_memory_struct.bits_of_byte8 b) val_))) (function m -> (function c -> (function a -> (Matita_freescale_memory_abs.mem_update_bit t m c a sub val_))))))))))
;;

let memory_filter_write =
(function m -> (function t -> 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function s -> (function addr -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC05 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC05 t s) addr val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HC05 t s mem)))))))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function s -> (function addr -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC08 t s) addr val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HC08 t s mem)))))))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function s -> (function addr -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HCS08 t s) addr val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HCS08 t s mem)))))))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function s -> (function addr -> (function val_ -> (rS08_memory_filter_write t s addr val_))))))
))
;;

let memory_filter_write_bit =
(function m -> (function t -> 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function s -> (function addr -> (function sub -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC05 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC05 t s) addr sub val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HC05 t s mem))))))))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function s -> (function addr -> (function sub -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HC08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HC08 t s) addr sub val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HC08 t s mem))))))))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function s -> (function addr -> (function sub -> (function val_ -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_abs.mem_update_bit t (Matita_freescale_status.get_mem_desc Matita_freescale_opcode.HCS08 t s) (Matita_freescale_status.get_chk_desc Matita_freescale_opcode.HCS08 t s) addr sub val_) (function mem -> (Matita_datatypes_constructors.Some((Matita_freescale_status.set_mem_desc Matita_freescale_opcode.HCS08 t s mem))))))))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function s -> (function addr -> (function sub -> (function val_ -> (rS08_memory_filter_write_bit t s addr sub val_)))))))
))
;;

let filtered_inc_w16 =
(function m -> (function t -> (function s -> (function w -> (Matita_freescale_status.get_pc_reg m t (Matita_freescale_status.set_pc_reg m t s (Matita_freescale_word16.succ_w16 w)))))))
;;

let filtered_plus_w16 =
let rec filtered_plus_w16 = 
(function m -> (function t -> (function s -> (function w -> (function n -> 
(match n with 
   Matita_nat_nat.O -> w
 | Matita_nat_nat.S(n') -> (filtered_plus_w16 m t s (filtered_inc_w16 m t s w) n'))
))))) in filtered_plus_w16
;;

let fetch =
(function m -> (function t -> (function s -> (let pc = (Matita_freescale_status.get_pc_reg m t s) in (let pc_next1 = (filtered_inc_w16 m t s pc) in (let pc_next2 = (filtered_inc_w16 m t s pc_next1) in 
(match (memory_filter_read m t s pc) with 
   Matita_datatypes_constructors.None -> (FetchERR(ILL_FETCH_AD))
 | Matita_datatypes_constructors.Some(bh) -> 
(match (Matita_freescale_translation.full_info_of_word16 m (Matita_freescale_opcode.Byte(bh))) with 
   Matita_datatypes_constructors.None -> 
(match m with 
   Matita_freescale_opcode.HC05 -> (FetchERR(ILL_OP))
 | Matita_freescale_opcode.HC08 -> 
(match (Matita_freescale_byte8.eq_b8 bh (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XE))) with 
   Matita_datatypes_bool.True -> 
(match (memory_filter_read m t s pc_next1) with 
   Matita_datatypes_constructors.None -> (FetchERR(ILL_FETCH_AD))
 | Matita_datatypes_constructors.Some(bl) -> 
(match (Matita_freescale_translation.full_info_of_word16 m (Matita_freescale_opcode.Word((Matita_freescale_word16.Mk_word16(bh,bl))))) with 
   Matita_datatypes_constructors.None -> (FetchERR(ILL_OP))
 | Matita_datatypes_constructors.Some(info) -> (FetchOK(info,pc_next2)))
)

 | Matita_datatypes_bool.False -> (FetchERR(ILL_OP)))

 | Matita_freescale_opcode.HCS08 -> 
(match (Matita_freescale_byte8.eq_b8 bh (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X9,Matita_freescale_exadecim.XE))) with 
   Matita_datatypes_bool.True -> 
(match (memory_filter_read m t s pc_next1) with 
   Matita_datatypes_constructors.None -> (FetchERR(ILL_FETCH_AD))
 | Matita_datatypes_constructors.Some(bl) -> 
(match (Matita_freescale_translation.full_info_of_word16 m (Matita_freescale_opcode.Word((Matita_freescale_word16.Mk_word16(bh,bl))))) with 
   Matita_datatypes_constructors.None -> (FetchERR(ILL_OP))
 | Matita_datatypes_constructors.Some(info) -> (FetchOK(info,pc_next2)))
)

 | Matita_datatypes_bool.False -> (FetchERR(ILL_OP)))

 | Matita_freescale_opcode.RS08 -> (FetchERR(ILL_OP)))

 | Matita_datatypes_constructors.Some(info) -> (FetchOK(info,pc_next1)))
)
))))))
;;

let loadb_from =
(function m -> (function t -> (function s -> (function addr -> (function cur_pc -> (function fetched -> (Matita_freescale_extra.opt_map (memory_filter_read m t s addr) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,b,(filtered_plus_w16 m t s cur_pc fetched)))))))))))))
;;

let loadbit_from =
(function m -> (function t -> (function s -> (function addr -> (function sub -> (function cur_pc -> (function fetched -> (Matita_freescale_extra.opt_map (memory_filter_read_bit m t s addr sub) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,b,(filtered_plus_w16 m t s cur_pc fetched))))))))))))))
;;

let loadw_from =
(function m -> (function t -> (function s -> (function addr -> (function cur_pc -> (function fetched -> (Matita_freescale_extra.opt_map (memory_filter_read m t s addr) (function bh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (Matita_freescale_word16.succ_w16 addr)) (function bl -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(bh,bl)),(filtered_plus_w16 m t s cur_pc fetched)))))))))))))))
;;

let writeb_to =
(function m -> (function t -> (function s -> (function addr -> (function cur_pc -> (function fetched -> (function writeb -> (Matita_freescale_extra.opt_map (memory_filter_write m t s addr writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,(filtered_plus_w16 m t s cur_pc fetched))))))))))))))
;;

let writebit_to =
(function m -> (function t -> (function s -> (function addr -> (function sub -> (function cur_pc -> (function fetched -> (function writeb -> (Matita_freescale_extra.opt_map (memory_filter_write_bit m t s addr sub writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,(filtered_plus_w16 m t s cur_pc fetched)))))))))))))))
;;

let writew_to =
(function m -> (function t -> (function s -> (function addr -> (function cur_pc -> (function fetched -> (function writew -> (Matita_freescale_extra.opt_map (memory_filter_write m t s addr (Matita_freescale_word16.w16h writew)) (function tmps1 -> (Matita_freescale_extra.opt_map (memory_filter_write m t tmps1 (Matita_freescale_word16.succ_w16 addr) (Matita_freescale_word16.w16l writew)) (function tmps2 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps2,(filtered_plus_w16 m t tmps2 cur_pc fetched))))))))))))))))
;;

type aux_load_typing = (Matita_freescale_status.any_status -> (Matita_freescale_word16.word16 -> (Matita_freescale_word16.word16 -> (Matita_nat_nat.nat -> ((Matita_freescale_status.any_status,unit (* TOO POLYMORPHIC TYPE *),Matita_freescale_word16.word16) Matita_freescale_extra.prod3T) Matita_datatypes_constructors.option))))
;;

let aux_load =
(function m -> (function t -> (function byteflag -> 
(match byteflag with 
   Matita_datatypes_bool.True -> Obj.magic ((loadb_from m t))
 | Matita_datatypes_bool.False -> Obj.magic ((loadw_from m t)))
)))
;;

type aux_write_typing = (Matita_freescale_status.any_status -> (Matita_freescale_word16.word16 -> (Matita_freescale_word16.word16 -> (Matita_nat_nat.nat -> (unit (* TOO POLYMORPHIC TYPE *) -> ((Matita_freescale_status.any_status,Matita_freescale_word16.word16) Matita_datatypes_constructors.prod) Matita_datatypes_constructors.option)))))
;;

let aux_write =
(function m -> (function t -> (function byteflag -> 
(match byteflag with 
   Matita_datatypes_bool.True -> Obj.magic ((writeb_to m t))
 | Matita_datatypes_bool.False -> Obj.magic ((writew_to m t)))
)))
;;

let mode_IMM1_load =
(function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,b,(filtered_inc_w16 m t s cur_pc)))))))))))
;;

let mode_IMM1EXT_load =
(function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),b)),(filtered_inc_w16 m t s cur_pc)))))))))))
;;

let mode_IMM2_load =
(function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function bh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function bl -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(bh,bl)),(filtered_plus_w16 m t s cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))
;;

let mode_DIR1_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addr -> (aux_load m t byteflag s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),addr)) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O))))))))))
;;

let mode_DIR1n_load =
(function m -> (function t -> (function s -> (function cur_pc -> (function sub -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addr -> (loadbit_from m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),addr)) sub cur_pc (Matita_nat_nat.S(Matita_nat_nat.O))))))))))
;;

let mode_DIR1_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addr -> (aux_write m t byteflag s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),addr)) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O)) writebw)))))))))
;;

let mode_DIR1n_write =
(function m -> (function t -> (function s -> (function cur_pc -> (function sub -> (function writeb -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addr -> (writebit_to m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),addr)) sub cur_pc (Matita_nat_nat.S(Matita_nat_nat.O)) writeb)))))))))
;;

let mode_DIR2_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addrh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function addrl -> (aux_load m t byteflag s (Matita_freescale_word16.Mk_word16(addrh,addrl)) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))
;;

let mode_DIR2_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function addrh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function addrl -> (aux_write m t byteflag s (Matita_freescale_word16.Mk_word16(addrh,addrl)) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))) writebw)))))))))))
;;

let get_IX =
(function m -> (function t -> (function s -> 
(match m with 
   Matita_freescale_opcode.HC05 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function indx -> (Matita_datatypes_constructors.Some((Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),indx))))))
 | Matita_freescale_opcode.HC08 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s) (function indx -> (Matita_datatypes_constructors.Some(indx))))
 | Matita_freescale_opcode.HCS08 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s) (function indx -> (Matita_datatypes_constructors.Some(indx))))
 | Matita_freescale_opcode.RS08 -> (Matita_datatypes_constructors.None))
)))
;;

let mode_IX0_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (aux_load m t byteflag s addr cur_pc Matita_nat_nat.O))))))))
;;

let mode_IX0_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (aux_write m t byteflag s addr cur_pc Matita_nat_nat.O writebw)))))))))
;;

let mode_IX1_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offs -> (aux_load m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),offs))) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O))))))))))))
;;

let mode_IX1ADD_load =
(function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function b -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),b))),(filtered_inc_w16 m t s cur_pc)))))))))))))
;;

let mode_IX1_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offs -> (aux_write m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),offs))) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O)) writebw)))))))))))
;;

let mode_IX2_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offsh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function offsl -> (aux_load m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16(offsh,offsl))) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))
;;

let mode_IX2ADD_load =
(function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function bh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function bl -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16(bh,bl))),(filtered_plus_w16 m t s cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))))))))))))))))))
;;

let mode_IX2_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (get_IX m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offsh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function offsl -> (aux_write m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16(offsh,offsl))) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))) writebw)))))))))))))
;;

let mode_SP1_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offs -> (aux_load m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),offs))) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O))))))))))))
;;

let mode_SP1_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offs -> (aux_write m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),offs))) cur_pc (Matita_nat_nat.S(Matita_nat_nat.O)) writebw)))))))))))
;;

let mode_SP2_load =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offsh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function offsl -> (aux_load m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16(offsh,offsl))) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O))))))))))))))))
;;

let mode_SP2_write =
(function byteflag -> (function m -> (function t -> (function s -> (function cur_pc -> (function writebw -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_sp_reg m t s) (function addr -> (Matita_freescale_extra.opt_map (memory_filter_read m t s cur_pc) (function offsh -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (filtered_inc_w16 m t s cur_pc)) (function offsl -> (aux_write m t byteflag s (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16(offsh,offsl))) cur_pc (Matita_nat_nat.S((Matita_nat_nat.S(Matita_nat_nat.O)))) writebw)))))))))))))
;;

let aux_inc_indX_16 =
(function m -> (function t -> (function s -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_16_reg m t s) (function x_op -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_16_reg m t s (Matita_freescale_word16.succ_w16 x_op)) (function s_tmp -> (Matita_datatypes_constructors.Some(s_tmp)))))))))
;;

let multi_mode_load =
(function byteflag -> (function m -> (function t -> 
(match byteflag with 
   Matita_datatypes_bool.True -> Obj.magic ((function s -> (function cur_pc -> (function i -> 
(match i with 
   Matita_freescale_opcode.MODE_INH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_status.get_acc_8_low_reg m t s),cur_pc))))
 | Matita_freescale_opcode.MODE_INHX -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function indx -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,indx,cur_pc))))))
 | Matita_freescale_opcode.MODE_INHH -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_high_reg m t s) (function indx -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,indx,cur_pc))))))
 | Matita_freescale_opcode.MODE_INHX0ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX1ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX2ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1 -> (mode_IMM1_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_IMM1EXT -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM2 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1 -> (mode_DIR1_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR2 -> (mode_DIR2_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX0 -> (mode_IX0_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX1 -> (mode_IX1_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX2 -> (mode_IX2_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_SP1 -> (mode_SP1_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_SP2 -> (mode_SP2_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR1_to_DIR1 -> (mode_DIR1_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_IMM1_to_DIR1 -> (mode_IMM1_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX0p_to_DIR1 -> (mode_IX0_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR1_to_IX0p -> (mode_DIR1_load Matita_datatypes_bool.True m t s cur_pc)
 | Matita_freescale_opcode.MODE_INHA_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX1p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_SP1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIRn(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIRn_and_IMM1(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_TNY(e) -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,e))))) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,b,cur_pc))))))
 | Matita_freescale_opcode.MODE_SRT(e) -> (Matita_freescale_extra.opt_map (memory_filter_read m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_aux_bases.byte8_of_bitrigesim e)))) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,b,cur_pc)))))))
))))
 | Matita_datatypes_bool.False -> Obj.magic ((function s -> (function cur_pc -> (function i -> 
(match i with 
   Matita_freescale_opcode.MODE_INH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX0ADD -> (Matita_freescale_extra.opt_map (get_IX m t s) (function w -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,w,cur_pc))))))
 | Matita_freescale_opcode.MODE_INHX1ADD -> (mode_IX1ADD_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_INHX2ADD -> (mode_IX2ADD_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1EXT -> (mode_IMM1EXT_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_IMM2 -> (mode_IMM2_load m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR1 -> (mode_DIR1_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR2 -> (mode_DIR2_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX0 -> (mode_IX0_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX1 -> (mode_IX1_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_IX2 -> (mode_IX2_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_SP1 -> (mode_SP1_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_SP2 -> (mode_SP2_load Matita_datatypes_bool.False m t s cur_pc)
 | Matita_freescale_opcode.MODE_DIR1_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0p_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1_to_IX0p -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc) (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16((Matita_freescale_status.get_acc_8_low_reg m t s),immb)),cur_pc')))))
))
 | Matita_freescale_opcode.MODE_INHX_and_IMM1 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.get_indX_8_low_reg m t s) (function x_op -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc) (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(x_op,immb)),cur_pc')))))
))))
 | Matita_freescale_opcode.MODE_IMM1_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc) (function s_immb1_and_PC -> 
(match s_immb1_and_PC with 
   Matita_freescale_extra.TripleT(_,immb1,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb2_and_PC -> 
(match s_immb2_and_PC with 
   Matita_freescale_extra.TripleT(_,immb2,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(immb1,immb2)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_DIR1_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_DIR1_load Matita_datatypes_bool.True m t s cur_pc) (function s_dirb_and_PC -> 
(match s_dirb_and_PC with 
   Matita_freescale_extra.TripleT(_,dirb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(dirb,immb)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_IX0_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IX0_load Matita_datatypes_bool.True m t s cur_pc) (function s_ixb_and_PC -> 
(match s_ixb_and_PC with 
   Matita_freescale_extra.TripleT(_,ixb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(ixb,immb)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_IX0p_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IX0_load Matita_datatypes_bool.True m t s cur_pc) (function s_ixb_and_PC -> 
(match s_ixb_and_PC with 
   Matita_freescale_extra.TripleT(_,ixb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_freescale_extra.opt_map (aux_inc_indX_16 m t s) (function s' -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s',(Matita_freescale_word16.Mk_word16(ixb,immb)),cur_pc'')))))))
)))
))
 | Matita_freescale_opcode.MODE_IX1_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IX1_load Matita_datatypes_bool.True m t s cur_pc) (function s_ixb_and_PC -> 
(match s_ixb_and_PC with 
   Matita_freescale_extra.TripleT(_,ixb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(ixb,immb)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_IX1p_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_IX1_load Matita_datatypes_bool.True m t s cur_pc) (function s_ixb_and_PC -> 
(match s_ixb_and_PC with 
   Matita_freescale_extra.TripleT(_,ixb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_freescale_extra.opt_map (aux_inc_indX_16 m t s) (function s' -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s',(Matita_freescale_word16.Mk_word16(ixb,immb)),cur_pc'')))))))
)))
))
 | Matita_freescale_opcode.MODE_SP1_and_IMM1 -> (Matita_freescale_extra.opt_map (mode_SP1_load Matita_datatypes_bool.True m t s cur_pc) (function s_spb_and_PC -> 
(match s_spb_and_PC with 
   Matita_freescale_extra.TripleT(_,spb,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16(spb,immb)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_DIRn(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIRn_and_IMM1(msk) -> (Matita_freescale_extra.opt_map (mode_DIR1n_load m t s cur_pc msk) (function s_dirbn_and_PC -> 
(match s_dirbn_and_PC with 
   Matita_freescale_extra.TripleT(_,dirbn,cur_pc') -> (Matita_freescale_extra.opt_map (mode_IMM1_load m t s cur_pc') (function s_immb_and_PC -> 
(match s_immb_and_PC with 
   Matita_freescale_extra.TripleT(_,immb,cur_pc'') -> (Matita_datatypes_constructors.Some((Matita_freescale_extra.TripleT(s,(Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,
(match dirbn with 
   Matita_datatypes_bool.True -> Matita_freescale_exadecim.X1
 | Matita_datatypes_bool.False -> Matita_freescale_exadecim.X0)
)),immb)),cur_pc'')))))
)))
))
 | Matita_freescale_opcode.MODE_TNY(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_SRT(_) -> (Matita_datatypes_constructors.None))
)))))
)))
;;

let multi_mode_write =
(function byteflag -> (function m -> (function t -> 
(match byteflag with 
   Matita_datatypes_bool.True -> Obj.magic ((function s -> (function cur_pc -> (function i -> (function writeb -> 
(match i with 
   Matita_freescale_opcode.MODE_INH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s writeb),cur_pc))))
 | Matita_freescale_opcode.MODE_INHX -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,cur_pc))))))
 | Matita_freescale_opcode.MODE_INHH -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_high_reg m t s writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,cur_pc))))))
 | Matita_freescale_opcode.MODE_INHX0ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX1ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX2ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1EXT -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM2 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1 -> (mode_DIR1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_DIR2 -> (mode_DIR2_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX0 -> (mode_IX0_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX1 -> (mode_IX1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX2 -> (mode_IX2_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_SP1 -> (mode_SP1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_SP2 -> (mode_SP2_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_DIR1_to_DIR1 -> (mode_DIR1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IMM1_to_DIR1 -> (mode_DIR1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX0p_to_DIR1 -> (Matita_freescale_extra.opt_map (mode_DIR1_write Matita_datatypes_bool.True m t s cur_pc writeb) (function s_and_PC -> 
(match s_and_PC with 
   Matita_datatypes_constructors.Pair(s_op,pC_op) -> (Matita_freescale_extra.opt_map (aux_inc_indX_16 m t s_op) (function s_op' -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_op',pC_op)))))))
))
 | Matita_freescale_opcode.MODE_DIR1_to_IX0p -> (Matita_freescale_extra.opt_map (mode_IX0_write Matita_datatypes_bool.True m t s cur_pc writeb) (function s_and_PC -> 
(match s_and_PC with 
   Matita_datatypes_constructors.Pair(s_op,pC_op) -> (Matita_freescale_extra.opt_map (aux_inc_indX_16 m t s_op) (function s_op' -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(s_op',pC_op)))))))
))
 | Matita_freescale_opcode.MODE_INHA_and_IMM1 -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair((Matita_freescale_status.set_acc_8_low_reg m t s writeb),cur_pc))))
 | Matita_freescale_opcode.MODE_INHX_and_IMM1 -> (Matita_freescale_extra.opt_map (Matita_freescale_status.set_indX_8_low_reg m t s writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,cur_pc))))))
 | Matita_freescale_opcode.MODE_IMM1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1_and_IMM1 -> (mode_DIR1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX0_and_IMM1 -> (mode_IX0_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX0p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX1_and_IMM1 -> (mode_IX1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_IX1p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_SP1_and_IMM1 -> (mode_SP1_write Matita_datatypes_bool.True m t s cur_pc writeb)
 | Matita_freescale_opcode.MODE_DIRn(msk) -> (mode_DIR1n_write m t s cur_pc msk (Matita_freescale_memory_struct.getn_array8T msk (Matita_freescale_memory_struct.bits_of_byte8 writeb)))
 | Matita_freescale_opcode.MODE_DIRn_and_IMM1(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_TNY(e) -> (Matita_freescale_extra.opt_map (memory_filter_write m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,e)))) writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,cur_pc))))))
 | Matita_freescale_opcode.MODE_SRT(e) -> (Matita_freescale_extra.opt_map (memory_filter_write m t s (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_aux_bases.byte8_of_bitrigesim e))) writeb) (function tmps -> (Matita_datatypes_constructors.Some((Matita_datatypes_constructors.Pair(tmps,cur_pc)))))))
)))))
 | Matita_datatypes_bool.False -> Obj.magic ((function s -> (function cur_pc -> (function i -> (function writew -> 
(match i with 
   Matita_freescale_opcode.MODE_INH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHH -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX0ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX1ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX2ADD -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1EXT -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM2 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1 -> (mode_DIR1_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_DIR2 -> (mode_DIR2_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_IX0 -> (mode_IX0_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_IX1 -> (mode_IX1_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_IX2 -> (mode_IX2_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_SP1 -> (mode_SP1_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_SP2 -> (mode_SP2_write Matita_datatypes_bool.False m t s cur_pc writew)
 | Matita_freescale_opcode.MODE_DIR1_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0p_to_DIR1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1_to_IX0p -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHA_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_INHX_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IMM1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIR1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX0p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_IX1p_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_SP1_and_IMM1 -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIRn(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_DIRn_and_IMM1(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_TNY(_) -> (Matita_datatypes_constructors.None)
 | Matita_freescale_opcode.MODE_SRT(_) -> (Matita_datatypes_constructors.None))
))))))
)))
;;
