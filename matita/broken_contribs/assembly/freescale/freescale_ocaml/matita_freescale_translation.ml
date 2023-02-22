let opcode_table =
(function m -> 
(match m with 
   Matita_freescale_opcode.HC05 -> Obj.magic (Matita_freescale_table_HC05.opcode_table_HC05)
 | Matita_freescale_opcode.HC08 -> Obj.magic (Matita_freescale_table_HC08.opcode_table_HC08)
 | Matita_freescale_opcode.HCS08 -> Obj.magic (Matita_freescale_table_HCS08.opcode_table_HCS08)
 | Matita_freescale_opcode.RS08 -> Obj.magic (Matita_freescale_table_RS08.opcode_table_RS08))
)
;;

let full_info_of_word16 =
(function m -> (function borw -> (let rec aux = 
(function param -> 
(match param with 
   Matita_list_list.Nil -> (Matita_datatypes_constructors.None)
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.thd4T hd) with 
   Matita_freescale_opcode.Byte(b) -> 
(match borw with 
   Matita_freescale_opcode.Byte(borw') -> 
(match (Matita_freescale_byte8.eq_b8 borw' b) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some(hd))
 | Matita_datatypes_bool.False -> (aux tl))

 | Matita_freescale_opcode.Word(_) -> (aux tl))

 | Matita_freescale_opcode.Word(w) -> 
(match borw with 
   Matita_freescale_opcode.Byte(_) -> (aux tl)
 | Matita_freescale_opcode.Word(borw') -> 
(match (Matita_freescale_word16.eq_w16 borw' w) with 
   Matita_datatypes_bool.True -> (Matita_datatypes_constructors.Some(hd))
 | Matita_datatypes_bool.False -> (aux tl))
)
)
)
) in aux (opcode_table m))))
;;

type t_byte8 =
TByte of Matita_freescale_byte8.byte8
;;

let t_byte8_rec =
(function m -> (function f -> (function t -> 
(match t with 
   TByte(b) -> (f b))
)))
;;

let t_byte8_rect =
(function m -> (function f -> (function t -> 
(match t with 
   TByte(b) -> (f b))
)))
;;

let t_byte8_OF_bitrigesim =
(function a -> (function m -> (TByte((Matita_freescale_aux_bases.byte8_of_bitrigesim a)))))
;;

type mA_check =
MaINH
 | MaINHA
 | MaINHX
 | MaINHH
 | MaINHX0ADD
 | MaINHX1ADD of Matita_freescale_byte8.byte8
 | MaINHX2ADD of Matita_freescale_word16.word16
 | MaIMM1 of Matita_freescale_byte8.byte8
 | MaIMM1EXT of Matita_freescale_byte8.byte8
 | MaIMM2 of Matita_freescale_word16.word16
 | MaDIR1 of Matita_freescale_byte8.byte8
 | MaDIR2 of Matita_freescale_word16.word16
 | MaIX0
 | MaIX1 of Matita_freescale_byte8.byte8
 | MaIX2 of Matita_freescale_word16.word16
 | MaSP1 of Matita_freescale_byte8.byte8
 | MaSP2 of Matita_freescale_word16.word16
 | MaDIR1_to_DIR1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaIMM1_to_DIR1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaIX0p_to_DIR1 of Matita_freescale_byte8.byte8
 | MaDIR1_to_IX0p of Matita_freescale_byte8.byte8
 | MaINHA_and_IMM1 of Matita_freescale_byte8.byte8
 | MaINHX_and_IMM1 of Matita_freescale_byte8.byte8
 | MaIMM1_and_IMM1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaDIR1_and_IMM1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaIX0_and_IMM1 of Matita_freescale_byte8.byte8
 | MaIX0p_and_IMM1 of Matita_freescale_byte8.byte8
 | MaIX1_and_IMM1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaIX1p_and_IMM1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaSP1_and_IMM1 of Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaDIRn of Matita_freescale_aux_bases.oct * Matita_freescale_byte8.byte8
 | MaDIRn_and_IMM1 of Matita_freescale_aux_bases.oct * Matita_freescale_byte8.byte8 * Matita_freescale_byte8.byte8
 | MaTNY of Matita_freescale_exadecim.exadecim
 | MaSRT of Matita_freescale_aux_bases.bitrigesim
;;

let mA_check_rec =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function f -> (function f1 -> (function f2 -> (function f3 -> (function f4 -> (function f5 -> (function f6 -> (function p5 -> (function f7 -> (function f8 -> (function f9 -> (function f10 -> (function f11 -> (function f12 -> (function f13 -> (function f14 -> (function f15 -> (function f16 -> (function f17 -> (function f18 -> (function f19 -> (function f20 -> (function f21 -> (function f22 -> (function f23 -> (function f24 -> (function f25 -> (function f26 -> (function f27 -> (function i -> (function m -> 
(match m with 
   MaINH -> p
 | MaINHA -> p1
 | MaINHX -> p2
 | MaINHH -> p3
 | MaINHX0ADD -> p4
 | MaINHX1ADD(b) -> (f b)
 | MaINHX2ADD(w) -> (f1 w)
 | MaIMM1(b) -> (f2 b)
 | MaIMM1EXT(b) -> (f3 b)
 | MaIMM2(w) -> (f4 w)
 | MaDIR1(b) -> (f5 b)
 | MaDIR2(w) -> (f6 w)
 | MaIX0 -> p5
 | MaIX1(b) -> (f7 b)
 | MaIX2(w) -> (f8 w)
 | MaSP1(b) -> (f9 b)
 | MaSP2(w) -> (f10 w)
 | MaDIR1_to_DIR1(b,b1) -> (f11 b b1)
 | MaIMM1_to_DIR1(b,b1) -> (f12 b b1)
 | MaIX0p_to_DIR1(b) -> (f13 b)
 | MaDIR1_to_IX0p(b) -> (f14 b)
 | MaINHA_and_IMM1(b) -> (f15 b)
 | MaINHX_and_IMM1(b) -> (f16 b)
 | MaIMM1_and_IMM1(b,b1) -> (f17 b b1)
 | MaDIR1_and_IMM1(b,b1) -> (f18 b b1)
 | MaIX0_and_IMM1(b) -> (f19 b)
 | MaIX0p_and_IMM1(b) -> (f20 b)
 | MaIX1_and_IMM1(b,b1) -> (f21 b b1)
 | MaIX1p_and_IMM1(b,b1) -> (f22 b b1)
 | MaSP1_and_IMM1(b,b1) -> (f23 b b1)
 | MaDIRn(o,b) -> (f24 o b)
 | MaDIRn_and_IMM1(o,b,b1) -> (f25 o b b1)
 | MaTNY(e) -> (f26 e)
 | MaSRT(b) -> (f27 b))
))))))))))))))))))))))))))))))))))))
;;

let mA_check_rect =
(function p -> (function p1 -> (function p2 -> (function p3 -> (function p4 -> (function f -> (function f1 -> (function f2 -> (function f3 -> (function f4 -> (function f5 -> (function f6 -> (function p5 -> (function f7 -> (function f8 -> (function f9 -> (function f10 -> (function f11 -> (function f12 -> (function f13 -> (function f14 -> (function f15 -> (function f16 -> (function f17 -> (function f18 -> (function f19 -> (function f20 -> (function f21 -> (function f22 -> (function f23 -> (function f24 -> (function f25 -> (function f26 -> (function f27 -> (function i -> (function m -> 
(match m with 
   MaINH -> p
 | MaINHA -> p1
 | MaINHX -> p2
 | MaINHH -> p3
 | MaINHX0ADD -> p4
 | MaINHX1ADD(b) -> (f b)
 | MaINHX2ADD(w) -> (f1 w)
 | MaIMM1(b) -> (f2 b)
 | MaIMM1EXT(b) -> (f3 b)
 | MaIMM2(w) -> (f4 w)
 | MaDIR1(b) -> (f5 b)
 | MaDIR2(w) -> (f6 w)
 | MaIX0 -> p5
 | MaIX1(b) -> (f7 b)
 | MaIX2(w) -> (f8 w)
 | MaSP1(b) -> (f9 b)
 | MaSP2(w) -> (f10 w)
 | MaDIR1_to_DIR1(b,b1) -> (f11 b b1)
 | MaIMM1_to_DIR1(b,b1) -> (f12 b b1)
 | MaIX0p_to_DIR1(b) -> (f13 b)
 | MaDIR1_to_IX0p(b) -> (f14 b)
 | MaINHA_and_IMM1(b) -> (f15 b)
 | MaINHX_and_IMM1(b) -> (f16 b)
 | MaIMM1_and_IMM1(b,b1) -> (f17 b b1)
 | MaDIR1_and_IMM1(b,b1) -> (f18 b b1)
 | MaIX0_and_IMM1(b) -> (f19 b)
 | MaIX0p_and_IMM1(b) -> (f20 b)
 | MaIX1_and_IMM1(b,b1) -> (f21 b b1)
 | MaIX1p_and_IMM1(b,b1) -> (f22 b b1)
 | MaSP1_and_IMM1(b,b1) -> (f23 b b1)
 | MaDIRn(o,b) -> (f24 o b)
 | MaDIRn_and_IMM1(o,b,b1) -> (f25 o b b1)
 | MaTNY(e) -> (f26 e)
 | MaSRT(b) -> (f27 b))
))))))))))))))))))))))))))))))))))))
;;

type instruction =
Instr of Matita_freescale_opcode.instr_mode * Matita_freescale_opcode.opcode * mA_check
;;

let instruction_rec =
(function f -> (function i -> 
(match i with 
   Instr(i1,o,m) -> (f i1 o m))
))
;;

let instruction_rect =
(function f -> (function i -> 
(match i with 
   Instr(i1,o,m) -> (f i1 o m))
))
;;

let args_picker =
(function m -> (function i -> (function args -> 
(match args with 
   MaINH -> Obj.magic ((Matita_list_list.Nil))
 | MaINHA -> Obj.magic ((Matita_list_list.Nil))
 | MaINHX -> Obj.magic ((Matita_list_list.Nil))
 | MaINHH -> Obj.magic ((Matita_list_list.Nil))
 | MaINHX0ADD -> Obj.magic ((Matita_list_list.Nil))
 | MaINHX1ADD(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaINHX2ADD(w) -> Obj.magic ((Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h w))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l w))),(Matita_list_list.Nil))))))
 | MaIMM1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIMM1EXT(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIMM2(w) -> Obj.magic ((Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h w))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l w))),(Matita_list_list.Nil))))))
 | MaDIR1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaDIR2(w) -> Obj.magic ((Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h w))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l w))),(Matita_list_list.Nil))))))
 | MaIX0 -> Obj.magic ((Matita_list_list.Nil))
 | MaIX1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIX2(w) -> Obj.magic ((Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h w))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l w))),(Matita_list_list.Nil))))))
 | MaSP1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaSP2(w) -> Obj.magic ((Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h w))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l w))),(Matita_list_list.Nil))))))
 | MaDIR1_to_DIR1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaIMM1_to_DIR1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaIX0p_to_DIR1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaDIR1_to_IX0p(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaINHA_and_IMM1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaINHX_and_IMM1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIMM1_and_IMM1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaDIR1_and_IMM1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaIX0_and_IMM1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIX0p_and_IMM1(b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaIX1_and_IMM1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaIX1p_and_IMM1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaSP1_and_IMM1(b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaDIRn(_,b) -> Obj.magic ((Matita_list_list.Cons((TByte(b)),(Matita_list_list.Nil))))
 | MaDIRn_and_IMM1(_,b1,b2) -> Obj.magic ((Matita_list_list.Cons((TByte(b1)),(Matita_list_list.Cons((TByte(b2)),(Matita_list_list.Nil))))))
 | MaTNY(_) -> Obj.magic ((Matita_list_list.Nil))
 | MaSRT(_) -> Obj.magic ((Matita_list_list.Nil)))
)))
;;

let bytes_of_pseudo_instr_mode_param =
(function m -> (function o -> (function i -> (function p -> (let rec aux = 
(function param -> 
(match param with 
   Matita_list_list.Nil -> (Matita_datatypes_constructors.None)
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_extra.and_bool (Matita_freescale_opcode.eqop m o (Matita_freescale_extra.fst4T hd)) (Matita_freescale_opcode.eqim i (Matita_freescale_extra.snd4T hd))) with 
   Matita_datatypes_bool.True -> 
(match (Matita_freescale_extra.thd4T hd) with 
   Matita_freescale_opcode.Byte(isab) -> (Matita_datatypes_constructors.Some((Matita_list_list.append (Matita_list_list.Cons((TByte(isab)),(Matita_list_list.Nil))) (args_picker m i p))))
 | Matita_freescale_opcode.Word(isaw) -> (Matita_datatypes_constructors.Some((Matita_list_list.append (Matita_list_list.Cons((TByte((Matita_freescale_word16.w16h isaw))),(Matita_list_list.Cons((TByte((Matita_freescale_word16.w16l isaw))),(Matita_list_list.Nil))))) (args_picker m i p)))))

 | Matita_datatypes_bool.False -> (aux tl))
)
) in aux (opcode_table m))))))
;;

let opcode_to_any =
(function m -> (function o -> (Matita_freescale_opcode.AnyOP(o))))
;;

let compile =
(function mcu -> (function i -> (function op -> (function arg -> (let res = (bytes_of_pseudo_instr_mode_param mcu (opcode_to_any mcu op) i arg) in (let value = (
(match res with 
   Matita_datatypes_constructors.None -> Obj.magic ((Matita_logic_connectives.false_rect))
 | Matita_datatypes_constructors.Some(v) -> Obj.magic (v))
) in value))))))
;;

let source_to_byte8 =
(function mcu -> 
(match mcu with 
   Matita_freescale_opcode.HC05 -> Obj.magic ((function l -> (let rec aux = 
(function p1 -> (function p2 -> 
(match p1 with 
   Matita_list_list.Nil -> p2
 | Matita_list_list.Cons(hd,tl) -> 
(match hd with 
   TByte(b) -> (aux tl (Matita_list_list.append p2 (Matita_list_list.Cons(b,(Matita_list_list.Nil))))))
)
)) in aux l (Matita_list_list.Nil))))
 | Matita_freescale_opcode.HC08 -> Obj.magic ((function l -> (let rec aux = 
(function p1 -> (function p2 -> 
(match p1 with 
   Matita_list_list.Nil -> p2
 | Matita_list_list.Cons(hd,tl) -> 
(match hd with 
   TByte(b) -> (aux tl (Matita_list_list.append p2 (Matita_list_list.Cons(b,(Matita_list_list.Nil))))))
)
)) in aux l (Matita_list_list.Nil))))
 | Matita_freescale_opcode.HCS08 -> Obj.magic ((function l -> (let rec aux = 
(function p1 -> (function p2 -> 
(match p1 with 
   Matita_list_list.Nil -> p2
 | Matita_list_list.Cons(hd,tl) -> 
(match hd with 
   TByte(b) -> (aux tl (Matita_list_list.append p2 (Matita_list_list.Cons(b,(Matita_list_list.Nil))))))
)
)) in aux l (Matita_list_list.Nil))))
 | Matita_freescale_opcode.RS08 -> Obj.magic ((function l -> (let rec aux = 
(function p1 -> (function p2 -> 
(match p1 with 
   Matita_list_list.Nil -> p2
 | Matita_list_list.Cons(hd,tl) -> 
(match hd with 
   TByte(b) -> (aux tl (Matita_list_list.append p2 (Matita_list_list.Cons(b,(Matita_list_list.Nil))))))
)
)) in aux l (Matita_list_list.Nil)))))
)
;;

