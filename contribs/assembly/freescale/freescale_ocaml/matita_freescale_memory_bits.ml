let mb_out_of_bound_memory =
(let base = (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND)) in (let lev4 = (Matita_freescale_memory_struct.Array_16T(base,base,base,base,base,base,base,base,base,base,base,base,base,base,base,base)) in (let lev3 = (Matita_freescale_memory_struct.Array_16T(lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4)) in (let lev2 = (Matita_freescale_memory_struct.Array_16T(lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3)) in (let lev1 = (Matita_freescale_memory_struct.Array_16T(lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2)) in lev1)))))
;;

let mb_zero_memory =
(let base = (Matita_freescale_memory_struct.Array_8T(Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False,Matita_datatypes_bool.False)) in (let lev4 = (Matita_freescale_memory_struct.Array_16T(base,base,base,base,base,base,base,base,base,base,base,base,base,base,base,base)) in (let lev3 = (Matita_freescale_memory_struct.Array_16T(lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4)) in (let lev2 = (Matita_freescale_memory_struct.Array_16T(lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3)) in (let lev1 = (Matita_freescale_memory_struct.Array_16T(lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2)) in lev1)))))
;;

let mb_mem_update_bit =
(function mem -> (function chk -> (function addr -> (function sub -> (function v -> 
(match (Matita_freescale_memory_struct.getn_array8T sub (Matita_freescale_memory_trees.mt_visit chk addr)) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some(mem))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_trees.mt_update mem addr (Matita_freescale_memory_struct.setn_array8T sub (Matita_freescale_memory_trees.mt_visit mem addr) v))))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
)))))
;;

let mb_chk_update_bit =
(function chk -> (function addr -> (function sub -> (function v -> (Matita_freescale_memory_trees.mt_update chk addr (Matita_freescale_memory_struct.setn_array8T sub (Matita_freescale_memory_trees.mt_visit chk addr) v))))))
;;

let mb_mem_read_bit =
(function mem -> (function chk -> (function addr -> (function sub -> 
(match (Matita_freescale_memory_struct.getn_array8T sub (Matita_freescale_memory_trees.mt_visit chk addr)) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T sub (Matita_freescale_memory_trees.mt_visit mem addr))))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T sub (Matita_freescale_memory_trees.mt_visit mem addr))))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
))))
;;

let mb_chk_get =
(function chk -> (function addr -> (let c = (Matita_freescale_memory_trees.mt_visit chk addr) in (Matita_freescale_memory_struct.Array_8T((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 c),(Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 c))))))
;;

let mb_mem_update =
(function mem -> (function chk -> (function addr -> (function v -> (let old_value = (Matita_freescale_memory_trees.mt_visit mem addr) in (let new_value = (Matita_freescale_memory_struct.bits_of_byte8 v) in (let newbit0 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit1 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit2 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit3 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit4 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit5 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit6 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit7 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 old_value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 new_value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (Matita_freescale_extra.opt_map newbit0 (function nb0 -> (Matita_freescale_extra.opt_map newbit1 (function nb1 -> (Matita_freescale_extra.opt_map newbit2 (function nb2 -> (Matita_freescale_extra.opt_map newbit3 (function nb3 -> (Matita_freescale_extra.opt_map newbit4 (function nb4 -> (Matita_freescale_extra.opt_map newbit5 (function nb5 -> (Matita_freescale_extra.opt_map newbit6 (function nb6 -> (Matita_freescale_extra.opt_map newbit7 (function nb7 -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_trees.mt_update mem addr (Matita_freescale_memory_struct.Array_8T(nb7,nb6,nb5,nb4,nb3,nb2,nb1,nb0)))))))))))))))))))))))))))))))))))
;;

let mb_mem_read =
(function mem -> (function chk -> (function addr -> (let bit_types = (Matita_freescale_memory_trees.mt_visit chk addr) in (let value = (Matita_freescale_memory_trees.mt_visit mem addr) in (let newbit0 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit1 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O1 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit2 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O2 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit3 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O3 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit4 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O4 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit5 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O5 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit6 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O6 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (let newbit7 = 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 bit_types) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 value)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O7 value)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
 in (Matita_freescale_extra.opt_map newbit0 (function nb0 -> (Matita_freescale_extra.opt_map newbit1 (function nb1 -> (Matita_freescale_extra.opt_map newbit2 (function nb2 -> (Matita_freescale_extra.opt_map newbit3 (function nb3 -> (Matita_freescale_extra.opt_map newbit4 (function nb4 -> (Matita_freescale_extra.opt_map newbit5 (function nb5 -> (Matita_freescale_extra.opt_map newbit6 (function nb6 -> (Matita_freescale_extra.opt_map newbit7 (function nb7 -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.byte8_of_bits (Matita_freescale_memory_struct.Array_8T(nb7,nb6,nb5,nb4,nb3,nb2,nb1,nb0))))))))))))))))))))))))))))))))))
;;

let mb_load_from_source_at =
let rec mb_load_from_source_at = 
(function old_mem -> (function source -> (function addr -> 
(match source with 
   Matita_list_list.Nil -> old_mem
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_word16.lt_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) with 
   Matita_datatypes_bool.True -> (mb_load_from_source_at (Matita_freescale_memory_trees.mt_update old_mem addr (Matita_freescale_memory_struct.bits_of_byte8 hd)) tl (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))))
 | Matita_datatypes_bool.False -> (Matita_freescale_memory_trees.mt_update old_mem addr (Matita_freescale_memory_struct.bits_of_byte8 hd)))
)
))) in mb_load_from_source_at
;;

