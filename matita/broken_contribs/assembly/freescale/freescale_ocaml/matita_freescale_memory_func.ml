let mf_check_update_ranged =
(function f -> (function i -> (function s -> (function v -> (function x -> 
(match (Matita_freescale_word16.in_range x i s) with 
   Matita_datatypes_bool.True -> v
 | Matita_datatypes_bool.False -> (f x))
)))))
;;

let mf_out_of_bound_memory =
(function _ -> Matita_freescale_memory_struct.MEM_OUT_OF_BOUND)
;;

let mf_chk_get =
(function c -> (function a -> 
(match (c a) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND)))
))
;;

let mf_mem_update =
(function f -> (function c -> (function a -> (function v -> 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 c) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some(f))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((function x -> 
(match (Matita_freescale_word16.eq_w16 x a) with 
   Matita_datatypes_bool.True -> v
 | Matita_datatypes_bool.False -> (f x))
)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
))))
;;

let mf_zero_memory =
(function _ -> (Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))
;;

let mf_mem_read =
(function f -> (function c -> (function a -> 
(match (c a) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((f a)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((f a)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
)))
;;

let mf_load_from_source_at =
let rec mf_load_from_source_at = 
(function old_mem -> (function source -> (function addr -> 
(match source with 
   Matita_list_list.Nil -> old_mem
 | Matita_list_list.Cons(hd,tl) -> (function x -> 
(match (Matita_freescale_word16.lt_w16 x addr) with 
   Matita_datatypes_bool.True -> (old_mem x)
 | Matita_datatypes_bool.False -> 
(match (Matita_freescale_word16.eq_w16 x addr) with 
   Matita_datatypes_bool.True -> hd
 | Matita_datatypes_bool.False -> (mf_load_from_source_at old_mem tl (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))) x))
)
))
))) in mf_load_from_source_at
;;

