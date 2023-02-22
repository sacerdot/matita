type memory_impl =
MEM_FUNC
 | MEM_TREE
 | MEM_BITS
;;

let memory_impl_rec =
(function p -> (function p1 -> (function p2 -> (function m -> 
(match m with 
   MEM_FUNC -> p
 | MEM_TREE -> p1
 | MEM_BITS -> p2)
))))
;;

let memory_impl_rect =
(function p -> (function p1 -> (function p2 -> (function m -> 
(match m with 
   MEM_FUNC -> p
 | MEM_TREE -> p1
 | MEM_BITS -> p2)
))))
;;

type aux_mem_type = unit (* TOO POLYMORPHIC TYPE *)
;;

type aux_chk_type = unit (* TOO POLYMORPHIC TYPE *)
;;

let out_of_bound_memory =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_out_of_bound_memory)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_out_of_bound_memory)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_out_of_bound_memory))
)
;;

let zero_memory =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_zero_memory)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_zero_memory)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_zero_memory))
)
;;

let mem_read_abs =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic ((function m -> (function addr -> (m addr))))
 | MEM_TREE -> Obj.magic ((function m -> (function addr -> (Matita_freescale_memory_trees.mt_visit m addr))))
 | MEM_BITS -> Obj.magic ((function m -> (function addr -> (Matita_freescale_memory_struct.byte8_of_bits (Matita_freescale_memory_trees.mt_visit m addr))))))
)
;;

let chk_get =
(function t -> (function c -> (function addr -> (
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_chk_get)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_chk_get)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_chk_get))
 c addr))))
;;

let mem_read =
(function t -> (function m -> (function c -> (function addr -> (
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_mem_read)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_mem_read)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_mem_read))
 m c addr)))))
;;

let mem_read_bit =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_func.mf_mem_read m c addr) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T o (Matita_freescale_memory_struct.bits_of_byte8 b)))))))))))
 | MEM_TREE -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_trees.mt_mem_read m c addr) (function b -> (Matita_datatypes_constructors.Some((Matita_freescale_memory_struct.getn_array8T o (Matita_freescale_memory_struct.bits_of_byte8 b)))))))))))
 | MEM_BITS -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (Matita_freescale_memory_bits.mb_mem_read_bit m c addr o)))))))
)
;;

let mem_update =
(function t -> (function m -> (function c -> (function addr -> (function v -> (
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_mem_update)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_mem_update)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_mem_update))
 m (chk_get t c addr) addr v))))))
;;

let mem_update_bit =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (function v -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_func.mf_mem_read m c addr) (function b -> (Matita_freescale_memory_func.mf_mem_update m (chk_get MEM_FUNC c addr) addr (Matita_freescale_memory_struct.byte8_of_bits (Matita_freescale_memory_struct.setn_array8T o (Matita_freescale_memory_struct.bits_of_byte8 b) v)))))))))))
 | MEM_TREE -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (function v -> (Matita_freescale_extra.opt_map (Matita_freescale_memory_trees.mt_mem_read m c addr) (function b -> (Matita_freescale_memory_trees.mt_mem_update m (chk_get MEM_TREE c addr) addr (Matita_freescale_memory_struct.byte8_of_bits (Matita_freescale_memory_struct.setn_array8T o (Matita_freescale_memory_struct.bits_of_byte8 b) v)))))))))))
 | MEM_BITS -> Obj.magic ((function m -> (function c -> (function addr -> (function o -> (function v -> (Matita_freescale_memory_bits.mb_mem_update_bit m c addr o v))))))))
)
;;

let load_from_source_at =
(function t -> (function m -> (function l -> (function addr -> (
(match t with 
   MEM_FUNC -> Obj.magic (Matita_freescale_memory_func.mf_load_from_source_at)
 | MEM_TREE -> Obj.magic (Matita_freescale_memory_trees.mt_load_from_source_at)
 | MEM_BITS -> Obj.magic (Matita_freescale_memory_bits.mb_load_from_source_at))
 m l addr)))))
;;

let check_update_ranged =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic ((function c -> (function inf -> (function sup -> (function v -> (Matita_freescale_memory_func.mf_check_update_ranged c inf sup v))))))
 | MEM_TREE -> Obj.magic ((function c -> (function inf -> (function sup -> (function v -> (Matita_freescale_memory_trees.mt_update_ranged c inf sup v))))))
 | MEM_BITS -> Obj.magic ((function c -> (function inf -> (function sup -> (function v -> (Matita_freescale_memory_trees.mt_update_ranged c inf sup (Matita_freescale_memory_struct.Array_8T(v,v,v,v,v,v,v,v)))))))))
)
;;

let check_update_bit =
(function t -> 
(match t with 
   MEM_FUNC -> Obj.magic ((function c -> (function addr -> (function o -> (function v -> c)))))
 | MEM_TREE -> Obj.magic ((function c -> (function addr -> (function o -> (function v -> c)))))
 | MEM_BITS -> Obj.magic ((function c -> (function addr -> (function o -> (function v -> (Matita_freescale_memory_bits.mb_chk_update_bit c addr o v)))))))
)
;;

