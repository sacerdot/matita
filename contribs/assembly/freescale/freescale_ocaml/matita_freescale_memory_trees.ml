let mt_out_of_bound_memory =
(let lev4 = (Matita_freescale_memory_struct.Array_16T(Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND)) in (let lev3 = (Matita_freescale_memory_struct.Array_16T(lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4)) in (let lev2 = (Matita_freescale_memory_struct.Array_16T(lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3)) in (let lev1 = (Matita_freescale_memory_struct.Array_16T(lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2)) in lev1))))
;;

let mt_zero_memory =
(let lev4 = (Matita_freescale_memory_struct.Array_16T((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)))) in (let lev3 = (Matita_freescale_memory_struct.Array_16T(lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4,lev4)) in (let lev2 = (Matita_freescale_memory_struct.Array_16T(lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3,lev3)) in (let lev1 = (Matita_freescale_memory_struct.Array_16T(lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2,lev2)) in lev1))))
;;

let mt_visit =
(function data -> (function addr -> 
(match addr with 
   Matita_freescale_word16.Mk_word16(wh,wl) -> (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8l wl) (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h wl) (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8l wh) (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h wh) data)))))
))
;;

let mt_update =
(function data -> (function addr -> (function v -> 
(match addr with 
   Matita_freescale_word16.Mk_word16(wh,wl) -> (let lev2 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h wh) data) in (let lev3 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8l wh) lev2) in (let lev4 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h wl) lev3) in (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h wh) data (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l wh) lev2 (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h wl) lev3 (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l wl) lev4 v))))))))
)))
;;

let mt_update_ranged =
(function data -> (function i -> (function s -> (function v -> 
(match (Matita_freescale_word16.le_w16 i s) with 
   Matita_datatypes_bool.True -> 
(match i with 
   Matita_freescale_word16.Mk_word16(ih,il) -> 
(match s with 
   Matita_freescale_word16.Mk_word16(sh,sl) -> (let ilev2 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h ih) data) in (let ilev3 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8l ih) ilev2) in (let ilev4 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h il) ilev3) in (let slev2 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h sh) data) in (let slev3 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8l sh) slev2) in (let slev4 = (Matita_freescale_memory_struct.getn_array16T (Matita_freescale_byte8.b8h sl) slev3) in (let vlev4 = (Matita_freescale_memory_struct.Array_16T(v,v,v,v,v,v,v,v,v,v,v,v,v,v,v,v)) in (let vlev3 = (Matita_freescale_memory_struct.Array_16T(vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4,vlev4)) in (let vlev2 = (Matita_freescale_memory_struct.Array_16T(vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3,vlev3)) in 
(match (Matita_freescale_exadecim.eq_ex (Matita_freescale_byte8.b8h ih) (Matita_freescale_byte8.b8h sh)) with 
   Matita_datatypes_bool.True -> 
(match (Matita_freescale_exadecim.eq_ex (Matita_freescale_byte8.b8l ih) (Matita_freescale_byte8.b8l sh)) with 
   Matita_datatypes_bool.True -> 
(match (Matita_freescale_exadecim.eq_ex (Matita_freescale_byte8.b8h il) (Matita_freescale_byte8.b8h sl)) with 
   Matita_datatypes_bool.True -> (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h ih) data (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l ih) ilev2 (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h il) ilev3 (Matita_freescale_memory_struct.setmn_array16T (Matita_freescale_byte8.b8l il) (Matita_freescale_byte8.b8l sl) ilev4 v))))
 | Matita_datatypes_bool.False -> (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h ih) data (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l ih) ilev2 (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h sl) (Matita_freescale_memory_struct.setmn_array16T_succ_pred (Matita_freescale_byte8.b8h il) (Matita_freescale_byte8.b8h sl) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h il) ilev3 (Matita_freescale_memory_struct.setmn_array16T (Matita_freescale_byte8.b8l il) Matita_freescale_exadecim.XF ilev4 v)) vlev4) (Matita_freescale_memory_struct.setmn_array16T Matita_freescale_exadecim.X0 (Matita_freescale_byte8.b8l sl) slev4 v)))))

 | Matita_datatypes_bool.False -> (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h ih) data (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l sh) (Matita_freescale_memory_struct.setmn_array16T_succ_pred (Matita_freescale_byte8.b8l ih) (Matita_freescale_byte8.b8l sh) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l ih) ilev2 (Matita_freescale_memory_struct.setmn_array16T_succ (Matita_freescale_byte8.b8h il) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h il) ilev3 (Matita_freescale_memory_struct.setmn_array16T (Matita_freescale_byte8.b8l il) Matita_freescale_exadecim.XF ilev4 v)) vlev4)) vlev3) (Matita_freescale_memory_struct.setmn_array16T_pred (Matita_freescale_byte8.b8h sl) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h sl) slev3 (Matita_freescale_memory_struct.setmn_array16T Matita_freescale_exadecim.X0 (Matita_freescale_byte8.b8l sl) slev4 v)) vlev4))))

 | Matita_datatypes_bool.False -> (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h sh) (Matita_freescale_memory_struct.setmn_array16T_succ_pred (Matita_freescale_byte8.b8h ih) (Matita_freescale_byte8.b8h sh) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h ih) data (Matita_freescale_memory_struct.setmn_array16T_succ (Matita_freescale_byte8.b8l ih) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l ih) ilev2 (Matita_freescale_memory_struct.setmn_array16T_succ (Matita_freescale_byte8.b8h il) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h il) ilev3 (Matita_freescale_memory_struct.setmn_array16T (Matita_freescale_byte8.b8l il) Matita_freescale_exadecim.XF ilev4 v)) vlev4)) vlev3)) vlev2) (Matita_freescale_memory_struct.setmn_array16T_pred (Matita_freescale_byte8.b8l sh) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8l sh) slev2 (Matita_freescale_memory_struct.setmn_array16T_pred (Matita_freescale_byte8.b8h sl) (Matita_freescale_memory_struct.setn_array16T (Matita_freescale_byte8.b8h sl) slev3 (Matita_freescale_memory_struct.setmn_array16T Matita_freescale_exadecim.X0 (Matita_freescale_byte8.b8l sl) slev4 v)) vlev4)) vlev3)))
))))))))))
)

 | Matita_datatypes_bool.False -> data)
))))
;;

let mt_chk_get =
(function chk -> (function addr -> 
(match (mt_visit chk addr) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY,Matita_freescale_memory_struct.MEM_READ_ONLY))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE,Matita_freescale_memory_struct.MEM_READ_WRITE))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_freescale_memory_struct.Array_8T(Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND,Matita_freescale_memory_struct.MEM_OUT_OF_BOUND)))
))
;;

let mt_mem_update =
(function mem -> (function chk -> (function addr -> (function v -> 
(match (Matita_freescale_memory_struct.getn_array8T Matita_freescale_aux_bases.O0 chk) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some(mem))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((mt_update mem addr v)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
))))
;;

let mt_mem_read =
(function mem -> (function chk -> (function addr -> 
(match (mt_visit chk addr) with 
   Matita_freescale_memory_struct.MEM_READ_ONLY -> (Matita_datatypes_constructors.Some((mt_visit mem addr)))
 | Matita_freescale_memory_struct.MEM_READ_WRITE -> (Matita_datatypes_constructors.Some((mt_visit mem addr)))
 | Matita_freescale_memory_struct.MEM_OUT_OF_BOUND -> (Matita_datatypes_constructors.None))
)))
;;

let mt_load_from_source_at =
let rec mt_load_from_source_at = 
(function old_mem -> (function source -> (function addr -> 
(match source with 
   Matita_list_list.Nil -> old_mem
 | Matita_list_list.Cons(hd,tl) -> 
(match (Matita_freescale_word16.lt_w16 addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.XF,Matita_freescale_exadecim.XF))))) with 
   Matita_datatypes_bool.True -> (mt_load_from_source_at (mt_update old_mem addr hd) tl (Matita_freescale_word16.plus_w16nc addr (Matita_freescale_word16.Mk_word16((Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X0)),(Matita_freescale_byte8.Mk_byte8(Matita_freescale_exadecim.X0,Matita_freescale_exadecim.X1))))))
 | Matita_datatypes_bool.False -> (mt_update old_mem addr hd))
)
))) in mt_load_from_source_at
;;

