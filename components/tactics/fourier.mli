type rational = { num : int; den : int; } 
val print_rational : rational -> unit
val pgcd : int -> int -> int
val r0 : rational
val r1 : rational
val rnorm : rational -> rational
val rop : rational -> rational
val rplus : rational -> rational -> rational
val rminus : rational -> rational -> rational
val rmult : rational -> rational -> rational
val rinv : rational -> rational
val rdiv : rational -> rational -> rational
val rinf : rational -> rational -> bool
val rinfeq : rational -> rational -> bool
type ineq = { coef : rational list; hist : rational list; strict : bool; } 
val pop : 'a -> 'a list ref -> unit
val partitionne : ineq list -> ineq list list
val add_hist : (rational list * bool) list -> ineq list
val ie_add : ineq -> ineq -> ineq
val ie_emult : rational -> ineq -> ineq
val ie_tl : ineq -> ineq
val hd_coef : ineq -> rational
val deduce_add : ineq list -> ineq list -> ineq list
val deduce1 : ineq list -> int -> ineq list
val deduce : (rational list * bool) list -> ineq list
val unsolvable :
  (rational list * bool) list -> (rational * bool * rational list) list
