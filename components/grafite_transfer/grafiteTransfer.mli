open Equivalence

class virtual status :
  object ('self)
    val equivalences: Equivalence.equivalence list
    method equivalences: Equivalence.equivalence list
    method add_equivalence: Equivalence.equivalence -> 'self
  end


val add_equivalence: (#status as 'status) -> NCic.term -> NCic.term -> (NCic.term * NCic.term) list -> 'status

val transfer: (#status as 'status) -> NCic.term -> 'status

val print_cic_term: NCic.term -> unit