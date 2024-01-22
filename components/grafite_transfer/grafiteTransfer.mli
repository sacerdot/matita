type equivalence

class virtual status :
  object ('self)
    val equivalences: equivalence list
    method equivalences: equivalence list
    method add_equivalence: equivalence -> 'self
  end


val add_equivalence: (#status as 'status) -> NCic.term -> NCic.term -> (NCic.term * NCic.term) list -> 'status

val transfer: (#status as 'status) -> NCic.term -> 'status

val print_cic_term: NCic.term -> unit