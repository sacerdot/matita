type equivalence = {
  sourceType: NCic.term;
  targetType: NCic.term;
  rest: string;
}

class virtual status :
  object ('self)
    val equivalences: equivalence list
    method equivalences: equivalence list
    method add_equivalence: equivalence -> 'self
    method equivalent_type: NCic.term -> NCic.term option
  end


val add_equivalence: (#status as 'status) -> NCic.term -> NCic.term -> 'status

val transfer: (#status as 'status) -> NCic.term -> 'status

val print_cic_term: NCic.term -> unit