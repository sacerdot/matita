
module Equivalence : sig
  type equivalence

  (*Given the (inductive) types T and T' and list of mappings between the constructors of the 2 terms
    creates an equivalence object for them*)
  val make_equivalence: NCic.term -> NCic.term -> (NCic.term * NCic.term) list -> equivalence
  

  (*Given a term that should be an inductive type or constructor and list of equivalencese
     returns the corresponding term modulo it's equivalence*)
  val equivalent_type: NCic.term -> equivalence list -> NCic.term option 
  
end