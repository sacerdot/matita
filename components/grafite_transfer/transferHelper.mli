
module TransferHelper : sig
  
  val stringify_cic_term: NCic.term -> string 

  val print_cic_term: NCic.term -> unit
  
end