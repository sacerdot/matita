open TransferHelper

let are_inductive_and_equal (type1: NCic.term) (type2: NCic.term): bool = 
  print_endline "comparing type1:";
  TransferHelper.print_cic_term type1;
  print_endline "with type2:";
  TransferHelper.print_cic_term type2;
  match type1, type2 with 
  | NCic.Const ref1, NCic.Const ref2 -> NReference.eq ref1 ref2
  | _ -> false


  
module Equivalence : sig
  type equivalence

  val make_equivalence: NCic.term -> NCic.term -> (NCic.term * NCic.term) list -> equivalence
  val equivalent_type: NCic.term -> equivalence list -> NCic.term option 
end = struct 
  type equivalence = {
    source_type: NCic.term;
    target_type: NCic.term;
    mappings: (NCic.term * NCic.term) list;
  }


  let make_equivalence (src: NCic.term) (trg: NCic.term) (mappings: (NCic.term * NCic.term) list) =
    let new_equiv: equivalence = {
      source_type=src;
      target_type=trg;
      mappings=mappings;
    } in
    new_equiv


  (*TODO: improve the way to scan the list
     could add something like equivalence_set type with added functionality instead of simple list*)
  let equivalent_type (original_type: NCic.term) (equivalences: equivalence list): NCic.term option =
    let check_mapping (mapping: NCic.term * NCic.term): NCic.term option = 
      let (cons1, cons2) = mapping in 
      (*we're looking for the equivalent type so the returned term is the other one*) 
      if are_inductive_and_equal cons1 original_type then
        Some cons2 
      else if are_inductive_and_equal cons2 original_type then 
        Some cons1 
      else None 
    in
    let check_equivalence (equiv: equivalence): NCic.term option = 
      let (type1, type2) = (equiv.target_type, equiv.source_type) in
      (*check the first 2 terms in case original_type is an inductive type*) 
      if are_inductive_and_equal type1 original_type then
        Some type2
      else if are_inductive_and_equal type2 original_type then 
        Some type1 

      (*checks the mappings in case original_type is a constructor*)
      else match 
        List.find_opt (fun mapping -> Option.is_some (check_mapping mapping)) equiv.mappings
      with
      | Some mapping -> check_mapping mapping
      | None -> None
    in 
  
  
    print_endline "scanning registered equivalences for type term:";
    TransferHelper.print_cic_term original_type;
    match List.find_opt (fun equiv -> Option.is_some (check_equivalence equiv)) equivalences with
    | Some right_equivalence -> check_equivalence right_equivalence
    | None -> None
end 