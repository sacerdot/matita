open Equivalence
open TransferHelper

let print_cic_term term = 
  TransferHelper.print_cic_term term

class virtual status =
  object
    val equivalences: Equivalence.equivalence list = []


    method equivalences =
      equivalences


    method add_equivalence (equiv: Equivalence.equivalence) = 
      {< equivalences = equiv :: equivalences >}

  end



(* Implements the proof term transformation as in https://dl.acm.org/doi/abs/10.1145/3453483.3454033*)
let rec transform_term (s: #status as 'status) (term: NCic.term): NCic.term =
  match term with
  | NCic.Rel (index) -> 
    NCic.Rel index 
  | NCic.Lambda (binder, source, target) -> 
    let transformed_src = transform_term s source in 
    let transformed_trg  = transform_term s target in
    NCic.Lambda (binder, transformed_src, transformed_trg)
  | NCic.Prod (binder, source, target) ->
    let transformed_src = transform_term s source in 
    let transformed_trg = transform_term s target in
    NCic.Prod (binder, transformed_src, transformed_trg)
  | NCic.Const ref -> 
    let equiv_type = Equivalence.equivalent_type term s#equivalences in 
    (match equiv_type with 
    | Some equiv_term ->
      print_endline "branch some";
      (*TODO: check if this needs to construct a new term*)
      equiv_term

    | _ -> print_endline "branch none"; term)
  (*TODO: check if this even needs a transformation*)
  | NCic.Sort s -> 
    NCic.Sort s
  | NCic.Appl terms -> 
    let transformed_terms = List.map (transform_term s) terms in
    NCic.Appl transformed_terms

  | NCic.LetIn (binder, typ, term, body) -> 
    let transformed_type = transform_term s typ in 
    let transformed_term = transform_term s term in 
    let transformed_body = transform_term s body in 
    NCic.LetIn (binder, transformed_type, transformed_term, transformed_body)

    
  (* non clear cases*)
  | NCic.Match (ref, out_type, ind_term, patterns) ->
    NCic.Match (ref, out_type, ind_term, patterns)
  | NCic.Meta (metaIndex, localContext) -> 
    NCic.Meta (metaIndex, localContext)
  | NCic.Implicit annot -> 
    NCic.Implicit annot


let add_equivalence status (src: NCic.term) (trg: NCic.term) (mappings: (NCic.term * NCic.term) list) =
  let newEquiv = (Equivalence.make_equivalence src trg mappings) in
  print_endline "adding equivalence between the 2 terms:";
  TransferHelper.print_cic_term (src);
  TransferHelper.print_cic_term (trg);
  print_endline "with constructor equivalences:";
  List.iter (fun (t1, t2) -> print_endline (TransferHelper.stringify_cic_term t1 ^" -> "^ TransferHelper.stringify_cic_term t2);) mappings;
  status#add_equivalence newEquiv


let transfer (status: #status as 'status) (term: NCic.term) = 
  let transformed_term = transform_term status term in 
  let src_string = TransferHelper.stringify_cic_term term in
  let trg_string = TransferHelper.stringify_cic_term transformed_term in
  print_endline "transfer result:";print_endline (src_string ^" -> "^trg_string);
    status

