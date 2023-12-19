type equivalence = {
  sourceType: NCic.term;
  targetType: NCic.term;
  rest: string;
}

class virtual status =
  object
    val equivalences: equivalence list = []


    method equivalences =
      equivalences


    method add_equivalence (equiv: equivalence) = 
      {< equivalences = equiv :: equivalences >}


    method equivalent_type (target_type: NCic.term): NCic.term option =
      let compare: equivalence -> bool = fun equiv ->
        true
      in 
      
      match List.find_opt (compare) equivalences with
      | Some right_equivalence -> Some right_equivalence.targetType
      | None -> None
  end

let rec app_strings_spaced (strings: string list): string =
  match strings with
  | [] -> ""
  | hd::tl -> hd ^" "^ (app_strings_spaced tl)

let add_constructor_annotation (spec: NReference.spec) (name: string): string =
  match spec with
  (*inductive constructor*)
  | NReference.Con (a,constructor_number,c) -> 
    "C"^string_of_int constructor_number^"(" ^ name ^ ")"
    (* "[CON]" ^ string_of_int a ^","^ string_of_int b ^","^ string_of_int c *)
  | _ -> name
  (*inductive type*)
  (* | NReference.Ind (bool_val, a, b) -> "[IND]" ^ string_of_bool bool_val ^","^ string_of_int a ^","^ string_of_int b *)
  (* | NReference.Decl -> "[DECL]" *)
  (* | NReference.Def (a) ->"[DEF]" ^ string_of_int a  *)
  (* | NReference.Fix (a,b,c) ->"[FIX]" ^ string_of_int a ^","^ string_of_int b ^","^ string_of_int c *)
  (* | NReference.CoFix (a) -> "[CoFIX]" ^ string_of_int a *)

let rec stringify_cic_term (vars: string list) (term: NCic.term) =
  match term with
  | NCic.Rel (index) -> 
    List.nth vars (index -1)
  (*applicazione*)
  | NCic.Appl terms -> 
    app_strings_spaced (List.map (stringify_cic_term vars) terms)
  (*per ogni*)
  | NCic.Prod (binder, source, target) ->
    "P"^binder^":" ^ stringify_cic_term (binder::vars) source ^ ". " ^ stringify_cic_term (binder::vars) target 
  (*astrazione*)
  | NCic.Lambda (binder, source, target) -> 
    "L"^binder^":" ^ stringify_cic_term (binder::vars) source ^ ". " ^ stringify_cic_term (binder::vars) target
  (*???*)
  | NCic.LetIn (binder, typ, term, body) -> 
    "let ("^binder^":"^ (stringify_cic_term (binder::vars) typ) ^") := " ^
    (stringify_cic_term (binder::vars) term) ^". "^ (stringify_cic_term (binder::vars) body)



  (*???*)
  | NCic.Const ref -> 
    (* "C" *)
    (match ref with
    | NReference.Ref (uri, spec) ->
      add_constructor_annotation spec (NUri.name_of_uri uri))
  (*??? shouldn't touch though, maybe EQUIVALENCE might have to check if this can include the type we're transfering over*)
  | NCic.Sort s -> 
    (match s with
    | NCic.Prop -> "Prop"
    | NCic.Type(_) -> "Type")
  (*ELIM rule, i guess*)
  | NCic.Match (ref, out_type, ind_term, patterns) -> 
    "[MATCH NI]"
  (*??? clueless*)
  | NCic.Meta (metaIndex, localContext) -> 
    "[META NI]"
  (*??? don't even know what this is supposed to be*)
  | NCic.Implicit annot -> 
    "[IMPLICIT NI]"

let print_cic_term term = 
  print_endline (stringify_cic_term [] term)

(* Implements the proof term transformation as in the paper*)
let rec transform_term (s: #status as 'status) (context: 'a list) (term: NCic.term): NCic.term * 'a list =
  match term with
  (*VAR rule*)
  | NCic.Rel (index) -> 
    (NCic.Rel index, context)
  (*LAM rule*)
  (*TODO: this case might have to change the context for further evaluation*)
  | NCic.Lambda (binder, source, target) -> 
    let (transformed_src, _) = transform_term s context source in 
    let (transformed_trg, _) = transform_term s context target in
    (NCic.Lambda (binder, transformed_src, transformed_trg), context)
  (*PROD rule*)
  (*TODO: this case might have to change the context for further evaluation*)
  | NCic.Prod (binder, source, target) ->
    let (transformed_src, _) = transform_term s context source in 
    let (transformed_trg, _) = transform_term s context target in
    (NCic.Prod (binder, transformed_src, transformed_trg), context)
  (*DEP-CONSTR like*)
  (*TODO: this is where the constructor mapping between the changed type is done*)
  | NCic.Const ref -> 
    let equiv_type = s#equivalent_type (term) in 
    (match equiv_type with 
    | Some (NCic.Const equiv_ref) ->
      (NCic.Const equiv_ref, context)
    | Some _ ->
      (NCic.Const ref, context)
    | None -> 
      (NCic.Const ref, context))
  (*TODO: check if this even needs a transformation*)
  | NCic.Sort s -> 
    (NCic.Sort s, context)
  (*APP rule*)
  | NCic.Appl terms -> 
    let transformation = List.map (transform_term s context) terms in
    let transformed_terms = List.map (fun (term, context) -> term) transformation in 
    (NCic.Appl transformed_terms, context)
  (*???*)
  (*TODO: make sure this is right*)
  | NCic.LetIn (binder, typ, term, body) -> 
    let (transformed_type, _) = transform_term s context typ in 
    let (transformed_term, _) = transform_term s context term in 
    let (transformed_body, _) = transform_term s context body in 
    (NCic.LetIn (binder, transformed_type, transformed_term, transformed_body), context)
  
  
  
  
  
  (*ELIM rule, i guess*)
  | NCic.Match (ref, out_type, ind_term, patterns) -> (NCic.Match (ref, out_type, ind_term, patterns), context)
  (*??? clueless*)
  | NCic.Meta (metaIndex, localContext) -> (NCic.Meta (metaIndex, localContext), context)
  (*??? don't even know what this is supposed to be*)
  | NCic.Implicit annot -> (NCic.Implicit annot, context)














let add_equivalence status (src: NCic.term) (trg: NCic.term) =
  let newEquiv: equivalence = {sourceType=src; targetType=trg; rest=""} in
  print_endline "adding equivalence between the 2 terms:";
  print_cic_term (newEquiv.sourceType);
  print_cic_term (newEquiv.targetType);
  print_endline "";
  status#add_equivalence newEquiv

let transfer (status: #status as 'status) (term: NCic.term) = 
  (*should take: a formula to transfer (proven theorem), the type for which the formula is proven and the changed type*)
  (*an equivalence between those two has to be registered.*)
  (*take the equivalence*)
  (*apply the transformation to the formula's term using the provided config*)
  (*return the obtained term and the new context in which to evaluate it*)
  (* let equivalences = status#equivalences in
  match equivalences with
  | [] -> 
    print_endline "failure";
    status
  | equiv :: l -> 
    print_endline (equiv.sourceType ^ " |^| " ^ equiv.targetType); *)
  let (transformed_term, _) = transform_term status [] term in 
  let src_string = stringify_cic_term [] term in
  let trg_string = stringify_cic_term [] transformed_term in
  print_endline "transfer result:";print_endline (src_string ^" -> "^trg_string);
    status

