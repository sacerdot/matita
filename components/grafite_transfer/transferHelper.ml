
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
  
  (*inductive type*)
  (* | NReference.Ind (bool_val, a, b) -> "[IND]" ^ string_of_bool bool_val ^","^ string_of_int a ^","^ string_of_int b *)
  (* | NReference.Decl -> "[DECL]" *)
  (* | NReference.Def (a) ->"[DEF]" ^ string_of_int a  *)
  (* | NReference.Fix (a,b,c) ->"[FIX]" ^ string_of_int a ^","^ string_of_int b ^","^ string_of_int c *)
  (* | NReference.CoFix (a) -> "[CoFIX]" ^ string_of_int a *)
  | _ -> name

let rec stringify_cic_term_impl (vars: string list) (term: NCic.term) =
  match term with
  | NCic.Rel (index) -> 
    List.nth vars (index -1)
  (*applicazione*)
  | NCic.Appl terms -> 
    app_strings_spaced (List.map (stringify_cic_term_impl vars) terms)
  (*per ogni*)
  | NCic.Prod (binder, source, target) ->
    "P"^binder^":" ^ stringify_cic_term_impl (binder::vars) source ^ ". " ^ stringify_cic_term_impl (binder::vars) target 
  (*astrazione*)
  | NCic.Lambda (binder, source, target) -> 
    "L"^binder^":" ^ stringify_cic_term_impl (binder::vars) source ^ ". " ^ stringify_cic_term_impl (binder::vars) target
  (*???*)
  | NCic.LetIn (binder, typ, term, body) -> 
    "let ("^binder^":"^ (stringify_cic_term_impl (binder::vars) typ) ^") := " ^
    (stringify_cic_term_impl (binder::vars) term) ^". "^ (stringify_cic_term_impl (binder::vars) body)
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




module TransferHelper : sig
  
  val stringify_cic_term: NCic.term -> string 
  val print_cic_term: NCic.term -> unit
  
end = struct
  let stringify_cic_term term =
    stringify_cic_term_impl [] term 

  let print_cic_term term = 
    print_endline (stringify_cic_term term)
end 

