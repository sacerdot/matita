module U = NUri
module C = NCic
module R = NReference
module P = NCicPp
module D = Dedukti
module F = Format

let pp ?(ctx= []) fmt term =
  Format.fprintf fmt "%s@." (new P.status#ppterm ctx [] [] term)


(**** Utilities ****)

exception NotImplemented of string

let not_implemented str = raise (NotImplemented str)

(* Find a fresh variant of the string [name] such that the function
   [avoid] returns false. **)
let fresh avoid name =
  let rec try_variant i =
    let variant = Format.sprintf "%s%d" name i in
    if avoid variant then try_variant (i + 1) else variant
  in
  if avoid name then try_variant 1 else name


(**** Global context ****)

(** Uris with the same base uri are extracted to the same Dedukti module.
    To keep track of the mapping, we use a hash table that maps base uris
    to module names and another from module names to module signatures.
    REMINDER : uris are represented as an abstract datatype while base uris
    are reparesented as strings. **)

(** Map from baseuris to dedukti module names **)
let baseuri_table : (string, D.modname) Hashtbl.t = Hashtbl.create 100

(** Map from dedukti module names to module signatures *)
let modules_table : (D.modname, D.signature) Hashtbl.t = Hashtbl.create 100

(** Add an entry to the signature of the module. **)
let add_entry modname entry =
  let signature = Hashtbl.find modules_table modname in
  Hashtbl.replace modules_table modname (entry :: signature)


(** Escape prefix and slashes in the base uri string. **)
let escape_baseuri baseuri =
  (*  let len = String.length baseuri in *)
  (* Cut out the cic:/ at the start *)
  let cic_start = Str.string_match (Str.regexp "cic:/\\(.*\\)") baseuri 0 in
  let name =
    if not cic_start then
      let () = HLog.warn "baseuri %s does not begin with cic:/" in
      baseuri
    else Str.matched_group 1 baseuri
  in
  let name = Str.global_replace (Str.regexp "/") "_" name in
  name


(** Generate a fresh Dedukti module name from the given base uri string. **)
let fresh_modname baseuri =
  let avoid modname' = Hashtbl.mem modules_table modname' in
  fresh avoid (escape_baseuri baseuri)


let translate_baseuri baseuri =
  try Hashtbl.find baseuri_table baseuri with Not_found ->
    let modname' = fresh_modname baseuri in
    let () =
      Hashtbl.add modules_table modname'
        [ D.Comment "This file was automatically generated from Matita." ]
    in
    let () = Hashtbl.add baseuri_table baseuri modname' in
    modname'


(** A global Matita constant can be uniquely represented by a base uri
    (the name of the module) and a name (the name of the constant).
    Each pair is mapped to a unique Dedukti constants.
    To keep track of the mapping, we use a hash table that maps these pairs
    to Dedukti constants and another to represent the set of used constants. **)

(** Map from references to dedukti constants **)
let reference_table : (string * string, D.const) Hashtbl.t = Hashtbl.create 100

(** Set of dedukti constants **)
let constants_table : (D.const, unit) Hashtbl.t = Hashtbl.create 100

(** Escape illegal names. **)
let escape_name name = if name = "_" then "__" else name

let fresh_const (baseuri, name) =
  let modname' = translate_baseuri baseuri in
  let avoid constname' = Hashtbl.mem constants_table (modname', constname') in
  let constname' = fresh avoid (escape_name name) in
  (modname', constname')


let translate_const (baseuri, name) =
  try Hashtbl.find reference_table (baseuri, name) with Not_found ->
    let const' = fresh_const (baseuri, name) in
    let () = Hashtbl.add constants_table const' () in
    let () = Hashtbl.add reference_table (baseuri, name) const' in
    const'


(** Return the name of the body function associated to the fixpoint. **)
let translate_body_const (baseuri, name) =
  translate_const (baseuri, Format.sprintf "%s_body" name)


(* A global Matita universe is mapped to a Dedukti constant.
    Since the universe constraints can change during the translation, universes
    are translated to a separate module. *)

(** Map from universe names to dedukti constants *)
let universe_table : (string, D.const) Hashtbl.t = Hashtbl.create 100

(** Map from dedukti universe constants to lesser dedukti universe constants *)
let constraints_table : (D.const, D.const list) Hashtbl.t = Hashtbl.create 100

(** Add a the constraint c1 < c2 between the two dedukti universe constants. **)
let add_constraint c1 c2 =
  let constraints = Hashtbl.find constraints_table c2 in
  Hashtbl.replace constraints_table c2 (c1 :: constraints)


let univs_modname = "univs"

let fresh_univ name =
  let modname' = univs_modname in
  let avoid constname' =
    Hashtbl.mem constraints_table (modname', constname')
  in
  let constname' = fresh avoid (escape_name name) in
  (modname', constname')


let translate_univ_uri (_, name) =
  try Hashtbl.find universe_table name with Not_found ->
    let const' = fresh_univ name in
    let () = Hashtbl.add constraints_table const' [] in
    let () = Hashtbl.add universe_table name const' in
    const'


(**** Local context ****)

(** Not every Matita variable is mapped to a Dedukti variable. Let-in variables
    are translated to applied global constants, i.e. Dedukti terms.
    We need to keep track of 3 things:
    1. The current Matita local context, needed for type-checking.
    2. The current Dedukti local context, needed for fresh-name generation
       and for lambda-lifting.
    3. The mapping between Matita local variables and Dedukti terms, needed
       for the translation. **)

type context = {cic: C.context; dk: D.context; map: D.term list}

let empty_context = {cic= []; dk= []; map= []}

(** Generate a Dedukti variable name from the given name that is fresh in
    the given Dedukti context. **)
let fresh_var context name =
  let avoid name' = List.mem_assoc name' context in
  fresh avoid (escape_name name)


(**** CIC constants ****)

let theory_modname = "cic"

let theory_const c args = D.apps (D.Const (theory_modname, c)) args

let nat_type = theory_const "Nat" []

let zero_nat = theory_const "z" []

let succ_nat i = theory_const "s" [i]

let max_nat i j = theory_const "m" [i; j]

let sort_type = theory_const "Sort" []

let prop_sort = theory_const "prop" []

let type_sort i = theory_const "type" [i]

let succ_sort s = theory_const "succ" [s]

let next_sort s = theory_const "next" [s]

let rule_sort s1 s2 = theory_const "rule" [s1; s2]

let max_sort s1 s2 = theory_const "max" [s1; s2]

let univ_type s = theory_const "Univ" [s]

let term_type s a = theory_const "Term" [s; a]

let univ_term s = theory_const "univ" [s]

let join_term s1 s2 a b = theory_const "join" [s1; s2; a; b]

let cast_term s1 s2 a = theory_const "lift" [s1; s2; a]

let prod_term s1 s2 a b = theory_const "prod" [s1; s2; a; b]

type univ = Prop | Type of int

module UMSet = Set.Make (struct
  type t = D.constname * univ

  let compare = compare
end)

let translated_match = ref UMSet.empty

module UFSet = Set.Make (struct
  type t = D.constname * univ

  let compare = compare
end)

let translated_filter = ref UFSet.empty

let pp_univ fmt u =
  match u with
  | Prop -> Format.fprintf fmt "Prop"
  | Type i -> Format.fprintf fmt "Type%d" i


let string_of_pp pp u = Format.asprintf "%a" pp u

let term_of_univ u =
  let rec type_univ i =
    if i = 0 then zero_nat else succ_nat (type_univ (i - 1))
  in
  match u with Prop -> prop_sort | Type i -> type_sort (type_univ i)


let back_to_sort s =
  let to_algebra i =
    [(`Type, U.uri_of_string (Format.sprintf "cic:/matita/pts/Type%d.univ" i))]
  in
  match s with Prop -> C.Prop | Type i -> C.Type (to_algebra i)


let univ_of_string u =
  let str_cprop = Str.regexp "CProp*" in
  let str_type = Str.regexp "Type*" in
  let n = int_of_string (Str.last_chars u 1) in
  if Str.string_match str_cprop u 0 then if n = 0 then Type 0 else Type n
  else if Str.string_match str_type u 0 then Type n
  else failwith "I don't know that universe"


let succ s = match s with Prop -> Type 0 | Type i -> Type (i + 1)

let max_sort s s' =
  match (s, s') with
  | Prop, Prop -> Prop
  | Type i, Prop | Prop, Type i -> Type i
  | Type i, Type j -> Type (max i j)


let back_to_univ t =
  let rec to_nat t =
    match t with
    | D.Const (_, z) when z = "z" -> 0
    | D.App (D.Const (_, s), t) when s = "s" -> 1 + to_nat t
    | _ -> assert false
  in
  match t with
  | D.Const (_, s) when s = "prop" -> Prop
  | D.App (D.Const (_, t), s) when t = "type" -> Type (to_nat s)
  | _ -> assert false


let rule_sort s s' =
  match (s, s') with
  | _, Prop -> Prop
  | Prop, _ -> s'
  | Type i, Type j -> Type (max i j)


let rec max_sorts sorts =
  match sorts with
  | [] -> Type 0
  | [s] -> s
  | s :: ss -> max_sort s (max_sorts ss)


(**** Sorts ****)

let translate_level i =
  let univ_algebra, uri = i in
  let name = U.name_of_uri uri in
  match univ_algebra with
  | `Type | `CProp -> univ_of_string name
  | `Succ -> succ (univ_of_string name)


let translate_univ u =
  let sorts' = List.map translate_level u in
  max_sorts sorts'


let translate_sort' s =
  match s with C.Prop -> Prop | C.Type u -> translate_univ u


let translate_sort s =
  match s with
  | C.Prop -> prop_sort
  | C.Type u -> term_of_univ (translate_univ u)


let inductive_registry = Hashtbl.create 81

(** Return the name of the match function associated to the inductive type. **)
let translate_match_const (baseuri, name) univ =
  let univ' = translate_sort' univ in
  let univ_name = string_of_pp pp_univ univ' in
  translate_const (baseuri, Format.sprintf "match_%s_%s" name univ_name)


(** Return the name of the filter function associated to the inductive type. **)
let translate_filter_const (baseuri, name) univ =
  let univ' = translate_sort' univ in
  let univ_name = string_of_pp pp_univ univ' in
  translate_const (baseuri, Format.sprintf "filter_%s_%s" name univ_name)


let translate_constraint u1 u2 =
  match (u1, u2) with
  | [(`Type, uri1)], [(`Type, uri2)] ->
      let baseuri1 = U.baseuri_of_uri uri1 in
      let baseuri2 = U.baseuri_of_uri uri2 in
      let name1 = U.name_of_uri uri1 in
      let name2 = U.name_of_uri uri2 in
      let c1' = translate_univ_uri (baseuri1, name1) in
      let c2' = translate_univ_uri (baseuri2, name2) in
      add_constraint c1' c2'
  | _ ->
      (* There should be no constraints between other shapes of universes. *)
      assert false


(** Topologically sort and return the universes according to the constraints. **)
let sorted_universes () =
  (* Keep track of universes being traversed to avoid cycles. *)
  let visiting = ref [] in
  (* The resulting list of sorted universes, in reverse order. *)
  let sorted = ref [] in
  (* Topologically insert the universe in the sorted list. *)
  let rec insert univ =
    if List.mem univ !sorted then (* Universe has already been added *)
      ()
    else if List.mem univ !visiting then
      (* There is a cycle in the constraints *)
      failwith "Cycle detected between universes"
    else
      (* Recursively insert the smaller universes first. *)
      let smaller_univs = Hashtbl.find constraints_table univ in
      visiting := univ :: !visiting ;
      List.iter insert smaller_univs ;
      visiting := List.tl !visiting ;
      sorted := univ :: !sorted
  in
  Hashtbl.iter (fun univ _ -> insert univ) constraints_table ;
  (* Reverse the sorted list to obtain the correct order. *)
  List.rev !sorted


(** Compute the signature of the universe module from the stored constraints. **)
let univs_signature () =
  let signature =
    [ D.Comment "This file was automatically generated from Matita." ]
  in
  let sorted_univs = sorted_universes () in
  let add_entry signature u =
    let vs = Hashtbl.find constraints_table u in
    let vs = List.map (fun (_, n) -> succ (univ_of_string n)) vs in
    let mvs = term_of_univ (max_sorts vs) in
    D.Definition (snd u, Some sort_type, mvs) :: signature
  in
  List.fold_left add_entry signature sorted_univs


(**** Terms and types ****)

let of_term t =
  match t with
  | D.App (D.App (D.Const (_, t), s), a) when t = "Term" -> (back_to_univ s, a)
  | D.App (D.Const (_, t), a) when t = "Univ" ->
      let s = back_to_univ a in
      (succ s, univ_term a)
  | _ ->
      Format.printf "debug term:%a@." DeduktiPrint.print_term t ;
      assert false


let rec to_cic_prods l a =
  match l with
  | [] -> a
  | (x, t) :: l ->
      let s', a = of_term a in
      let s, t' = of_term t in
      let ss = term_of_univ s in
      let ss' = term_of_univ s' in
      to_cic_prods l
        (term_type
           (term_of_univ (rule_sort s s'))
           (prod_term ss ss' t' (D.Lam (x, t, a))))


(** The translation of terms and types is parameterized by:
    - The baseuri of the current Matita object, used to compute the name
      of the current context.
    - A status object, needed for typechecking and evaluation. **)
module type INFO = sig
  val baseuri : string

  val status : C.status
end

module Translation (I : INFO) = struct
  let translate_reference reference =
    let R.Ref (uri, _) = reference in
    let baseuri = U.baseuri_of_uri uri in
    let name = NCicPp.r2s I.status true reference in
    translate_const (baseuri, name)


  let lift i term = NCicSubstitution.lift I.status i term

  let subst term1 term2 = NCicSubstitution.subst I.status term1 term2

  let are_convertible context term1 term2 =
    NCicReduction.are_convertible I.status ~metasenv:[] ~subst:[]
      ~test_eq_only:true context.cic term1 term2


  let whd context term = NCicReduction.whd I.status ~subst:[] context.cic term

  let split_prods context n term =
    NCicReduction.split_prods I.status ~subst:[] context.cic n term


  let type_of context term =
    NCicTypeChecker.typeof I.status ~metasenv:[] ~subst:[] context.cic term


  let rec split_ind_arity context bindings arity =
    match whd context arity with
    | C.Prod (x, a, b) ->
        let context = {context with cic= (x, C.Decl a) :: context.cic} in
        split_ind_arity context ((x, a) :: bindings) b
    | C.Sort s -> (List.rev bindings, s)
    | _ -> failwith "not an inductive arity"


  let rec split_cons_type context bindings ty =
    match whd context ty with
    | C.Prod (y, b, c) ->
        let context = {context with cic= (y, C.Decl b) :: context.cic} in
        split_cons_type context ((y, b) :: bindings) c
    | C.Appl ((C.Const R.Ref (_, R.Ind _)) :: args) -> (List.rev bindings, args)
    | C.Const R.Ref (_, R.Ind _) -> (List.rev bindings, [])
    | _ -> failwith "invalid constructor type"


  let get_inductive_type uri =
    let _, _, inductives, _, i =
      NCicEnvironment.get_checked_indtys I.status uri
    in
    List.nth inductives i


  let sort_of context term =
    match term with
    | C.Sort C.Prop -> C.Type []
    | C.Sort C.Type t ->
        let u = translate_univ t in
        back_to_sort (succ u)
    | _ ->
      match whd context (type_of context term) with
      | C.Sort s -> s
      | _ -> failwith "not a sort"


  (** Split list into left and right parameters or arguments **)
  let rec split_list i left right =
    match (i, right) with
    | 0, _ -> (List.rev left, right)
    | n, x :: right when n > 0 -> split_list (i - 1) (x :: left) right
    | _ -> raise (Invalid_argument "split_list")


  let rec is_sort b =
    match b with
    | C.Sort _ -> true
    | C.Prod (_, _, b) -> is_sort b
    | _ -> false


  and translate_term context term =
    match term with
    | C.Rel i -> List.nth context.map (i - 1)
    | C.Meta _ ->
        (* There should be no unresolved meta-variables at this point. *)
        assert false
    | C.Appl [] ->
        (* There should be no empty list in an application. *)
        assert false
    | C.Appl (m :: ns) ->
        let a = type_of context m in
        let m' = translate_term context m in
        let ns' = translate_args context ns a in
        D.apps m' ns'
    | C.Prod (x, a, b) ->
        let s1 = sort_of context a in
        let s1' = translate_sort s1 in
        let a' = translate_term context a in
        let a'' = translate_type context a in
        let x' = fresh_var context.dk x in
        let context_x =
          { cic= (x, C.Decl a) :: context.cic
          ; dk= (x', a'') :: context.dk
          ; map= D.Var x' :: context.map }
        in
        let s2 = sort_of context_x b in
        let s2' = translate_sort s2 in
        let b' = translate_term context_x b in
        prod_term s1' s2' a' (D.Lam (x', a'', b'))
    | C.Lambda (x, a, m) ->
        let a'' = translate_type context a in
        let x' = fresh_var context.dk x in
        let context_x =
          { cic= (x, C.Decl a) :: context.cic
          ; dk= (x', a'') :: context.dk
          ; map= D.Var x' :: context.map }
        in
        let m' = translate_term context_x m in
        D.Lam (x', a'', m')
    | C.LetIn (x, a, n, m) ->
        let a' = translate_type context a in
        let n' = translate_term context n in
        let c' = fresh_const (I.baseuri, Format.sprintf "let_%s" x) in
        let () = Hashtbl.add constants_table c' () in
        let lifted_a' = to_cic_prods context.dk a' in
        let lifted_n' = D.lams (List.rev context.dk) n' in
        let () =
          add_entry (fst c') (D.Definition (snd c', Some lifted_a', lifted_n'))
        in
        let applied_c' = D.app_context (D.Const c') context.dk in
        let context_x =
          { context with
            cic= (x, C.Def (n, a)) :: context.cic
          ; map= applied_c' :: context.map }
        in
        translate_term context_x m
    | C.Const reference ->
        let const' = translate_reference reference in
        D.Const const'
    | C.Sort s ->
        let s' = translate_sort s in
        univ_term s'
    | C.Implicit _ ->
        (* There should be no implicits at this point. *)
        assert false
    | C.Match
        ( (R.Ref (uri, R.Ind (_, _, leftno)) as ind_ref)
        , return_type
        , matched
        , cases ) ->
        let ind_baseuri = U.baseuri_of_uri uri in
        let ind_name = U.name_of_uri uri in
        let ind_args =
          match whd context (type_of context matched) with
          | C.Appl ((C.Const R.Ref (_, R.Ind _)) :: args) -> args
          | C.Const R.Ref (_, R.Ind _) -> []
          | _ -> failwith "invalid matched type"
        in
        (* Need the type of the parameters because the arguments might have
           a strict subtype. *)
        let _, _, ind_arity, _ = get_inductive_type ind_ref in
        let return_sort =
          match
            snd (split_prods context (-1) (type_of context return_type))
          with
          | C.Sort s -> s
          | _ -> failwith "invalid return type"
        in
        let match_const' =
          translate_match_const (ind_baseuri, ind_name) return_sort
        in
        let return_type' = translate_term context return_type in
        let cases' = List.map (translate_term context) cases in
        let ind_args' = translate_args context ind_args ind_arity in
        let left_ind_args', right_ind_args' = split_list leftno [] ind_args' in
        let matched' = translate_term context matched in
        D.apps (D.Const match_const')
          ( left_ind_args' @ [return_type'] @ cases' @ right_ind_args'
          @ [matched'] )
    | C.Match _ -> failwith "invalid match"


  and translate_type context ty =
    match ty with
    | C.Prod (x, a, b) ->
        let a'' = translate_type context a in
        let x' = fresh_var context.dk x in
        let context_x =
          { cic= (x, C.Decl a) :: context.cic
          ; dk= (x', a'') :: context.dk
          ; map= D.Var x' :: context.map }
        in
        let b'' = translate_type context_x b in
        to_cic_prods [(x', a'')] b''
    | C.Sort s ->
        let s' = translate_sort s in
        univ_type s'
    | _ ->
        let s = sort_of context ty in
        let s' = translate_sort s in
        let ty' = translate_term context ty in
        term_type s' ty'

  (** Translate a term according to the given type. If the type does not
          correspond to the minimal type of the term, a coercion is added. **)
  and translate_term_as context term ty =
    let minimal_ty = type_of context term in
    if are_convertible context minimal_ty ty then
      match whd context ty with
      | C.Sort C.Prop -> translate_term context term
      | C.Sort s ->
        let s' = translate_sort s in
        let term' = translate_term context term in cast_term s' s' term'
      | _ -> translate_term context term
    else
      translate_cast context term ty

  (** Add a coercion to life a term to the given type. **)
  and translate_cast context term ty =
    let apply m n =
      match m with
      | C.Appl ms -> C.Appl (ms @ [n])
      | _ -> C.Appl [m; n]
    in
    match whd context ty with
    | C.Prod (x, a, b) ->
      let a'' = translate_type context a in
      let x'  = fresh_var context.dk x in
      let context_x = {
        cic = (x, C.Decl a) :: context.cic;
        dk  = (x', a'') :: context.dk;
        map = (D.Var x') :: context.map;
      } in
      let mx  = (apply (lift 1 term) (C.Rel 1)) in
      let mx' = translate_cast context_x mx b in
      D.Lam (x', a'', mx')
    | C.Sort s2 ->
      let s1 = sort_of context term in
      let s1' = translate_sort s1 in
      let s2' = translate_sort s2 in
      let term' = translate_term context term in
      cast_term s1' s2' term'
    | _ -> assert false

  (** Translate the arguments of an application according to the type
        of the applied function. **)
  and translate_args context terms ty =
    match terms with
    | [] -> []
    | n :: ns ->
        let a, b =
          match whd context ty with
          | C.Prod (_, a, b) -> (a, b)
          | _ ->
              failwith "Left term of an application should have product type"
        in
        let n' = translate_term_as context n a in
        let ns' = translate_args context ns (subst n b) in
        n' :: ns'


  let translate_binding (context, (x, a)) : context * (D.var * D.term) =
    let a'' = translate_type context a in
    let x' = fresh_var context.dk x in
    let context_x =
      { cic= (x, C.Decl a) :: context.cic
      ; dk= (x', a'') :: context.dk
      ; map= D.Var x' :: context.map }
    in
    (context_x, (x', a''))


  let rec translate_bindings context (bindings: (string * C.term) list)
      translated : context * (D.var * D.term) list =
    match bindings with
    | (x, a) :: bindings ->
        let context_x, (x', a'') = translate_binding (context, (x, a)) in
        translate_bindings context_x bindings ((x', a'') :: translated)
    | [] -> (context, List.rev translated)


  let translate_declaration name ty =
    Format.eprintf "%s@." name ;
    let const' = translate_const (I.baseuri, name) in
    let ty' = translate_type empty_context ty in
    add_entry (fst const') (D.StcDeclaration (snd const', ty'))


  let translate_definition name ty body =
    Format.eprintf "%s@." name ;
    let ty' = translate_type empty_context ty in
    let body' = translate_term empty_context body in
    let const' = translate_const (I.baseuri, name) in
    add_entry (fst const') (D.Definition (snd const', Some ty', body'))


  let translate_constructor _ (_, name, ty) =
    translate_declaration name ty


  (** Translate the match elimination scheme for the given inductive type.

        For the inductive type

        ind : p_1 : C_1 -> ... -> p_k : C_k -> x_1 : A_1 -> ... -> x_n : A_n -> ind_sort
        c_1 : p_1 : C_1 -> ... -> p_k : C_k -> y_1_1 : B_1_1 -> ... -> y_1_n1 : B_1_n1 -> I p_1 ... p_k M_1_1 ... M_1_n
        ...
        c_m : p_1 : C_1 -> ... -> p_k : C_k -> y_m_1 : B_m_1 -> ... -> y_m_nm : B_m_nm -> I p_1 ... p_k M_m_1 ... M_m_n

        the match scheme looks is

        match_ind :
          p_1 : ||C_1|| -> ... -> p_k : ||C_k|| ->
          return_sort : Sort ->
          return_type : (
            x_1 : ||A_1|| -> ... -> x_n : ||A_n|| ->
            T ind_sort (ind p_1 ... p_k x_1 ... x_n) -> U return_sort) ->
          case_1 : (
            y_1_1 : ||B_1_1|| -> ... -> y_1_n1 : ||B_1_n1|| ->
            T return_sort (return_type |M_1_1| ... |M_1_n| (c_1 p_1 ... p_k y_1_1 ... y_1_n1))) ->
          ...
          case_m : (
            y_m_1 : ||B_m_1|| -> ... -> y_m_nm : ||B_m_nm|| ->
            T return_sort (return_type |M_m_1| ... |M_m_n| (c_m p_1 ... p_k y_1_1 y_m_1 ... y_m_nm))) ->
          x_1 : ||A_1|| -> ... -> x_n : ||A_n|| ->
          z : T ind_sort (ind p_1 ... p_k x_1 ... x_n) ->
          T return_sort (return_type x_1 ... x_n z)

        with the rewrite rules

        [...] match_ind p_1 ... p_k y_1_1 {return_sort} return_type
                case_1 ... case_m {|M_1_1|} ... {|M_1_n1|}
                (c_1 p_1 ... p_k y_1_1 y_1_1 ... y_1_n1) -->
              case_1 y_1_1 ... y_1_n1
         ...
        [...] match_ind p_1 ... p_k y_1_1 {return_sort} return_type
                case_1 ... case_m {|M_m_1|} ... {|M_m_nm|}
                (c_m p_1 ... p_k y_1_1 y_m_1 ... y_m_nm) -->
              case_m y_m_1 ... y_m_nm
     **)

  let translate_match_scheme leftno ind_name arity constructors sort =
    (*      Format.printf "size match set: %d@." (UMSet.cardinal !translated_match); *)
    (*      Format.printf "size match: %s %a@." ind_name pp_univ sort'; *)
    (* Extract (p_i : C_i), (x_i : A_i), s_ind, (y_i_j : B_i_j), and M_i_j *)
    let context = empty_context in
    let left_ind_params, right_ind_params, ind_sort =
      let ind_params, ind_sort = split_ind_arity context [] arity in
      let left_params, right_ind_params = split_list leftno [] ind_params in
      (left_params, right_ind_params, ind_sort)
    in
    let cons_info (_, cons_name, cons_type) =
      let cons_params, cons_args = split_cons_type context [] cons_type in
      let _, right_cons_params =
        split_list leftno [] cons_params
      in
      let _, right_cons_args = split_list leftno [] cons_args in
      (cons_name, right_cons_params, right_cons_args)
    in
    let cons_infos = List.map cons_info constructors in
    (* Translate the name of the inductive type and its constructors. *)
    let ind_const' = translate_const (I.baseuri, ind_name) in
    let ind_sort' = translate_sort ind_sort in
    let ind' = D.Const ind_const' in
    (* Translate left parameters *)
    let context, left_params' =
      translate_bindings context left_ind_params []
    in
    (* Translate match_ind *)
    let match_const' = translate_match_const (I.baseuri, ind_name) sort in
    (* Translate return_type *)
    let return_type_name' = fresh_var context.dk "return_type" in
    let sort' = translate_sort sort in
    let _, right_ind_params' =
      translate_bindings context right_ind_params []
    in
    let quant_var_name' = fresh_var context.dk "z" in
    let quant_var_type' =
      term_type ind_sort'
        (D.app_bindings ind' (left_params' @ right_ind_params'))
    in
    let return_type_type' =
      to_cic_prods
        (List.rev (right_ind_params' @ [(quant_var_name', quant_var_type')]))
        (univ_type sort')
    in
    let context =
      {context with dk= (return_type_name', return_type_type') :: context.dk}
    in
    let return_type' = D.Var return_type_name' in
    (* Translate cases *)
    let translate_case (cons_name, right_cons_params, right_cons_args) =
      let cons_const' = translate_const (I.baseuri, cons_name) in
      let cons' = D.Const cons_const' in
      let case_name' =
        fresh_var context.dk (Format.sprintf "case_%s" cons_name)
      in
      let context, right_cons_params' =
        translate_bindings context right_cons_params []
      in
      let right_cons_args' =
        List.map (translate_term context) right_cons_args
      in
      let case_type' =
        to_cic_prods
          (List.rev right_cons_params')
          (term_type sort'
             (D.apps return_type'
                ( right_cons_args'
                @ [D.app_bindings cons' (left_params' @ right_cons_params')] )))
      in
      (case_name', case_type')
    in
    let rec translate_cases context cons_infos translated =
      match cons_infos with
      | cons_info :: cons_infos ->
          let case_name', case_type' = translate_case cons_info in
          let context =
            {context with dk= (case_name', case_type') :: context.dk}
          in
          let case' = D.Var case_name' in
          translate_cases context cons_infos (case' :: translated)
      | [] -> (context, List.rev translated)
    in
    let context, cases' = translate_cases context cons_infos [] in
    (* Context common to the declaration and the rewrite rules *)
    let common_context = context in
    (* Translate conclusion *)
    let context, right_ind_params' =
      translate_bindings context right_ind_params []
    in
    let quant_var_name' = fresh_var context.dk "z" in
    let quant_var_type' =
      term_type ind_sort'
        (D.app_bindings ind' (left_params' @ right_ind_params'))
    in
    (*      let context = {
          context with
          dk = (quant_var_name', quant_var_type') :: context.dk;
        } in *)
    let quant_var' = D.Var quant_var_name' in
    let conclusion =
      to_cic_prods
        (List.rev (right_ind_params' @ [(quant_var_name', quant_var_type')]))
        (term_type sort'
           (D.App (D.app_bindings return_type' right_ind_params', quant_var')))
    in
    (* Declare the match function *)
    let match_type' = to_cic_prods common_context.dk conclusion in
    add_entry (fst match_const')
      (D.DefDeclaration (snd match_const', match_type')) ;
    (* Rewrite rules of the match function *)
    let match_ind' = D.PConst match_const' in
    let translate_rule i (cons_name, right_cons_params, right_cons_args) =
      let cons_const' = translate_const (I.baseuri, cons_name) in
      let cons' = D.PConst cons_const' in
      let context = common_context in
      let context, right_cons_params' =
        translate_bindings context right_cons_params []
      in
      let right_cons_args' =
        List.map (translate_term context) right_cons_args
      in
      let left_pattern' =
        D.papps
          (D.papp_context match_ind' common_context.dk)
          ( List.map (fun m -> D.PGuard m) right_cons_args'
          @ [D.papp_bindings cons' (left_params' @ right_cons_params')] )
      in
      let case' = List.nth cases' i in
      let right_term' = D.app_bindings case' right_cons_params' in
      add_entry (fst match_const')
        (D.RewriteRule (context.dk, left_pattern', right_term'))
    in
    List.iteri translate_rule cons_infos


  (** A filter is similar to a match in that it blocks the application of
        a function until a constructor is passed as an argument. It does not
        reduce on variables for example. However only one uniform case
        is given for all the constructors

        For the inductive type

        ind : x_1 : A_1 -> ... -> x_n : A_n -> ind_sort
        c_1 : y_1_1 : B_1_1 -> ... -> y_1_n1 : B_1_n1 -> I p_1 ... p_k M_1_1 ... M_1_n
        ...
        c_m : y_m_1 : B_m_1 -> ... -> y_m_nm : B_m_nm -> I p_1 ... p_k M_m_1 ... M_m_n

        the filter scheme is

        filter_ind :
          x_1 : ||A_1|| -> ... -> x_n : ||A_n|| ->
          return_sort : Sort ->
          return_type : (T ind_sort (ind x_1 ... x_n) -> U return_sort) ->
          return : (
            z : T ind_sort (ind x_1 ... x_n) ->
            T return_sort (return_type x_1 ... x_n z)) ->
          z : T ind_sort (ind x_1 ... x_n) ->
          T return_sort (return_type x_1 ... x_n z)

        with the rewrite rules

        [y_1_1 : ||B_1_1||, ..., y_1_n1 : ||B_1_n1||]
          filter_ind {|M_1_1|} ... {|M_1_n|} return_sort return_type return (c_1 y_1_1 ... y_1_n1) -->
          return (c_1 y_1_1 ... y_1_n1)
        [...]
          filter_ind {|M_m_1|} ... {|M_m_n|} return_sort return_type return (c_m y_m_1 ... y_m_nm) -->
          return (c_m y_m_1 ... y_m_nm)
        **)

  let translate_filter_scheme _ ind_name arity constructors sort =
    let sort' = translate_sort' sort in
    let context = empty_context in
    let ind_params, ind_sort = split_ind_arity context [] arity in
    let cons_info (_, cons_name, cons_type) =
      let cons_params, cons_args = split_cons_type context [] cons_type in
      (cons_name, cons_params, cons_args)
    in
    let cons_infos = List.map cons_info constructors in
    (* Translate the name of the inductive type and its constructors. *)
    let ind_const' = translate_const (I.baseuri, ind_name) in
    let ind_sort' = translate_sort ind_sort in
    let ind' = D.Const ind_const' in
    (* Translate inductive parameters *)
    let context, ind_params' = translate_bindings context ind_params [] in
    (* Translate filter_ind *)
    let filter_const' = translate_filter_const (I.baseuri, ind_name) in
    (* Translate return_type *)
    let return_type_name' = fresh_var context.dk "return_type" in
    let quant_var_name' = fresh_var context.dk "z" in
    let quant_var_type' =
      term_type ind_sort' (D.app_bindings ind' ind_params')
    in
    let return_type_type' =
      to_cic_prods [(quant_var_name', quant_var_type')]
        (univ_type (term_of_univ sort'))
    in
    let context =
      {context with dk= (return_type_name', return_type_type') :: context.dk}
    in
    let return_type' = D.Var return_type_name' in
    (* Translate return *)
    let return_term_name' = fresh_var context.dk "return" in
    let quant_var_name' = fresh_var context.dk "z" in
    let quant_var_type' =
      term_type ind_sort' (D.app_bindings ind' ind_params')
    in
    let return_term_type' =
      to_cic_prods [(quant_var_name', quant_var_type')]
        (term_type (term_of_univ sort')
           (D.App (return_type', D.Var quant_var_name')))
    in
    let context =
      {context with dk= (return_term_name', return_term_type') :: context.dk}
    in
    (*      let return_term' = D.Var return_term_name' in *)
    let quant_var_name' = fresh_var context.dk "z" in
    let quant_var_type' =
      term_type ind_sort' (D.app_bindings ind' ind_params')
    in
    let conclusion' =
      to_cic_prods [(quant_var_name', quant_var_type')]
        (term_type (term_of_univ sort')
           (D.App (return_type', D.Var quant_var_name')))
    in
    (* Declare the filter function *)
    let filter_type' = to_cic_prods context.dk conclusion' in
    add_entry
      (fst @@ filter_const' sort)
      (D.DefDeclaration (snd @@ filter_const' sort, filter_type')) ;
    (* Rewrite rules of the match function *)
    let filter_ind' = D.PConst (filter_const' sort) in
    let translate_rule _ (cons_name, cons_params, cons_args) sort =
      let cons_const' = translate_const (I.baseuri, cons_name) in
      let context = empty_context in
      let context, cons_params' = translate_bindings context cons_params [] in
      let cons_args' = List.map (translate_term context) cons_args in
      (* Translate return_type *)
      let return_type_name' = fresh_var context.dk "return_type" in
      let quant_var_name' = fresh_var context.dk "z" in
      let quant_var_type' = term_type ind_sort' (D.apps ind' cons_args') in
      let return_type_type' =
        to_cic_prods [(quant_var_name', quant_var_type')] (univ_type ind_sort')
      in
      let context =
        {context with dk= (return_type_name', return_type_type') :: context.dk}
      in
      let return_type' = D.Var return_type_name' in
      (* Translate return *)
      let return_term_name' = fresh_var context.dk "return" in
      let quant_var_name' = fresh_var context.dk "z" in
      let quant_var_type' = term_type ind_sort' (D.apps ind' cons_args') in
      let return_term_type' =
        to_cic_prods [(quant_var_name', quant_var_type')]
          (term_type ind_sort' (D.App (return_type', D.Var quant_var_name')))
      in
      let context =
        {context with dk= (return_term_name', return_term_type') :: context.dk}
      in
      let return_term' = D.Var return_term_name' in
      let left_pattern' =
        D.papps filter_ind'
          ( List.map (fun m -> D.PGuard m) cons_args'
          @ [ D.PVar return_type_name'
            ; D.PVar return_term_name'
            ; D.papp_bindings (D.PConst cons_const') cons_params' ] )
      in
      let right_term' =
        D.App (return_term', D.app_bindings (D.Const cons_const') cons_params')
      in
      add_entry
        (fst @@ filter_const' sort)
        (D.RewriteRule (context.dk, left_pattern', right_term'))
    in
    List.iteri (fun i x -> translate_rule i x sort) cons_infos


  let translate_inductive leftno ((_, name, ty, constructors) as ind) =
    (*      Format.printf "translate inductive: %s@." name; *)
    Hashtbl.add inductive_registry name (leftno, ind) ;
    translate_declaration name ty ;
    List.iter (translate_constructor leftno) constructors ;
    let univs =
      let rec types n = if n = 0 then [Type 0] else Type n :: types (n - 1) in
      [Prop] @ types 5
    in
    let univs = List.map back_to_sort univs in
    List.iter (translate_match_scheme leftno name ty constructors) univs ;
    List.iter (translate_filter_scheme leftno name ty constructors) univs


  (*      translate_match_scheme leftno name ty constructors;
        translate_filter_scheme leftno name ty constructors *)

  let translate_inductives leftno types =
    List.iter (translate_inductive leftno) types


  let get_inductive_arguments context ty =
    match whd context ty with
    | C.Appl ((C.Const R.Ref (uri, R.Ind _)) :: args) -> (uri, args)
    | C.Const R.Ref (uri, R.Ind _) -> (uri, [])
    | _ -> failwith "not an inductive type"


  (** Translate one recursive function definition.

        For the inductive type

        ind : x_1 : A_1 -> ... -> x_n : A_n -> sort_ind.
        ...

        the recursive function

        f : w_1 : D_1 -> ... -> w_k : D_k -> z : ind M_1 ... M_n -> R = M.

        where R : s is translated as

        f : w_1 : ||D_1|| -> ... -> w_k : ||D_k|| -> z : ||ind M_1 ... M_n|| -> ||R||.
        f_body : w_1 : ||D_1|| -> ... -> w_k : ||D_k|| -> z : ||ind M_1 ... M_n|| -> ||R||.

        with the rewrite rules

        [w_1 : ||D_1||, ..., w_k : ||D_k||, z : ||ind M_1 ... M_n||]
          f w_1 ... w_k z --> filter_ind |M_1| ... |M_n| |s| (z : ||ind M_1 ... M_n|| => |R|) (f_body w_1 ... w_k) z.
        [w_1 : ||D_1||, ..., w_k : ||D_k||, z : ||ind M_1 ... M_n||]
          f_body w_1 ... w_k z --> |M|.
    **)
  let translate_fixpoint (_, name, recno, ty, body) =
    (*      Format.printf "Dedukti Fixpoint: %s@." name;
        Format.printf "Body: %s@." (new P.status#ppterm [] [] [] body); *)
    let rec split_fixpoint recno params ty body =
      match (ty, body) with
      | C.Prod (x, a, b), C.Lambda (_, _, m) when recno = 0 ->
          (List.rev params, (x, a), b, m)
      | C.Prod (x, a, b), C.Lambda (_, _, m) when recno > 0 ->
          split_fixpoint (recno - 1) ((x, a) :: params) b m
      | _ -> failwith "invalid fixpoint"
    in
    let context = empty_context in
    let params, rec_param, return_type, return =
      split_fixpoint recno [] ty body
    in
    let ind_uri, ind_args = get_inductive_arguments context (snd rec_param) in
    let fun_const' = translate_const (I.baseuri, name) in
    (*      Format.printf "new name: %s@." (snd fun_const'); *)
    let fun_body' = translate_body_const (I.baseuri, name) in
    let filter_ind' =
      translate_filter_const (U.baseuri_of_uri ind_uri, U.name_of_uri ind_uri)
    in
    let context, params' = translate_bindings context params [] in
    let ind_args' = List.map (translate_term context) ind_args in
    let context, rec_param' = translate_binding (context, rec_param) in
    let return_sort = sort_of context return_type in
    let return_type' = translate_term context return_type in
    let return_type'' = translate_type context return_type in
    let fun_const_type'' =
      to_cic_prods (List.rev (params' @ [rec_param'])) return_type''
    in
    let () =
      add_entry (fst fun_const')
        (D.DefDeclaration (snd fun_const', fun_const_type''))
    in
    let fun_body_type'' =
      to_cic_prods (List.rev (params' @ [rec_param'])) return_type''
    in
    let () =
      add_entry (fst fun_body')
        (D.DefDeclaration (snd fun_body', fun_body_type''))
    in
    (* Must translate return AFTER declaring the functions otherwise some
         let definitions referring to the functions inside the body will
         be lifted before the function declarations, and therefore not
        typecheck. *)
    let return' = translate_term context return in
    let left_fun_pattern' =
      D.papp_bindings (D.PConst fun_const') (params' @ [rec_param'])
    in
    let right_fun_term' =
      D.apps (D.Const (filter_ind' return_sort))
        ( ind_args'
        @ [ D.Lam (fst rec_param', snd rec_param', return_type')
          ; D.app_bindings (D.Const fun_body') params'
          ; D.Var (fst rec_param') ] )
    in
    let () =
      add_entry (fst fun_const')
        (D.RewriteRule (context.dk, left_fun_pattern', right_fun_term'))
    in
    let left_body_pattern' =
      D.papp_bindings (D.PConst fun_body') (params' @ [rec_param'])
    in
    let right_body_term' = return' in
    let () =
      add_entry (fst fun_body')
        (D.RewriteRule (context.dk, left_body_pattern', right_body_term'))
    in
    ()


  let translate_fixpoints funs = List.iter translate_fixpoint funs

  (** Translate a Matita object. There are 4 kinds of objects:
        - Constant declarations (i.e. axioms)
        - Constant definitions
        - Fixpoints definitions (i.e. top-level recursive functions)
        - Inductive type definitions **)
  let translate_obj_kind obj_kind =
    match obj_kind with
    | C.Constant (_, name, None, ty, _) ->
        HLog.debug
          (Format.sprintf "Dedukti: Translating constant declaration %s" name) ;
        (* The relevance argument is irrelevant for our purposes (no pun intended).
           The [c_attr] argument is not needed by the kernel. *)
        translate_declaration name ty
    | C.Constant (_, name, Some body, ty, _) ->
        HLog.debug
          (Format.sprintf "Dedukti: Translating constant definition %s" name) ;
        (* Hack for prop irrelevance *)
        let problematic =
          []
          (* "lemmaK"; "eq_sigma_true"; "Vector_eq"; "vec_expand"; "vector_nil";
            "change_vec_cons_tail"; "pmap_vec_cons"; "pmap_change";
            "while_trans_false"; "sem_obj_to_cfg"; "sem_cfg_to_obj"; *)
          (* "le_fact_10"; *)
        in
        if List.mem name problematic then translate_declaration name ty
        else translate_definition name ty body
    | C.Fixpoint (is_recursive, funs, _) ->
        HLog.debug (Format.sprintf "Dedukti: Translating fixpoint definitions") ;
        (* The boolean [is_recursive] indicates if the functions are recursive
           (when true) or co-recursive (when false).
           The [f_attr] argument is not needed by the kernel. *)
        if not is_recursive then not_implemented "co-recursive fixpoint" ;
        translate_fixpoints funs
    | C.Inductive (is_inductive, leftno, types, _) ->
        HLog.debug
          (Format.sprintf "Dedukti: Translating inductive definitions") ;
        (* The boolean [is_inductive] indicates if the types are inductive
           (when true) or co-inductive (when false).
           The [leftno] indicates the number of left parameters.
           The [i_attr] argument is not needed by the kernel. *)
        if not is_inductive then not_implemented "co-inductive type" ;
        translate_inductives leftno types
end

(** Extraction entry-points **)

let extraction_enabled () =
  let safe_get_bool name default =
    try Helm_registry.get_bool name with Helm_registry.Key_not_found _ ->
      default
  in
  safe_get_bool "extract_dedukti" false


(** This function is called every time an object is added to the library. **)
let extract_obj status obj =
  if extraction_enabled () then (
    let uri, _, metasenv, subst, obj_kind = obj in
    (* The depth is the maximum of the depth of the objects occuring
       in the definition plus one, used for reduction strategies.
       It is equal to 0 if the object does not have a body (e.g. an axiom). *)
    HLog.message
      (Format.sprintf "Dedukti: Extracting object %s" (U.string_of_uri uri)) ;
    (* There should be no unresolved meta-variables at this point. *)
    assert (List.length metasenv = 0) ;
    assert (List.length subst = 0) ;
    let module I = struct
      let status = status

      let baseuri = U.baseuri_of_uri uri
    end in
    let module T = Translation (I) in
    T.translate_obj_kind obj_kind ;
    HLog.message
      (Format.sprintf "Dedukti: Done extracting object %s"
         (U.string_of_uri uri)) )


(** This function is called every time a constraint is added to the library. **)
let extract_constraint _ u1 u2 =
  if extraction_enabled () then
    HLog.message (Format.sprintf "Dedukti: Extracting universe constraint") ;
  translate_constraint u1 u2


let basedir = "."

let filename_of_modname modname = Format.sprintf "%s.dk" modname

let filepath_of_modname modname =
  let filename = filename_of_modname modname in
  Filename.concat basedir filename


let output_module modname signature =
  let filepath = filepath_of_modname modname in
  let out_channel = open_out filepath in
  let formatter = F.formatter_of_out_channel out_channel in
  F.fprintf formatter "%a@." DeduktiPrint.print_signature signature ;
  close_out out_channel


let output_modules () =
  if extraction_enabled () then (
    HLog.message (Format.sprintf "Dedukti: Writing files") ;
    Hashtbl.iter output_module modules_table ;
    HLog.message (Format.sprintf "Dedukti: Writing universes") ;
    output_module univs_modname (univs_signature ()) )
