type comment = string

type var = string

type constname = string

type modname = string

type const = modname * constname

type sort = Type | Kind

type term =
  | Var of var
  | Const of const
  | Sort of sort
  | Prod of var * term * term
  | Lam of var * term * term
  | App of term * term

let prods bs a = List.fold_right (fun (x, b) a -> Prod (x, b, a)) bs a

let lams bs m = List.fold_right (fun (x, b) m -> Lam (x, b, m)) bs m

let apps m ns = List.fold_left (fun m n -> App (m, n)) m ns

let theory_modname = "cic"

let theory_const c args = apps (Const (theory_modname, c)) args

let univ_term s = theory_const "univ" [s]

let succ_sort s = theory_const "succ" [s]

let lift_term s1 s2 a = theory_const "lift" [s1; s2; a]

let is_sort ty =
  match ty with App (Const (_, s), _) when s = "Univ" -> true | _ -> false

let extract_sort ty =
  match ty with
  | App (Const (_, s), t) when s = "Univ" -> t
  | _ -> assert false

let rec is_sort_product ty =
  match ty with
  | App(Const (_, s), _) when s = "Univ" || s = "univ" -> true
  | App(App(Const (_,_), _), a) -> is_prod_product a
  | _ -> false

and is_prod_product ty =
  match ty with
  | App(App(App(App(Const(_,s),_),_),_),Lam(_,_,ty)) when s = "prod" -> is_sort_product ty
  | _ -> false

let get_sort_product ty =
  match ty with
  | App(App(Const (_,_), s), _) -> s
  | _ -> assert false

let extract_type ty =
  match ty with
  | App(App(Const (_,_), _), ty) -> ty
  | _ -> assert false

let prods bs a = List.fold_right (fun (x, b) a -> Prod(x, b, a)) bs a
let lams bs m = List.fold_right (fun (x, b) m -> Lam(x, b, m)) bs m
let apps m ns = List.fold_left (fun m n -> App(m, n)) m ns

let app_bindings m bs =
  let translate_var x =
    let ty = List.assoc x bs in
    if is_sort ty then
      let ty' = extract_sort ty in
      lift_term ty' ty' (Var x)
    else if is_sort_product ty then
      Var x
    else  Var x
  in
  let xs = fst (List.split bs) in
  apps m (List.map translate_var xs)


type pattern =
  | PVar of var
  | PConst of const
  | PLam of var * pattern * pattern
  | PApp of pattern * pattern
  | PGuard of term

let plams bs m = List.fold_right (fun (x, b) m -> PLam (x, PGuard b, m)) bs m

let papps m ns = List.fold_left (fun m n -> PApp (m, n)) m ns

let papp_bindings m bs =
  let xs = fst (List.split bs) in
  papps m (List.map (fun x -> PVar x) xs)


type context = (var * term) list

let app_context m context =
  (* Contexts are stored in reverse order. *)
  app_bindings m (List.rev context)


let papp_context m context =
  (* Contexts are stored in reverse order. *)
  papp_bindings m (List.rev context)

type command =
| Require of modname

type entry =
  | StcDeclaration of constname * term
  | DefDeclaration of constname * term
  | Definition of constname * term option * term
  | RewriteRule of context * pattern * term
  | Command of command
  | Comment of string

type signature = entry list

let dk_keywords = [ "thm"; "def"; "injective" ]
