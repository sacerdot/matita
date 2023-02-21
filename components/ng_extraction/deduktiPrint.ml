module D = Dedukti
module F = Format

let print_var out var =
  F.fprintf out "%s" var

let print_constname out constname =
  F.fprintf out "%s" constname

let print_modname out modname =
  F.fprintf out "%s" modname

let print_const out (modname, constname) =
  F.fprintf out "%a.%a"
    print_modname modname
    print_constname constname

let print_sort out sort =
  match sort with
  | D.Type -> F.fprintf out "Type"
  | D.Kind -> assert false

let rec print_abs_term out term =
  match term with
  | D.Prod (x, a, b) ->
    F.fprintf out "@[%a :@;<1 2>%a ->@ %a@]"
      print_var x
      print_app_term a
      print_abs_term b
  | D.Lam (x, a, m) ->
    F.fprintf out "@[%a :@;<1 2>%a =>@ %a@]"
      print_var x
      print_app_term a
      print_abs_term m
  | _ ->
    F.fprintf out "%a" print_app_term term

and print_app_term out term =
  match term with
  | D.App (m, n) ->
    F.fprintf out "@[%a@;<1 2>%a@]"
      print_app_term m
      print_atomic_term n
  | _ ->
    F.fprintf out "%a" print_atomic_term term

and print_atomic_term out term =
  match term with
  | D.Var x ->
    F.fprintf out "%a" print_var x
  | D.Const c ->
    F.fprintf out "%a" print_const c
  | D.Sort s ->
    F.fprintf out "%a" print_sort s
  | D.Prod _ | D.Lam _ | D.App _ ->
    F.fprintf out "(%a)" print_abs_term term

let print_term out term =
  print_abs_term out term

let rec print_abs_pattern out pattern =
  match pattern with
  | D.PLam (x, a, m) ->
    F.fprintf out "@[%a :@;<1 2>%a =>@ %a@]"
      print_var x
      print_app_pattern a
      print_abs_pattern m
  | _ ->
    F.fprintf out "%a" print_app_pattern pattern

and print_app_pattern out pattern =
  match pattern with
  | D.PApp (m, n) ->
    F.fprintf out "@[%a@;<1 2>%a@]"
      print_app_pattern m
      print_atomic_pattern n
  | _ ->
    F.fprintf out "%a" print_atomic_pattern pattern

and print_atomic_pattern out pattern =
  match pattern with
  | D.PVar x   -> F.fprintf out "%a" print_var x
  | D.PConst c -> F.fprintf out "%a" print_const c
  | D.PGuard m -> F.fprintf out "(%a)" print_abs_term m
  | D.PLam _
  | D.PApp _   -> F.fprintf out "(%a)" print_abs_pattern pattern

let rec print_pattern out pattern =
  (* Because Dedukti does not allow referring to the head constant by its fully
     qualified name (module_name.constant_name), we have to hack around it. *)
  match pattern with
  | D.PApp (m, n) ->
    F.fprintf out "@[%a@;<1 2>%a@]"
      print_pattern m
      print_atomic_pattern n
  | D.PConst (_, constname) ->
      print_constname out constname
  | _ -> failwith "Invalid pattern"

let rec print_context out = function
  | [] -> ()
  | [x, _] -> F.fprintf out "@[%a@]" print_var x
  | (x, _) :: g ->
    (* Contexts are stored in reverse order. *)
    F.fprintf out "@[%a,@ %a@]"
      print_context g
      print_var x

let print_command out = function
  | D.Require modname -> F.fprintf out "#REQUIRE %a" print_modname modname

let print_comment out comment =
  F.fprintf out "(; %s ;)" comment

let print_entry out entry =
  match entry with
  | D.StcDeclaration (name, ty) ->
    F.fprintf out "@[%a :@;<1 2>%a.@]"
      print_constname name
      print_term ty
  | D.DefDeclaration (name, ty) ->
    F.fprintf out "def @[%a :@;<1 2>%a.@]"
      print_constname name
      print_term ty
  | D.Definition (name, None, body) ->
    F.fprintf out "def @[%a :=@;<1 2>%a.@]"
      print_constname name
      print_term body
  | D.Definition (name, Some(ty), body) ->
    F.fprintf out "def @[%a :@;<1 2>%a@;<1 2>:=@;<1 2>%a.@]"
      print_constname name
      print_term ty
      print_term body
  | D.RewriteRule (context, left_pattern, right_term) ->
    F.fprintf out "@[[ %a ]@;<1 2>%a -->@;<1 2>%a.@]"
      print_context context
      print_pattern left_pattern
      print_term right_term
  | D.Command command ->
    F.fprintf out "%a." print_command command
  | D.Comment comment ->
    F.fprintf out "%a" print_comment comment

let print_signature out signature =
  (* Signatures are stored in reverse order. *)
  (* Reverse first and print one at a time to avoid stack overflow. *)
  let entries = List.rev signature in
  let rec print_entries out entries =
    match entries with
    | [] -> ()
    | entry :: entries ->
      F.fprintf out "@[%a@.@.@]" print_entry entry;
      print_entries out entries
  in
  print_entries out entries
