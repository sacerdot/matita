(* Copyright (C) 2000, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(* $Id: cicPp.ml 7413 2007-05-29 15:30:53Z tassi $ *)

exception CicExportationInternalError;;
exception NotEnoughElements;;

(* *)

let is_mcu_type u = 
  UriManager.eq (UriManager.uri_of_string
  "cic:/matita/freescale/opcode/mcu_type.ind") u
;;

(* Utility functions *)

let analyze_term context t =
 match fst(CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph)with
  | Cic.Sort _ -> `Type
  | Cic.MutInd (u,0,_) when is_mcu_type u -> `Optimize
  | ty -> 
     match
      fst (CicTypeChecker.type_of_aux' [] context ty CicUniv.oblivion_ugraph)
     with
     | Cic.Sort Cic.Prop -> `Proof
     | _ -> `Term
;;

let analyze_type context t =
 let rec aux =
  function
     Cic.Sort s -> `Sort s
   | Cic.MutInd (u,0,_) when is_mcu_type u -> `Optimize
   | Cic.Prod (_,_,t) -> aux t
   | _ -> `SomethingElse
 in
 match aux t with
    `Sort _ | `Optimize as res -> res
  | `SomethingElse ->
      match
       fst(CicTypeChecker.type_of_aux' [] context t CicUniv.oblivion_ugraph)
      with
          Cic.Sort Cic.Prop -> `Statement
       | _ -> `Type
;;

let ppid =
 let reserved =
  [ "to";
    "mod";
    "val";
    "in";
    "function"
  ]
 in
  function n ->
   let n = String.uncapitalize n in
    if List.mem n reserved then n ^ "_" else n
;;

let ppname =
 function
    Cic.Name s     -> ppid s
  | Cic.Anonymous  -> "_"
;;

(* get_nth l n   returns the nth element of the list l if it exists or *)
(* raises NotEnoughElements if l has less than n elements             *)
let rec get_nth l n =
 match (n,l) with
    (1, he::_) -> he
  | (n, he::tail) when n > 1 -> get_nth tail (n-1)
  | (_,_) -> raise NotEnoughElements
;;

let qualified_name_of_uri current_module_uri ?(capitalize=false) uri =
 let name =
  if capitalize then
   String.capitalize (UriManager.name_of_uri uri)
  else
   ppid (UriManager.name_of_uri uri) in
  let filename =
   let suri = UriManager.buri_of_uri uri in
   let s = String.sub suri 5 (String.length suri - 5) in
   let s = Pcre.replace ~pat:"/" ~templ:"_" s in
    String.uncapitalize s in
  if current_module_uri = UriManager.buri_of_uri uri then
   name
  else
   String.capitalize filename ^ "." ^ name
;;

let current_go_up = ref "(.!(";;
let at_level2 f x = 
  try 
    current_go_up := "(.~(";
    let rc = f x in 
    current_go_up := "(.!("; 
    rc
  with exn -> 
    current_go_up := "(.!("; 
    raise exn
;;

let pp current_module_uri ?metasenv ~in_type =
let rec pp ~in_type t context =
 let module C = Cic in
   match t with
      C.Rel n ->
       begin
        try
         (match get_nth context n with
             Some (C.Name s,_) -> ppid s
           | Some (C.Anonymous,_) -> "__" ^ string_of_int n
           | None -> "_hidden_" ^ string_of_int n
         )
        with
         NotEnoughElements -> string_of_int (List.length context - n)
       end
    | C.Var (uri,exp_named_subst) ->
        qualified_name_of_uri current_module_uri uri ^
         pp_exp_named_subst exp_named_subst context
    | C.Meta (n,l1) ->
       (match metasenv with
           None ->
            "?" ^ (string_of_int n) ^ "[" ^ 
             String.concat " ; "
              (List.rev_map
                (function
                    None -> "_"
                  | Some t -> pp ~in_type:false t context) l1) ^
             "]"
         | Some metasenv ->
            try
             let _,context,_ = CicUtil.lookup_meta n metasenv in
              "?" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev
                  (List.map2
                    (fun x y ->
                      match x,y with
                         _, None
                       | None, _ -> "_"
                       | Some _, Some t -> pp ~in_type:false t context
                    ) context l1)) ^
               "]"
            with
	      CicUtil.Meta_not_found _ 
            | Invalid_argument _ ->
              "???" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev_map (function None -> "_" | Some t ->
                  pp ~in_type:false t context) l1) ^
               "]"
       )
    | C.Sort s ->
       (match s with
           C.Prop  -> "Prop"
         | C.Set   -> "Set"
         | C.Type _ -> "Type"
         (*| C.Type u -> ("Type" ^ CicUniv.string_of_universe u)*)
	 | C.CProp _ -> "CProp" 
       )
    | C.Implicit (Some `Hole) -> "%"
    | C.Implicit _ -> "?"
    | C.Prod (b,s,t) ->
       (match b with
          C.Name n ->
           let n = "'" ^ String.uncapitalize n in
            "(" ^ pp ~in_type:true s context ^ " -> " ^
            pp ~in_type:true t ((Some (Cic.Name n,Cic.Decl s))::context) ^ ")"
        | C.Anonymous ->
           "(" ^ pp ~in_type:true s context ^ " -> " ^
           pp ~in_type:true t ((Some (b,Cic.Decl s))::context) ^ ")")
    | C.Cast (v,t) -> pp ~in_type v context
    | C.Lambda (b,s,t) ->
       (match analyze_type context s with
           `Sort _
         | `Statement -> pp ~in_type t ((Some (b,Cic.Decl s))::context)
         | `Optimize -> prerr_endline "XXX lambda";assert false
         | `Type ->
            "(function " ^ ppname b ^ " -> " ^
             pp ~in_type t ((Some (b,Cic.Decl s))::context) ^ ")")
    | C.LetIn (b,s,ty,t) ->
       (match analyze_term context s with
         | `Type
         | `Proof -> pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context)
         | `Optimize 
         | `Term ->
            "(let " ^ ppname b ^ (*" : " ^ pp ~in_type:true ty context ^*)
            " = " ^ pp ~in_type:false s context ^ " in " ^
             pp ~in_type t ((Some (b,Cic.Def (s,ty)))::context) ^ ")")
    | C.Appl (he::tl) when in_type ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutInd _ as he::tl) ->
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_ty context tl) in
        (if stl = "" then "" else "(" ^ stl ^ ") ") ^ hes
    | C.Appl (C.MutConstruct (uri,n,_,_) as he::tl) ->
       let nparams =
        match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
           C.InductiveDefinition (_,_,nparams,_) -> nparams
         | _ -> assert false in
       let hes = pp ~in_type he context in
       let stl = String.concat "," (clean_args_for_constr nparams context tl) in
        "(" ^ hes ^ (if stl = "" then "" else "(" ^ stl ^ ")") ^ ")"
    | C.Appl li ->
       "(" ^ String.concat " " (clean_args context li) ^ ")"
    | C.Const (uri,exp_named_subst) ->
       qualified_name_of_uri current_module_uri uri ^
        pp_exp_named_subst exp_named_subst context
    | C.MutInd (uri,n,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let (name,_,_,_) = get_nth dl (n+1) in
              qualified_name_of_uri current_module_uri
               (UriManager.uri_of_string
                 (UriManager.buri_of_uri uri ^ "/" ^ name ^ ".con")) ^
              pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ -> UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n + 1)
       )
    | C.MutConstruct (uri,n1,n2,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let _,_,_,cons = get_nth dl (n1+1) in
              let id,_ = get_nth cons n2 in
               qualified_name_of_uri current_module_uri ~capitalize:true
                (UriManager.uri_of_string
                  (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")) ^
               pp_exp_named_subst exp_named_subst context
          | _ -> raise CicExportationInternalError
        with
           Sys.Break as exn -> raise exn
         | _ ->
          UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n1 + 1) ^ "/" ^
           string_of_int n2
       )
    | C.MutCase (uri,n1,ty,te,patterns) ->
       if in_type then
        "unit (* TOO POLYMORPHIC TYPE *)"
       else (
       let rec needs_obj_magic ty =
        match CicReduction.whd context ty with
         | Cic.Lambda (_,_,(Cic.Lambda(_,_,_) as t)) -> needs_obj_magic t
         | Cic.Lambda (_,_,t) -> not (DoubleTypeInference.does_not_occur 1 t)
         | _ -> false (* it can be a Rel, e.g. in *_rec *)
       in
       let needs_obj_magic = needs_obj_magic ty in
       (match analyze_term context te with
           `Type -> assert false
         | `Proof ->
             (match patterns with
                 [] -> "assert false"   (* empty type elimination *)
               | [he] ->
                  pp ~in_type:false he context  (* singleton elimination *)
               | _ -> assert false)
         | `Optimize 
         | `Term ->
            if patterns = [] then "assert false"
            else
             (let connames_and_argsno, go_up, go_pu, go_down, go_nwod =
               (match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) with
                   C.InductiveDefinition (dl,_,paramsno,_) ->
                    let (_,_,_,cons) = get_nth dl (n1+1) in
                    let rc = 
                     List.map
                      (fun (id,ty) ->
                        (* this is just an approximation since we do not have
                           reduction yet! *)
                        let rec count_prods toskip =
                         function
                            C.Prod (_,_,bo) when toskip > 0 ->
                             count_prods (toskip - 1) bo
                          | C.Prod (_,_,bo) -> 1 + count_prods 0 bo
                          | _ -> 0
                        in
                         qualified_name_of_uri current_module_uri
                          ~capitalize:true
                          (UriManager.uri_of_string
                            (UriManager.buri_of_uri uri ^ "/" ^ id ^ ".con")),
                         count_prods paramsno ty
                      ) cons
                    in
                    if not (is_mcu_type uri) then rc, "","","",""
                    else rc, !current_go_up, "))", "( .< (", " ) >.)"
                 | _ -> raise CicExportationInternalError
               )
              in
               let connames_and_argsno_and_patterns =
                let rec combine =
                   function
                      [],[] -> []
                    | (x,no)::tlx,y::tly -> (x,no,y)::(combine (tlx,tly))
                    | _,_ -> assert false
                in
                 combine (connames_and_argsno,patterns)
               in
                go_up ^
                "\n(match " ^ pp ~in_type:false te context ^ " with \n   " ^
                 (String.concat "\n | "
                  (List.map
                   (fun (x,argsno,y) ->
                     let rec aux argsno context =
                      function
                         Cic.Lambda (name,ty,bo) when argsno > 0 ->
                          let name =
                           match name with
                              Cic.Anonymous -> Cic.Anonymous
                            | Cic.Name n -> Cic.Name (ppid n) in
                          let args,res =
                           aux (argsno - 1) (Some (name,Cic.Decl ty)::context)
                            bo
                          in
                           (match analyze_type context ty with
                             | `Optimize -> prerr_endline "XXX contructor with l2 arg"; assert false
                             | `Statement
                             | `Sort _ -> args,res
                             | `Type ->
                                 (match name with
                                     C.Anonymous -> "_"
                                   | C.Name s -> s)::args,res)
                       | t when argsno = 0 -> [],pp ~in_type:false t context
                       | t ->
                          ["{" ^ string_of_int argsno ^ " args missing}"],
                           pp ~in_type:false t context
                     in
                      let pattern,body =
                       if argsno = 0 then x,pp ~in_type:false y context
                       else
                        let args,body = aux argsno context y in
                        let sargs = String.concat "," args in
                         x ^ (if sargs = "" then "" else "(" ^ sargs^ ")"),
                          body
                      in
                       pattern ^ " -> " ^ go_down ^
                        (if needs_obj_magic then
                         "Obj.magic (" ^ body ^ ")"
                        else
                         body) ^ go_nwod
                   ) connames_and_argsno_and_patterns)) ^
                 ")\n"^go_pu)))
    | C.Fix (no, funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,_,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "let rec " ^
         List.fold_right
          (fun (name,ind,ty,bo) i -> name ^ " = \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         " in " ^
         (match get_nth names (no + 1) with
             Some (Cic.Name n,_) -> n
           | _ -> assert false)
    | C.CoFix (no,funs) ->
       let names,_ =
        List.fold_left
         (fun (types,len) (n,ty,_) ->
            (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
             len+1)
         ) ([],0) funs
       in
         "\nCoFix " ^ " {" ^
         List.fold_right
          (fun (name,ty,bo) i -> "\n" ^ name ^ 
            " : " ^ pp ~in_type:true ty context ^ " := \n" ^
            pp ~in_type:false bo (names@context) ^ i)
          funs "" ^
         "}\n"
and pp_exp_named_subst exp_named_subst context =
 if exp_named_subst = [] then "" else
  "\\subst[" ^
   String.concat " ; " (
    List.map
     (function (uri,t) -> UriManager.name_of_uri uri ^ " \\Assign " ^ pp ~in_type:false t context)
     exp_named_subst
   ) ^ "]"
and clean_args_for_constr nparams context =
 let nparams = ref nparams in
 HExtlib.filter_map
  (function t ->
    decr nparams;
    match analyze_term context t with
       `Term when !nparams < 0 -> Some (pp ~in_type:false t context)
     | `Optimize 
     | `Term
     | `Type
     | `Proof -> None)
and clean_args context =
 function
 | [] | [_] -> assert false
 | he::arg1::tl as l ->
    let head_arg1, rest = 
       match analyze_term context arg1 with
      | `Optimize -> 
         !current_go_up :: pp ~in_type:false he context :: 
                 pp ~in_type:false arg1 context :: ["))"], tl
      | _ -> [], l
    in
    head_arg1 @ 
    HExtlib.filter_map
     (function t ->
       match analyze_term context t with
        | `Term -> Some (pp ~in_type:false t context)
        | `Optimize -> 
            prerr_endline "XXX function taking twice (or not as first) a l2 term"; assert false
        | `Type
        | `Proof -> None) rest
and clean_args_for_ty context =
 HExtlib.filter_map
  (function t ->
    match analyze_term context t with
       `Type -> Some (pp ~in_type:true t context)
     | `Optimize -> None
     | `Proof -> None
     | `Term -> None)
in
 pp ~in_type
;;

let ppty current_module_uri =
 (* nparams is the number of left arguments
    left arguments should either become parameters or be skipped altogether *)
 let rec args nparams context =
  function
     Cic.Prod (n,s,t) ->
      let n =
       match n with
          Cic.Anonymous -> Cic.Anonymous
        | Cic.Name n -> Cic.Name (String.uncapitalize n)
      in
       (match analyze_type context s with
         | `Optimize
         | `Statement
         | `Sort Cic.Prop ->
             args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Type when nparams > 0 ->
             args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Type ->
             let abstr,args =
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t in
               abstr,pp ~in_type:true current_module_uri s context::args
         | `Sort _ when nparams <= 0 ->
             let n = Cic.Name "unit (* EXISTENTIAL TYPE *)" in
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
         | `Sort _ ->
             let n =
              match n with
                 Cic.Anonymous -> Cic.Anonymous
               | Cic.Name name -> Cic.Name ("'" ^ name) in
             let abstr,args =
              args (nparams - 1) ((Some (n,Cic.Decl s))::context) t
             in
              (match n with
                  Cic.Anonymous -> abstr
                | Cic.Name name -> name::abstr),
              args)
   | _ -> [],[]
 in
  args
;;

exception DoNotExtract;;

let pp_abstracted_ty current_module_uri =
 let rec args context =
  function
     Cic.Lambda (n,s,t) ->
      let n =
       match n with
          Cic.Anonymous -> Cic.Anonymous
        | Cic.Name n -> Cic.Name (String.uncapitalize n)
      in
       (match analyze_type context s with
         | `Optimize 
         | `Statement
         | `Type
         | `Sort Cic.Prop ->
             args ((Some (n,Cic.Decl s))::context) t
         | `Sort _ ->
             let n =
              match n with
                 Cic.Anonymous -> Cic.Anonymous
               | Cic.Name name -> Cic.Name ("'" ^ name) in
             let abstr,res =
              args ((Some (n,Cic.Decl s))::context) t
             in
              (match n with
                  Cic.Anonymous -> abstr
                | Cic.Name name -> name::abstr),
              res)
   | ty ->
     match analyze_type context ty with
      | `Optimize ->
           prerr_endline "XXX abstracted l2 ty"; assert false
      | `Sort _
      | `Statement -> raise DoNotExtract
      | `Type ->
          (* BUG HERE: this can be a real System F type *)
          let head = pp ~in_type:true current_module_uri ty context in
          [],head
 in
  args
;;


(* ppinductiveType (typename, inductive, arity, cons)                       *)
(* pretty-prints a single inductive definition                              *)
(* (typename, inductive, arity, cons)                                       *)
let ppinductiveType current_module_uri nparams (typename, inductive, arity, cons)
=
 match analyze_type [] arity with
    `Sort Cic.Prop -> ""
  | `Optimize 
  | `Statement
  | `Type -> assert false
  | `Sort _ ->
    if cons = [] then
     "type " ^ String.uncapitalize typename ^ " = unit (* empty type *)\n"
    else (
     let abstr,scons =
      List.fold_right
       (fun (id,ty) (_abstr,i) -> (* we should verify _abstr = abstr' *)
          let abstr',sargs = ppty current_module_uri nparams [] ty in
          let sargs = String.concat " * " sargs in
           abstr',
           String.capitalize id ^
            (if sargs = "" then "" else " of " ^ sargs) ^
            (if i = "" then "" else "\n | ") ^ i)
       cons ([],"")
      in
       let abstr =
        let s = String.concat "," abstr in
        if s = "" then "" else "(" ^ s ^ ") "
       in
       "type " ^ abstr ^ String.uncapitalize typename ^ " =\n" ^ scons ^ "\n")
;;

let ppobj current_module_uri obj =
 let module C = Cic in
 let module U = UriManager in
  let pp ~in_type = pp ~in_type current_module_uri in
  match obj with
    C.Constant (name, Some t1, t2, params, _) ->
      (match analyze_type [] t2 with
        | `Sort Cic.Prop
        | `Statement -> ""
        | `Optimize 
        | `Type -> 
            (match t1 with
            | Cic.Lambda (Cic.Name arg, s, t) ->
                            (match analyze_type [] s with
                | `Optimize -> 

                    "let " ^ ppid name ^ "__1 = function " ^ ppid arg 
                    ^ " -> .< " ^ 
                    at_level2 (pp ~in_type:false t) [Some (Cic.Name arg, Cic.Decl s)] 
                    ^ " >. ;;\n"
                    ^ "let " ^ ppid name ^ "__2 = ref ([] : (unit list*unit list) list);;\n"
                    ^ "let " ^ ppid name ^ " = function " ^ ppid arg
                    ^ " -> (try ignore (List.assoc "^ppid arg^" (Obj.magic  !"^ppid name
                    ^"__2)) with Not_found -> "^ppid name^"__2 := (Obj.magic ("
                    ^ ppid arg^",.! ("^ppid name^"__1 "^ppid arg^")))::!"
                    ^ppid name^"__2); .< List.assoc "^ppid arg^" (Obj.magic (!"
                    ^ppid name^"__2)) >.\n;;\n"
                    ^" let xxx = prerr_endline \""^ppid name^"\"; .!("^ppid
                    name^" Matita_freescale_opcode.HCS08)"
                | _ -> 
                   "let " ^ ppid name ^ " =\n" ^ pp ~in_type:false t1 [] ^ "\n")
            | _ -> "let " ^ ppid name ^ " =\n" ^ pp ~in_type:false t1 [] ^ "\n")
        | `Sort _ ->
            match analyze_type [] t1 with
               `Sort Cic.Prop -> ""
             | `Optimize -> prerr_endline "XXX aliasing l2 type"; assert false
             | _ ->
               (try
                 let abstr,res = pp_abstracted_ty current_module_uri [] t1 in
                 let abstr =
                  let s = String.concat "," abstr in
                  if s = "" then "" else "(" ^ s ^ ") "
                 in
                  "type " ^ abstr ^ ppid name ^ " = " ^ res ^ "\n"
                with
                 DoNotExtract -> ""))
   | C.Constant (name, None, ty, params, _) ->
      (match analyze_type [] ty with
          `Sort Cic.Prop
        | `Optimize -> prerr_endline "XXX axiom l2"; assert false
        | `Statement -> ""
        | `Sort _ -> "type " ^ ppid name ^ "\n"
        | `Type -> "let " ^ ppid name ^ " = assert false\n")
   | C.Variable (name, bo, ty, params, _) ->
      "Variable " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^
       pp ~in_type:true ty [] ^ "\n" ^
       (match bo with None -> "" | Some bo -> ":= " ^ pp ~in_type:false bo [])
   | C.CurrentProof (name, conjectures, value, ty, params, _) ->
      "Current Proof of " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^
      let separate s = if s = "" then "" else s ^ " ; " in
       List.fold_right
        (fun (n, context, t) i -> 
          let conjectures',name_context =
	         List.fold_right 
	          (fun context_entry (i,name_context) ->
	            (match context_entry with
	                Some (n,C.Decl at) ->
                         (separate i) ^
                           ppname n ^ ":" ^
                            pp ~in_type:true ~metasenv:conjectures
                            at name_context ^ " ",
                            context_entry::name_context
	              | Some (n,C.Def (at,aty)) ->
                         (separate i) ^
                           ppname n ^ ":" ^
                            pp ~in_type:true ~metasenv:conjectures
                            aty name_context ^
                           ":= " ^ pp ~in_type:false
                            ~metasenv:conjectures at name_context ^ " ",
                            context_entry::name_context
                      | None ->
                         (separate i) ^ "_ :? _ ", context_entry::name_context)
            ) context ("",[])
          in
           conjectures' ^ " |- " ^ "?" ^ (string_of_int n) ^ ": " ^
            pp ~in_type:true ~metasenv:conjectures t name_context ^ "\n" ^ i
        ) conjectures "" ^
        "\n" ^ pp ~in_type:false ~metasenv:conjectures value [] ^ " : " ^
          pp ~in_type:true ~metasenv:conjectures ty [] 
   | C.InductiveDefinition (l, params, nparams, _) ->
      List.fold_right
       (fun x i -> ppinductiveType current_module_uri nparams x ^ i) l ""
;;

let ppobj current_module_uri obj =
 let res = ppobj current_module_uri obj in
  if res = "" then "" else res ^ ";;\n\n"
;;
