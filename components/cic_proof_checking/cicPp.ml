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

(*****************************************************************************)
(*                                                                           *)
(*                               PROJECT HELM                                *)
(*                                                                           *)
(* This module implements a very simple Coq-like pretty printer that, given  *)
(* an object of cic (internal representation) returns a string describing    *)
(* the object in a syntax similar to that of coq                             *)
(*                                                                           *)
(* It also contains the utility functions to check a name w.r.t the Matita   *)
(* naming policy                                                             *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

exception CicPpInternalError;;
exception NotEnoughElements;;

(* Utility functions *)

let ppname =
 function
    Cic.Name s     -> s
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

(* pp t l                                                                  *)
(* pretty-prints a term t of cic in an environment l where l is a list of  *)
(* identifier names used to resolve DeBrujin indexes. The head of l is the *)
(* name associated to the greatest DeBrujin index in t                     *)
let pp ?metasenv =
let rec pp t l =
 let module C = Cic in
   match t with
      C.Rel n ->
       begin
        try
         (match get_nth l n with
             Some (C.Name s) -> s
           | Some C.Anonymous -> "__" ^ string_of_int n
           | None -> "_hidden_" ^ string_of_int n
         )
        with
         NotEnoughElements -> string_of_int (List.length l - n)
       end
    | C.Var (uri,exp_named_subst) ->
       UriManager.string_of_uri (*UriManager.name_of_uri*) uri ^ pp_exp_named_subst exp_named_subst l
    | C.Meta (n,l1) ->
       (match metasenv with
           None ->
            "?" ^ (string_of_int n) ^ "[" ^ 
             String.concat " ; "
              (List.rev_map (function None -> "_" | Some t -> pp t l) l1) ^
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
                       | Some _, Some t -> pp t l
                    ) context l1)) ^
               "]"
            with
	      CicUtil.Meta_not_found _ 
            | Invalid_argument _ ->
              "???" ^ (string_of_int n) ^ "[" ^ 
               String.concat " ; "
                (List.rev_map (function None -> "_" | Some t -> pp t l) l1) ^
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
          C.Name n -> "(\\forall " ^ n ^ ":" ^ pp s l ^ "." ^ pp t ((Some b)::l) ^ ")"
        | C.Anonymous -> "(" ^ pp s l ^ "\\to " ^ pp t ((Some b)::l) ^ ")"
       )
    | C.Cast (v,t) -> "(" ^ pp v l ^ ":" ^ pp t l ^ ")"
    | C.Lambda (b,s,t) ->
       "(\\lambda " ^ ppname b ^ ":" ^ pp s l ^ "." ^ pp t ((Some b)::l) ^ ")"
    | C.LetIn (b,s,ty,t) ->
       " let " ^ ppname b ^ ": " ^ pp ty l ^ " \\def " ^ pp s l ^ " in " ^ pp t ((Some b)::l)
    | C.Appl li ->
       "(" ^
       (List.fold_right
        (fun x i -> pp x l ^ (match i with "" -> "" | _ -> " ") ^ i)
        li ""
       ) ^ ")"
    | C.Const (uri,exp_named_subst) ->
       UriManager.name_of_uri uri ^ pp_exp_named_subst exp_named_subst l
    | C.MutInd (uri,n,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.empty_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let (name,_,_,_) = get_nth dl (n+1) in
              name ^ pp_exp_named_subst exp_named_subst l
          | _ -> raise CicPpInternalError
        with
           Sys.Break as exn -> raise exn
         | _ -> UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n + 1)
       )
    | C.MutConstruct (uri,n1,n2,exp_named_subst) ->
       (try
         match fst(CicEnvironment.get_obj CicUniv.empty_ugraph uri) with
            C.InductiveDefinition (dl,_,_,_) ->
             let (_,_,_,cons) = get_nth dl (n1+1) in
              let (id,_) = get_nth cons n2 in
               id ^ pp_exp_named_subst exp_named_subst l
          | _ -> raise CicPpInternalError
        with
           Sys.Break as exn -> raise exn
         | _ ->
          UriManager.string_of_uri uri ^ "#1/" ^ string_of_int (n1 + 1) ^ "/" ^
           string_of_int n2
       )
    | C.MutCase (uri,n1,ty,te,patterns) ->
       let connames_and_argsno =
        (match fst(CicEnvironment.get_obj CicUniv.empty_ugraph uri) with
            C.InductiveDefinition (dl,_,paramsno,_) ->
             let (_,_,_,cons) = get_nth dl (n1+1) in
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
                  id, count_prods paramsno ty
               ) cons
          | _ -> raise CicPpInternalError
        )
       in
        let connames_and_argsno_and_patterns =
         let rec combine =
            function
               [],[] -> []
             | [],l -> List.map (fun x -> "???",0,Some x) l
             | l,[] -> List.map (fun (x,no) -> x,no,None) l
             | (x,no)::tlx,y::tly -> (x,no,Some y)::(combine (tlx,tly))
         in
          combine (connames_and_argsno,patterns)
        in
         "\nmatch " ^ pp te l ^ " return " ^ pp ty l ^ " with \n [ " ^
          (String.concat "\n | "
           (List.map
            (fun (x,argsno,y) ->
              let rec aux argsno l =
               function
                  Cic.Lambda (name,ty,bo) when argsno > 0 ->
                   let args,res = aux (argsno - 1) (Some name::l) bo in
                    ("(" ^ (match name with C.Anonymous -> "_" | C.Name s -> s)^
                     ":" ^ pp ty l ^ ")")::args, res
                | t when argsno = 0 -> [],pp t l
                | t -> ["{" ^ string_of_int argsno ^ " args missing}"],pp t l
              in
               let pattern,body =
                match y with
                   None -> x,""
                 | Some y when argsno = 0 -> x,pp y l
                 | Some y ->
                    let args,body = aux argsno l y in
                     "(" ^ x ^ " " ^ String.concat " " args ^ ")",body
               in
                pattern ^ " => " ^ body
            ) connames_and_argsno_and_patterns)) ^
          "\n]"
    | C.Fix (no, funs) ->
       let snames = List.map (fun (name,_,_,_) -> name) funs in
        let names =
         List.rev (List.map (function name -> Some (C.Name name)) snames)
        in
         "\nFix " ^ get_nth snames (no + 1) ^ " {" ^
         List.fold_right
          (fun (name,ind,ty,bo) i -> "\n" ^ name ^ " / " ^ string_of_int ind ^
            " : " ^ pp ty l ^ " := \n" ^
            pp bo (names@l) ^ i)
          funs "" ^
         "}\n"
    | C.CoFix (no,funs) ->
       let snames = List.map (fun (name,_,_) -> name) funs in
        let names =
         List.rev (List.map (function name -> Some (C.Name name)) snames)
        in
         "\nCoFix " ^ get_nth snames (no + 1) ^ " {" ^
         List.fold_right
          (fun (name,ty,bo) i -> "\n" ^ name ^ 
            " : " ^ pp ty l ^ " := \n" ^
            pp bo (names@l) ^ i)
          funs "" ^
         "}\n"
and pp_exp_named_subst exp_named_subst l =
 if exp_named_subst = [] then "" else
  "\\subst[" ^
   String.concat " ; " (
    List.map
     (function (uri,t) -> UriManager.name_of_uri uri ^ " \\Assign " ^ pp t l)
     exp_named_subst
   ) ^ "]"
in
 pp
;;

let ppterm ?metasenv t =
 pp ?metasenv t []
;;

(* ppinductiveType (typename, inductive, arity, cons)                       *)
(* pretty-prints a single inductive definition                              *)
(* (typename, inductive, arity, cons)                                       *)
let ppinductiveType (typename, inductive, arity, cons) =
  (if inductive then "\nInductive " else "\nCoInductive ") ^ typename ^ ": " ^
  pp arity [] ^ " =\n   " ^
  List.fold_right
   (fun (id,ty) i -> id ^ " : " ^ pp ty [] ^ 
    (if i = "" then "\n" else "\n | ") ^ i)
   cons ""
;;

let ppcontext ?metasenv ?(sep = "\n") context =
 let separate s = if s = "" then "" else s ^ sep in
 fst (List.fold_right 
   (fun context_entry (i,name_context) ->
     match context_entry with
        Some (n,Cic.Decl t) ->
         Printf.sprintf "%s%s : %s" (separate i) (ppname n)
          (pp ?metasenv t name_context), (Some n)::name_context
      | Some (n,Cic.Def (bo,ty)) ->
         Printf.sprintf "%s%s : %s := %s" (separate i) (ppname n)
          (pp ?metasenv ty name_context)
          (pp ?metasenv bo name_context), (Some n)::name_context
       | None ->
          Printf.sprintf "%s_ :? _" (separate i), None::name_context
    ) context ("",[]))

(* ppobj obj  returns a string with describing the cic object obj in a syntax *)
(* similar to the one used by Coq                                             *)
let ppobj obj =
 let module C = Cic in
 let module U = UriManager in
  match obj with
    C.Constant (name, Some t1, t2, params, _) ->
      "Definition of " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^ pp t1 [] ^ " : " ^ pp t2 []
   | C.Constant (name, None, ty, params, _) ->
      "Axiom " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       "):\n" ^ pp ty []
   | C.Variable (name, bo, ty, params, _) ->
      "Variable " ^ name ^
       "(" ^ String.concat ";" (List.map UriManager.string_of_uri params) ^
       ")" ^ ":\n" ^
       pp ty [] ^ "\n" ^
       (match bo with None -> "" | Some bo -> ":= " ^ pp bo [])
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
                            pp ~metasenv:conjectures at name_context ^ " ",
                            (Some n)::name_context
                      | Some (n,C.Def (at,aty)) ->
                         (separate i) ^
                           ppname n ^ ": " ^
                            pp ~metasenv:conjectures aty name_context ^
                            ":= " ^ pp ~metasenv:conjectures
                            at name_context ^ " ",
                            (Some n)::name_context
                      | None ->
                         (separate i) ^ "_ :? _ ", None::name_context)
            ) context ("",[])
          in
           conjectures' ^ " |- " ^ "?" ^ (string_of_int n) ^ ": " ^
            pp ~metasenv:conjectures t name_context ^ "\n" ^ i
        ) conjectures "" ^
        "\n" ^ pp ~metasenv:conjectures value [] ^ " : " ^
          pp ~metasenv:conjectures ty [] 
   | C.InductiveDefinition (l, params, nparams, _) ->
      "Parameters = " ^
       String.concat ";" (List.map UriManager.string_of_uri params) ^ "\n" ^
       "NParams = " ^ string_of_int nparams ^ "\n" ^
        List.fold_right (fun x i -> ppinductiveType x ^ i) l ""
;;

let ppsort = function
  | Cic.Prop -> "Prop"
  | Cic.Set -> "Set"
  | Cic.Type _ -> "Type"
  | Cic.CProp _ -> "CProp"


(* MATITA NAMING CONVENTION *)

let is_prefix prefix string =
  let len = String.length prefix in
  let len1 = String.length string in
  if len <= len1 then
    begin
      let head = String.sub string 0 len in
      if 
      (String.compare (String.lowercase head) (String.lowercase prefix)=0) then 
	begin
	  let diff = len1-len in
	  let tail = String.sub string len diff in
	  if ((diff > 0) && (String.rcontains_from tail 0 '_')) then
	    Some (String.sub tail 1 (diff-1))
	    else Some tail
	  end
	else None
    end
  else None

let remove_prefix prefix (last,string) =
  if string = "" then (last,string)
  else 
    match is_prefix prefix string with
      None ->
	if last <> "" then 
	  match is_prefix last prefix with
	    None -> (last,string)
	  | Some _ ->
              (match is_prefix prefix (last^string) with
		None -> (last,string)
	      | Some tail -> (prefix,tail))
	else (last,string)
    | Some tail -> (prefix, tail)
	
let legal_suffix string = 
  if string = "" then true else
  begin
    let legal_s = Str.regexp "_?\\([0-9]+\\|r\\|l\\|'\\|\"\\)" in
    (Str.string_match legal_s string 0) && (Str.matched_string string = string)
  end

(** check if a prefix of string_name is legal for term and returns the tail.
    chec_rec cannot fail: at worst it return string_name.
    The algorithm is greedy, but last contains the last name matched, providing
    a one slot buffer. 
    string_name is here a pair (last,string_name).*)

let rec check_rec ctx string_name =
  function
    | Cic.Rel m -> 
	(match List.nth ctx (m-1) with
	  Cic.Name name ->
	    remove_prefix name string_name
	| Cic.Anonymous -> string_name)
    | Cic.Meta _ -> string_name
    | Cic.Sort sort -> remove_prefix (ppsort sort) string_name  
    | Cic.Implicit _ -> string_name
    | Cic.Cast (te,ty) -> check_rec ctx string_name te
    | Cic.Prod (name,so,dest) -> 
	let l_string_name = check_rec ctx string_name so in
	check_rec (name::ctx) l_string_name dest
    | Cic.Lambda (name,so,dest) -> 
        let string_name =
          match name with
            Cic.Anonymous -> string_name
          | Cic.Name name -> remove_prefix name string_name in
        let l_string_name = check_rec ctx string_name so in
	check_rec (name::ctx) l_string_name dest
    | Cic.LetIn (name,so,_,dest) -> 
        let string_name = check_rec ctx string_name so in
	check_rec (name::ctx) string_name dest
    | Cic.Appl l ->
	List.fold_left (check_rec ctx) string_name l
    | Cic.Var (uri,exp_named_subst) ->
	let name = UriManager.name_of_uri uri in
	remove_prefix name string_name
    | Cic.Const (uri,exp_named_subst) ->
	let name = UriManager.name_of_uri uri in
	remove_prefix name string_name
    | Cic.MutInd (uri,_,exp_named_subst) -> 
	let name = UriManager.name_of_uri uri in
	remove_prefix name string_name  
    | Cic.MutConstruct (uri,n,m,exp_named_subst) ->
	let name =
          (match fst(CicEnvironment.get_obj CicUniv.empty_ugraph uri) with
	    Cic.InductiveDefinition (dl,_,_,_) ->
	      let (_,_,_,cons) = get_nth dl (n+1) in
	      let (id,_) = get_nth cons m in
	      id 
	  | _ -> assert false) in
	remove_prefix name string_name  
    | Cic.MutCase (_,_,_,te,pl) ->
	let string_name = remove_prefix "match" string_name in
	let string_name = check_rec ctx string_name te in
        List.fold_right (fun t s -> check_rec ctx s t) pl string_name
    | Cic.Fix (_,fl) ->
        let string_name = remove_prefix "fix" string_name in
        let names = List.map (fun (name,_,_,_) -> name) fl in
        let onames =
          List.rev (List.map (function name -> Cic.Name name) names)
        in
        List.fold_right 
	  (fun (_,_,_,bo) s -> check_rec (onames@ctx) s bo) fl string_name
    | Cic.CoFix (_,fl) ->
	let string_name = remove_prefix "cofix" string_name in
        let names = List.map (fun (name,_,_) -> name) fl in
        let onames =
          List.rev (List.map (function name -> Cic.Name name) names)
        in
        List.fold_right 
	  (fun (_,_,bo) s -> check_rec (onames@ctx) s bo) fl string_name

let check_name ?(allow_suffix=false) ctx name term =
  let (_,tail) = check_rec ctx ("",name) term in
  if (not allow_suffix) then (String.length tail = 0) 
  else legal_suffix tail

let check_elim ctx conclusion_name =
  let elim = Str.regexp "_elim\\|_case" in
  if (Str.string_match elim conclusion_name 0) then
    let len = String.length conclusion_name in
    let tail = String.sub conclusion_name 5 (len-5) in
    legal_suffix tail
  else false

let rec check_names ctx hyp_names conclusion_name t =
  match t with
    | Cic.Prod (name,s,t) -> 
	(match hyp_names with
	     [] -> check_names (name::ctx) hyp_names conclusion_name t
	   | hd::tl ->
	       if check_name ctx hd s then 
		 check_names (name::ctx) tl conclusion_name t
	       else 
		 check_names (name::ctx) hyp_names conclusion_name t)
    | Cic.Appl ((Cic.Rel n)::args) -> 
  	(match hyp_names with
 	  | [] ->
	      (check_name ~allow_suffix:true ctx conclusion_name t) ||
              (check_elim ctx conclusion_name)
	  | [what_to_elim] ->   
              (* what to elim could be an argument 
                 of the predicate: e.g. leb_elim *)
	      let (last,tail) = 
		List.fold_left (check_rec ctx) ("",what_to_elim) args in
              (tail = "" && check_elim ctx conclusion_name)
	  | _ -> false)
    | Cic.MutCase  (_,_,Cic.Lambda(name,so,ty),te,_) ->
	(match hyp_names with
 	  | [] ->
               (match is_prefix "match" conclusion_name with
		   None -> check_name ~allow_suffix:true ctx conclusion_name t
	       | Some tail -> check_name ~allow_suffix:true ctx tail t)
	  | [what_to_match] ->   
              (* what to match could be the term te or its type so; in this case the
                 conclusion name should match ty *)
	      check_name ~allow_suffix:true (name::ctx) conclusion_name ty &&
              (check_name ctx what_to_match te || check_name ctx what_to_match so)
	  | _ -> false)
    | _ -> 
	hyp_names=[] && check_name ~allow_suffix:true ctx conclusion_name t

let check name term =
  let names = Str.split (Str.regexp_string "_to_") name in
  let hyp_names,conclusion_name =
    match List.rev names with
	[] -> assert false
      | hd::tl -> 
          let elim = Str.regexp "_elim\\|_case" in
          let len = String.length hd in
          try 
	    let pos = Str.search_backward elim hd len in
	    let hyp = String.sub hd 0 pos in
	    let concl = String.sub hd pos (len-pos) in
	    List.rev (hyp::tl),concl
          with Not_found -> (List.rev tl),hd in
  check_names [] hyp_names conclusion_name term
;;


