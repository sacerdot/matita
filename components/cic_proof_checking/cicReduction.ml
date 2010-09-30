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

(* $Id$ *)

(* TODO unify exceptions *)

exception WrongUriToInductiveDefinition;;
exception Impossible of int;;
exception ReferenceToConstant;;
exception ReferenceToVariable;;
exception ReferenceToCurrentProof;;
exception ReferenceToInductiveDefinition;;

let ndebug = ref false;;
let indent = ref "";;
let times = ref [];;
let pp s =
 if !ndebug then
  prerr_endline (Printf.sprintf "%-20s" !indent ^ " " ^ Lazy.force s)
;;
let inside c =
 if !ndebug then
  begin
   let time1 = Unix.gettimeofday () in
   indent := !indent ^ String.make 1 c;
   times := time1 :: !times;
   prerr_endline ("{{{" ^ !indent ^ " ")
  end
;;
let outside ok =
 if !ndebug then
  begin
   let time2 = Unix.gettimeofday () in
   let time1 =
    match !times with time1::tl -> times := tl; time1 | [] -> assert false in
   prerr_endline ("}}} " ^ string_of_float (time2 -. time1));
   if not ok then prerr_endline "exception raised!";
   try
    indent := String.sub !indent 0 (String.length !indent -1)
   with
    Invalid_argument _ -> indent := "??"; ()
 end
;;

let debug = false
let profile = false
let debug_print s = if debug then prerr_endline (Lazy.force s)

let fdebug = ref 1;;
let debug t env s =
 let rec debug_aux t i =
  let module C = Cic in
  let module U = UriManager in
   CicPp.ppobj (C.Variable ("DEBUG", None, t, [], [])) ^ "\n" ^ i
 in
  if !fdebug = 0 then
   debug_print (lazy (s ^ "\n" ^ List.fold_right debug_aux (t::env) ""))
;;

module type Strategy =
 sig
  type stack_term
  type env_term
  type ens_term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  val to_env :
   reduce: (config -> config) ->
   unwind: (config -> Cic.term) ->
   config -> env_term
  val to_ens :
   reduce: (config -> config) ->
   unwind: (config -> Cic.term) ->
   config -> ens_term
  val from_stack : stack_term -> config
  val from_stack_list_for_unwind :
   unwind: (config -> Cic.term) ->
   stack_term list -> Cic.term list
  val from_env : env_term -> config
  val from_env_for_unwind :
   unwind: (config -> Cic.term) ->
   env_term -> Cic.term
  val from_ens : ens_term -> config
  val from_ens_for_unwind :
   unwind: (config -> Cic.term) ->
   ens_term -> Cic.term
  val stack_to_env :
   reduce: (config -> config) ->
   unwind: (config -> Cic.term) ->
   stack_term -> env_term
  val compute_to_env :
   reduce: (config -> config) ->
   unwind: (config -> Cic.term) ->
   int -> env_term list -> ens_term Cic.explicit_named_substitution ->
    Cic.term -> env_term
  val compute_to_stack :
   reduce: (config -> config) ->
   unwind: (config -> Cic.term) ->
   config -> stack_term
 end
;;

module CallByValueByNameForUnwind =
 struct
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  and stack_term = config
  and env_term = config * config (* cbv, cbn *)
  and ens_term = config * config (* cbv, cbn *)

  let to_env c = c,c
  let to_ens c = c,c
  let from_stack config = config
  let from_stack_list_for_unwind ~unwind l = List.map unwind l
  let from_env (c,_) = c
  let from_ens (c,_) = c
  let from_env_for_unwind ~unwind (_,c) = unwind c
  let from_ens_for_unwind ~unwind (_,c) = unwind c
  let stack_to_env ~reduce ~unwind config = reduce config, (0,[],[],unwind config,[])
  let compute_to_env ~reduce ~unwind k e ens t = (k,e,ens,t,[]), (k,e,ens,t,[])
  let compute_to_stack ~reduce ~unwind config = config
 end
;;

module CallByValueByNameForUnwind' =
 struct
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  and stack_term = config lazy_t * Cic.term lazy_t (* cbv, cbn *)
  and env_term = config lazy_t * Cic.term lazy_t (* cbv, cbn *)
  and ens_term = config lazy_t * Cic.term lazy_t (* cbv, cbn *)

  let to_env ~reduce ~unwind c = lazy (reduce c),lazy (unwind c)
  let to_ens ~reduce ~unwind c = lazy (reduce c),lazy (unwind c)
  let from_stack (c,_) = Lazy.force c
  let from_stack_list_for_unwind ~unwind l = List.map (function (_,c) -> Lazy.force c) l
  let from_env (c,_) = Lazy.force c
  let from_ens (c,_) = Lazy.force c
  let from_env_for_unwind ~unwind (_,c) = Lazy.force c
  let from_ens_for_unwind ~unwind (_,c) = Lazy.force c
  let stack_to_env ~reduce ~unwind config = config
  let compute_to_env ~reduce ~unwind k e ens t =
   lazy (reduce (k,e,ens,t,[])), lazy (unwind (k,e,ens,t,[]))
  let compute_to_stack ~reduce ~unwind config = lazy (reduce config), lazy (unwind config)
 end
;;


(* Old Machine
module CallByNameStrategy =
 struct
  type stack_term = Cic.term
  type env_term = Cic.term
  type ens_term = Cic.term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = v
  let to_ens v = v
  let from_stack ~unwind v = v
  let from_stack_list ~unwind l = l
  let from_env v = v
  let from_ens v = v
  let from_env_for_unwind ~unwind v = v
  let from_ens_for_unwind ~unwind v = v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t = unwind k e ens t
  let compute_to_env ~reduce ~unwind k e ens t = unwind k e ens t
 end
;;
*)

module CallByNameStrategy =
 struct
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  and stack_term = config
  and env_term = config
  and ens_term = config

  let to_env c = c
  let to_ens c = c
  let from_stack config = config
  let from_stack_list_for_unwind ~unwind l = List.map unwind l
  let from_env c = c
  let from_ens c = c
  let from_env_for_unwind ~unwind c = unwind c
  let from_ens_for_unwind ~unwind c = unwind c
  let stack_to_env ~reduce ~unwind config = 0,[],[],unwind config,[]
  let compute_to_env ~reduce ~unwind k e ens t = k,e,ens,t,[]
  let compute_to_stack ~reduce ~unwind config = config
 end
;;

module CallByValueStrategy =
 struct
  type stack_term = Cic.term
  type env_term = Cic.term
  type ens_term = Cic.term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = v
  let to_ens v = v
  let from_stack ~unwind v = v
  let from_stack_list ~unwind l = l
  let from_env v = v
  let from_ens v = v
  let from_env_for_unwind ~unwind v = v
  let from_ens_for_unwind ~unwind v = v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t = reduce (k,e,ens,t,[])
  let compute_to_env ~reduce ~unwind k e ens t = reduce (k,e,ens,t,[])
 end
;;

module CallByValueStrategyByNameOnConstants =
 struct
  type stack_term = Cic.term
  type env_term = Cic.term
  type ens_term = Cic.term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = v
  let to_ens v = v
  let from_stack ~unwind v = v
  let from_stack_list ~unwind l = l
  let from_env v = v
  let from_ens v = v
  let from_env_for_unwind ~unwind v = v
  let from_ens_for_unwind ~unwind v = v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens =
   function
      Cic.Const _ as t -> unwind k e ens t    
    | t -> reduce (k,e,ens,t,[])
  let compute_to_env ~reduce ~unwind k e ens =
   function
      Cic.Const _ as t -> unwind k e ens t    
    | t -> reduce (k,e,ens,t,[])
 end
;;

module LazyCallByValueStrategy =
 struct
  type stack_term = Cic.term lazy_t
  type env_term = Cic.term lazy_t
  type ens_term = Cic.term lazy_t
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = lazy v
  let to_ens v = lazy v
  let from_stack ~unwind v = Lazy.force v
  let from_stack_list ~unwind l = List.map (from_stack ~unwind) l
  let from_env v = Lazy.force v
  let from_ens v = Lazy.force v
  let from_env_for_unwind ~unwind v = Lazy.force v
  let from_ens_for_unwind ~unwind v = Lazy.force v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t = lazy (reduce (k,e,ens,t,[]))
  let compute_to_env ~reduce ~unwind k e ens t = lazy (reduce (k,e,ens,t,[]))
 end
;;

module LazyCallByValueStrategyByNameOnConstants =
 struct
  type stack_term = Cic.term lazy_t
  type env_term = Cic.term lazy_t
  type ens_term = Cic.term lazy_t
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = lazy v
  let to_ens v = lazy v
  let from_stack ~unwind v = Lazy.force v
  let from_stack_list ~unwind l = List.map (from_stack ~unwind) l
  let from_env v = Lazy.force v
  let from_ens v = Lazy.force v
  let from_env_for_unwind ~unwind v = Lazy.force v
  let from_ens_for_unwind ~unwind v = Lazy.force v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t =
   lazy (
    match t with
       Cic.Const _ as t -> unwind k e ens t    
     | t -> reduce (k,e,ens,t,[]))
  let compute_to_env ~reduce ~unwind k e ens t =
   lazy (
    match t with
       Cic.Const _ as t -> unwind k e ens t    
     | t -> reduce (k,e,ens,t,[]))
 end
;;

module LazyCallByNameStrategy =
 struct
  type stack_term = Cic.term lazy_t
  type env_term = Cic.term lazy_t
  type ens_term = Cic.term lazy_t
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = lazy v
  let to_ens v = lazy v
  let from_stack ~unwind v = Lazy.force v
  let from_stack_list ~unwind l = List.map (from_stack ~unwind) l
  let from_env v = Lazy.force v
  let from_ens v = Lazy.force v
  let from_env_for_unwind ~unwind v = Lazy.force v
  let from_ens_for_unwind ~unwind v = Lazy.force v
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t = lazy (unwind k e ens t)
  let compute_to_env ~reduce ~unwind k e ens t = lazy (unwind k e ens t)
 end
;;

module
 LazyCallByValueByNameOnConstantsWhenFromStack_ByNameStrategyWhenFromEnvOrEns
=
 struct
  type stack_term = reduce:bool -> Cic.term
  type env_term = reduce:bool -> Cic.term
  type ens_term = reduce:bool -> Cic.term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v =
   let value = lazy v in
    fun ~reduce -> Lazy.force value
  let to_ens v =
   let value = lazy v in
    fun ~reduce -> Lazy.force value
  let from_stack ~unwind v = (v ~reduce:false)
  let from_stack_list ~unwind l = List.map (from_stack ~unwind) l
  let from_env v = (v ~reduce:true)
  let from_ens v = (v ~reduce:true)
  let from_env_for_unwind ~unwind v = (v ~reduce:true)
  let from_ens_for_unwind ~unwind v = (v ~reduce:true)
  let stack_to_env ~reduce ~unwind v = v
  let compute_to_stack ~reduce ~unwind k e ens t =
   let svalue =
     lazy (
      match t with
         Cic.Const _ as t -> unwind k e ens t    
       | t -> reduce (k,e,ens,t,[])
     ) in
   let lvalue =
    lazy (unwind k e ens t)
   in
    fun ~reduce ->
     if reduce then Lazy.force svalue else Lazy.force lvalue
  let compute_to_env ~reduce ~unwind k e ens t =
   let svalue =
     lazy (
      match t with
         Cic.Const _ as t -> unwind k e ens t    
       | t -> reduce (k,e,ens,t,[])
     ) in
   let lvalue =
    lazy (unwind k e ens t)
   in
    fun ~reduce ->
     if reduce then Lazy.force svalue else Lazy.force lvalue
 end
;;

module ClosuresOnStackByValueFromEnvOrEnsStrategy =
 struct
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  and stack_term = config
  and env_term = config
  and ens_term = config

  let to_env config = config
  let to_ens config = config
  let from_stack config = config
  let from_stack_list_for_unwind ~unwind l = List.map unwind l
  let from_env v = v
  let from_ens v = v
  let from_env_for_unwind ~unwind config = unwind config
  let from_ens_for_unwind ~unwind config = unwind config
  let stack_to_env ~reduce ~unwind config = reduce config
  let compute_to_env ~reduce ~unwind k e ens t = (k,e,ens,t,[])
  let compute_to_stack ~reduce ~unwind config = config
 end
;;

module ClosuresOnStackByValueFromEnvOrEnsByNameOnConstantsStrategy =
 struct
  type stack_term =
   int * Cic.term list * Cic.term Cic.explicit_named_substitution * Cic.term
  type env_term = Cic.term
  type ens_term = Cic.term
  type config = int * env_term list * ens_term Cic.explicit_named_substitution * Cic.term * stack_term list
  let to_env v = v
  let to_ens v = v
  let from_stack ~unwind (k,e,ens,t) = unwind k e ens t
  let from_stack_list ~unwind l = List.map (from_stack ~unwind) l
  let from_env v = v
  let from_ens v = v
  let from_env_for_unwind ~unwind v = v
  let from_ens_for_unwind ~unwind v = v
  let stack_to_env ~reduce ~unwind (k,e,ens,t) =
   match t with
      Cic.Const _ as t -> unwind k e ens t    
    | t -> reduce (k,e,ens,t,[])
  let compute_to_env ~reduce ~unwind k e ens t =
   unwind k e ens t
  let compute_to_stack ~reduce ~unwind k e ens t = (k,e,ens,t)
 end
;;

module Reduction(RS : Strategy) =
 struct
  type env = RS.env_term list
  type ens = RS.ens_term Cic.explicit_named_substitution
  type stack = RS.stack_term list
  type config = int * env * ens * Cic.term * stack

  (* k is the length of the environment e *)
  (* m is the current depth inside the term *)
  let rec unwind' m k e ens t = 
   let module C = Cic in
   let module S = CicSubstitution in
    if k = 0 && ens = [] then
     t
    else 
     let rec unwind_aux m =
      function
         C.Rel n as t ->
          if n <= m then t else
           let d =
            try
             Some (RS.from_env_for_unwind ~unwind (List.nth e (n-m-1)))
            with Failure _ -> None
           in
            (match d with 
                Some t' ->
                 if m = 0 then t' else S.lift m t'
              | None -> C.Rel (n-k)
            )
       | C.Var (uri,exp_named_subst) ->
(*
debug_print (lazy ("%%%%%UWVAR " ^ String.concat " ; " (List.map (function (uri,t) -> UriManager.string_of_uri uri ^ " := " ^ CicPp.ppterm t) ens))) ;
*)
         if List.exists (function (uri',_) -> UriManager.eq uri' uri) ens then
          CicSubstitution.lift m (RS.from_ens_for_unwind ~unwind (List.assq uri ens))
         else
          let params =
            let o,_ = 
              CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
            in
           (match o with
               C.Constant _ -> raise ReferenceToConstant
             | C.Variable (_,_,_,params,_) -> params
             | C.CurrentProof _ -> raise ReferenceToCurrentProof
             | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
           )
          in
           let exp_named_subst' =
            substaux_in_exp_named_subst params exp_named_subst m 
           in
            C.Var (uri,exp_named_subst')
       | C.Meta (i,l) ->
          let l' =
           List.map
            (function
                None -> None
              | Some t -> Some (unwind_aux m t)
            ) l
          in
           C.Meta (i, l')
       | C.Sort _ as t -> t
       | C.Implicit _ as t -> t
       | C.Cast (te,ty) -> C.Cast (unwind_aux m te, unwind_aux m ty) (*CSC ???*)
       | C.Prod (n,s,t) -> C.Prod (n, unwind_aux m s, unwind_aux (m + 1) t)
       | C.Lambda (n,s,t) -> C.Lambda (n, unwind_aux m s, unwind_aux (m + 1) t)
       | C.LetIn (n,s,ty,t) ->
          C.LetIn (n, unwind_aux m s, unwind_aux m ty, unwind_aux (m + 1) t)
       | C.Appl l -> C.Appl (List.map (unwind_aux m) l)
       | C.Const (uri,exp_named_subst) ->
          let params =
            let o,_ = 
              CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
            in
           (match o with
               C.Constant (_,_,_,params,_) -> params
             | C.Variable _ -> raise ReferenceToVariable
             | C.CurrentProof (_,_,_,_,params,_) -> params
             | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
           )
          in
           let exp_named_subst' =
            substaux_in_exp_named_subst params exp_named_subst m 
           in
            C.Const (uri,exp_named_subst')
       | C.MutInd (uri,i,exp_named_subst) ->
          let params =
            let o,_ = 
              CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
            in
           (match o with
               C.Constant _ -> raise ReferenceToConstant
             | C.Variable _ -> raise ReferenceToVariable
             | C.CurrentProof _ -> raise ReferenceToCurrentProof
             | C.InductiveDefinition (_,params,_,_) -> params
           )
          in
           let exp_named_subst' =
            substaux_in_exp_named_subst params exp_named_subst m 
           in
            C.MutInd (uri,i,exp_named_subst')
       | C.MutConstruct (uri,i,j,exp_named_subst) ->
          let params =
            let o,_ = 
              CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
            in
           (match o with
               C.Constant _ -> raise ReferenceToConstant
             | C.Variable _ -> raise ReferenceToVariable
             | C.CurrentProof _ -> raise ReferenceToCurrentProof
             | C.InductiveDefinition (_,params,_,_) -> params
           )
          in
           let exp_named_subst' =
            substaux_in_exp_named_subst params exp_named_subst m 
           in
            C.MutConstruct (uri,i,j,exp_named_subst')
       | C.MutCase (sp,i,outt,t,pl) ->
          C.MutCase (sp,i,unwind_aux m outt, unwind_aux m t,
           List.map (unwind_aux m) pl)
       | C.Fix (i,fl) ->
          let len = List.length fl in
          let substitutedfl =
           List.map
            (fun (name,i,ty,bo) ->
              (name, i, unwind_aux m ty, unwind_aux (m+len) bo))
             fl
          in
           C.Fix (i, substitutedfl)
       | C.CoFix (i,fl) ->
          let len = List.length fl in
          let substitutedfl =
           List.map
            (fun (name,ty,bo) -> (name, unwind_aux m ty, unwind_aux (m+len) bo))
             fl
          in
           C.CoFix (i, substitutedfl)
     and substaux_in_exp_named_subst params exp_named_subst' m  =
     (*CSC: codice copiato e modificato dalla cicSubstitution.subst_vars *)
      let rec filter_and_lift already_instantiated =
       function
          [] -> []
        | (uri,t)::tl when
            List.for_all
             (function (uri',_)-> not (UriManager.eq uri uri')) exp_named_subst'
            &&
             not (List.mem uri already_instantiated)
            &&
             List.mem uri params
           ->
            (uri,CicSubstitution.lift m (RS.from_ens_for_unwind ~unwind t)) ::
             (filter_and_lift (uri::already_instantiated) tl)
        | _::tl -> filter_and_lift already_instantiated tl
      in
       let res =
        List.map (function (uri,t) -> uri, unwind_aux m t) exp_named_subst' @
         (filter_and_lift [] (List.rev ens))
       in
        let rec reorder =
         function
            [] -> []
          | uri::tl ->
             let he =
              try
               [uri,List.assoc uri res]
              with
               Not_found -> []
             in
              he@reorder tl
        in
         reorder params
     in
      unwind_aux m t          
  
  and unwind (k,e,ens,t,s) =
   let t' = unwind' 0 k e ens t in
    if s = [] then t' else Cic.Appl (t'::(RS.from_stack_list_for_unwind ~unwind s))
  ;;

(*
  let unwind =
   let profiler_unwind = HExtlib.profile ~enable:profile "are_convertible.unwind" in
    fun k e ens t ->
     profiler_unwind.HExtlib.profile (unwind k e ens) t
  ;;
*)
  
  let reduce ~delta ?(subst = []) context : config -> config = 
   let module C = Cic in
   let module S = CicSubstitution in 
   let rec reduce =
    function
       (k, e, _, C.Rel n, s) as config ->
        let config' =
         if not delta then None
         else
          try
           Some (RS.from_env (List.nth e (n-1)))
          with
           Failure _ ->
            try
             begin
              match List.nth context (n - 1 - k) with
                 None -> assert false
               | Some (_,C.Decl _) -> None
               | Some (_,C.Def (x,_)) -> Some (0,[],[],S.lift (n - k) x,[])
             end
            with
             Failure _ -> None
        in
         (match config' with 
             Some (k',e',ens',t',s') -> reduce (k',e',ens',t',s'@s)
           | None -> config)
     | (k, e, ens, C.Var (uri,exp_named_subst), s) as config -> 
         if List.exists (function (uri',_) -> UriManager.eq uri' uri) ens then
          let (k',e',ens',t',s') = RS.from_ens (List.assq uri ens) in
           reduce (k',e',ens',t',s'@s)
         else
          ( let o,_ = 
              CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
            in
            match o with
              C.Constant _ -> raise ReferenceToConstant
            | C.CurrentProof _ -> raise ReferenceToCurrentProof
            | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
            | C.Variable (_,None,_,_,_) -> config
            | C.Variable (_,Some body,_,_,_) ->
               let ens' = push_exp_named_subst k e ens exp_named_subst in
                reduce (0, [], ens', body, s)
          )
     | (k, e, ens, C.Meta (n,l), s) as config ->
        (try 
           let (_, term,_) = CicUtil.lookup_subst n subst in
           reduce (k, e, ens,CicSubstitution.subst_meta l term,s)
         with  CicUtil.Subst_not_found _ -> config)
     | (_, _, _, C.Sort _, _)
     | (_, _, _, C.Implicit _, _) as config -> config
     | (k, e, ens, C.Cast (te,ty), s) ->
        reduce (k, e, ens, te, s)
     | (_, _, _, C.Prod _, _) as config -> config
     | (_, _, _, C.Lambda _, []) as config -> config
     | (k, e, ens, C.Lambda (_,_,t), p::s) ->
         reduce (k+1, (RS.stack_to_env ~reduce ~unwind p)::e, ens, t,s)
     | (k, e, ens, C.LetIn (_,m,_,t), s) ->
        let m' = RS.compute_to_env ~reduce ~unwind k e ens m in
         reduce (k+1, m'::e, ens, t, s)
     | (_, _, _, C.Appl [], _) -> assert false
     | (k, e, ens, C.Appl (he::tl), s) ->
        let tl' =
         List.map
          (function t -> RS.compute_to_stack ~reduce ~unwind (k,e,ens,t,[])) tl
        in
         reduce (k, e, ens, he, (List.append tl') s)
     | (_, _, _, C.Const _, _) as config when delta=false-> config
     | (k, e, ens, C.Const (uri,exp_named_subst), s) as config ->
        (let o,_ = 
           CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri
         in
          match o with
            C.Constant (_,Some body,_,_,_) ->
             let ens' = push_exp_named_subst k e ens exp_named_subst in
              (* constants are closed *)
              reduce (0, [], ens', body, s) 
          | C.Constant (_,None,_,_,_) -> config
          | C.Variable _ -> raise ReferenceToVariable
          | C.CurrentProof (_,_,body,_,_,_) ->
             let ens' = push_exp_named_subst k e ens exp_named_subst in
              (* constants are closed *)
              reduce (0, [], ens', body, s)
          | C.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
        )
     | (_, _, _, C.MutInd _, _)
     | (_, _, _, C.MutConstruct _, _) as config -> config 
     | (k, e, ens, C.MutCase (mutind,i,outty,term,pl),s) as config ->
        let decofix =
         function
            (k, e, ens, C.CoFix (i,fl), s) ->
             let (_,_,body) = List.nth fl i in
              let body' =
               let counter = ref (List.length fl) in
                List.fold_right
                 (fun _ -> decr counter ; S.subst (C.CoFix (!counter,fl)))
                 fl
                 body
              in
               reduce (k,e,ens,body',s)
          | config -> config
        in
         (match decofix (reduce (k,e,ens,term,[])) with
             (k', e', ens', C.MutConstruct (_,_,j,_), []) ->
              reduce (k, e, ens, (List.nth pl (j-1)), s)
           | (k', e', ens', C.MutConstruct (_,_,j,_), s') ->
              let r =
                let o,_ = 
                  CicEnvironment.get_cooked_obj CicUniv.empty_ugraph mutind 
                in
                  match o with
                      C.InductiveDefinition (_,_,r,_) -> r
                    | _ -> raise WrongUriToInductiveDefinition
              in
               let ts =
                let num_to_eat = r in
                 let rec eat_first =
                  function
                     (0,l) -> l
                   | (n,he::s) when n > 0 -> eat_first (n - 1, s)
                   | _ -> raise (Impossible 5)
                 in
                  eat_first (num_to_eat,s')
               in
                reduce (k, e, ens, (List.nth pl (j-1)), ts@s)
           | (_, _, _, C.Cast _, _)
           | (_, _, _, C.Implicit _, _) ->
              raise (Impossible 2) (* we don't trust our whd ;-) *)
           | config' ->
              (*CSC: here I am unwinding the configuration and for sure I
                will do it twice; to avoid this unwinding I should push the
                "match [] with _" continuation on the stack;
                another possibility is to just return the original configuration,
                partially undoing the weak-head computation *)
              (*this code is uncorrect since term' lives in e' <> e
              let term' = unwind config' in
               (k, e, ens, C.MutCase (mutind,i,outty,term',pl),s)
              *)
              config)
     | (k, e, ens, C.Fix (i,fl), s) as config ->
        let (_,recindex,_,body) = List.nth fl i in
         let recparam =
          try
           Some (RS.from_stack (List.nth s recindex))
          with
           Failure _ -> None
         in
          (match recparam with
              Some recparam ->
               (match reduce recparam with
                   (_,_,_,C.MutConstruct _,_) as config ->
                    let leng = List.length fl in
                    let new_env =
                     let counter = ref 0 in
                     let rec build_env e' =
                      if !counter = leng then e'
                      else
                       (incr counter ;
                        build_env
                         ((RS.to_env ~reduce ~unwind (k,e,ens,C.Fix (!counter -1, fl),[]))::e'))
                     in
                      build_env e
                    in
                    let rec replace i s t =
                     match i,s with
                        0,_::tl -> t::tl
                      | n,he::tl -> he::(replace (n - 1) tl t)
                      | _,_ -> assert false in
                    let new_s =
                     replace recindex s (RS.compute_to_stack ~reduce ~unwind config)
                    in
                     reduce (k+leng, new_env, ens, body, new_s)
                 | _ -> config)
            | None -> config
          )
     | (_,_,_,C.CoFix _,_) as config -> config
   and push_exp_named_subst k e ens =
    function
       [] -> ens
     | (uri,t)::tl ->
         push_exp_named_subst k e ((uri,RS.to_ens ~reduce ~unwind (k,e,ens,t,[]))::ens) tl
   in
    reduce
  ;;

  let whd ?(delta=true) ?(subst=[]) context t = 
   unwind (reduce ~delta ~subst context (0, [], [], t, []))
  ;;

 end
;;


(* ROTTO = rompe l'unificazione poiche' riduce gli argomenti di un'applicazione
           senza ridurre la testa
module R = Reduction CallByNameStrategy;; OK 56.368s
module R = Reduction CallByValueStrategy;; ROTTO
module R = Reduction CallByValueStrategyByNameOnConstants;; ROTTO
module R = Reduction LazyCallByValueStrategy;; ROTTO
module R = Reduction LazyCallByValueStrategyByNameOnConstants;; ROTTO
module R = Reduction LazyCallByNameStrategy;; OK 0m56.398s
module R = Reduction
 LazyCallByValueByNameOnConstantsWhenFromStack_ByNameStrategyWhenFromEnvOrEns;;
 OK 59.058s
module R = Reduction ClosuresOnStackByValueFromEnvOrEnsStrategy;; OK 58.583s
module R = Reduction
 ClosuresOnStackByValueFromEnvOrEnsByNameOnConstantsStrategy;; OK 58.094s
module R = Reduction(ClosuresOnStackByValueFromEnvOrEnsStrategy);; OK 58.127s
*)
(*module R = Reduction(CallByValueByNameForUnwind);;*)
module RS = CallByValueByNameForUnwind';;
(*module R = Reduction(CallByNameStrategy);;*)
(*module R = Reduction(ClosuresOnStackByValueFromEnvOrEnsStrategy);;*)
module R = Reduction(RS);;
module U = UriManager;;

let whd = R.whd

(*
let whd =
 let profiler_whd = HExtlib.profile ~enable:profile "are_convertible.whd" in
  fun ?(delta=true) ?(subst=[]) context t ->
   profiler_whd.HExtlib.profile (whd ~delta ~subst context) t
*)

  (* mimic ocaml (<< 3.08) "=" behaviour. Tests physical equality first then
    * fallbacks to structural equality *)
let (===) x y =
  Pervasives.compare x y = 0

(* t1, t2 must be well-typed *)
let are_convertible whd ?(subst=[]) ?(metasenv=[])  =
 let heuristic = ref true in
 let rec aux test_equality_only context t1 t2 ugraph =
 (*D*)inside 'B'; try let rc = 
  pp (lazy (CicPp.ppterm t1 ^ " vs " ^ CicPp.ppterm t2));
  let rec aux2 test_equality_only t1 t2 ugraph =

   (* this trivial euristic cuts down the total time of about five times ;-) *)
   (* this because most of the time t1 and t2 are "sintactically" the same   *)
   if t1 === t2 then
     true,ugraph
   else
    begin
     let module C = Cic in
       match (t1,t2) with
          (C.Rel n1, C.Rel n2) -> (n1 = n2),ugraph
        | (C.Var (uri1,exp_named_subst1), C.Var (uri2,exp_named_subst2)) ->
            if U.eq uri1 uri2 then
             (try
               List.fold_right2
                (fun (uri1,x) (uri2,y) (b,ugraph) ->
                  let b',ugraph' = aux test_equality_only context x y ugraph in
                  (U.eq uri1 uri2 && b' && b),ugraph'
                ) exp_named_subst1 exp_named_subst2 (true,ugraph) 
              with
               Invalid_argument _ -> false,ugraph
             )
            else
              false,ugraph
        | (C.Meta (n1,l1), C.Meta (n2,l2)) ->
            if n1 = n2 then
              let b2, ugraph1 = 
                let l1 = CicUtil.clean_up_local_context subst metasenv n1 l1 in
                let l2 = CicUtil.clean_up_local_context subst metasenv n2 l2 in
                  List.fold_left2
                    (fun (b,ugraph) t1 t2 ->
                       if b then 
                         match t1,t2 with
                             None,_
                           | _,None  -> true,ugraph
                           | Some t1',Some t2' -> 
                               aux test_equality_only context t1' t2' ugraph
                       else
                         false,ugraph
                    ) (true,ugraph) l1 l2
              in
                if b2 then true,ugraph1 else false,ugraph 
            else
              false,ugraph
        | C.Meta (n1,l1), _ ->
           (try 
              let _,term,_ = CicUtil.lookup_subst n1 subst in
              let term' = CicSubstitution.subst_meta l1 term in
(*
prerr_endline ("%?: " ^ CicPp.ppterm t1 ^ " <==> " ^ CicPp.ppterm t2);
prerr_endline ("%%%%%%: " ^ CicPp.ppterm term' ^ " <==> " ^ CicPp.ppterm t2);
*)
               aux test_equality_only context term' t2 ugraph
            with  CicUtil.Subst_not_found _ -> false,ugraph)
        | _, C.Meta (n2,l2) ->
           (try 
              let _,term,_ = CicUtil.lookup_subst n2 subst in
              let term' = CicSubstitution.subst_meta l2 term in
(*
prerr_endline ("%?: " ^ CicPp.ppterm t1 ^ " <==> " ^ CicPp.ppterm t2);
prerr_endline ("%%%%%%: " ^ CicPp.ppterm term' ^ " <==> " ^ CicPp.ppterm t1);
*)
               aux test_equality_only context t1 term' ugraph
            with  CicUtil.Subst_not_found _ -> false,ugraph)
        | (C.Sort (C.CProp t1|C.Type t1), C.Sort (C.CProp t2|C.Type t2)) 
          when test_equality_only ->
            (try true,(CicUniv.add_eq t2 t1 ugraph)
            with CicUniv.UniverseInconsistency _ -> false,ugraph)
        | (C.Sort (C.CProp t1|C.Type t1), C.Sort (C.CProp t2|C.Type t2))
          when not test_equality_only ->
            (try true,(CicUniv.add_ge t2 t1 ugraph)
            with CicUniv.UniverseInconsistency _ -> false,ugraph)
        | (C.Sort s1, C.Sort (C.Type _))
        | (C.Sort s1, C.Sort (C.CProp _)) -> (not test_equality_only),ugraph
        | (C.Sort s1, C.Sort s2) -> (s1 = s2),ugraph
        | (C.Prod (name1,s1,t1), C.Prod(_,s2,t2)) ->
            let b',ugraph' = aux true context s1 s2 ugraph in
            if b' then 
              aux test_equality_only ((Some (name1, (C.Decl s1)))::context) 
                t1 t2 ugraph'
            else
              false,ugraph
        | (C.Lambda (name1,s1,t1), C.Lambda(_,s2,t2)) ->
           let b',ugraph' = aux true context s1 s2 ugraph in
           if b' then
             aux test_equality_only ((Some (name1, (C.Decl s1)))::context) 
               t1 t2 ugraph'
           else
             false,ugraph
        | (C.LetIn (name1,s1,ty1,t1), C.LetIn(_,s2,ty2,t2)) ->
           let b',ugraph' = aux test_equality_only context s1 s2 ugraph in
           if b' then
            let b',ugraph = aux test_equality_only context ty1 ty2 ugraph in
            if b' then
             aux test_equality_only
              ((Some (name1, (C.Def (s1,ty1))))::context) t1 t2 ugraph'
            else
              false,ugraph
           else
             false,ugraph
        | (C.Appl l1, C.Appl l2) ->
           let b, ugraph = 
             aux test_equality_only context (List.hd l1) (List.hd l2) ugraph
           in
           if not b then false, ugraph
           else
           (try
             List.fold_right2
               (fun  x y (b,ugraph) -> 
                 if b then
                   aux true context x y ugraph
                 else
                   false,ugraph) (List.tl l1) (List.tl l2) (true,ugraph)
            with
             Invalid_argument _ -> false,ugraph
           )
        | (C.Const (uri1,exp_named_subst1), C.Const (uri2,exp_named_subst2)) ->
            let b' = U.eq uri1 uri2 in
            if b' then
             (try
               List.fold_right2
                (fun (uri1,x) (uri2,y) (b,ugraph) ->
                  if b && U.eq uri1 uri2 then
                    aux test_equality_only context x y ugraph 
                  else
                    false,ugraph
                ) exp_named_subst1 exp_named_subst2 (true,ugraph)
              with
               Invalid_argument _ -> false,ugraph
             )
            else
              false,ugraph
        | (C.MutInd (uri1,i1,exp_named_subst1),
           C.MutInd (uri2,i2,exp_named_subst2)
          ) ->
            let b' = U.eq uri1 uri2 && i1 = i2 in
            if b' then
             (try
               List.fold_right2
                (fun (uri1,x) (uri2,y) (b,ugraph) ->
                  if b && U.eq uri1 uri2 then
                    aux test_equality_only context x y ugraph
                  else
                   false,ugraph
                ) exp_named_subst1 exp_named_subst2 (true,ugraph)
              with
               Invalid_argument _ -> false,ugraph
             )
            else 
              false,ugraph
        | (C.MutConstruct (uri1,i1,j1,exp_named_subst1),
           C.MutConstruct (uri2,i2,j2,exp_named_subst2)
          ) ->
            let b' = U.eq uri1 uri2 && i1 = i2 && j1 = j2 in
            if b' then
             (try
               List.fold_right2
                (fun (uri1,x) (uri2,y) (b,ugraph) ->
                  if b && U.eq uri1 uri2 then
                    aux test_equality_only context x y ugraph
                  else
                    false,ugraph
                ) exp_named_subst1 exp_named_subst2 (true,ugraph)
              with
               Invalid_argument _ -> false,ugraph
             )
            else
              false,ugraph
        | (C.MutCase (uri1,i1,outtype1,term1,pl1),
           C.MutCase (uri2,i2,outtype2,term2,pl2)) -> 
            let b' = U.eq uri1 uri2 && i1 = i2 in
            if b' then
             let b'',ugraph''=aux test_equality_only context 
                 outtype1 outtype2 ugraph in
             if b'' then 
               let b''',ugraph'''= aux true context 
                   term1 term2 ugraph'' in
               List.fold_right2
                 (fun x y (b,ugraph) -> 
                   if b then
                     aux test_equality_only context x y ugraph 
                   else 
                     false,ugraph)
                 pl1 pl2 (b''',ugraph''')
             else
               false,ugraph
            else
              false,ugraph
        | (C.Fix (i1,fl1), C.Fix (i2,fl2)) ->
            let tys,_ =
              List.fold_left
                (fun (types,len) (n,_,ty,_) ->
                   (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                    len+1)
	        ) ([],0) fl1
            in
            if i1 = i2 then
             List.fold_right2
              (fun (_,recindex1,ty1,bo1) (_,recindex2,ty2,bo2) (b,ugraph) ->
                if b && recindex1 = recindex2 then
                  let b',ugraph' = aux test_equality_only context ty1 ty2 
                      ugraph in
                  if b' then
                    aux test_equality_only (tys@context) bo1 bo2 ugraph'
                  else
                    false,ugraph
                else
                  false,ugraph)
             fl1 fl2 (true,ugraph)
            else
              false,ugraph
        | (C.CoFix (i1,fl1), C.CoFix (i2,fl2)) ->
            let tys,_ =
              List.fold_left
                (fun (types,len) (n,ty,_) ->
                   (Some (C.Name n,(C.Decl (CicSubstitution.lift len ty)))::types,
                    len+1)
	        ) ([],0) fl1
            in
            if i1 = i2 then
              List.fold_right2
              (fun (_,ty1,bo1) (_,ty2,bo2) (b,ugraph) ->
                if b then
                  let b',ugraph' = aux test_equality_only context ty1 ty2 
                      ugraph in
                  if b' then
                    aux test_equality_only (tys@context) bo1 bo2 ugraph'
                  else
                    false,ugraph
                else
                  false,ugraph)
             fl1 fl2 (true,ugraph)
            else
              false,ugraph
        | C.Cast (bo,_),t -> aux2 test_equality_only bo t ugraph
        | t,C.Cast (bo,_) -> aux2 test_equality_only t bo ugraph
        | (C.Implicit _, _) | (_, C.Implicit _) -> assert false
        | (_,_) -> false,ugraph
    end
  in
   let res =
    if !heuristic then
     aux2 test_equality_only t1 t2 ugraph
    else
     false,ugraph
   in
    if fst res = true then
     res
    else
begin
(*if !heuristic then prerr_endline ("NON FACILE: " ^ CicPp.ppterm t1 ^ " <===> " ^ CicPp.ppterm t2);*)
   (* heuristic := false; *)
   debug t1 [t2] "PREWHD";
(*prerr_endline ("PREWHD: " ^ CicPp.ppterm t1 ^ " <===> " ^ CicPp.ppterm t2);*)
(*
prerr_endline ("PREWHD: " ^ CicPp.ppterm t1 ^ " <===> " ^ CicPp.ppterm t2);
   let t1' = whd ?delta:(Some true) ?subst:(Some subst) context t1 in
   let t2' = whd ?delta:(Some true) ?subst:(Some subst) context t2 in
    debug t1' [t2'] "POSTWHD";
*)
let rec convert_machines test_equality_only ugraph =
 function
    [] -> true,ugraph
  | ((k1,env1,ens1,h1,s1),(k2,env2,ens2,h2,s2))::tl ->
     let (b,ugraph) as res =
      aux2 test_equality_only
       (R.unwind (k1,env1,ens1,h1,[])) (R.unwind (k2,env2,ens2,h2,[])) ugraph
     in
      if b then
       let problems =
        try
         Some
          (List.combine
            (List.map
              (fun si-> R.reduce ~delta:false ~subst context(RS.from_stack si))
              s1)
            (List.map
              (fun si-> R.reduce ~delta:false ~subst context(RS.from_stack si))
              s2)
          @ tl)
        with
         Invalid_argument _ -> None
       in
        match problems with
           None -> false,ugraph
         | Some problems -> convert_machines true ugraph problems
      else
       res
in
 convert_machines test_equality_only ugraph
  [R.reduce ~delta:true ~subst context (0,[],[],t1,[]),
   R.reduce ~delta:true ~subst context (0,[],[],t2,[])]
(*prerr_endline ("POSTWH: " ^ CicPp.ppterm t1' ^ " <===> " ^ CicPp.ppterm t2');*)
(*
    aux2 test_equality_only t1' t2' ugraph
*)
end
 (*D*)in outside true; rc with exc -> outside false; raise exc
 in
  aux false (*c t1 t2 ugraph *)
;;

(* DEBUGGING ONLY
let whd ?(delta=true) ?(subst=[]) context t = 
 let res = whd ~delta ~subst context t in
 let rescsc = CicReductionNaif.whd ~delta ~subst context t in
  if not (fst (are_convertible CicReductionNaif.whd ~subst context res rescsc CicUniv.empty_ugraph)) then
   begin
    debug_print (lazy ("PRIMA: " ^ CicPp.ppterm t)) ;
    flush stderr ;
    debug_print (lazy ("DOPO: " ^ CicPp.ppterm res)) ;
    flush stderr ;
    debug_print (lazy ("CSC: " ^ CicPp.ppterm rescsc)) ;
    flush stderr ;
fdebug := 0 ;
let _ =  are_convertible CicReductionNaif.whd ~subst context res rescsc CicUniv.empty_ugraph in
    assert false ;
   end
  else 
   res
;;
*)

let are_convertible = are_convertible whd

let whd = R.whd

(*
let profiler_other_whd = HExtlib.profile ~enable:profile "~are_convertible.whd"
let whd ?(delta=true) ?(subst=[]) context t = 
 let foo () =
  whd ~delta ~subst context t
 in
  profiler_other_whd.HExtlib.profile foo ()
*)

let rec normalize ?(delta=true) ?(subst=[]) ctx term =
  let module C = Cic in
  let t = whd ~delta ~subst ctx term in
  let aux = normalize ~delta ~subst in
  let decl name t = Some (name, C.Decl t) in
  match t with
  | C.Rel n -> t
  | C.Var (uri,exp_named_subst) ->
      C.Var (uri, List.map (fun (n,t) -> n,aux ctx t) exp_named_subst)
  | C.Meta (i,l) -> 
      C.Meta (i,List.map (function Some t -> Some (aux ctx t) | None -> None) l)
  | C.Sort _ -> t
  | C.Implicit _ -> t
  | C.Cast (te,ty) -> C.Cast (aux ctx te, aux ctx ty)
  | C.Prod (n,s,t) -> 
      let s' = aux ctx s in
      C.Prod (n, s', aux ((decl n s')::ctx) t)
  | C.Lambda (n,s,t) -> 
      let s' = aux ctx s in
      C.Lambda (n, s', aux ((decl n s')::ctx) t)
  | C.LetIn (n,s,_,t) ->
      (* the term is already in weak head normal form *)
      assert false
  | C.Appl (h::l) -> C.Appl (h::(List.map (aux ctx) l))
  | C.Appl [] -> assert false
  | C.Const (uri,exp_named_subst) ->
      C.Const (uri, List.map (fun (n,t) -> n,aux ctx t) exp_named_subst)
  | C.MutInd (uri,typeno,exp_named_subst) ->
      C.MutInd (uri,typeno, List.map (fun (n,t) -> n,aux ctx t) exp_named_subst)
  | C.MutConstruct (uri,typeno,consno,exp_named_subst) ->
      C.MutConstruct (uri, typeno, consno, 
        List.map (fun (n,t) -> n,aux ctx t) exp_named_subst)
  | C.MutCase (sp,i,outt,t,pl) ->
      C.MutCase (sp,i, aux ctx outt, aux ctx t, List.map (aux ctx) pl)
(*CSC: to be completed, I suppose *)
  | C.Fix _ -> t 
  | C.CoFix _ -> t

let normalize ?delta ?subst ctx term =  
(*  prerr_endline ("NORMALIZE:" ^ CicPp.ppterm term); *)
  let t = normalize ?delta ?subst ctx term in
(*  prerr_endline ("NORMALIZED:" ^ CicPp.ppterm t); *)
  t
  
  
(* performs an head beta/cast reduction *)
let rec head_beta_reduce ?(delta=false) ?(upto=(-1)) t =
 match upto with
    0 -> t
  | n ->
    match t with
       (Cic.Appl (Cic.Lambda (_,_,t)::he'::tl')) ->
         let he'' = CicSubstitution.subst he' t in
          if tl' = [] then
           he''
          else
           let he''' =
            match he'' with
               Cic.Appl l -> Cic.Appl (l@tl')
             | _ -> Cic.Appl (he''::tl')
           in
            head_beta_reduce ~delta ~upto:(upto - 1) he'''
     | Cic.Cast (te,_) -> head_beta_reduce ~delta ~upto te
     | Cic.Appl (Cic.Const (uri,ens)::tl) as t when delta=true ->
        let bo =
         match fst (CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri) with
            Cic.Constant (_,bo,_,_,_) -> bo
          | Cic.Variable _ -> raise ReferenceToVariable
          | Cic.CurrentProof (_,_,bo,_,_,_) -> Some bo
          | Cic.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
        in
         (match bo with
             None -> t
           | Some bo ->
              head_beta_reduce ~upto
               ~delta (Cic.Appl ((CicSubstitution.subst_vars ens bo)::tl)))
     | Cic.Const (uri,ens) as t when delta=true ->
        let bo =
         match fst (CicEnvironment.get_cooked_obj CicUniv.empty_ugraph uri) with
            Cic.Constant (_,bo,_,_,_) -> bo
          | Cic.Variable _ -> raise ReferenceToVariable
          | Cic.CurrentProof (_,_,bo,_,_,_) -> Some bo
          | Cic.InductiveDefinition _ -> raise ReferenceToInductiveDefinition
        in
         (match bo with
             None -> t
           | Some bo ->
              head_beta_reduce ~delta ~upto (CicSubstitution.subst_vars ens bo))
     | t -> t

(*
let are_convertible ?subst ?metasenv context t1 t2 ugraph =
 let before = Unix.gettimeofday () in
 let res = are_convertible ?subst ?metasenv context t1 t2 ugraph in
 let after = Unix.gettimeofday () in
 let diff = after -. before in
  if diff > 0.1 then
   begin
    let nc = List.map (function None -> None | Some (n,_) -> Some n) context in
     prerr_endline
      ("\n#(" ^ string_of_float diff ^ "):\n" ^ CicPp.pp t1 nc ^ "\n<=>\n" ^ CicPp.pp t2 nc);
   end;
  res
*)
