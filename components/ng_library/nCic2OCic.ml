(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id$ *)

let ouri_of_nuri u = UriManager.uri_of_string (NUri.string_of_uri u);;

let ouri_of_reference (NReference.Ref (u,_)) = ouri_of_nuri u;;

let cprop = [`CProp, NUri.uri_of_string ("cic:/matita/pts/Type.univ")];;

let nn_2_on = function
  | "_" -> Cic.Anonymous
  | s -> Cic.Name s
;;

let convert_term uri n_fl t =
 let rec convert_term k = function (* pass k along *)
 | NCic.Rel i -> Cic.Rel i
 | NCic.Meta _ -> assert false
 | NCic.Appl l -> Cic.Appl (List.map (convert_term k) l)
 | NCic.Prod (n,s,t) -> 
     Cic.Prod (nn_2_on n,convert_term k s, convert_term (k+1) t)
 | NCic.Lambda  (n,s,t) -> 
     Cic.Lambda(nn_2_on n,convert_term k s, convert_term (k+1) t)
 | NCic.LetIn (n,ty_s,s,t) -> 
     Cic.LetIn (nn_2_on n,convert_term k s,convert_term k ty_s, convert_term (k+1) t)
 | NCic.Sort NCic.Prop -> Cic.Sort Cic.Prop 
 | NCic.Sort (NCic.Type u) when
    (* BUG HERE: I should use NCicEnvironment.universe_eq, but I do not
       want to add this recursion between the modules *)
    (*NCicEnvironment.universe_eq*) u=cprop -> Cic.Sort (Cic.CProp (CicUniv.fresh ()))
 | NCic.Sort (NCic.Type _) -> Cic.Sort (Cic.Type (CicUniv.fresh ()))
 | NCic.Implicit _ -> assert false
 | NCic.Const (NReference.Ref (u,NReference.Ind (_,i,_))) -> 
     Cic.MutInd (ouri_of_nuri u,i,[])
 | NCic.Const (NReference.Ref (u,NReference.Con (i,j,_))) -> 
     Cic.MutConstruct (ouri_of_nuri u,i,j,[])
 | NCic.Const (NReference.Ref (u,NReference.Def _))
 | NCic.Const (NReference.Ref (u,NReference.Decl)) ->
     Cic.Const (ouri_of_nuri u,[])
 | NCic.Match (NReference.Ref (u,NReference.Ind (_,i,_)),oty,t,pl) ->
     Cic.MutCase (ouri_of_nuri u,i, convert_term k oty, convert_term k t,
       List.map (convert_term k) pl)
 | NCic.Const (NReference.Ref (u,NReference.Fix (i,_,_))) 
 | NCic.Const (NReference.Ref (u,NReference.CoFix i)) ->
    if NUri.eq u uri then             
      Cic.Rel (n_fl - i + k)
    else
     let ouri = ouri_of_nuri u in
     let ouri =
      UriManager.uri_of_string 
       (UriManager.buri_of_uri ouri ^ "/" ^
        UriManager.name_of_uri ouri ^ string_of_int i ^ ".con") in
      Cic.Const (ouri,[])
 | _ -> assert false
 in
  convert_term 0 t
;;

let convert_fix is_fix uri k fl = 
  let n_fl = List.length fl in
  if is_fix then 
    let fl = 
      List.map
      (fun (_, name,recno,ty,bo) -> 
        name, recno, convert_term uri n_fl ty, convert_term uri n_fl bo)
      fl
    in 
     Cic.Fix (k, fl) 
  else 
    let fl = 
      List.map
      (fun (_, name,_,ty,bo) -> 
        name, convert_term uri n_fl ty, convert_term uri n_fl bo)
      fl
    in 
     Cic.CoFix (k, fl) 
;;

let convert_nobj = function 
 | u,_,_,_,NCic.Constant (_, name, Some bo, ty, _) ->
     [ouri_of_nuri u,Cic.Constant 
        (name, Some (convert_term u 0 bo), convert_term u 0 ty, [],[])]
 | u,_,_,_,NCic.Constant (_, name,  None, ty, _) ->
     [ouri_of_nuri u,Cic.Constant (name, None, convert_term u 0 ty, [],[])]
 | u,_,_,_,NCic.Fixpoint (is_fix, fl, _) ->
     List.map 
      (fun nth ->
        let name =
         UriManager.name_of_uri (ouri_of_nuri u) ^ string_of_int nth in
        let buri = UriManager.buri_of_uri (ouri_of_nuri u) in
        let uri = UriManager.uri_of_string (buri ^"/"^name^".con") in
        uri,
        Cic.Constant (name, 
         Some (convert_fix is_fix u nth fl), 
          convert_term u 0 (let _,_,_,ty,_ = List.hd fl in ty), [], []))
     (let rec seq = function 0 -> [0]|n -> n::seq (n-1) in 
      seq (List.length fl-1))
 | u,_,_,_,NCic.Inductive (inductive,leftno,itl,_) ->
    let itl =
     List.map
      (function (_,name,ty,cl) ->
        let cl=List.map (function (_,name,ty) -> name,convert_term u 0 ty) cl in
         name,inductive,convert_term u 0 ty,cl
      ) itl
    in
     [ouri_of_nuri u, Cic.InductiveDefinition (itl,[],leftno,[])]
;;
