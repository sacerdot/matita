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

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)
 
let rec normalize ?(delta=0) ~subst ctx t =
 let aux = normalize ~delta ~subst in
  match NCicReduction.whd ~delta ~subst ctx t with
     NCic.Meta (n,(s,lc)) ->
      let l = NCicUtils.expand_local_context lc in
      let l' = List.map (aux ctx) l in
       if l = l' then t
       else
        NCic.Meta (n,(s,NCic.Ctx l))
   | t -> NCicUtils.map (fun h ctx -> h::ctx) ctx aux t
;;
