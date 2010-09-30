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

val auto_tac:
  params:(NTacStatus.tactic_term list option * (string * string) list) -> 
  ?trace_ref:CicNotationPt.term list ref ->
   's NTacStatus.tactic

val group_by_tac:
  eq_predicate:
    ((#NTacStatus.tac_status as 'a) ->
      Continuationals.goal list -> Continuationals.goal -> bool) ->
  action:'a NTacStatus.tactic -> 
    'a NTacStatus.tactic

val debug : bool ref
