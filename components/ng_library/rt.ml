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

let _ =
  Helm_registry.load_from "conf.xml";
  CicParser.impredicative_set := false;
  let u = UriManager.uri_of_string Sys.argv.(1) in
  let o, _ = CicEnvironment.get_obj CicUniv.oblivion_ugraph u in
  prerr_endline "VECCHIO";
  prerr_endline (CicPp.ppobj o);
  let l = OCic2NCic.convert_obj u o in
  prerr_endline "OGGETTI:.........................................";
  List.iter (fun o -> prerr_endline (NCicPp.ppobj o)) l;
  prerr_endline "/OGGETTI:.........................................";
  let objs = 
    List.flatten 
    (List.map NCic2OCic.convert_nobj l) in
  List.iter 
   (fun (u,o) -> 
     prerr_endline ("round trip: " ^ UriManager.string_of_uri u);
     prerr_endline (CicPp.ppobj o);
     prerr_endline "tipo.......";
     try CicTypeChecker.typecheck_obj u o
     with
       CicTypeChecker.TypeCheckerFailure s
     | CicTypeChecker.AssertFailure s ->
       prerr_endline (Lazy.force s)
     | CicEnvironment.Object_not_found uri ->
       prerr_endline
        ("CicEnvironment: Object not found " ^ UriManager.string_of_uri uri))
   objs;
;;
