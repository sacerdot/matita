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

module G = Arg

module R = Helm_registry

module L = Lib
module A = Ast
module E = Engine 

let unm_ex s =
   Scanf.sscanf s "%u %u" A.mk_exists

let unm_or s =
   Scanf.sscanf s "%u" A.mk_or 

let unm_and s =
   Scanf.sscanf s "%u" A.mk_and 

let process conf =
   let preamble = L.get_preamble conf in
   if R.has "xoa.objects" && R.has "xoa.notations" then begin
      let ooch = L.open_out preamble (R.get_string "xoa.objects") in
      let noch = L.open_out preamble (R.get_string "xoa.notations") in
      List.iter (L.out_include ooch) (R.get_list R.string "xoa.include");   
      L.out_include ooch (R.get_string "xoa.notations" ^ ".ma");      
      List.iter (E.generate ooch noch) (R.get_list unm_ex "xoa.ex");
      List.iter (E.generate ooch noch) (R.get_list unm_or "xoa.or");
      List.iter (E.generate ooch noch) (R.get_list unm_and "xoa.and");
      close_out noch; close_out ooch
   end

let _ =
   let help = "Usage: xoa [ -X | <configuration file> ]*\n" in
   let help_X  = " Clear configuration" in   
   Arg.parse [
      "-X" , G.Unit R.clear, help_X;
   ] process help
