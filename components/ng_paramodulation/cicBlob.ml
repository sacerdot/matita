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

(* $Id: terms.mli 9822 2009-06-03 15:37:06Z tassi $ *)

module type CicContext = 
  sig
    val metasenv : Cic.metasenv
    val subst : Cic.substitution
    val context : Cic.context
  end

module CicBlob(C : CicContext) : Terms.Blob with type t = Cic.term = struct

  type t = Cic.term

  (* XXX this alpha-eq is a bit strange, since it does not take a 
   *     context nor a subst ... *)
  let eq x y = CicUtil.alpha_equivalence x y;;

  (* TODO: take this from tactics/paramodulation/utils.ml *)
  let compare x y = assert false;;

  let names = List.map (function Some (x,_) -> Some x | _ -> None) C.context;;
  let pp t = CicPp.pp t names;;

  type input = t

  let embed t = assert false;;

  let eqP = assert false;;

  let is_eq = assert false;;

  let saturate = assert false;;

end

