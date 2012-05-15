(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)


(* COMPARE BIT

*)

include "turing/universal/copy.ma".

(*

step :

init_current;
init_table;
match_tuple;
if is_marked(current) = false (* match *)
   then init_current; (* preconditions? *)
        adv_to_mark_r;
        adv_mark_r;
        copy;
        ...move...
        

*)