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
moves:
0_ = N
10 = L
11 = R
*)

(*

step :

if is_true(current) (* current state is final *)
   then nop
   else
   match_tuple;
   if is_marked(current) = false (* match *)
      then adv_mark_r;
           move_l;
           init_current;
           move_r;
           adv_to_mark_r;
           copy;
           ...move...
           reset;
      else sink;
        
MANCANO MOVE E RESET

*)