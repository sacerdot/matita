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


(* ALphabet of the universal machine *)

include "basics/finset.ma".

(*
include "turing/if_machine.ma".
include "turing/universal/tests.ma". *)

inductive unialpha : Type[0] ≝ 
| bit : bool → unialpha
| comma : unialpha
| bar : unialpha
| grid : unialpha.

definition unialpha_eq ≝ 
  λa1,a2.match a1 with
  [ bit x ⇒ match a2 with [ bit y ⇒ ¬ xorb x y | _ ⇒ false ]
  | comma ⇒ match a2 with [ comma ⇒ true | _ ⇒ false ]
  | bar ⇒ match a2 with [ bar ⇒ true | _ ⇒ false ]
  | grid ⇒ match a2 with [ grid ⇒ true | _ ⇒ false ] ].
  
definition DeqUnialpha ≝ mk_DeqSet unialpha unialpha_eq ?.
* [ #x * [ #y cases x cases y normalize % // #Hfalse destruct
         | *: normalize % #Hfalse destruct ]
  |*: * [1,5,9,13: #y ] normalize % #H1 destruct % ]
qed.

axiom unialpha_unique : uniqueb DeqUnialpha [bit true;bit false;comma;bar;grid] = true.

definition FSUnialpha ≝ 
  mk_FinSet DeqUnialpha [bit true;bit false;comma;bar;grid] unialpha_unique.

definition is_bit ≝ λc.match c with [ bit _ ⇒ true | _ ⇒ false ].

definition is_grid ≝ λc.match c with [ grid ⇒ true | _ ⇒ false ].

definition is_bar ≝ λc.match c with [ bar ⇒ true | _ ⇒ false ].

definition is_comma ≝ λc.match c with [ comma ⇒ true | _ ⇒ false ].

