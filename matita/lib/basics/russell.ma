(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/jmeq.ma".
include "basics/types.ma".

coercion inject nocomposites: ∀A.∀P:A → Type[0].∀a.∀p:P a.Σx:A.P x ≝ λA,P,a,p. mk_Sig … a p on a:? to Σx:?.?.
coercion eject nocomposites: ∀A.∀P:A → Type[0].∀c:Σx:A.P x.A ≝ λA,P,c. pi1 … c on _c:Σx:?.? to ?.
