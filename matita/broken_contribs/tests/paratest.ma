(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "nat/plus.ma".

(*ntheorem boo:
   (∀x. x = x) → 0 = 0. 
##[ #H; nwhd in H ⊢ %; nauto by H.*)

ntheorem bboo:
  (∀x. x + 0 = x) ->
  (∀x, y. x + S y = S (x + y)) →
  (∀x, y. x + y = y + x) →
  3 + 2 = 5.
#H; #H1; #H2; nauto by H, H1. H2.
  
ntheorem foo:  
   ((λx.x + 0 = x) ?) → 
   ((λx,y.x + S y = S (x + y)) ? ?) →
   ((λx,y.x y = x y) ? ?) →
   ∀x. ((λz. x + x = z + z) ?). 
##[ #H; #H1; #H2; #x; nwhd in H H1 H2 ⊢ %; nauto by H, H1, H2.