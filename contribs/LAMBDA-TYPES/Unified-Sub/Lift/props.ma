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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Unified-Sub/Lift/props".

include "Lift/fwd.ma".

alias id "nplus_conf" = "cic:/matita/RELATIONAL/NPlus/props/nplus_conf.con".

axiom pippo: \forall x,y. x < y \to y <= x \to False.

theorem lift_conf: \forall q,h,d,t,x. Lift q h d t x \to
                   \forall y. Lift q h d t y \to
                   x = y.
 intros 6. elim H; clear H q h d t x;
 [ lapply linear lift_sort_fwd to H1.
   subst. auto
 | lapply linear lift_lref_fwd to H1. 
   decompose; subst; 
   [ auto | destruct H1 | destruct H ]
 | lapply linear lift_lref_fwd to H2. 
   decompose; subst;
   [ destruct H | auto | lapply pippo to H1, H4. decompose ]
 | lapply linear lift_lref_fwd to H3. 
   decompose; subst;
   [ destruct H
   | lapply linear pippo to H5, H1. decompose 
   | lapply linear nplus_conf to H2, H4. subst. auto 
   ]

(* 
theorem lift_ct_le: \forall q,h,d,t,y. (Lift q h d t y) \to
                    \forall k,e,x. (Lift q k e t x) \to
                    \forall z. (Lift q k e y z) \to
                    e <= d \to \forall d'. (k + d == d') \to
                    (Lift q h d' x z).
 intros 6. elim H; clear H q h d t y;
 [ lapply linear lift_sort_fwd to H1.
   lapply linear lift_sort_fwd to H2.
   subst. auto
 | lapply linear lift_lref_fwd to H1. 
   lapply linear lift_lref_fwd to H2.
   decompose; subst;
   [ auto
   | auto
   |  
 *)