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

(* NOTATION FOR THE LAMBDA CALCULUS *******************************************)

(* equivalences *)

notation "hvbox(a break ≅ b)" 
  non associative with precedence 45
  for @{'Eq $a $b}.

notation "hvbox(a break (≅ ^ term 90 c) b)"
  non associative with precedence 45
  for @{'Eq1 $c $a $b}.

(* lifting, substitution *)

notation "hvbox(M break [ l ])"
   non associative with precedence 90
   for @{'Subst1 $M $l}.

(* evaluation, interpretation *)

notation "hvbox(〚term 90 T〛)"
   non associative with precedence 50
   for @{'Eval $T}.

notation "hvbox(〚term 90 T〛 break _ [term 90 E])"
   non associative with precedence 50
   for @{'Eval1 $T $E}.

notation "hvbox(〚term 90 T〛 break _ [term 90 E1 break , term 90 E2])"
   non associative with precedence 50
   for @{'Eval2 $T $E1 $E2}.
