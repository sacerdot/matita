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

(* equivalence, invariance *)

notation "hvbox(a break ≅ b)" 
  non associative with precedence 45
  for @{'Eq $a $b}.

notation "hvbox(a break (≅ ^ term 90 c) b)"
  non associative with precedence 45
  for @{'Eq1 $c $a $b}.

notation "hbox(! term 50 a)"
  non associative with precedence 50
  for @{'Invariant $a}.

notation "hbox((! ^ term 90 b) term 50 a)"
  non associative with precedence 50
  for @{'Invariant1 $a $b}.

(* lifting, substitution *)

notation "hvbox(M break [ l ])"
   non associative with precedence 90
   for @{'Subst1 $M $l}.

(* interpretation *)

notation "hvbox(〚term 90 T〛)"
   non associative with precedence 50
   for @{'IInt $T}.

notation "hvbox(〚term 90 T〛 break _ [term 90 E])"
   non associative with precedence 50
   for @{'IInt1 $T $E}.

notation "hvbox(〚term 90 T〛 break _ [term 90 E1 break , term 90 E2])"
   non associative with precedence 50
   for @{'IInt2 $T $E1 $E2}.

notation "hvbox(《term 90 T》)"
   non associative with precedence 50
   for @{'EInt $T}.

notation "hvbox(《term 90 T》 break _ [term 90 E])"
   non associative with precedence 50
   for @{'EInt1 $T $E}.

notation "hvbox(《term 90 T》 break _ [term 90 E1 break , term 90 E2])"
   non associative with precedence 50
   for @{'EInt2 $T $E1 $E2}.
