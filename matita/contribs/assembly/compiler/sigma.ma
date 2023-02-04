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

(* ********************************************************************** *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

(* coppia dipendente *)

inductive sigma (A:Type) (P:A → Type) : Type ≝
    sigma_intro: ∀x:A.P x → sigma A P.

notation < "hvbox(\Sigma ident i opt (: tx) break . p)"
  right associative with precedence 20
for @{ 'Sigma ${default
  @{\lambda ${ident i} : $tx. $p}  
  @{\lambda ${ident i} . $p}}}.

notation > "\Sigma list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'Sigma (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'Sigma (λ${ident x}.$acc)} } }
       }.

notation "\ll term 19 a, break term 19 b \gg"
with precedence 90 for @{'dependent_pair (λx:?.? x) $a $b}.
interpretation "dependent pair" 'dependent_pair \eta.c a b = (sigma_intro ? c a b).

interpretation "sigma" 'Sigma \eta.x = (sigma ? x).

definition sigmaFst ≝
λT:Type.λf:T → Type.λs:sigma T f.match s with [ sigma_intro x _ ⇒ x ].
definition sigmaSnd ≝
λT:Type.λf:T → Type.λs:sigma T f.match s return λs.f (sigmaFst ?? s) with [ sigma_intro _ x ⇒ x ].
