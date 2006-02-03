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

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/domain_defs".

include "class_defs.ma".

(* QUANTIFICATION DOMAINS
   - These are the categories on which we allow quantification
   - We set up single quantifiers, parametric on the domain, so they
     already have the properties  that usually are axiomatized inside the 
     domain structure. This makes domains easier to use
*)

record Domain: Type \def {
   qd:> Class
}.

(* internal universal quantification *)
inductive dall (D:Domain) (P:D \to Prop) : Prop \def
   | dall_intro: (\forall d:D. cin D d \to P d) \to dall D P.

(* internal existential quantification *)
inductive dex (D:Domain) (P:D \to Prop) : Prop \def
   | dex_intro: \forall d:D. cin D d \land P d \to dex D P.

(* notations **************************************************************)

(*CSC: the URI must disappear: there is a bug now *)
interpretation "internal for all" 'iforall \eta.x =
  (cic:/matita/PREDICATIVE-TOPOLOGY/domain_defs/dall.ind#xpointer(1/1) _ x).

notation > "hvbox(\iforall ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'iforall ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "internal exists" 'dexists \eta.x =
  (cic:/matita/PREDICATIVE-TOPOLOGY/domain_defs/dex.ind#xpointer(1/1) _ x).

notation > "hvbox(\iexists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'dexists ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.
