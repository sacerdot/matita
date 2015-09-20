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

(* Project started Wed Oct 12, 2005 ***************************************)
(* Project taken over by "formal_topology" and restarted Mon Apr 6, 2009 **)

include "logic/connectives.ma".
include "datatypes/constructors.ma".
include "datatypes/bool.ma".

(* notations **************************************************************)

notation < "hvbox(\iforall ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'iforall ${ default
  @{λ ${ident i}: $ty. $p}
  @{λ ${ident i}. $p}
}}.

notation > "\iforall list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
for ${ default
  @{ ${ fold right @{$Px} rec acc @{'iforall (λ ${ident x} :$T . $acc)} } }
  @{ ${ fold right @{$Px} rec acc @{'iforall (λ ${ident x} . $acc)} } }
}.

notation < "hvbox(\iexists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'iexists ${ default
  @{λ ${ident i}: $ty. $p}
  @{λ ${ident i}. $p}
}}.

notation > "\iexists list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
for ${ default
  @{ ${ fold right @{$Px} rec acc @{'iexists (λ ${ident x}: $T. $acc)} } }
  @{ ${ fold right @{$Px} rec acc @{'iexists (λ ${ident x}. $acc)} } }
}.
