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

(* GENERAL NOTATION USED BY THE FORMAL SYSTEM λδ ****************************)

(* Lists ********************************************************************)

notation "hvbox( ◊ )"
  non associative with precedence 90
  for @{'Nil}.

notation "hvbox( hd :: break tl )"
  right associative with precedence 47
  for @{'Cons $hd $tl}.

notation "hvbox( l1 @ break l2 )"
  right associative with precedence 47
  for @{'Append $l1 $l2 }.

notation "hvbox( ⟠ )"
  non associative with precedence 90
  for @{'Nil2}.

notation "hvbox( { hd1 , break hd2 } :: break tl )"
  non associative with precedence 47
  for @{'Cons $hd1 $hd2 $tl}.
