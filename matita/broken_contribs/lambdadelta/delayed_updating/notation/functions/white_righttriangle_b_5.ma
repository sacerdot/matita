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

(* NOTATION FOR DELAYED UPDATING ********************************************)

notation > "hvbox( ▷ 𝐛 opt ( { break term 46 S } ) [ break term 46 K ] ❨ break term 46 p, break term 46 n, break term 46 q ❩ )"
  non associative with precedence 90
  for @{ 'WhiteRightTriangleB ${default @{$S}@{?}} $K $p $n $q }.

notation < "hvbox( ▷ 𝐛 [ break term 46 K ] ❨ break term 46 p, break term 46 n, break term 46 q ❩ )"
  non associative with precedence 90
  for @{ 'WhiteRightTriangleB $S $K $p $n $q }.
