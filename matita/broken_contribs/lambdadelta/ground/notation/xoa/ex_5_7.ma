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

(* NOTATION FOR GROUND ******************************************************)

(* NOTE: This file was generated by xoa, do not edit ************************)

(* Note: multiple existental quantifier (5, 7) *)
notation > "hvbox(∃∃ ident x0 , ident x1 , ident x2 , ident x3 , ident x4 , ident x5 , ident x6 break . term 19 P0 break & term 19 P1 break & term 19 P2 break & term 19 P3 break & term 19 P4)"
  non associative with precedence 20
  for @{ 'Ex7 (λ${ident x0}.λ${ident x1}.λ${ident x2}.λ${ident x3}.λ${ident x4}.λ${ident x5}.λ${ident x6}.$P0) (λ${ident x0}.λ${ident x1}.λ${ident x2}.λ${ident x3}.λ${ident x4}.λ${ident x5}.λ${ident x6}.$P1) (λ${ident x0}.λ${ident x1}.λ${ident x2}.λ${ident x3}.λ${ident x4}.λ${ident x5}.λ${ident x6}.$P2) (λ${ident x0}.λ${ident x1}.λ${ident x2}.λ${ident x3}.λ${ident x4}.λ${ident x5}.λ${ident x6}.$P3) (λ${ident x0}.λ${ident x1}.λ${ident x2}.λ${ident x3}.λ${ident x4}.λ${ident x5}.λ${ident x6}.$P4) }.

notation < "hvbox(∃∃ ident x0 , ident x1 , ident x2 , ident x3 , ident x4 , ident x5 , ident x6 break . term 19 P0 break & term 19 P1 break & term 19 P2 break & term 19 P3 break & term 19 P4)"
  non associative with precedence 20
  for @{ 'Ex7 (λ${ident x0}:$T0.λ${ident x1}:$T1.λ${ident x2}:$T2.λ${ident x3}:$T3.λ${ident x4}:$T4.λ${ident x5}:$T5.λ${ident x6}:$T6.$P0) (λ${ident x0}:$T0.λ${ident x1}:$T1.λ${ident x2}:$T2.λ${ident x3}:$T3.λ${ident x4}:$T4.λ${ident x5}:$T5.λ${ident x6}:$T6.$P1) (λ${ident x0}:$T0.λ${ident x1}:$T1.λ${ident x2}:$T2.λ${ident x3}:$T3.λ${ident x4}:$T4.λ${ident x5}:$T5.λ${ident x6}:$T6.$P2) (λ${ident x0}:$T0.λ${ident x1}:$T1.λ${ident x2}:$T2.λ${ident x3}:$T3.λ${ident x4}:$T4.λ${ident x5}:$T5.λ${ident x6}:$T6.$P3) (λ${ident x0}:$T0.λ${ident x1}:$T1.λ${ident x2}:$T2.λ${ident x3}:$T3.λ${ident x4}:$T4.λ${ident x5}:$T5.λ${ident x6}:$T6.$P4) }.
