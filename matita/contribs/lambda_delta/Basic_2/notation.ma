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

(* NOTATION FOR THE FORMAL SYSTEM λδ ****************************************)

(* Grammar ******************************************************************)

notation "hvbox( ⋆ )"
 non associative with precedence 90
 for @{ 'Star }.

notation "hvbox( ⋆ term 90 k )"
 non associative with precedence 90
 for @{ 'Star $k }.

notation "hvbox( # term 90 i )"
 non associative with precedence 90
 for @{ 'LRef $i }.

notation "hvbox( § term 90 p )"
 non associative with precedence 90
 for @{ 'GRef $p }.

notation "hvbox( 𝕒 { I } )"
 non associative with precedence 90
 for @{ 'SItem $I }.

notation "hvbox( 𝕔 { I } break term 90 T1 . break term 90 T )"
 non associative with precedence 90
 for @{ 'SItem $I $T1 $T }.

notation "hvbox( 𝕓 { I } break term 90 T1 . break term 90 T )"
 non associative with precedence 90
 for @{ 'SBind $I $T1 $T }.

notation "hvbox( 𝕗 { I } break term 90 T1 . break term 90 T )"
 non associative with precedence 90
 for @{ 'SFlat $I $T1 $T }.

notation "hvbox( T . break 𝕓 { I } break term 90 T1 )"
 non associative with precedence 89
 for @{ 'DBind $T $I $T1 }.
(*
notation > "hvbox( T . break 𝕔 { I } break term 90 T1 )"
 non associative with precedence 89
 for @{ 'DBind $T $I $T1 }.
*) (**) (* this breaks all parsing *)
notation "hvbox( # [ x ] )"
 non associative with precedence 90
 for @{ 'Weight $x }.

notation "hvbox( # [ x , break y ] )"
 non associative with precedence 90
 for @{ 'Weight $x $y }.

notation "hvbox( 𝕊 [ T ] )"
   non associative with precedence 45
   for @{ 'Simple $T }.

notation "hvbox( T1 break [ d , break e ] ≼ break T2 )"
   non associative with precedence 45
   for @{ 'SubEq $T1 $d $e $T2 }.

(* Substitution *************************************************************)

notation "hvbox( ↑ [ d , break e ] break T1 ≡ break T2 )"
   non associative with precedence 45
   for @{ 'RLift $d $e $T1 $T2 }.

notation "hvbox( ↓ [ d , break e ] break L1 ≡ break L2 )"
   non associative with precedence 45
   for @{ 'RDrop $d $e $L1 $L2 }.

notation "hvbox( T1 break [ d , break e ] ≫ break T2 )"
   non associative with precedence 45
   for @{ 'PSubst $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break term 90 T1 break [ d , break e ] ≫ break T2 )"
   non associative with precedence 45
   for @{ 'PSubst $L $T1 $d $e $T2 }.

(* Unfold *******************************************************************)

notation "hvbox( T1 break [ d , break e ] ≫* break T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break term 90 T1 break [ d , break e ] ≫* break T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $L $T1 $d $e $T2 }.

(* Reduction ****************************************************************)

notation "hvbox( T1 ⇒ break T2 )"
   non associative with precedence 45
   for @{ 'PRed $T1 $T2 }.

notation "hvbox( L ⊢ break term 90 T1 ⇒ break T2 )"
   non associative with precedence 45
   for @{ 'PRed $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ⇒ break L2 )"
   non associative with precedence 45
   for @{ 'CPRed $L1 $L2 }.

(* Computation **************************************************************)

notation "hvbox( T1 ⇒* break T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $T1 $T2 }.

notation "hvbox( L ⊢ break term 90 T1 ⇒* break T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ⇒* break L2 )"
   non associative with precedence 45
   for @{ 'CPRedStar $L1 $L2 }.
