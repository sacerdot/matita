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

notation "hvbox( 𝕒 )"
 non associative with precedence 90
 for @{ 'SItem }.

notation "hvbox( 𝕒 { I } )"
 non associative with precedence 90
 for @{ 'SItem $I }.

notation "hvbox( 𝕔 term 90 T1 . break term 90 T )"
 non associative with precedence 90
 for @{ 'SItem $T1 $T }.

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

notation "hvbox( ↓ [ e ] break L1 ≡ break L2 )"
   non associative with precedence 45
   for @{ 'RDrop $e $L1 $L2 }.

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

notation "hvbox( T1 break [ d , break e ] ≡ break T2 )"
   non associative with precedence 45
   for @{ 'TSubst $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break term 90 T1 break [ d , break e ] ≡ break T2 )"
   non associative with precedence 45
   for @{ 'TSubst $L $T1 $d $e $T2 }.

(* Static Typing ************************************************************)

notation "hvbox( L ⊢ break term 90 T ÷ break A )"
   non associative with precedence 45
   for @{ 'AtomicArity $L $T $A }.

(* Reducibility *************************************************************)

notation "hvbox( ℝ [ T ] )"
   non associative with precedence 45
   for @{ 'Reducible $T }.

notation "hvbox( L ⊢ ℝ [ T ] )"
   non associative with precedence 45
   for @{ 'Reducible $L $T }.

notation "hvbox( 𝕀 [ T ] )"
   non associative with precedence 45
   for @{ 'NotReducible $T }.

notation "hvbox( L ⊢ 𝕀 [ T ] )"
   non associative with precedence 45
   for @{ 'NotReducible $L $T }.

notation "hvbox( ℕ [ T ] )"
   non associative with precedence 45
   for @{ 'Normal $T }.

notation "hvbox( L ⊢ ℕ [ T ] )"
   non associative with precedence 45
   for @{ 'Normal $L $T }.

notation "hvbox( 𝕎ℍℝ [ T ] )"
   non associative with precedence 45
   for @{ 'WHdReducible $T }.

notation "hvbox( L ⊢ 𝕎ℍℝ [ T ] )"
   non associative with precedence 45
   for @{ 'WHdReducible $L $T }.

notation "hvbox( 𝕎ℍ𝕀 [ T ] )"
   non associative with precedence 45
   for @{ 'NotWHdReducible $T }.

notation "hvbox( L ⊢ 𝕎ℍ𝕀 [ T ] )"
   non associative with precedence 45
   for @{ 'NotWHdReducible $L $T }.

notation "hvbox( 𝕎ℍℕ [ T ] )"
   non associative with precedence 45
   for @{ 'WHdNormal $T }.

notation "hvbox( L ⊢ 𝕎ℍℕ [ T ] )"
   non associative with precedence 45
   for @{ 'WHdNormal $L $T }.

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

notation "hvbox( ⇓ T  )"
   non associative with precedence 45
   for @{ 'SN $T }.

notation "hvbox( L ⊢ ⇓ T )"
   non associative with precedence 45
   for @{ 'SN $L $T }.

notation "hvbox( { L, break T } ϵ break 〚 A 〛 )"
   non associative with precedence 45
   for @{ 'InEInt $L $T $A }.

notation "hvbox( R ⊢ break { L, break T } ϵ break 〚 A 〛 )"
   non associative with precedence 45
   for @{ 'InEInt $R $L $T $A }.

notation "hvbox( T1 ⊑ break T2 )"
   non associative with precedence 45
   for @{ 'CrSubEq $T1 $T2 }.

notation "hvbox( T1 break [ R ] ⊑ break T2 )"
   non associative with precedence 45
   for @{ 'CrSubEq $T1 $R $T2 }.

(* Functional ***************************************************************)

notation "hvbox( ↟ [ d , break e ] break T )"
   non associative with precedence 80
   for @{ 'Lift $d $e $T }.

notation "hvbox( ↡ [ d ← break V ] break T )"
   non associative with precedence 80
   for @{ 'Subst $V $d $T }.

