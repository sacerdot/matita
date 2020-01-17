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

notation "hvbox( ⦃G, L⦄ ⊢ break ⌘ ⦃ term 46 T ⦄ ≡ break term 46 k )"
   non associative with precedence 45
   for @{ 'ICM $L $T $k }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T ÷ break term 46 A )"
   non associative with precedence 45
   for @{ 'BinaryArity $h $L $T $A }.

notation "hvbox( h ⊢ break term 46 L1 ÷ ⫃ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'LRSubEqB $h $L1 $L2 }.

notation "hvbox( L1 ⊢ ⬌ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PConvSn $L1 $L2 }.

notation "hvbox( L1 ⊢ ⬌* break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PConvSnStar $L1 $L2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeType $h $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeAlt $h $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeStar $h $L $T1 $T2 }.
