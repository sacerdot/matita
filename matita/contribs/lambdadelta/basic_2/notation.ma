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

notation "⓪"
 non associative with precedence 55
 for @{ 'Item0 }.

notation "hvbox( ⓪ { term 46 I } )"
 non associative with precedence 55
 for @{ 'Item0 $I }.

notation "⋆"
 non associative with precedence 46
 for @{ 'Star }.

notation "hvbox( ⋆ term 90 k )"
 non associative with precedence 55
 for @{ 'Star $k }.

notation "hvbox( # term 90 i )"
 non associative with precedence 55
 for @{ 'LRef $i }.

notation "hvbox( § term 90 p )"
 non associative with precedence 55
 for @{ 'GRef $p }.

notation "hvbox( ② term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnItem2 $T1 $T }.

notation "hvbox( ② { term 46 I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnItem2 $I $T1 $T }.

notation "hvbox( ⓑ { term 46 a , break term 46 I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2 $a $I $T1 $T }.

notation "hvbox( + ⓑ { term 46 I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2Pos $I $T1 $T }.

notation "hvbox( - ⓑ { term 46 I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2Neg $I $T1 $T }.

notation "hvbox( ⓕ { term 46 I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnFlat2 $I $T1 $T }.

notation "hvbox( ⓓ { term 46 a } break term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbr $a $T1 $T2 }.

notation "hvbox( + ⓓ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbrPos $T1 $T2 }.

notation "hvbox( - ⓓ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbrNeg $T1 $T2 }.

notation "hvbox( ⓛ { term 46 a } break term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbst $a $T1 $T2 }.

notation "hvbox( + ⓛ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbstPos $T1 $T2 }.

notation "hvbox( - ⓛ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbstNeg $T1 $T2 }.

notation "hvbox( ⓐ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAppl $T1 $T2 }.

notation "hvbox( ⓝ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnCast $T1 $T2 }.

notation "hvbox( Ⓐ term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnApplV $T1 $T }.

notation > "hvbox( T . break ②{ term 46 I } break term 47 T1 )"
 non associative with precedence 46
 for @{ 'DxBind2 $T $I $T1 }.

notation "hvbox( T . break ⓑ { term 46 I } break term 48 T1 )"
 non associative with precedence 47
 for @{ 'DxBind2 $T $I $T1 }.

notation "hvbox( T1 . break ⓓ T2 )"
 left associative with precedence 48
 for @{ 'DxAbbr $T1 $T2 }.

notation "hvbox( T1 . break ⓛ T2 )"
 left associative with precedence 49
 for @{ 'DxAbst $T1 $T2 }.

notation "hvbox( ♯ { term 46 x } )"
 non associative with precedence 90
 for @{ 'Weight $x }.

notation "hvbox( ♯ { term 46 x , break term 46 y } )"
 non associative with precedence 90
 for @{ 'Weight $x $y }.

notation "hvbox( 𝐒 ⦃ term 46 T ⦄ )"
   non associative with precedence 45
   for @{ 'Simple $T }.

notation "hvbox( T1 ≃ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'Iso $T1 $T2 }.

(* Relocation ***************************************************************)

notation "hvbox( ⇧ [ term 46 d , break term 46 e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RLift $d $e $T1 $T2 }.

notation "hvbox( ⇩ [ term 46 e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDrop $e $L1 $L2 }.

notation "hvbox( ⇩ [ term 46 d , break term 46 e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDrop $d $e $L1 $L2 }.

notation "hvbox( ⦃ term 46 L1, break term 46 T1 ⦄ ⊃ break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'SupTerm $L1 $T1 $L2 $T2 }.

notation "hvbox( ⦃ term 46 L1, break term 46 T1 ⦄ ⊃⸮ break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'SupTermOpt $L1 $T1 $L2 $T2 }.

notation "hvbox( L ⊢ break ⌘ ⦃ term 46 T ⦄ ≡ break term 46 k )"
   non associative with precedence 45
   for @{ 'ICM $L $T $k }.

(* Substitution *************************************************************)

notation "hvbox( @ ⦃ term 46 T1 , break term 46 f ⦄ ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RAt $T1 $f $T2 }.

notation "hvbox( T1 ▭ break term 46 T2 ≡ break term 46 T )"
   non associative with precedence 45
   for @{ 'RMinus $T1 $T2 $T }.

notation "hvbox( ⇧ * [ term 46 e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RLiftStar $e $T1 $T2 }.

notation "hvbox( ⇩ * [ term 46 e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDropStar $e $L1 $L2 }.

notation "hvbox( ⦃ term 46 L1, break term 46 T1 ⦄ ⊃ + break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'SupTermPlus $L1 $T1 $L2 $T2 }.

notation "hvbox( ⦃ term 46 L1, break term 46 T1 ⦄ ⊃ * break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'SupTermStar $L1 $T1 $L2 $T2 }.

notation "hvbox( L1 ⊑ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'SubEq $L1 $L2 }.

notation "hvbox( L ⊢ break term 46 T1 ▶* break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $L $T1 $T2 }.

notation "hvbox( T1 ⊢ ▶ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarSn $T1 $T2 }.

(* Static typing ************************************************************)

notation "hvbox( L ⊢ break term 46 T ⁝ break term 46 A )"
   non associative with precedence 45
   for @{ 'AtomicArity $L $T $A }.

notation "hvbox( T1 ⁝ ⊑ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'CrSubEqA $T1 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T ÷ break term 46 A )"
   non associative with precedence 45
   for @{ 'BinaryArity $h $L $T $A }.

notation "hvbox( h ⊢ break term 46 L1 ÷ ⊑ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CrSubEqB $h $L1 $L2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 • break [ term 46 g ] break ⦃ term 46 l , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'StaticType $h $g $L $T1 $T2 $l }.

(* Unfold *******************************************************************)

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 •* break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'StaticTypeStar $h $g $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ⧫ * break term 46 T ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'Unfold $L1 $T $L2 }.

notation "hvbox( L ⊢ break term 46 T1 ➤ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRestStar $L $T1 $T2 }.

notation "hvbox( T1 ⊢ ➤ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRestStarSn $T1 $T2 }.

(* Reduction ****************************************************************)

notation "hvbox( L ⊢ break 𝐑 ⦃ term 46 T ⦄ )"
   non associative with precedence 45
   for @{ 'Reducible $L $T }.

notation "hvbox( L ⊢ break 𝐈 ⦃ term 46 T ⦄ )"
   non associative with precedence 45
   for @{ 'NotReducible $L $T }.

notation "hvbox( L ⊢ break 𝐍 ⦃ term 46 T ⦄ )"
   non associative with precedence 45
   for @{ 'Normal $L $T }.

notation "hvbox( L ⊢ break term 46 T1 ➡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRed $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h, break term 46 L ⦄ ⊢ break term 46 T1 ➡ break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRed $h $g $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ➡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PRedSn $L1 $L2 }.

notation "hvbox( ⦃ term 46 h, break term 46 L1 ⦄ ⊢ ➡ break [ term 46 g ] break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PRedSn $h $g $L1 $L2 }.

(* Computation **************************************************************)

notation "hvbox( L ⊢ break term 46 T1 ➡ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ➡* break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PRedSnStar $L1 $L2 }.

notation "hvbox( L1 ⊢ ➡➡* break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PRedSnStarAlt $L1 $L2 }.

notation "hvbox( L ⊢ break term 46 T1 ➡ * break 𝐍 ⦃ term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'PEval $L $T1 $T2 }.

notation "hvbox( L ⊢ ⬊ * break term 46 T )"
   non associative with precedence 45
   for @{ 'SN $L $T }.

notation "hvbox( L ⊢ ⬊ ⬊ * break term 46 T )"
   non associative with precedence 45
   for @{ 'SNAlt $L $T }.

notation "hvbox( ⦃ term 46 h, break term 46 L ⦄ ⊢ break term 46 T1 ➡ * break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $h $g $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h, break term 46 L ⦄ ⊢ ⬊ * break [ term 46 g ] break term 46 T )"
   non associative with precedence 45
   for @{ 'SN $h $g $L $T }.

notation "hvbox( ⦃ term 46 h, break term 46 L ⦄ ⊢ ⬊ ⬊ * break [ term 46 g ] break term 46 T )"
   non associative with precedence 45
   for @{ 'SNAlt $h $g $L $T }.

notation "hvbox( ⦃ term 46 L, break term 46 T ⦄ ϵ break [ term 46 R ] break 〚term 46  A 〛 )"
   non associative with precedence 45
   for @{ 'InEInt $R $L $T $A }.

notation "hvbox( T1 ⊑ break [ term 46 R ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'CrSubEq $T1 $R $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 • * ➡ * break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'DecomposedXPRedStar $h $g $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ • * ⬊ * break [ term 46 g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'DecomposedXSN $h $g $L $T }.

(* Conversion ***************************************************************)

notation "hvbox( L ⊢ break term 46 T1 ⬌ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PConv $L $T1 $T2 }.

notation "hvbox( L1 ⊢ ⬌ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PConvSn $L1 $L2 }.

(* Equivalence **************************************************************)

notation "hvbox( L ⊢ break term 46 T1 ⬌* break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PConvStar $L $T1 $T2 }.

notation "hvbox( h ⊢ break term 46 L1 • ⊑ break [ term 46 g ] break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CrSubEqS $h $g $L1 $L2 }.

notation "hvbox( L1 ⊢ ⬌* break term 46 L2 )"
   non associative with precedence 45
   for @{ 'PConvSnStar $L1 $L2 }.

(* Dynamic typing ***********************************************************)

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T ¡ break [ term 46 g ] )"
   non associative with precedence 45
   for @{ 'NativeValid $h $g $L $T }.

notation "hvbox( h ⊢ break term 46 L1 ¡ ⊑ break [ term 46 g ] break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CrSubEqV $h $g $L1 $L2 }.

notation "hvbox( h ⊢ break ⦃ term 46 L1, break term 46 T1 ⦄ ≽ break [ term 46 g ] break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'BTPRed $h $g $L1 $T1 $L2 $T2 }.

notation "hvbox( h ⊢ break ⦃ term 46 L1, break term 46 T1 ⦄ ≻ break [ term 46 g ] break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'BTPRedProper $h $g $L1 $T1 $L2 $T2 }.

notation "hvbox( h ⊢ break ⦃ term 46 L1, break term 46 T1 ⦄ ≥ break [ term 46 g ] break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'BTPRedStar $h $g $L1 $T1 $L2 $T2 }.

notation "hvbox( h ⊢ break ⦃ term 46 L1, break term 46 T1 ⦄ > break [ term 46 g ] break ⦃ term 46 L2 , break term 46 T2 ⦄ )"
   non associative with precedence 45
   for @{ 'BTPRedStarProper $h $g $L1 $T1 $L2 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeType $h $L $T1 $T2 }.

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeAlt $h $L $T1 $T2 }.

(* Higher order dynamic typing **********************************************)

notation "hvbox( ⦃ term 46 h , break term 46 L ⦄ ⊢ break term 46 T1 : * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeStar $h $L $T1 $T2 }.
