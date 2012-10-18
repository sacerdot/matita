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
 non associative with precedence 90
 for @{ 'Item0 }.

notation "hvbox( ⓪ { I } )"
 non associative with precedence 90
 for @{ 'Item0 $I }.

notation "⋆"
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

notation "hvbox( ② term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnItem2 $T1 $T }.

notation "hvbox( ② { I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnItem2 $I $T1 $T }.

notation "hvbox( ⓑ { a , I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2 $a $I $T1 $T }.

notation "hvbox( + ⓑ { I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2Pos $I $T1 $T }.

notation "hvbox( - ⓑ { I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnBind2Neg $I $T1 $T }.

notation "hvbox( ⓕ { I } break term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnFlat2 $I $T1 $T }.

notation "hvbox( ⓓ { a } term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbr $a $T1 $T2 }.

notation "hvbox( + ⓓ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbrPos $T1 $T2 }.

notation "hvbox( - ⓓ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbbrNeg $T1 $T2 }.

notation "hvbox( ⓛ { a } term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbst $a $T1 $T2 }.

notation "hvbox( + ⓛ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbstPos $T1 $T2 }.

notation "hvbox( - ⓛ term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAbstNeg $T1 $T2 }.

notation "hvbox( ⓐ  term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnAppl $T1 $T2 }.

notation "hvbox( ⓝ  term 55 T1 . break term 55 T2 )"
 non associative with precedence 55
 for @{ 'SnCast $T1 $T2 }.

notation "hvbox( Ⓐ term 55 T1 . break term 55 T )"
 non associative with precedence 55
 for @{ 'SnApplV $T1 $T }.

notation > "hvbox( T . break ②{ I } break term 47 T1 )"
 non associative with precedence 46
 for @{ 'DxBind2 $T $I $T1 }.

notation "hvbox( T . break ⓑ { I } break term 48 T1 )"
 non associative with precedence 47
 for @{ 'DxBind2 $T $I $T1 }.

notation "hvbox( T1 . break ⓓ T2 )"
 left associative with precedence 48
 for @{ 'DxAbbr $T1 $T2 }.

notation "hvbox( T1 . break ⓛ T2 )"
 left associative with precedence 49
 for @{ 'DxAbst $T1 $T2 }.

notation "hvbox( T . break ④ { I } break { T1 , break T2 , break T3 } )"
 non associative with precedence 50
 for @{ 'DxItem4 $T $I $T1 $T2 $T3 }.

notation "hvbox( # { x } )"
 non associative with precedence 90
 for @{ 'Weight $x }.

notation "hvbox( # { x , break y } )"
 non associative with precedence 90
 for @{ 'Weight $x $y }.

notation "hvbox( 𝐒  ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'Simple $T }.

notation "hvbox( L ⊢ break term 46 T1 ≈ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'Hom $L $T1 $T2 }.

notation "hvbox( T1 ≃ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'Iso $T1 $T2 }.

(* Substitution *************************************************************)

notation "hvbox( ⇧ [ d , break e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RLift $d $e $T1 $T2 }.

notation "hvbox( T1 break ≼ [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'SubEq $T1 $d $e $T2 }.

notation "hvbox( ≽ [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'SubEqBottom $d $e $T2 }.

notation "hvbox( ⇩ [ e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDrop $e $L1 $L2 }.

notation "hvbox( ⇩ [ d , break e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDrop $d $e $L1 $L2 }.

notation "hvbox( L ⊢ break ⌘ ⦃ T ⦄ ≡ break term 46 k )"
   non associative with precedence 45
   for @{ 'ICM $L $T $k }.

notation "hvbox( L ⊢ break term 46 T1 break ▶ [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubst $L $T1 $d $e $T2 }.

(* Unfold *******************************************************************)

notation "hvbox( @ ⦃ T1 , break f ⦄ ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RAt $T1 $f $T2 }.

notation "hvbox( T1 ▭ break term 46 T2 ≡ break term 46 T )"
   non associative with precedence 45
   for @{ 'RMinus $T1 $T2 $T }.

notation "hvbox( ⇧ * [ e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'RLiftStar $e $T1 $T2 }.

notation "hvbox( ⇩ * [ e ] break term 46 L1 ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'RDropStar $e $L1 $L2 }.

notation "hvbox( T1 break ▶ * [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break term 46 T1 break ▶ * [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStar $L $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break term 46 T1 break ▶ ▶ * [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarAlt $L $T1 $d $e $T2 }.

notation "hvbox( T1 break ⊢ ▶ * [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarSn $T1 $d $e $T2 }.

notation "hvbox( T1 break ⊢ ▶ ▶ * [ d , break e ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PSubstStarSnAlt $T1 $d $e $T2 }.

notation "hvbox( ▼ * [ d , break e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'TSubst $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break ▼ * [ d , break e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'TSubst $L $T1 $d $e $T2 }.

notation "hvbox( ▼ ▼ * [ d , break e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'TSubstAlt $T1 $d $e $T2 }.

notation "hvbox( L ⊢ break ▼ ▼ * [ d , break e ] break term 46 T1 ≡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'TSubstAlt $L $T1 $d $e $T2 }.

(* Static typing ************************************************************)

notation "hvbox( L ⊢ break term 46 T ⁝ break term 46 A )"
   non associative with precedence 45
   for @{ 'AtomicArity $L $T $A }.

notation "hvbox( T1 ⁝ ⊑ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'CrSubEqA $T1 $T2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T ÷ break term 46 A )"
   non associative with precedence 45
   for @{ 'BinaryArity $h $L $T $A }.

notation "hvbox( h ⊢ break term 46 L1 ÷ ⊑ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CrSubEqB $h $L1 $L2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 • break [ g , break l ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'StaticType $h $g $l $L $T1 $T2 }.

notation "hvbox( h ⊢ break term 46 L1 • ⊑ [ g ] break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CrSubEqS $h $g $L1 $L2 }.

(* Unwind *******************************************************************)

notation "hvbox( L1 ⊢ ⧫ * break term 46 T ≡ break term 46 L2 )"
   non associative with precedence 45
   for @{ 'Unwind $L1 $T $L2 }.

(* Reducibility *************************************************************)

notation "hvbox( L ⊢ break 𝐑 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'Reducible $L $T }.

notation "hvbox( L ⊢ break 𝐈 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'NotReducible $L $T }.

notation "hvbox( L ⊢ break 𝐍 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'Normal $L $T }.

(* this might be removed *)
notation "hvbox( 𝐇𝐑 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'HdReducible $T }.

(* this might be removed *)
notation "hvbox( L ⊢ break 𝐇𝐑  ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'HdReducible $L $T }.

(* this might be removed *)
notation "hvbox( 𝐇𝐈  ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'NotHdReducible $T }.

(* this might be removed *)
notation "hvbox( L ⊢ break 𝐇𝐈 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'NotHdReducible $L $T }.

(* this might be removed *)
notation "hvbox( 𝐇𝐍 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'HdNormal $T }.

(* this might be removed *)
notation "hvbox( L ⊢ break 𝐇𝐍 ⦃ T ⦄ )"
   non associative with precedence 45
   for @{ 'HdNormal $L $T }.

notation "hvbox( T1 ➡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRed $T1 $T2 }.

notation "hvbox( L ⊢ break term 46 T1 ➡ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRed $L $T1 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ➡ break ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRed $L1 $L2 }.

notation "hvbox( ⦃ L1, break T1 ⦄ ➡ break ⦃ L2 , break T2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRed $L1 $T1 $L2 $T2 }.

notation "hvbox( L ⊢ break ⦃ L1, break T1 ⦄ ➡ break ⦃ L2 , break T2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRed $L $L1 $T1 $L2 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ➡ ➡ break ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRedAlt $L1 $L2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 ➸ break [ g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'XPRed $h $g $L $T1 $T2 }.

(* Computation **************************************************************)

notation "hvbox( T1 ➡ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $T1 $T2 }.

notation "hvbox( L ⊢ break term 46 T1 ➡ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRedStar $L $T1 $T2 }.

notation "hvbox( T1 ➡ ➡ * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PRedStarAlt $T1 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ➡ * break ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRedStar $L1 $L2 }.

notation "hvbox( ⦃ L1 , T1 ⦄ ➡ * break ⦃ L2 , T2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRedStar $L1 $T1 $L2 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ➡ ➡ * break ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRedStarAlt $L1 $L2 }.

notation "hvbox( ⦃ L1 , T1 ⦄ ➡ ➡ * break ⦃ L2 , T2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPRedStarAlt $L1 $T1 $L2 $T2 }.

notation "hvbox( L ⊢ break term 46 T1 ➡ * break 𝐍 ⦃ T2 ⦄ )"
   non associative with precedence 45
   for @{ 'PEval $L $T1 $T2 }.

notation "hvbox( ⬊ * term 46 T )"
   non associative with precedence 45
   for @{ 'SN $T }.

notation "hvbox( L ⊢ ⬊ * break term 46 T )"
   non associative with precedence 45
   for @{ 'SN $L $T }.

notation "hvbox( L ⊢ ⬊ ⬊ * break term 46 T )"
   non associative with precedence 45
   for @{ 'SNAlt $L $T }.

notation "hvbox( ⦃ L, break T ⦄ ϵ break [ R ] break 〚 A 〛 )"
   non associative with precedence 45
   for @{ 'InEInt $R $L $T $A }.

notation "hvbox( T1 ⊑ break [ R ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'CrSubEq $T1 $R $T2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 ➸ * break [ g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'XPRedStar $h $g $L $T1 $T2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ ➷ * break [ g ] break term 46 T2 )"
   non associative with precedence 45
   for @{ 'XSN $h $g $L $T }.

(* Conversion ***************************************************************)

notation "hvbox( L ⊢ break term 46 T1 ⬌ break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PConv $L $T1 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ⬌ ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPConv $L1 $L2 }.

(* Equivalence **************************************************************)

notation "hvbox( L ⊢ break term 46 T1 ⬌* break term 46 T2 )"
   non associative with precedence 45
   for @{ 'PConvStar $L $T1 $T2 }.

notation "hvbox( ⦃ L1 ⦄ ⬌ * ⦃ L2 ⦄ )"
   non associative with precedence 45
   for @{ 'FocalizedPConvStar $L1 $L2 }.

notation "hvbox( L1 ⊢ ⬌* break term 46 L2 )"
   non associative with precedence 45
   for @{ 'CPConvStar $L1 $L2 }.

(* Dynamic typing ***********************************************************)

notation "hvbox( ⦃ h , break L ⦄ ⊩ break term 46 T : break [ g ] )"
   non associative with precedence 45
   for @{ 'NativeValid $h $g $L $T }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeType $h $L $T1 $T2 }.

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 : : break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeAlt $h $L $T1 $T2 }.

(* Higher order dynamic typing **********************************************)

notation "hvbox( ⦃ h , break L ⦄ ⊢ break term 46 T1 : * break term 46 T2 )"
   non associative with precedence 45
   for @{ 'NativeTypeStar $h $L $T1 $T2 }.
