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

include "nat/nat.ma".

inductive sequence (O:Type) : Type ≝  
 | mk_seq : (nat → O) → sequence O.

definition fun_of_seq: ∀O:Type.sequence O → nat → O ≝ 
  λO.λx:sequence O.match x with [ mk_seq f ⇒ f ].

coercion fun_of_seq 1.

notation < "hvbox((\lfloor term 19 p \rfloor) \sub ident i)" with precedence 90
for @{ 'sequence (\lambda ${ident i} : $t . $p)}.

notation > "hvbox((\lfloor term 19 p \rfloor) \sub ident i)" with precedence 90
for @{ 'sequence (\lambda ${ident i} . $p)}.

notation > "hvbox(\lfloor ident i, term 19 p \rfloor)" with precedence 90
for @{ 'sequence (\lambda ${ident i} . $p)}.
  
notation "a \sub i" left associative with precedence 90 
  for @{ 'sequence_appl $a $i }.

interpretation "sequence" 'sequence \eta.x = (mk_seq ? x).
interpretation "sequence element" 'sequence_appl s i = (fun_of_seq ? s i).
