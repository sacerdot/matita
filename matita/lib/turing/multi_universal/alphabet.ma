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

include "basics/finset.ma".

inductive unialpha : Type[0] ≝ 
| bit : bool → unialpha
| bar : unialpha.

definition unialpha_eq ≝ 
  λa1,a2.match a1 with
  [ bit x ⇒ match a2 with [ bit y ⇒ ¬ xorb x y | _ ⇒ false ]
  | bar ⇒ match a2 with [ bar ⇒ true | _ ⇒ false ] ].
  
definition DeqUnialpha ≝ mk_DeqSet unialpha unialpha_eq ?.
* [ #x * [ #y cases x cases y normalize % // #Hfalse destruct
         | *: normalize % #Hfalse destruct ]
  | * [ #y ] normalize % #H1 destruct % ]
qed.

lemma unialpha_unique : 
  uniqueb DeqUnialpha [bit true;bit false;bar] = true.
// qed.

lemma unialpha_complete :∀x:DeqUnialpha. 
  memb ? x [bit true;bit false;bar] = true.
* // * //
qed.

definition FSUnialpha ≝ 
  mk_FinSet DeqUnialpha [bit true;bit false;bar] 
  unialpha_unique unialpha_complete.

(*************************** testing characters *******************************)
definition is_bit ≝ λc.match c with [ bit _ ⇒ true | _ ⇒ false ].
definition is_bar ≝ λc.match c with [ bar ⇒ true | _ ⇒ false ].