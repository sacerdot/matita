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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "common/comp.ma".
include "num/bool_lemmas.ma".

(* ****** *)
(* OTTALI *)
(* ****** *)

ninductive oct : Type ≝
  o0: oct
| o1: oct
| o2: oct
| o3: oct
| o4: oct
| o5: oct
| o6: oct
| o7: oct.

(* iteratore sugli ottali *)
ndefinition forall_oct ≝ λP.
 P o0 ⊗ P o1 ⊗ P o2 ⊗ P o3 ⊗ P o4 ⊗ P o5 ⊗ P o6 ⊗ P o7.

(* operatore = *)
ndefinition eq_oct ≝
λn1,n2:oct.
 match n1 with
  [ o0 ⇒ match n2 with [ o0 ⇒ true  | _ ⇒ false ]
  | o1 ⇒ match n2 with [ o1 ⇒ true  | _ ⇒ false ] 
  | o2 ⇒ match n2 with [ o2 ⇒ true  | _ ⇒ false ]
  | o3 ⇒ match n2 with [ o3 ⇒ true  | _ ⇒ false ] 
  | o4 ⇒ match n2 with [ o4 ⇒ true  | _ ⇒ false ]  
  | o5 ⇒ match n2 with [ o5 ⇒ true  | _ ⇒ false ] 
  | o6 ⇒ match n2 with [ o6 ⇒ true  | _ ⇒ false ]  
  | o7 ⇒ match n2 with [ o7 ⇒ true  | _ ⇒ false ] 
  ].

(* operatore and *)
ndefinition and_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o0 | o3 ⇒ o0 
  | o4 ⇒ o0 | o5 ⇒ o0 | o6 ⇒ o0 | o7 ⇒ o0 ]
 | o1 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o0 | o7 ⇒ o1 ]
 | o2 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o2 | o3 ⇒ o2 
  | o4 ⇒ o0 | o5 ⇒ o0 | o6 ⇒ o2 | o7 ⇒ o2 ]
 | o3 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o2 | o7 ⇒ o3 ]
 | o4 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o0 | o3 ⇒ o0 
  | o4 ⇒ o4 | o5 ⇒ o4 | o6 ⇒ o4 | o7 ⇒ o4 ]
 | o5 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o4 | o7 ⇒ o5 ]
 | o6 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o0 | o2 ⇒ o2 | o3 ⇒ o2 
  | o4 ⇒ o4 | o5 ⇒ o4 | o6 ⇒ o6 | o7 ⇒ o6 ]
 | o7 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 ]. 

(* operatore or *)
ndefinition or_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o1 ⇒ match e2 with
  [ o0 ⇒ o1 | o1 ⇒ o1 | o2 ⇒ o3 | o3 ⇒ o3 
  | o4 ⇒ o5 | o5 ⇒ o5 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o2 ⇒ match e2 with
  [ o0 ⇒ o2 | o1 ⇒ o3 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o3 ⇒ match e2 with
  [ o0 ⇒ o3 | o1 ⇒ o3 | o2 ⇒ o3 | o3 ⇒ o3 
  | o4 ⇒ o7 | o5 ⇒ o7 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o4 ⇒ match e2 with
  [ o0 ⇒ o4 | o1 ⇒ o5 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o5 ⇒ match e2 with
  [ o0 ⇒ o5 | o1 ⇒ o5 | o2 ⇒ o7 | o3 ⇒ o7 
  | o4 ⇒ o5 | o5 ⇒ o5 | o6 ⇒ o7 | o7 ⇒ o7 ]
 | o6 ⇒ match e2 with
  [ o0 ⇒ o6 | o1 ⇒ o7 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o6 | o7 ⇒ o7 ]
 | o7 ⇒ match e2 with
  [ o0 ⇒ o7 | o1 ⇒ o7 | o2 ⇒ o7 | o3 ⇒ o7 
  | o4 ⇒ o7 | o5 ⇒ o7 | o6 ⇒ o7 | o7 ⇒ o7 ]
 ].

(* operatore xor *)
ndefinition xor_oct ≝
λe1,e2:oct.match e1 with
 [ o0 ⇒ match e2 with
  [ o0 ⇒ o0 | o1 ⇒ o1 | o2 ⇒ o2 | o3 ⇒ o3 
  | o4 ⇒ o4 | o5 ⇒ o5 | o6 ⇒ o6 | o7 ⇒ o7 ] 
 | o1 ⇒ match e2 with
  [ o0 ⇒ o1 | o1 ⇒ o0 | o2 ⇒ o3 | o3 ⇒ o2 
  | o4 ⇒ o5 | o5 ⇒ o4 | o6 ⇒ o7 | o7 ⇒ o6 ] 
 | o2 ⇒ match e2 with
  [ o0 ⇒ o2 | o1 ⇒ o3 | o2 ⇒ o0 | o3 ⇒ o1 
  | o4 ⇒ o6 | o5 ⇒ o7 | o6 ⇒ o4 | o7 ⇒ o5 ] 
 | o3 ⇒ match e2 with
  [ o0 ⇒ o3 | o1 ⇒ o2 | o2 ⇒ o1 | o3 ⇒ o0 
  | o4 ⇒ o7 | o5 ⇒ o6 | o6 ⇒ o5 | o7 ⇒ o4 ] 
 | o4 ⇒ match e2 with
  [ o0 ⇒ o4 | o1 ⇒ o5 | o2 ⇒ o6 | o3 ⇒ o7 
  | o4 ⇒ o0 | o5 ⇒ o1 | o6 ⇒ o2 | o7 ⇒ o3 ] 
 | o5 ⇒ match e2 with
  [ o0 ⇒ o5 | o1 ⇒ o4 | o2 ⇒ o7 | o3 ⇒ o6 
  | o4 ⇒ o1 | o5 ⇒ o0 | o6 ⇒ o3 | o7 ⇒ o2 ] 
 | o6 ⇒ match e2 with
  [ o0 ⇒ o6 | o1 ⇒ o7 | o2 ⇒ o4 | o3 ⇒ o5 
  | o4 ⇒ o2 | o5 ⇒ o3 | o6 ⇒ o0 | o7 ⇒ o1 ] 
 | o7 ⇒ match e2 with
  [ o0 ⇒ o7 | o1 ⇒ o6 | o2 ⇒ o5 | o3 ⇒ o4 
  | o4 ⇒ o3 | o5 ⇒ o2 | o6 ⇒ o1 | o7 ⇒ o0 ] 
 ].

(* operatore predecessore *)
ndefinition pred_oct ≝
λn.match n with
 [ o0 ⇒ o7 | o1 ⇒ o0 | o2 ⇒ o1 | o3 ⇒ o2 | o4 ⇒ o3 | o5 ⇒ o4 | o6 ⇒ o5 | o7 ⇒ o6 ].

(* operatore successore *)
ndefinition succ_oct ≝
λn.match n with
 [ o0 ⇒ o1 | o1 ⇒ o2 | o2 ⇒ o3 | o3 ⇒ o4 | o4 ⇒ o5 | o5 ⇒ o6 | o6 ⇒ o7 | o7 ⇒ o0 ].

(* ottali ricorsivi *)
ninductive rec_oct : oct → Type ≝
  oc_O : rec_oct o0
| oc_S : ∀n.rec_oct n → rec_oct (succ_oct n).

(* ottali → ottali ricorsivi *)
ndefinition oct_to_recoct ≝
λn.match n return λx.rec_oct x with
 [ o0 ⇒ oc_O
 | o1 ⇒ oc_S ? oc_O
 | o2 ⇒ oc_S ? (oc_S ? oc_O)
 | o3 ⇒ oc_S ? (oc_S ? (oc_S ? oc_O))
 | o4 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O)))
 | o5 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O))))
 | o6 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O)))))
 | o7 ⇒ oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? (oc_S ? oc_O))))))
 ].

ndefinition oct_destruct_aux ≝
Πn1,n2:oct.ΠP:Prop.n1 = n2 →
 match eq_oct n1 n2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition oct_destruct : oct_destruct_aux.
 #n1; #n2; #P; #H;
 nrewrite < H;
 nelim n1;
 nnormalize;
 napply (λx.x).
nqed.

nlemma eq_to_eqoct : ∀n1,n2.n1 = n2 → eq_oct n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqoct_to_neq : ∀n1,n2.eq_oct n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_oct n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqoct n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqoct_to_eq : ∀n1,n2.eq_oct n1 n2 = true → n1 = n2.
 #n1; #n2;
 ncases n1;
 ncases n2;
 nnormalize;
 ##[ ##1,10,19,28,37,46,55,64: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqoct : ∀n1,n2.n1 ≠ n2 → eq_oct n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_oct n1 n2));
 napply (not_to_not (eq_oct n1 n2 = true) (n1 = n2) ? H);
 napply (eqoct_to_eq n1 n2).
nqed.

nlemma decidable_oct : ∀x,y:oct.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_oct x y = true) (eq_oct x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqoct_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqoct_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqoct : symmetricT oct bool eq_oct.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_oct n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqoct n1 n2 H);
          napply (symmetric_eq ? (eq_oct n2 n1) false);
          napply (neq_to_neqoct n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma oct_is_comparable : comparable.
 @ oct
  ##[ napply o0
  ##| napply forall_oct
  ##| napply eq_oct
  ##| napply eqoct_to_eq
  ##| napply eq_to_eqoct
  ##| napply neqoct_to_neq
  ##| napply neq_to_neqoct
  ##| napply decidable_oct
  ##| napply symmetric_eqoct
  ##]
nqed.

unification hint 0 ≔ ⊢ carr oct_is_comparable ≡ oct.
