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

(* **************************** *)
(* TIPI PER I MODULI DI MEMORIA *)
(* **************************** *)

(* tipi di memoria:RAM/ROM/non installata *)
ninductive memory_type : Type ≝
  MEM_READ_ONLY: memory_type
| MEM_READ_WRITE: memory_type
| MEM_OUT_OF_BOUND: memory_type.

(* iteratore sugli ottali *)
ndefinition forall_memory_type ≝ λP.
 P MEM_READ_ONLY ⊗ P MEM_READ_WRITE ⊗ P MEM_OUT_OF_BOUND.

(* operatore = *)
ndefinition eq_memorytype ≝
λm1,m2.match m1 with
  [ MEM_READ_ONLY ⇒ match m2 with [ MEM_READ_ONLY ⇒ true  | _ ⇒ false ]
  | MEM_READ_WRITE ⇒ match m2 with [ MEM_READ_WRITE ⇒ true  | _ ⇒ false ] 
  | MEM_OUT_OF_BOUND ⇒ match m2 with [ MEM_OUT_OF_BOUND ⇒ true  | _ ⇒ false ]
  ].

ndefinition memorytype_destruct_aux ≝
Πn1,n2:memory_type.ΠP:Prop.n1 = n2 →
 match eq_memorytype n1 n2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition memorytype_destruct : memorytype_destruct_aux.
 #n1; #n2; #P; #H;
 nrewrite < H;
 nelim n1;
 nnormalize;
 napply (λx.x).
nqed.

nlemma eq_to_eqmemorytype : ∀n1,n2.n1 = n2 → eq_memorytype n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqmemorytype_to_neq : ∀n1,n2.eq_memorytype n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_memorytype n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqmemorytype n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqmemorytype_to_eq : ∀n1,n2.eq_memorytype n1 n2 = true → n1 = n2.
 #n1; #n2;
 ncases n1;
 ncases n2;
 nnormalize;
 ##[ ##1,5,9: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqmemorytype : ∀n1,n2.n1 ≠ n2 → eq_memorytype n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_memorytype n1 n2));
 napply (not_to_not (eq_memorytype n1 n2 = true) (n1 = n2) ? H);
 napply (eqmemorytype_to_eq n1 n2).
nqed.

nlemma decidable_memorytype : ∀x,y:memory_type.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_memorytype x y = true) (eq_memorytype x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqmemorytype_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqmemorytype_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqmemorytype : symmetricT memory_type bool eq_memorytype.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_memorytype n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqmemorytype n1 n2 H);
          napply (symmetric_eq ? (eq_memorytype n2 n1) false);
          napply (neq_to_neqmemorytype n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma memorytype_is_comparable : comparable.
 @ memory_type
  ##[ napply MEM_READ_ONLY
  ##| napply forall_memory_type
  ##| napply eq_memorytype
  ##| napply eqmemorytype_to_eq
  ##| napply eq_to_eqmemorytype
  ##| napply neqmemorytype_to_neq
  ##| napply neq_to_neqmemorytype
  ##| napply decidable_memorytype
  ##| napply symmetric_eqmemorytype
  ##]
nqed.

unification hint 0 ≔ ⊢ carr memorytype_is_comparable ≡ memory_type.
