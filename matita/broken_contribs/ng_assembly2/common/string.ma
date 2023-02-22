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

include "common/ascii.ma".
include "common/list.ma".

(* ******* *)
(* STRINGA *)
(* ******* *)

(* tipo pubblico *)
ndefinition aux_str_type ≝ list ascii.

unification hint 0 ≔ ⊢ carr (list_is_comparable ascii_is_comparable) ≡ list ascii.
unification hint 0 ≔ ⊢ carr (list_is_comparable ascii_is_comparable) ≡ aux_str_type.

(* ************ *)
(* STRINGA + ID *)
(* ************ *)

(* tipo pubblico *)
nrecord strId : Type ≝
 {
 str_elem: aux_str_type;
 id_elem: nat
 }.

(* confronto *)
ndefinition eq_strId ≝
λsid,sid':strId.
 (eqc ? (str_elem sid) (str_elem sid'))⊗
 (eqc ? (id_elem sid) (id_elem sid')).

nlemma strid_destruct_1 : ∀x1,x2,y1,y2.mk_strId x1 y1 = mk_strId x2 y2 → x1 = x2.
 #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_strId x2 y2 with [ mk_strId a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma strid_destruct_2 : ∀x1,x2,y1,y2.mk_strId x1 y1 = mk_strId x2 y2 → y1 = y2.
 #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_strId x2 y2 with [ mk_strId _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqstrid : symmetricT strId bool eq_strId.
 #si1; #si2;
 nchange with (
  ((eqc ? (str_elem si1) (str_elem si2))⊗(eqc ? (id_elem si1) (id_elem si2))) =
  ((eqc ? (str_elem si2) (str_elem si1))⊗(eqc ? (id_elem si2) (id_elem si1))));
 nrewrite > (symmetric_eqc ? (str_elem si1) (str_elem si2));
 nrewrite > (symmetric_eqc ? (id_elem si1) (id_elem si2));
 napply refl_eq.
nqed.

nlemma eqstrid_to_eq : ∀s,s'.eq_strId s s' = true → s = s'.
 #si1; #si2;
 nelim si1;
 #l1; #n1;
 nelim si2;
 #l2; #n2; #H;
 nchange in H:(%) with (((eqc ? l1 l2)⊗(eqc ? n1 n2)) = true);
 nrewrite > (eqc_to_eq ? l1 l2 (andb_true_true_l … H));
 nrewrite > (eqc_to_eq ? n1 n2 (andb_true_true_r … H));
 napply refl_eq.
nqed.

nlemma eq_to_eqstrid : ∀s,s'.s = s' → eq_strId s s' = true.
 #si1; #si2;
 nelim si1;
 #l1; #n1;
 nelim si2;
 #l2; #n2; #H;
 nchange with (((eqc ? l1 l2)⊗(eqc ? n1 n2)) = true);
 nrewrite > (strid_destruct_1 … H);
 nrewrite > (strid_destruct_2 … H);
 nrewrite > (eq_to_eqc ? l2 l2 (refl_eq …));
 nrewrite > (eq_to_eqc ? n2 n2 (refl_eq …));
 nnormalize;
 napply refl_eq.
nqed.

nlemma decidable_strid_aux1 : ∀s1,n1,s2,n2.s1 ≠ s2 → (mk_strId s1 n1) ≠ (mk_strId s2 n2).
 #s1; #n1; #s2; #n2;
 nnormalize; #H; #H1;
 napply (H (strid_destruct_1 … H1)).
nqed.

nlemma decidable_strid_aux2 : ∀s1,n1,s2,n2.n1 ≠ n2 → (mk_strId s1 n1) ≠ (mk_strId s2 n2).
 #s1; #n1; #s2; #n2;
 nnormalize; #H; #H1;
 napply (H (strid_destruct_2 … H1)).
nqed.

nlemma decidable_strid : ∀x,y:strId.decidable (x = y).
 #x; nelim x; #s1; #n1;
 #y; nelim y; #s2; #n2;
 nnormalize;
 napply (or2_elim (s1 = s2) (s1 ≠ s2) ? (decidable_c ? s1 s2) …);
 ##[ ##2: #H; napply (or2_intro2 … (decidable_strid_aux1 … H))
 ##| ##1: #H; napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_c ? n1 n2) …);
          ##[ ##2: #H1; napply (or2_intro2 … (decidable_strid_aux2 … H1))
          ##| ##1: #H1; nrewrite > H; nrewrite > H1;
                        napply (or2_intro1 … (refl_eq ? (mk_strId s2 n2)))
          ##]
 ##]
nqed.

nlemma neqstrid_to_neq : ∀sid1,sid2:strId.(eq_strId sid1 sid2 = false) → (sid1 ≠ sid2).
 #sid1; nelim sid1; #s1; #n1;
 #sid2; nelim sid2; #s2; #n2;
 nchange with ((((eqc ? s1 s2) ⊗ (eqc ? n1 n2)) = false) → ?);
 #H;
 napply (or2_elim ((eqc ? s1 s2) = false) ((eqc ? n1 n2) = false) ? (andb_false2 … H) …);
 ##[ ##1: #H1; napply (decidable_strid_aux1 … (neqc_to_neq … H1))
 ##| ##2: #H1; napply (decidable_strid_aux2 … (neqc_to_neq … H1))
 ##]
nqed.

nlemma strid_destruct : ∀s1,s2,n1,n2.(mk_strId s1 n1) ≠ (mk_strId s2 n2) → s1 ≠ s2 ∨ n1 ≠ n2.
 #s1; #s2; #n1; #n2;
 nnormalize; #H;
 napply (or2_elim (s1 = s2) (s1 ≠ s2) ? (decidable_c ? s1 s2) …);
 ##[ ##2: #H1; napply (or2_intro1 … H1)
 ##| ##1: #H1; napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_c ? n1 n2) …);
          ##[ ##2: #H2; napply (or2_intro2 … H2)
          ##| ##1: #H2; nrewrite > H1 in H:(%);
                   nrewrite > H2;
                   #H; nelim (H (refl_eq …))
          ##]
 ##]
nqed.

nlemma neq_to_neqstrid : ∀sid1,sid2.sid1 ≠ sid2 → eq_strId sid1 sid2 = false.
 #sid1; nelim sid1; #s1; #n1;
 #sid2; nelim sid2; #s2; #n2;
 #H; nchange with (((eqc ? s1 s2) ⊗ (eqc ? n1 n2)) = false);
 napply (or2_elim (s1 ≠ s2) (n1 ≠ n2) ? (strid_destruct … H) …);
 ##[ ##1: #H1; nrewrite > (neq_to_neqc … H1); nnormalize; napply refl_eq
 ##| ##2: #H1; nrewrite > (neq_to_neqc … H1);
          nrewrite > (symmetric_andbool (eqc ? s1 s2) false);
          nnormalize; napply refl_eq
 ##]
nqed.

nlemma strid_is_comparable : comparable.
 napply (mk_comparable strId);
 ##[ napply (mk_strId (nil ?) O)
 ##| napply (λx.false)
 ##| napply eq_strId
 ##| napply eqstrid_to_eq
 ##| napply eq_to_eqstrid
 ##| napply neqstrid_to_neq
 ##| napply neq_to_neqstrid
 ##| napply decidable_strid
 ##| napply symmetric_eqstrid
 ##]
nqed.

unification hint 0 ≔ ⊢ carr strid_is_comparable ≡ strId.
