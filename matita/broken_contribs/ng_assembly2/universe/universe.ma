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

include "common/nelist.ma".
include "common/prod.ma".

nlet rec nmember_natList (elem:nat) (l:ne_list nat) on l ≝
 match l with
  [ ne_nil h ⇒ ⊖(eqc ? elem h)
  | ne_cons h t ⇒ match eqc ? elem h with
   [ true ⇒ false | false ⇒ nmember_natList elem t ]
  ].

(* elem presente una ed una sola volta in l *)
nlet rec member_natList (elem:nat) (l:ne_list nat) on l ≝
 match l with
  [ ne_nil h ⇒ eqc ? elem h
  | ne_cons h t ⇒ match eqc ? elem h with
    [ true ⇒ nmember_natList elem t | false ⇒ member_natList elem t ]
  ].

(* costruttore di un sottouniverso:
   S_EL cioe' uno qualsiasi degli elementi del sottouniverso
*)
ninductive S_UN (l:ne_list nat) : Type ≝
 S_EL : Πx:nat.((member_natList x l) = true) → S_UN l.

ndefinition getelem : ∀l.∀e:S_UN l.nat.
 #l; #s; nelim s;
 #u; #dim;
 napply u.
nqed.

ndefinition eq_SUN ≝ λl.λx,y:S_UN l.eq_nat (getelem ? x) (getelem ? y).

ndefinition getdim : ∀l.∀e:S_UN l.member_natList (getelem ? e) l = true.
 #l; #s; nelim s;
 #u; #dim;
 napply dim.
nqed.

nlemma SUN_destruct_1
 : ∀l.∀e1,e2.∀dim1,dim2.S_EL l e1 dim1 = S_EL l e2 dim2 → e1 = e2.
 #l; #e1; #e2; #dim1; #dim2; #H;
 nchange with (match S_EL l e2 dim2 with [ S_EL a _ ⇒ e1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(* destruct universale *)
ndefinition SUN_destruct : ∀l.∀x,y:S_UN l.∀P:Prop.x = y → match eq_SUN l x y with [ true ⇒ P → P | false ⇒ P ].
 #l; #x; nelim x;
 #u1; #dim1;
 #y; nelim y;
 #u2; #dim2;
 #P;
 nchange with (? → (match eq_nat u1 u2 with [ true ⇒ P → P | false ⇒ P ]));
 #H;
 nrewrite > (SUN_destruct_1 l … H);
 nrewrite > (eq_to_eqc ? u2 u2 (refl_eq …));
 nnormalize;
 napply (λx.x).
nqed.

(* eq_to_eqxx universale *)
nlemma eq_to_eqSUN : ∀l.∀x,y:S_UN l.x = y → eq_SUN l x y = true.
 #l; #x; nelim x;
 #u1; #dim1;
 #y; nelim y;
 #u2; #dim2;
 nchange with (? → (eqc ? u1 u2) = true);
 #H; napply (eq_to_eqc ? u1 u2);
 napply (SUN_destruct_1 l … H).
nqed.

(* neqxx_to_neq universale *)
nlemma neqSUN_to_neq : ∀l.∀x,y:S_UN l.eq_SUN l x y = false → x ≠ y.
 #l; #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_SUN l n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqSUN l n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

(* eqxx_to_eq universale *)
(* !!! evidente ma come si fa? *)
naxiom eqSUN_to_eq_aux : ∀l,x,y.((getelem l x) = (getelem l y)) → x = y.

nlemma eqSUN_to_eq : ∀l.∀x,y:S_UN l.eq_SUN l x y = true → x = y.
 #l; #x; #y;
 nchange with (((eqc ? (getelem ? x) (getelem ? y)) = true) → x = y);
 #H; napply (eqSUN_to_eq_aux l x y (eqc_to_eq … H)).
nqed.

(* neq_to_neqxx universale *)
nlemma neq_to_neqSUN : ∀l.∀x,y:S_UN l.x ≠ y → eq_SUN l x y = false.
 #l; #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_SUN l n1 n2));
 napply (not_to_not (eq_SUN l n1 n2 = true) (n1 = n2) ? H);
 napply (eqSUN_to_eq l n1 n2).
nqed.

(* decidibilita' universale *)
nlemma decidable_SUN : ∀l.∀x,y:S_UN l.decidable (x = y).
 #l; #x; #y; nnormalize;
 napply (or2_elim (eq_SUN l x y = true) (eq_SUN l x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqSUN_to_eq l … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqSUN_to_neq l … H))
 ##]
nqed.

(* simmetria di uguaglianza universale *)
nlemma symmetric_eqSUN : ∀l.symmetricT (S_UN l) bool (eq_SUN l).
 #l; #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_SUN l n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqSUN l n1 n2 H);
          napply (symmetric_eq ? (eq_SUN l n2 n1) false);
          napply (neq_to_neqSUN l n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

(* scheletro di funzione generica ad 1 argomento *)
nlet rec farg1_auxT (T:Type) (l:ne_list nat) on l ≝
 match l with
  [ ne_nil _ ⇒ T
  | ne_cons _ t ⇒ ProdT T (farg1_auxT T t)
  ].

nlemma farg1_auxDim : ∀h,t,x.(eqc ? x h) = false → member_natList x (h§§t) = true → member_natList x t = true.
 #h; #t; #x; #H; #H1;
 nnormalize in H1:(%);
 nrewrite > H in H1:(%);
 nnormalize;
 napply (λx.x).
nqed.

nlet rec farg1 (T:Type) (l:ne_list nat) on l ≝
 match l with
  [ ne_nil h ⇒ λarg:farg1_auxT T «£h».λx:S_UN «£h».arg
  | ne_cons h t ⇒ λarg:farg1_auxT T (h§§t).λx:S_UN (h§§t).
   match eqc ? (getelem ? x) h
    return λy.(eqc ? (getelem ? x) h) = y → ?
   with
    [ true ⇒ λp:((eqc ? (getelem ? x) h) = true).fst … arg
    | false ⇒ λp:((eqc ? (getelem ? x) h) = false).
     farg1 T t
      (snd … arg)
      (S_EL t (getelem ? x) (farg1_auxDim h t (getelem ? x) p (getdim ? x)))
    ] (refl_eq ? (eqc ? (getelem ? x) h))
  ].

(* scheletro di funzione generica a 2 argomenti *)
nlet rec farg2 (T:Type) (l,lfix:ne_list nat) on l ≝
 match l with
  [ ne_nil h ⇒ λarg:farg1_auxT (farg1_auxT T lfix) «£h».λx:S_UN «£h».farg1 T lfix arg
  | ne_cons h t ⇒ λarg:farg1_auxT (farg1_auxT T lfix) (h§§t).λx:S_UN (h§§t).
   match eqc ? (getelem ? x) h
    return λy.(eqc ? (getelem ? x) h) = y → ?
   with
    [ true ⇒ λp:((eqc ? (getelem ? x) h) = true).farg1 T lfix (fst … arg)
    | false ⇒ λp:((eqc ? (getelem ? x) h) = false).
     farg2 T t lfix
      (snd … arg)
      (S_EL t (getelem ? x) (farg1_auxDim h t (getelem ? x) p (getdim ? x)))
    ] (refl_eq ? (eqc ? (getelem ? x) h))
  ].

(* esempio0: universo ottale *)
ndefinition oct0 ≝ O.
ndefinition oct1 ≝ nat1.
ndefinition oct2 ≝ nat2.
ndefinition oct3 ≝ nat3.
ndefinition oct4 ≝ nat4.
ndefinition oct5 ≝ nat5.
ndefinition oct6 ≝ nat6.
ndefinition oct7 ≝ nat7.

ndefinition oct_UN ≝ « oct0 ; oct1 ; oct2 ; oct3 ; oct4 ; oct5 ; oct6 £ oct7 ».

ndefinition uoct0 ≝ S_EL oct_UN oct0 (refl_eq …).
ndefinition uoct1 ≝ S_EL oct_UN oct1 (refl_eq …).
ndefinition uoct2 ≝ S_EL oct_UN oct2 (refl_eq …).
ndefinition uoct3 ≝ S_EL oct_UN oct3 (refl_eq …).
ndefinition uoct4 ≝ S_EL oct_UN oct4 (refl_eq …).
ndefinition uoct5 ≝ S_EL oct_UN oct5 (refl_eq …).
ndefinition uoct6 ≝ S_EL oct_UN oct6 (refl_eq …).
ndefinition uoct7 ≝ S_EL oct_UN oct7 (refl_eq …).

(* esempio1: NOT ottale *)
ndefinition octNOT ≝
 farg1 (S_UN oct_UN) oct_UN
  (pair … uoct7 (pair … uoct6 (pair … uoct5 (pair … uoct4 (pair … uoct3 (pair … uoct2 (pair … uoct1 uoct0))))))). 

(* esempio2: AND ottale *)
ndefinition octAND0 ≝ pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct0 uoct0)))))).
ndefinition octAND1 ≝ pair … uoct0 (pair … uoct1 (pair … uoct0 (pair … uoct1 (pair … uoct0 (pair … uoct1 (pair … uoct0 uoct1)))))).
ndefinition octAND2 ≝ pair … uoct0 (pair … uoct0 (pair … uoct2 (pair … uoct2 (pair … uoct0 (pair … uoct0 (pair … uoct2 uoct2)))))).
ndefinition octAND3 ≝ pair … uoct0 (pair … uoct1 (pair … uoct2 (pair … uoct3 (pair … uoct0 (pair … uoct1 (pair … uoct2 uoct3)))))).
ndefinition octAND4 ≝ pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct0 (pair … uoct4 (pair … uoct4 (pair … uoct4 uoct4)))))).
ndefinition octAND5 ≝ pair … uoct0 (pair … uoct1 (pair … uoct0 (pair … uoct1 (pair … uoct4 (pair … uoct5 (pair … uoct4 uoct5)))))).
ndefinition octAND6 ≝ pair … uoct0 (pair … uoct0 (pair … uoct2 (pair … uoct2 (pair … uoct4 (pair … uoct4 (pair … uoct6 uoct6)))))).
ndefinition octAND7 ≝ pair … uoct0 (pair … uoct1 (pair … uoct2 (pair … uoct3 (pair … uoct4 (pair … uoct5 (pair … uoct6 uoct7)))))).

ndefinition octAND ≝
 farg2 (S_UN oct_UN) oct_UN oct_UN
  (pair … octAND0 (pair … octAND1 (pair … octAND2 (pair … octAND3 (pair … octAND4 (pair … octAND5 (pair … octAND6 octAND7))))))).

(* ora e' possibile fare
   octNOT uoctX
   octAND uoctX uoctY
*)
