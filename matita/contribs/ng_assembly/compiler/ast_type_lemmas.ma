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

include "compiler/ast_type.ma".
include "common/list_utility_lemmas.ma".

(* ************************* *)
(* dimensioni degli elementi *)
(* ************************* *)

(*
ndefinition astbasetype_destruct_aux ≝
Πb1,b2:ast_base_type.ΠP:Prop.b1 = b2 →
 match eq_astbasetype b1 b2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition astbasetype_destruct : astbasetype_destruct_aux.
 #b1; #b2; #P; #H;
 nrewrite < H;
 nelim b1;
 nnormalize;
 napply (λx.x).
nqed.
*)

nlemma eq_to_eqastbasetype : ∀n1,n2.n1 = n2 → eq_astbasetype n1 n2 = true.
 #n1; #n2; #H;
 nrewrite > H;
 nelim n2;
 nnormalize;
 napply refl_eq.
nqed.

nlemma neqastbasetype_to_neq : ∀n1,n2.eq_astbasetype n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_astbasetype n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqastbasetype n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqastbasetype_to_eq : ∀b1,b2.eq_astbasetype b1 b2 = true → b1 = b2.
 #b1; #b2; ncases b1; ncases b2; nnormalize;
 ##[ ##1,5,9: #H; napply refl_eq
 ##| ##*: #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma neq_to_neqastbasetype : ∀n1,n2.n1 ≠ n2 → eq_astbasetype n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_astbasetype n1 n2));
 napply (not_to_not (eq_astbasetype n1 n2 = true) (n1 = n2) ? H);
 napply (eqastbasetype_to_eq n1 n2).
nqed.

nlemma decidable_astbasetype : ∀x,y:ast_base_type.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_astbasetype x y = true) (eq_astbasetype x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqastbasetype_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqastbasetype_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqastbasetype : symmetricT ast_base_type bool eq_astbasetype.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_astbasetype n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqastbasetype n1 n2 H);
          napply (symmetric_eq ? (eq_astbasetype n2 n1) false);
          napply (neq_to_neqastbasetype n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma asttype_destruct_base_base : ∀b1,b2.AST_TYPE_BASE b1 = AST_TYPE_BASE b2 → b1 = b2.
 #b1; #b2; #H;
 nchange with (match AST_TYPE_BASE b2 with [ AST_TYPE_BASE a ⇒ b1 = a | _ ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma asttype_destruct_array_array_1 : ∀x1,x2,y1,y2.AST_TYPE_ARRAY x1 y1 = AST_TYPE_ARRAY x2 y2 → x1 = x2.
 #x1; #x2; #y1; #y2; #H;
 nchange with (match AST_TYPE_ARRAY x2 y2 with [ AST_TYPE_ARRAY a _ ⇒ x1 = a | _ ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma asttype_destruct_array_array_2 : ∀x1,x2,y1,y2.AST_TYPE_ARRAY x1 y1 = AST_TYPE_ARRAY x2 y2 → y1 = y2.
 #x1; #x2; #y1; #y2; #H;
 nchange with (match AST_TYPE_ARRAY x2 y2 with [ AST_TYPE_ARRAY _ b ⇒ y1 = b | _ ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma asttype_destruct_struct_struct : ∀b1,b2.AST_TYPE_STRUCT b1 = AST_TYPE_STRUCT b2 → b1 = b2.
 #b1; #b2; #H;
 nchange with (match AST_TYPE_STRUCT b2 with [ AST_TYPE_STRUCT a ⇒ b1 = a | _ ⇒ False ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

(*
ndefinition asttype_destruct_aux ≝
Πb1,b2:ast_type.ΠP:Prop.b1 = b2 →
 match eq_asttype b1 b2 with [ true ⇒ P → P | false ⇒ P ].

ndefinition asttype_destruct : asttype_destruct_aux.
 #b1; #b2; #P; #H;
 nrewrite > H;
 napply (ast_type_index … b2);
 ##[ ##1: #e; nchange with (match eq_astbasetype e e with [ true ⇒ P → P | false ⇒ P ]);
          nrewrite > (eq_to_eqastbasetype e e (refl_eq …));
          nnormalize; napply (λx.x);
 ##| ##2: #e; #n; #H; nchange with (match (eq_asttype e e)⊗(eq_nat n n) with [ true ⇒ P → P | false ⇒ P]);
          nrewrite > (eq_to_eqnat n n (refl_eq …));
          nrewrite > (symmetric_andbool (eq_asttype e e) true);
          nchange with (match eq_asttype e e with [ true ⇒ P → P | false ⇒ P]);
          napply H;
 ##| ##3: #e; #H; nchange with (match eq_asttype e e with [ true ⇒ P → P | false ⇒ P]);
          napply H;
 ##| ##4: #hh; #tt; #H;
          nchange with (match bfold_right_neList2 ?? tt tt with [ true ⇒ P → P | false ⇒ P ] →
                        match (eq_asttype hh hh)⊗(bfold_right_neList2 ?? tt tt) with [ true ⇒ P → P | false ⇒ P ]);
          #H1;
          ncases (eq_asttype hh hh) in H:(%) ⊢ %; #H;
          ncases (bfold_right_neList2 ? (λx1,x2.eq_asttype x1 x2) tt tt) in H1:(%) ⊢ %; #H1;
          ##[ ##1: nnormalize; napply (λx.x);
          ##| ##3: nnormalize in H:(%) ⊢ %; napply H
          ##| ##*: nnormalize in H1:(%) ⊢ %; napply H1
          ##]
 ##]
nqed.
*)

nlemma eq_to_eqasttype_aux1
 : ∀nl1,nl2.
  ((eq_asttype (AST_TYPE_STRUCT nl1) (AST_TYPE_STRUCT nl2)) = true) →
  ((bfold_right_neList2 ? (λx,y.eq_asttype x y) nl1 nl2) = true).
 #nl1; #nl2; #H;
 napply H.
nqed.

nlemma eq_to_eqasttype : ∀t1,t2.t1 = t2 → eq_asttype t1 t2 = true.
 #t1;
 napply (ast_type_index … t1);
 ##[ ##1: #b1; #t2; ncases t2;
          ##[ ##1: #b2; #H; nrewrite > (asttype_destruct_base_base … H);
                   nchange with ((eq_astbasetype b2 b2) = true);
                   nrewrite > (eq_to_eqastbasetype b2 b2 (refl_eq …));
                   napply refl_eq
          ##| ##2: #st2; #n2; #H; ndestruct (*napply (asttype_destruct … H)*)
          ##| ##3: #nl2; #H; ndestruct (*napply (asttype_destruct … H)*)
          ##]
 ##| ##2: #st1; #n1; #H; #t2; ncases t2;
          ##[ ##2: #st2; #n2; #H1;  nchange with (((eq_asttype st1 st2)⊗(eq_nat n1 n2)) = true);
                   nrewrite > (H st2 (asttype_destruct_array_array_1 … H1));
                   nrewrite > (eq_to_eqnat n1 n2 (asttype_destruct_array_array_2 … H1));
                   nnormalize;
                   napply refl_eq
          ##| ##1: #b2; #H1; ndestruct (*napply (asttype_destruct … H1)*)
          ##| ##3: #nl2; #H1; ndestruct (*napply (asttype_destruct … H1)*)
          ##]
 ##| ##3: #hh1; #H; #t2; ncases t2;
          ##[ ##3: #nl2; ncases nl2;
                   ##[ ##1: #hh2; #H1; nchange with ((eq_asttype hh1 hh2) = true);
                            nrewrite > (H hh2 (nelist_destruct_nil_nil ? hh1 hh2 (asttype_destruct_struct_struct … H1)));
                            napply refl_eq
                   ##| ##2: #hh2; #ll2; #H1;
                            (* !!! ndestruct non va *)
                            nelim (nelist_destruct_nil_cons ? hh1 hh2 ll2 (asttype_destruct_struct_struct … H1))
                   ##]
          ##| ##1: #b2; #H1; ndestruct (*napply (asttype_destruct … H1)*)
          ##| ##2: #st2; #n2; #H1; ndestruct (*napply (asttype_destruct … H1)*)
          ##]
 ##| ##4: #hh1; #ll1; #H; #H1; #t2; ncases t2;
          ##[ ##3: #nl2; ncases nl2;
                   ##[ ##1: #hh2; #H2;
                            (* !!! ndestruct non va *)
                            nelim (nelist_destruct_cons_nil ? hh1 hh2 ll1 (asttype_destruct_struct_struct … H2))
                   ##| ##2: #hh2; #ll2; #H2; nchange with (((eq_asttype hh1 hh2)⊗(bfold_right_neList2 ? (λx,y.eq_asttype x y) ll1 ll2)) = true);
                            nrewrite > (H hh2 (nelist_destruct_cons_cons_1 … (asttype_destruct_struct_struct … H2)));
                            nrewrite > (eq_to_eqasttype_aux1 ll1 ll2 (H1 (AST_TYPE_STRUCT ll2) ?));
                            ##[ ##1: nnormalize; napply refl_eq
                            ##| ##2: nrewrite > (nelist_destruct_cons_cons_2 … (asttype_destruct_struct_struct … H2));
                                     napply refl_eq
                            ##]
                   ##]
          ##| ##1: #b2; #H2; ndestruct (*napply (asttype_destruct … H2)*)
          ##| ##2: #st2; #n2; #H2; ndestruct (*napply (asttype_destruct … H2)*)
          ##]
 ##]
nqed.

nlemma neqasttype_to_neq : ∀n1,n2.eq_asttype n1 n2 = false → n1 ≠ n2.
 #n1; #n2; #H;
 napply (not_to_not (n1 = n2) (eq_asttype n1 n2 = true) …);
 ##[ ##1: napply (eq_to_eqasttype n1 n2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqasttype_to_eq : ∀t1,t2.eq_asttype t1 t2 = true → t1 = t2.
 #t1;
 napply (ast_type_index … t1);
 ##[ ##1: #b1; #t2; ncases t2;
          ##[ ##1: #b2; #H; nchange in H:(%) with ((eq_astbasetype b1 b2) = true);
                   nrewrite > (eqastbasetype_to_eq b1 b2 H);
                   napply refl_eq
          ##| ##2: #st2; #n2; nnormalize; #H; ndestruct (*napply (bool_destruct … H)*)
          ##| ##3: #nl2; nnormalize; #H; ndestruct (*napply (bool_destruct … H)*)
          ##]
 ##| ##2: #st1; #n1; #H; #t2; ncases t2;
          ##[ ##2: #st2; #n2; #H1; nchange in H1:(%) with (((eq_asttype st1 st2)⊗(eq_nat n1 n2)) = true);
                   nrewrite > (H st2 (andb_true_true_l … H1));
                   nrewrite > (eqnat_to_eq n1 n2 (andb_true_true_r … H1));
                   napply refl_eq
          ##| ##1: #b2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##| ##3: #nl2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##3: #hh1; #H; #t2; ncases t2;
          ##[ ##3: #nl2; ncases nl2;
                   ##[ ##1: #hh2; #H1; nchange in H1:(%) with ((eq_asttype hh1 hh2) = true);
                            nrewrite > (H hh2 H1);
                            napply refl_eq
                   ##| ##2: #hh2; #ll2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
                   ##]
          ##| ##1: #b2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##| ##2: #st2; #n2; nnormalize; #H1; ndestruct (*napply (bool_destruct … H1)*)
          ##]
 ##| ##4: #hh1; #ll1; #H; #H1; #t2; ncases t2;
          ##[ ##3: #nl2; ncases nl2;
                   ##[ ##1: #hh2; nnormalize; #H2; ndestruct (*napply (bool_destruct … H2)*)
                   ##| ##2: #hh2; #ll2; #H2; nchange in H2:(%) with (((eq_asttype hh1 hh2)⊗(bfold_right_neList2 ? (λx,y.eq_asttype x y) ll1 ll2)) = true);
                            nrewrite > (H hh2 (andb_true_true_l … H2));
                            nrewrite > (asttype_destruct_struct_struct ll1 ll2 (H1 (AST_TYPE_STRUCT ll2) (andb_true_true_r … H2)));
                            napply refl_eq
                   ##]
          ##| ##1: #b2; nnormalize; #H2; ndestruct (*napply (bool_destruct … H2)*)
          ##| ##2: #st2; #n2; nnormalize; #H2; ndestruct (*napply (bool_destruct … H2)*)
          ##]
 ##]
nqed.

nlemma neq_to_neqasttype : ∀n1,n2.n1 ≠ n2 → eq_asttype n1 n2 = false.
 #n1; #n2; #H;
 napply (neqtrue_to_eqfalse (eq_asttype n1 n2));
 napply (not_to_not (eq_asttype n1 n2 = true) (n1 = n2) ? H);
 napply (eqasttype_to_eq n1 n2).
nqed.

nlemma decidable_asttype : ∀x,y:ast_type.decidable (x = y).
 #x; #y; nnormalize;
 napply (or2_elim (eq_asttype x y = true) (eq_asttype x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqasttype_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqasttype_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqasttype : symmetricT ast_type bool eq_asttype.
 #n1; #n2;
 napply (or2_elim (n1 = n2) (n1 ≠ n2) ? (decidable_asttype n1 n2));
 ##[ ##1: #H; nrewrite > H; napply refl_eq
 ##| ##2: #H; nrewrite > (neq_to_neqasttype n1 n2 H);
          napply (symmetric_eq ? (eq_asttype n2 n1) false);
          napply (neq_to_neqasttype n2 n1 (symmetric_neq ? n1 n2 H))
 ##]
nqed.

nlemma isbastbasetype_to_isastbasetype : ∀ast.isb_ast_base_type ast = true → is_ast_base_type ast.
 #ast;
 ncases ast;
 nnormalize;
 ##[ ##1: #t; #H; napply I
 ##| ##2: #t; #n; #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##3: #t; #H; ndestruct (*napply (bool_destruct … H)*)
 ##]
nqed.

nlemma isntbastbasetype_to_isntastbasetype : ∀ast.isntb_ast_base_type ast = true → isnt_ast_base_type ast.
 #ast;
 ncases ast;
 nnormalize;
 ##[ ##1: #t; #H; ndestruct (*napply (bool_destruct … H)*)
 ##| ##2: #t; #n; #H; napply I
 ##| ##3: #l; #H; napply I
 ##]
nqed.
