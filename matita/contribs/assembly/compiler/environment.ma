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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "string/string.ma".
include "compiler/ast_type.ma".

(* ***************** *)
(* GESTIONE AMBIENTE *)
(* ***************** *)

(* descrittore: const + type *)
inductive desc_elem : Type ≝
DESC_ELEM: bool → ast_type → desc_elem.

(* elemento: name + desc *)
inductive var_elem : Type ≝
VAR_ELEM: aux_str_type → desc_elem → var_elem.

(* ambiente globale: (ambiente base + ambienti annidati) *)
inductive env_list : nat → Type ≝
  env_nil: list var_elem → env_list O
| env_cons: ∀n.list var_elem → env_list n → env_list (S n).

definition defined_envList ≝
λd.λl:env_list d.match l with [ env_nil _ ⇒ False | env_cons _ _ _ ⇒ True ].

definition cut_first_envList : Πd.env_list d → ? → env_list (pred d) ≝
λd.λl:env_list d.λp:defined_envList ? l.
 let value ≝
  match l
   return λX.λY:env_list X.defined_envList X Y → env_list (pred X)
  with
   [ env_nil h ⇒ λp:defined_envList O (env_nil h).False_rect ? p
   | env_cons n h t ⇒ λp:defined_envList (S n) (env_cons n h t).t
   ] p in value.

definition get_first_envList ≝
λd.λl:env_list d.
 match l with
  [ env_nil h ⇒ h
  | env_cons _ h _ ⇒ h
  ].

lemma defined_envList_S :
∀d.∀l:env_list (S d).defined_envList (S d) l.
 intros;
 inversion l;
  [ intros; destruct H
  | intros; simplify; apply I
  ]
qed.

definition aux_env_type ≝ λd.env_list d.

(* getter *)
definition get_const_desc ≝ λd:desc_elem.match d with [ DESC_ELEM c _ ⇒ c ].
definition get_type_desc ≝ λd:desc_elem.match d with [ DESC_ELEM _ t ⇒ t ].

definition eqDesc_elem ≝ λd,d'.(eq_bool (get_const_desc d) (get_const_desc d'))⊗(eq_ast_type (get_type_desc d) (get_type_desc d')).

lemma eq_to_eqdescelem : ∀d,d'.d = d' → eqDesc_elem d d' = true.
 intros 3;
 rewrite < H;
 elim d;
 simplify;
 rewrite > (eq_to_eqbool b b (refl_eq ??));
 rewrite > (eq_to_eqasttype a a (refl_eq ??));
 reflexivity.
qed.

lemma eqdescelem_to_eq : ∀d,d'.eqDesc_elem d d' = true → d = d'.
 intros 2;
 elim d 0;
 elim d' 0;
 intros 4;
 simplify;
 intro;
 rewrite > (eqbool_to_eq b1 b (andb_true_true ?? H));
 rewrite > (eqasttype_to_eq a1 a (andb_true_true_r ?? H));
 reflexivity.
qed.

definition get_name_var ≝ λv:var_elem.match v with [ VAR_ELEM n _ ⇒ n ].
definition get_desc_var ≝ λv:var_elem.match v with [ VAR_ELEM _ d ⇒ d ].

(* ambiente vuoto *)
definition empty_env ≝ env_nil [].

(* setter *)
definition enter_env ≝ λd.λe:aux_env_type d.env_cons d [] e.
definition leave_env ≝ λd.λe:aux_env_type (S d).cut_first_envList (S d) e (defined_envList_S ??).

(* recupera descrittore da ambiente: il primo trovato, ma e' anche l'unico *)
let rec get_desc_from_lev_env (env:list var_elem) (str:aux_str_type) on env ≝
match env with
 [ nil ⇒ None ?
 | cons h t ⇒ match eqStr_str str (get_name_var h) with
  [ true ⇒ Some ? (get_desc_var h)
  | false ⇒ get_desc_from_lev_env t str ]].

(* recupera descrittore da ambiente globale: il primo trovato *)
let rec get_desc_env_aux d (env:aux_env_type d) (str:aux_str_type) on env ≝
 match env with
  [ env_nil h ⇒ get_desc_from_lev_env h str 
  | env_cons n h t ⇒  match get_desc_from_lev_env h str with 
   [ None ⇒ get_desc_env_aux n t str | Some res' ⇒ Some ? res' ]
  ].

definition check_desc_env ≝ λd.λe:aux_env_type d.λstr:aux_str_type.
 match get_desc_env_aux d e str with [ None ⇒ False | Some _ ⇒ True ].

definition checkb_desc_env ≝ λd.λe:aux_env_type d.λstr:aux_str_type.
 match get_desc_env_aux d e str with [ None ⇒ false | Some _ ⇒ true ].

lemma checkbdescenv_to_checkdescenv : ∀d.∀e:aux_env_type d.∀str.checkb_desc_env d e str = true → check_desc_env d e str.
 unfold checkb_desc_env;
 unfold check_desc_env;
 intros;
 letin K ≝ (get_desc_env_aux d e str);
 elim K;
 [ normalize; autobatch |
   normalize; autobatch ]
qed.

definition get_desc_env ≝ λd.λe:aux_env_type d.λstr:aux_str_type.
 match get_desc_env_aux d e str with
  [ None ⇒ DESC_ELEM true (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) | Some x ⇒ x ].

definition check_not_already_def_env ≝ λd.λe:aux_env_type d.λstr:aux_str_type.
 match get_desc_from_lev_env (get_first_envList d e) str with [ None ⇒ True | Some _ ⇒ False ].

definition checkb_not_already_def_env ≝ λd.λe:aux_env_type d.λstr:aux_str_type.
 match get_desc_from_lev_env (get_first_envList d e) str with [ None ⇒ true | Some _ ⇒ false ].

lemma checkbnotalreadydefenv_to_checknotalreadydefenv : ∀d.∀e:aux_env_type d.∀str.checkb_not_already_def_env d e str = true → check_not_already_def_env d e str.
 unfold checkb_not_already_def_env;
 unfold check_not_already_def_env;
 intros;
 letin K ≝ (get_desc_from_lev_env (get_first_envList d e) str);
 elim K;
 [ normalize; autobatch |
   normalize; autobatch ]
qed.

(* aggiungi descrittore ad ambiente globale: in testa al primo ambiente *)
definition add_desc_env ≝
λd.λe:aux_env_type d.λstr:aux_str_type.λc:bool.λdesc:ast_type.
(*let var ≝ VAR_ELEM str (DESC_ELEM c desc) in*)
 match e
  return λX.λe:aux_env_type X.aux_env_type X
 with
  [ env_nil h ⇒ env_nil ((VAR_ELEM str (DESC_ELEM c desc))::h)
  | env_cons n h t ⇒ env_cons n ((VAR_ELEM str (DESC_ELEM c desc))::h) t
  ].

(* controllo e <= e' *)
definition eq_env_elem ≝
λe1,e2.match e1 with
 [ VAR_ELEM s1 d1 ⇒ match e2 with
  [ VAR_ELEM s2 d2 ⇒ (eqStr_str s1 s2)⊗(eqDesc_elem d1 d2) ]].

lemma eq_to_eqenv : ∀e1,e2.e1 = e2 → eq_env_elem e1 e2 = true.
 intros 3;
 rewrite < H;
 elim e1;
 simplify;
 rewrite > (eq_to_eqstr a a (refl_eq ??));
 rewrite > (eq_to_eqdescelem d d (refl_eq ??));
 reflexivity.
qed.

lemma eqenv_to_eq : ∀e1,e2.eq_env_elem e1 e2 = true → e1 = e2.
 intros 2;
 elim e1 0;
 elim e2 0;
 intros 4;
 simplify;
 intro;
 rewrite > (eqstr_to_eq a1 a (andb_true_true ?? H));
 rewrite > (eqdescelem_to_eq d1 d (andb_true_true_r ?? H));
 reflexivity.
qed.
