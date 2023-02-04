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

include "string/ascii_min.ma".
include "compiler/utility.ma".

(* ************************ *)
(* MANIPOLAZIONE DI STRINGA *)
(* ************************ *)

(* tipo pubblico *)
definition aux_str_type ≝ list ascii_min.

(* empty string *)
definition empty_str ≝ nil ascii_min.

(* is empty ? *)
definition isNull_str ≝
λstr:aux_str_type.match str with
 [ nil ⇒ true | cons _ _ ⇒ false ].

(* strcmp *)
let rec eqStr_str (str,str':aux_str_type) ≝
 match str with
  [ nil ⇒ match str' with
   [ nil => true
   | cons _ _ => false ]
  | cons h t ⇒ match str' with
   [ nil ⇒ false
   | cons h' t' ⇒ (eqAsciiMin h h')⊗(eqStr_str t t')
   ]
  ].

lemma eqex_switch : ∀e1,e2.eq_ex e1 e2 = eq_ex e2 e1.
 intros;
 elim e1;
 elim e2;
 reflexivity.
qed.

lemma eqb8_switch : ∀b1,b2.eq_b8 b1 b2 = eq_b8 b2 b1.
 intros;
 elim b1;
 elim b2;
 unfold eq_b8;
 rewrite > eqex_switch in ⊢ (? ? % ?);
 rewrite > eqex_switch in ⊢ (? ? (? ? %) ?);
 reflexivity.
qed.

lemma eqasciimin_switch : ∀a1,a2.eqAsciiMin a1 a2 = eqAsciiMin a2 a1.
 intros;
 unfold eqAsciiMin;
 rewrite > eqb8_switch in ⊢ (? ? % ?);
 reflexivity.
qed.

lemma eq_to_eqstr : ∀s,s'.s = s' → eqStr_str s s' = true.
 do 2 intro;
 intro;
 rewrite < H;
 elim s;
 [ 1: reflexivity
 | 2: simplify;
      rewrite > (eq_to_eqasciimin a a (refl_eq ??));
      rewrite > H1;
      reflexivity
 ].
qed.

lemma eqstr_to_eq : ∀s,s'.eqStr_str s s' = true → s = s'.
 intros 1;
 elim s 0;
 intros;
 [ simplify in H:(%);
   cases s' in H;
   simplify;
   intros;
   [ reflexivity
   | destruct H
   ]
 | elim s' in H1;
   [ simplify in H1;
     destruct H1
   | simplify in H2;
     lapply (andb_true_true ?? H2);
     lapply (andb_true_true_r ?? H2);
     rewrite > (H ? Hletin1);
     rewrite > (eqasciimin_to_eq ?? Hletin);
     reflexivity
   ]
 ].
qed.

(* strcat *)
definition strCat_str ≝
λstr,str':aux_str_type.str@str'.

(* strlen *)
definition strLen_str ≝ λstr:aux_str_type.len_list ? str.

(* ************ *)
(* STRINGA + ID *)
(* ************ *)

(* tipo pubblico *)
inductive aux_strId_type : Type ≝
 STR_ID: aux_str_type → nat → aux_strId_type.

(* getter *)
definition get_name_strId ≝ λsid:aux_strId_type.match sid with [ STR_ID n _ ⇒ n ].
definition get_id_strId ≝ λsid:aux_strId_type.match sid with [ STR_ID _ d ⇒ d ].

(* confronto *)
definition eqStrId_str ≝
λsid,sid':aux_strId_type.(eqStr_str (get_name_strId sid) (get_name_strId sid'))⊗(eqb (get_id_strId sid) (get_id_strId sid')).

lemma eq_to_eqstrid : ∀s,s'.s = s' → eqStrId_str s s' = true.
 intros 3;
 rewrite < H;
 elim s;
 simplify;
 rewrite > (eq_to_eqstr a a (refl_eq ??));
 rewrite > (eq_to_eqb_true n n (refl_eq ??));
 reflexivity.
qed.

lemma eqstrid_to_eq : ∀s,s'.eqStrId_str s s' = true → s = s'.
 intros 2;
 elim s 0;
 elim s' 0;
 intros 4;
 simplify;
 intro;
 rewrite > (eqstr_to_eq a1 a (andb_true_true ?? H));
 rewrite > (eqb_true_to_eq n1 n (andb_true_true_r ?? H));
 reflexivity.
qed.
