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

include "compiler/environment.ma".
include "compiler/ast_tree.ma".

(* ********************** *)
(* GESTIONE AMBIENTE FLAT *)
(* ********************** *)

(* ambiente flat *)
inductive var_flatElem : Type ≝
VAR_FLAT_ELEM: aux_strId_type → desc_elem → var_flatElem.

definition get_name_flatVar ≝ λv:var_flatElem.match v with [ VAR_FLAT_ELEM n _ ⇒ n ].
definition get_desc_flatVar ≝ λv:var_flatElem.match v with [ VAR_FLAT_ELEM _ d ⇒ d ].

definition aux_flatEnv_type ≝ list var_flatElem.

definition empty_flatEnv ≝ nil var_flatElem.

(* mappa: nome + max + cur *)
inductive map_list : nat → Type ≝
  map_nil: map_list O
| map_cons: ∀n.option nat → map_list n → map_list (S n).

definition defined_mapList ≝
λd.λl:map_list d.match l with [ map_nil ⇒ False | map_cons _ _ _ ⇒ True ].

definition cut_first_mapList : Πd.map_list d → ? → map_list (pred d) ≝
λd.λl:map_list d.λp:defined_mapList ? l.
 let value ≝
  match l
   return λX.λY:map_list X.defined_mapList X Y → map_list (pred X)
  with
   [ map_nil ⇒ λp:defined_mapList O map_nil.False_rect ? p
   | map_cons n h t ⇒ λp:defined_mapList (S n) (map_cons n h t).t
   ] p in value.

definition get_first_mapList : Πd.map_list d → ? → option nat ≝
λd.λl:map_list d.λp:defined_mapList ? l.
 let value ≝
  match l
   return λX.λY:map_list X.defined_mapList X Y → option nat
  with
   [ map_nil ⇒ λp:defined_mapList O map_nil.False_rect ? p
   | map_cons n h t ⇒ λp:defined_mapList (S n) (map_cons n h t).h
   ] p in value.

inductive map_elem (d:nat) : Type ≝
MAP_ELEM: aux_str_type → nat → map_list (S d) → map_elem d.

definition get_name_mapElem ≝ λd.λm:map_elem d.match m with [ MAP_ELEM n _ _ ⇒ n ].
definition get_max_mapElem ≝ λd.λm:map_elem d.match m with [ MAP_ELEM _ m _ ⇒ m ].
definition get_cur_mapElem ≝ λd.λm:map_elem d.match m with [ MAP_ELEM _ _ c ⇒ c ].

definition aux_map_type ≝ λd.list (map_elem d).

definition empty_map ≝ nil (map_elem O).

lemma defined_mapList_S_to_true :
∀d.∀l:map_list (S d).defined_mapList (S d) l = True.
 intros;
 inversion l;
  [ intros; destruct H
  | intros; simplify; reflexivity
  ]
qed.

lemma defined_mapList_get :
 ∀d.∀h:map_elem d.defined_mapList (S d) (get_cur_mapElem d h).
 intros 2;
 rewrite > (defined_mapList_S_to_true ? (get_cur_mapElem d h));
 apply I.
qed.

(* get_id *)
let rec get_id_map_aux d (map:aux_map_type d) (name:aux_str_type) on map : option nat ≝
 match map with
  [ nil ⇒ None ?
  | cons h t ⇒ match eqStr_str name (get_name_mapElem d h) with
                [ true ⇒ get_first_mapList (S d) (get_cur_mapElem d h) (defined_mapList_get ??)
                | false ⇒ get_id_map_aux d t name
                ]
  ].

definition get_id_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_id_map_aux d map name with [ None ⇒ O | Some x ⇒ x ].

(* get_max *)
let rec get_max_map_aux d (map:aux_map_type d) (name:aux_str_type) on map ≝
 match map with
  [ nil ⇒ None ?
  | cons h t ⇒ match eqStr_str name (get_name_mapElem d h) with
                [ true ⇒ Some ? (get_max_mapElem d h)
                | false ⇒ get_max_map_aux d t name
                ]
  ].

definition get_max_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_max_map_aux d map name with [ None ⇒ O | Some x ⇒ x ].

(* check_id *)
definition check_id_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_id_map_aux d map name with [ None ⇒ False | Some _ ⇒ True ].

definition checkb_id_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_id_map_aux d map name with [ None ⇒ false | Some _ ⇒ true ].

lemma checkbidmap_to_checkidmap :
 ∀d.∀map:aux_map_type d.∀name.
  checkb_id_map d map name = true → check_id_map d map name.
 unfold checkb_id_map;
 unfold check_id_map;
 intros 3;
 elim (get_id_map_aux d map name) 0;
 [ simplify; intro; destruct H
 | simplify; intros; apply I
 ].
qed.

definition checknot_id_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_id_map_aux d map name with [ None ⇒ True | Some _ ⇒ False ].

definition checknotb_id_map ≝ λd.λmap:aux_map_type d.λname:aux_str_type.
 match get_id_map_aux d map name with [ None ⇒ true | Some _ ⇒ false ].

lemma checknotbidmap_to_checknotidmap :
 ∀d.∀map:aux_map_type d.∀name.
  checknotb_id_map d map name = true → checknot_id_map d map name.
 unfold checknotb_id_map;
 unfold checknot_id_map;
 intros 3;
 elim (get_id_map_aux d map name) 0;
 [ simplify; intro; apply I
 | simplify; intros; destruct H
 ].
qed.

(* get_desc *)
let rec get_desc_flatEnv_aux (fe:aux_flatEnv_type) (name:aux_strId_type) on fe ≝
 match fe with
  [ nil ⇒ None ?
  | cons h t ⇒ match eqStrId_str name (get_name_flatVar h) with
               [ true ⇒ Some ? (get_desc_flatVar h)
               | false ⇒ get_desc_flatEnv_aux t name
               ]
  ].

definition get_desc_flatEnv ≝ λfe:aux_flatEnv_type.λstr:aux_strId_type.
 match get_desc_flatEnv_aux fe str with
  [ None ⇒ DESC_ELEM true (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) | Some x ⇒ x ].

definition check_desc_flatEnv ≝ λfe:aux_flatEnv_type.λstr:aux_strId_type.
 match get_desc_flatEnv_aux fe str with [ None ⇒ False | Some _ ⇒ True ].

definition checkb_desc_flatEnv ≝ λfe:aux_flatEnv_type.λstr:aux_strId_type.
 match get_desc_flatEnv_aux fe str with [ None ⇒ false | Some _ ⇒ true ].

lemma checkbdescflatenv_to_checkdescflatenv :
 ∀fe,str.checkb_desc_flatEnv fe str = true → check_desc_flatEnv fe str.
 unfold checkb_desc_flatEnv;
 unfold check_desc_flatEnv;
 intros 2;
 elim (get_desc_flatEnv_aux fe str) 0;
 [ simplify; intro; destruct H
 | simplify; intros; apply I
 ].
qed.

definition checknot_desc_flatEnv ≝ λfe:aux_flatEnv_type.λstr:aux_strId_type.
 match get_desc_flatEnv_aux fe str with [ None ⇒ True | Some _ ⇒ False ].

definition checknotb_desc_flatEnv ≝ λfe:aux_flatEnv_type.λstr:aux_strId_type.
 match get_desc_flatEnv_aux fe str with [ None ⇒ true | Some _ ⇒ false ].

lemma checknotbdescflatenv_to_checknotdescflatenv :
 ∀fe,str.checknotb_desc_flatEnv fe str = true → checknot_desc_flatEnv fe str.
 unfold checknotb_desc_flatEnv;
 unfold checknot_desc_flatEnv;
 intros 2;
 elim (get_desc_flatEnv_aux fe str) 0;
 [ simplify; intro; apply I
 | simplify; intros; destruct H
 ].
qed.

(* leave: elimina la testa (il "cur" corrente) *)
let rec leave_map d (map:aux_map_type (S d)) on map ≝
 match map with
  [ nil ⇒ []
  | cons h t ⇒
   (MAP_ELEM d
             (get_name_mapElem (S d) h)
             (get_max_mapElem (S d) h)
             (cut_first_mapList ? (get_cur_mapElem (S d) h) (defined_mapList_get ??))
   )::(leave_map d t)
  ].

(* enter: propaga in testa la vecchia testa (il "cur" precedente) *)
let rec enter_map d (map:aux_map_type d) on map ≝
 match map with
  [ nil ⇒ []
  | cons h t ⇒
   (MAP_ELEM (S d)
             (get_name_mapElem d h)
             (get_max_mapElem d h)
             (map_cons (S d)
                       (get_first_mapList ? (get_cur_mapElem d h) (defined_mapList_get ??))
                       (get_cur_mapElem d h))
   )::(enter_map d t)
  ].

(* aggiungi descrittore *)
let rec new_map_elem_from_depth_aux (d:nat) on d ≝
 match d
  return λd.map_list d
 with
  [ O ⇒ map_nil
  | S n ⇒ map_cons n (None ?) (new_map_elem_from_depth_aux n)
  ].

let rec new_max_map_aux d (map:aux_map_type d) (name:aux_str_type) (max:nat) on map ≝
 match map with
  [ nil ⇒ []
  | cons h t ⇒ match eqStr_str name (get_name_mapElem d h) with
                [ true ⇒ (MAP_ELEM d name max (map_cons d (Some ? max) (cut_first_mapList (S d) (get_cur_mapElem d h) (defined_mapList_get ??))))::t
                | false ⇒ h::(new_max_map_aux d t name max)
                ] 
  ].

definition add_desc_env_flatEnv_map ≝
λd.λmap:aux_map_type d.λstr.
 match get_max_map_aux d map str with
  [ None ⇒ map@[ MAP_ELEM d str O (map_cons d (Some ? O) (new_map_elem_from_depth_aux d)) ]
  | Some x ⇒ new_max_map_aux d map str (S x)
  ].

definition add_desc_env_flatEnv_fe ≝
λd.λmap:aux_map_type d.λfe.λstr.λc.λdesc.
 fe@[ VAR_FLAT_ELEM (STR_ID str match get_max_map_aux d map str with [ None ⇒ O | Some x ⇒ (S x)])
                    (DESC_ELEM c desc) ].

let rec build_trasfEnv_env (d:nat) (trsf:list (Prod3T aux_str_type bool ast_type)) on trsf : aux_env_type d → aux_env_type d ≝
 match trsf with
  [ nil ⇒ (λx.x)
  | cons h t ⇒ (λx.(build_trasfEnv_env d t) (add_desc_env d x (fst3T ??? h) (snd3T ??? h) (thd3T ??? h)))
  ].

let rec build_trasfEnv_mapFe (d:nat) (trsf:list (Prod3T aux_str_type bool ast_type)) on trsf :
 Prod (aux_map_type d) aux_flatEnv_type → Prod (aux_map_type d) aux_flatEnv_type ≝
 match trsf with
  [ nil ⇒ (λx.x)
  | cons h t ⇒ (λx.(build_trasfEnv_mapFe d t)
                   (pair ?? (add_desc_env_flatEnv_map d (fst ?? x) (fst3T ??? h))
                            (add_desc_env_flatEnv_fe d (fst ?? x) (snd ?? x) (fst3T ??? h) (snd3T ??? h) (thd3T ??? h))))
  ].

(* ********************************************* *)

(* fe <= fe' *)
definition eq_flatEnv_elem ≝
λe1,e2.match e1 with
 [ VAR_FLAT_ELEM sId1 d1 ⇒ match e2 with
  [ VAR_FLAT_ELEM sId2 d2 ⇒ (eqStrId_str sId1 sId2)⊗(eqDesc_elem d1 d2) ]].

lemma eq_to_eqflatenv : ∀e1,e2.e1 = e2 → eq_flatEnv_elem e1 e2 = true.
 intros 3;
 rewrite < H;
 elim e1;
 simplify;
 rewrite > (eq_to_eqstrid a a (refl_eq ??));
 rewrite > (eq_to_eqdescelem d d (refl_eq ??));
 reflexivity.
qed.

lemma eqflatenv_to_eq : ∀e1,e2.eq_flatEnv_elem e1 e2 = true → e1 = e2.
 intros 2;
 elim e1 0;
 elim e2 0;
 intros 4;
 simplify;
 intro;
 rewrite > (eqstrid_to_eq a1 a (andb_true_true ?? H));
 rewrite > (eqdescelem_to_eq d1 d (andb_true_true_r ?? H));
 reflexivity.
qed.

let rec le_flatEnv (fe,fe':aux_flatEnv_type) on fe ≝
match fe with
  [ nil ⇒ true
  | cons h tl ⇒ match fe' with
   [ nil ⇒ false | cons h' tl' ⇒ (eq_flatEnv_elem h h')⊗(le_flatEnv tl tl') ]
  ].

lemma eq_to_leflatenv : ∀e1,e2.e1 = e2 → le_flatEnv e1 e2 = true.
 intros 3;
 rewrite < H;
 elim e1;
 [ reflexivity
 | simplify;
   rewrite > (eq_to_eqflatenv a a (refl_eq ??));
   rewrite > H1;
   reflexivity
 ].
qed.

lemma leflatenv_to_le : ∀fe,fe'.le_flatEnv fe fe' = true → ∃x.fe@x=fe'.
 intro;
 elim fe 0;
 [ intros; exists; [ apply fe' | reflexivity ]
 | intros 4; elim fe';
   [ simplify in H1:(%); destruct H1
   | simplify in H2:(%);
     rewrite < (eqflatenv_to_eq a a1 (andb_true_true ?? H2));
     cases (H l1 (andb_true_true_r ?? H2));
     simplify;
     rewrite < H3;
     exists; [ apply x | reflexivity ]
   ]
 ].
qed.

lemma le_to_leflatenv : ∀fe,x.le_flatEnv fe (fe@x) = true.
 intros;
 elim fe;
 [ simplify;
   reflexivity
 | simplify;
   rewrite > (eq_to_eqflatenv a a (refl_eq ??));
   rewrite > H;
   reflexivity
 ].
qed.

lemma leflatenv_to_check :
 ∀fe,fe',str.
  (le_flatEnv fe fe' = true) →
  (check_desc_flatEnv fe str) →
  (check_desc_flatEnv fe' str).
 intros 4;
 cases (leflatenv_to_le fe fe' H);
 rewrite < H1;
 elim fe 0;
 [ intro; simplify in H2:(%); elim H2;
 | intros 3;
   simplify;
   cases (eqStrId_str str (get_name_flatVar a));
   [ simplify; intro; apply H3
   | simplify; apply H2
   ]
 ].
qed.

lemma leflatenv_to_get :
 ∀fe,fe',str.
  (le_flatEnv fe fe' = true) →
  (check_desc_flatEnv fe str) →
  (get_desc_flatEnv fe str = get_desc_flatEnv fe' str).
 intros 4;
 cases (leflatenv_to_le fe fe' H);
 rewrite < H1;
 elim fe 0;
 [ intro;
   simplify in H2:(%);
   elim H2
 | simplify;
   intros 2;
   cases (eqStrId_str str (get_name_flatVar a));
   [ simplify;
     intros;
     reflexivity
   | simplify;
     unfold check_desc_flatEnv;
     unfold get_desc_flatEnv;
     cases (get_desc_flatEnv_aux l str);
     [ simplify; intros; elim H3
     | simplify; intros; rewrite < (H2 H3); reflexivity
     ]
   ]
 ].
qed.

lemma leflatenv_trans :
 ∀fe,fe',fe''.
  le_flatEnv fe fe' = true →
  le_flatEnv fe' fe'' = true →
  le_flatEnv fe fe'' = true.
 intros 4;
 cases (leflatenv_to_le fe ? H);
 rewrite < H1;
 intro;
 cases (leflatenv_to_le (fe@x) fe'' H2);
 rewrite < H3;
 rewrite > associative_append;
 apply (le_to_leflatenv fe ?).
qed.

lemma env_map_flatEnv_add_aux_fe_al :
 ∀trsf.∀d.∀m:aux_map_type d.∀a,l.
  snd ?? (build_trasfEnv_mapFe d trsf (pair ?? m (a::l))) =
  a::(snd ?? (build_trasfEnv_mapFe d trsf (pair ?? m l))).
 intro;
 elim trsf;
 [ simplify; reflexivity
 | simplify;
   elim a;
   simplify;
   rewrite > (H ????);
   reflexivity
 ].
qed.

lemma env_map_flatEnv_add_aux_fe_l :
 ∀trsf.∀d.∀m:aux_map_type d.∀l.
  snd ?? (build_trasfEnv_mapFe d trsf (pair ?? m l)) =
  l@(snd ?? (build_trasfEnv_mapFe d trsf (pair ?? m []))).
 intros;
 elim l;
 [ simplify; reflexivity
 | rewrite > (env_map_flatEnv_add_aux_fe_al ????);
   rewrite > H;
   reflexivity
 ].
qed.

lemma env_map_flatEnv_add_aux_fe :
 ∀d.∀map:aux_map_type d.∀fe,trsf.
  ∃x.fe@x = (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))).
 intros 3;
 elim fe 0;
 [ simplify;
   intro;
   exists;
   [ apply (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map [])))
   | reflexivity
   ]
 | intros 4;
   exists;
   [ apply (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map [])))
   | rewrite > (env_map_flatEnv_add_aux_fe_al trsf d map a l);
     rewrite > (env_map_flatEnv_add_aux_fe_l trsf d map l);
     rewrite < (cons_append_commute ????);
     reflexivity
   ]
 ].
qed.

lemma buildtrasfenvadd_to_le :
 ∀d.∀m:aux_map_type d.∀fe,trsf.
  le_flatEnv fe (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? m fe))) = true.
 intros 4;
  cases (env_map_flatEnv_add_aux_fe d m fe trsf);
 rewrite < H;
 rewrite > (le_to_leflatenv fe x);
 reflexivity.
qed.

(* ********************************************* *)

(* miscellanea *)
lemma leave_env_enter_env : ∀d.∀e:aux_env_type d.leave_env d (enter_env d e) = e.
 intros;
 elim e;
 reflexivity.
qed.

lemma leave_map_enter_map : ∀d.∀map. leave_map d (enter_map d map) = map.
 intros;
 elim map;
  [ reflexivity
  | simplify;
    rewrite > H;
    cases a;
    simplify;
    reflexivity
  ]
qed.

lemma leave_add_enter_env_aux :
 ∀d.∀a:aux_env_type d.∀trsf.∀c.
  ∃b.build_trasfEnv_env (S d) trsf (env_cons d c a) = (env_cons d b a).
 intros 3;
 elim trsf;
 [ simplify; exists; [ apply c | reflexivity ]
 | simplify; apply H
 ].
qed.

lemma leave_add_enter_env :
 ∀d.∀e:aux_env_type d.∀trsf.
  leave_env d (build_trasfEnv_env (S d) trsf (enter_env d e)) = e.
 intros;
 unfold enter_env;
 lapply (leave_add_enter_env_aux d e trsf []);
 cases Hletin;
 rewrite > H;
 simplify;
 reflexivity.
qed.

(* ********************************************* *)

(* invariante a un livello *)
definition env_to_flatEnv_inv_one_level ≝
 λd.λe:aux_env_type d.λmap:aux_map_type d.λfe:aux_flatEnv_type.
  ∀str.
   check_desc_env d e str →
    check_id_map d map str ∧
    check_desc_flatEnv fe (STR_ID str (get_id_map d map str)) ∧
    get_desc_env d e str = get_desc_flatEnv fe (STR_ID str (get_id_map d map str)).

(* invariante su tutti i livelli *)
let rec env_to_flatEnv_inv (d:nat) : aux_env_type d → aux_map_type d → aux_flatEnv_type → Prop ≝
 match d
  return λd.aux_env_type d → aux_map_type d → aux_flatEnv_type → Prop
 with
  [ O ⇒ λe:aux_env_type O.λmap:aux_map_type O.λfe:aux_flatEnv_type.
   env_to_flatEnv_inv_one_level O e map fe
  | S n ⇒ λe:aux_env_type (S n).λmap:aux_map_type (S n).λfe:aux_flatEnv_type.
   env_to_flatEnv_inv_one_level (S n) e map fe ∧
   env_to_flatEnv_inv n (leave_env n e) (leave_map n map) fe
  ].

(* invariante full -> invariante a un livello *)
lemma env_to_flatEnv_inv_last :
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv_one_level d e map fe.
 intro;
 cases d;
 intros;
  [ apply H
  | simplify in H;
    apply (proj1 ?? H)
  ]
qed.

(* invariante caso base *)
lemma env_map_flatEnv_empty_aux : env_to_flatEnv_inv O empty_env empty_map empty_flatEnv.
 unfold env_to_flatEnv_inv;
 unfold empty_env;
 unfold empty_map;
 unfold empty_flatEnv;
 simplify;
 intros;
 elim H.
qed.

(* invariante & leflatenv *)
lemma leflatenv_to_inv :
 ∀d.∀e.∀map:aux_map_type d.∀fe,fe'.
  le_flatEnv fe fe' = true →
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv d e map fe'.
 intro;
 elim d;
 [ simplify;
   unfold env_to_flatEnv_inv_one_level;
   intros;
   split;
   [ split;
     [ lapply (H1 str H2);
       apply (proj1 ?? (proj1 ?? Hletin))
     | lapply (H1 str H2);
       apply (leflatenv_to_check fe fe' ? H (proj2 ?? (proj1 ?? Hletin)))
     ]
   | lapply (H1 str H2);
     rewrite < (leflatenv_to_get fe fe' ? H (proj2 ?? (proj1 ?? Hletin)));
     apply (proj2 ?? Hletin)
   ]
 | simplify in H2 ⊢ %;
   cases H2;
   split;
   [ unfold env_to_flatEnv_inv_one_level;
     intros;
     split;
     [ split;
       [ lapply (H3 str H5);
         apply (proj1 ?? (proj1 ?? Hletin))
       | lapply (H3 str H5);
         apply (leflatenv_to_check fe fe' ? H1 (proj2 ?? (proj1 ?? Hletin)))
       ]
     | lapply (H3 str H5);
       rewrite < (leflatenv_to_get fe fe' ? H1 (proj2 ?? (proj1 ?? Hletin)));
       apply (proj2 ?? Hletin)
     ]
   | apply (H ???? H1 H4)
   ]
 ].
qed.

(* invariante & enter *)
lemma getidmap_to_enter :
 ∀d.∀m:aux_map_type d.∀str.
  get_id_map_aux (S d) (enter_map d m) str = get_id_map_aux d m str.
 intros;
 elim m;
 [ simplify; reflexivity
 | simplify; rewrite > H; reflexivity
 ]
qed.

lemma checkdescenter_to_checkdesc :
 ∀d.∀e:aux_env_type d.∀str.
  check_desc_env (S d) (enter_env d e) str →
  check_desc_env d e str.
 intros;
 unfold enter_env in H:(%);
 simplify in H:(%);
 apply H.
qed.


lemma env_map_flatEnv_enter_aux : 
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv (S d) (enter_env d e) (enter_map d map) fe.
 intro;
 elim d;
 [ simplify in H;
   split;
   [ unfold env_to_flatEnv_inv_one_level;
     intros;
     split;
     [ split;
       [ unfold check_id_map;
         rewrite > (getidmap_to_enter ???);
         apply (proj1 ?? (proj1 ?? (H str (checkdescenter_to_checkdesc ??? H1))))
       | unfold get_id_map;
         rewrite > (getidmap_to_enter ???);
         apply (proj2 ?? (proj1 ?? (H str (checkdescenter_to_checkdesc ??? H1))))
       ]
     | unfold get_id_map;
       rewrite > (getidmap_to_enter ???);
       apply (proj2 ?? (H str (checkdescenter_to_checkdesc ??? H1)))
     ]
   | rewrite > leave_env_enter_env;
     rewrite > leave_map_enter_map;
     change with (env_to_flatEnv_inv_one_level O e map fe);
     apply H
   ]
 | split;
   [ cases H1;
     simplify in H2;
     unfold env_to_flatEnv_inv_one_level;
     intros;
     split;
     [ split;
       [ unfold check_id_map;
         rewrite > (getidmap_to_enter ???);
         apply (proj1 ?? (proj1 ?? (H2 str (checkdescenter_to_checkdesc ??? H4))))
       | unfold get_id_map;
         rewrite > (getidmap_to_enter ???);
         apply (proj2 ?? (proj1 ?? (H2 str (checkdescenter_to_checkdesc ??? H4))))
       ]
     | unfold get_id_map;
       rewrite > (getidmap_to_enter ???);
       apply (proj2 ?? (H2 str (checkdescenter_to_checkdesc ??? H4)))
     ]
   | rewrite > leave_env_enter_env;
     rewrite > leave_map_enter_map;
     change with (env_to_flatEnv_inv (S n) e map fe);
     apply H1
   ]
 ]
qed.

(* invariante & leave *)
lemma env_map_flatEnv_leave_aux :
 ∀d.∀e:aux_env_type (S d).∀map:aux_map_type (S d).∀fe.∀trsf.
  env_to_flatEnv_inv (S d) (build_trasfEnv_env (S d) trsf e) map fe →
  env_to_flatEnv_inv d (leave_env d (build_trasfEnv_env (S d) trsf e)) (leave_map d map) fe.
 intros;
 simplify in H;
 cases H;
 apply H2.
qed.

(* invariante & add *)
definition occurs_in_trsf ≝
λtrsf:list (Prod3T aux_str_type bool ast_type).λstr.
 fold_right_list ?? (λhe,b.eqStr_str (fst3T ??? he) str ⊕ b) false trsf.

lemma occurs_in_subTrsf_r :
 ∀a,l,str.
  occurs_in_trsf (a::l) str = false →
  occurs_in_trsf l str = false.
 intros;
 simplify in H:(%);
 rewrite > (orb_false_false_r ?? H);
 reflexivity.
qed.

lemma occurs_in_subTrsf_l :
 ∀a,l,str.
  occurs_in_trsf (a::l) str = false →
  eqStr_str (fst3T ??? a) str = false.
 intros;
 simplify in H:(%);
 rewrite > (orb_false_false ?? H);
 reflexivity.
qed.

axiom get_id_map_aux_add_not_occurs :
 ∀d.∀map:aux_map_type d.∀fe,trsf,str.
  occurs_in_trsf trsf str = false →
  get_id_map_aux d map str =
  get_id_map_aux d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str.

lemma get_id_map_add_not_occurs :
 ∀d.∀map:aux_map_type d.∀fe,trsf,str.
  occurs_in_trsf trsf str = false →
  get_id_map d map str =
  get_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str.
 intros;
 unfold get_id_map;
 rewrite < (get_id_map_aux_add_not_occurs ????? H);
 reflexivity.
qed.

lemma check_id_map_not_occurs :
 ∀d.∀map:aux_map_type d.∀fe.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  check_id_map d map str →
  check_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str.
 intros;
 whd in H1 ⊢ %;
 rewrite < (get_id_map_aux_add_not_occurs ????? H);
 apply H1.
qed.

lemma check_desc_flatEnv_not_occurs :
 ∀d.∀map:aux_map_type d.∀fe.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  check_desc_flatEnv fe (STR_ID str (get_id_map d map str)) →
  check_desc_flatEnv (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe)))
                     (STR_ID str (get_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str)).
 intros;
 rewrite < (get_id_map_add_not_occurs ????? H);
 apply (leflatenv_to_check ??? (buildtrasfenvadd_to_le ????) H1).
qed.

lemma get_desc_flatEnv_not_occurs :
 ∀d.∀map:aux_map_type d.∀fe.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  check_desc_flatEnv fe (STR_ID str (get_id_map d map str)) →
  get_desc_flatEnv (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe)))
                   (STR_ID str (get_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str)) =
  get_desc_flatEnv fe (STR_ID str (get_id_map d map str)).
 intros;
 rewrite < (get_id_map_add_not_occurs ????? H);
 rewrite < (leflatenv_to_get ??? (buildtrasfenvadd_to_le ????) H1);
 reflexivity.
qed.

axiom get_desc_env_aux_not_occurs :
 ∀d.∀e:aux_env_type d.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  get_desc_env_aux d (build_trasfEnv_env d trsf e) str =
  get_desc_env_aux d e str.

lemma get_desc_env_not_occurs :
 ∀d.∀e:aux_env_type d.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  get_desc_env d (build_trasfEnv_env d trsf e) str =
  get_desc_env d e str.
 intros;
 unfold get_desc_env;
 rewrite > (get_desc_env_aux_not_occurs ???? H);
 reflexivity.
qed.

lemma check_desc_env_not_occurs :
 ∀d.∀e:aux_env_type d.∀trsf.∀str.
  occurs_in_trsf trsf str = false →
  check_desc_env d (build_trasfEnv_env d trsf e) str →
  check_desc_env d e str.
 intros 5;
 unfold check_desc_env;
 intro;
 rewrite < (get_desc_env_aux_not_occurs ???? H);
 apply H1.
qed.

axiom get_id_map_aux_add_occurs :
 ∀d.∀map:aux_map_type d.∀fe,trsf,str.
  occurs_in_trsf trsf str = true →
  ∃x.get_id_map_aux d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str = Some ? x.

lemma check_id_map_occurs :
 ∀d.∀map:aux_map_type d.∀fe.∀trsf.∀str.
  occurs_in_trsf trsf str = true →
  check_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str.
 intros;
 cases (get_id_map_aux_add_occurs d map fe trsf str H);
 unfold check_id_map;
 rewrite > H1;
 simplify;
 apply I.
qed.

axiom check_desc_flatEnv_occurs :
 ∀d.∀map:aux_map_type d.∀fe.∀trsf.∀str. 
  occurs_in_trsf trsf str = true →
  check_desc_flatEnv (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe)))
                     (STR_ID str (get_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str)).

axiom get_desc_env_eq_get_desc_flatEnv_occurs :
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.∀trsf.∀str.
 occurs_in_trsf trsf str = true →
 get_desc_env d (build_trasfEnv_env d trsf e) str =
 get_desc_flatEnv (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe)))
                  (STR_ID str (get_id_map d (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))) str)).

axiom leave_env_build_trasfEnv :
 ∀d.∀e:aux_env_type (S d).∀trsf.
  leave_env d (build_trasfEnv_env (S d) trsf e) = leave_env d e.

axiom leave_map_build_trasfEnv_mapFe:
 ∀d.∀map:aux_map_type (S d).∀fe.∀trsf.
  leave_map d (fst ?? (build_trasfEnv_mapFe (S d) trsf (pair ?? map fe))) =
  leave_map d map.

lemma env_map_flatEnv_add_aux : 
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.∀trsf.
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv d
                     (build_trasfEnv_env d trsf e)
                     (fst ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe)))
                     (snd ?? (build_trasfEnv_mapFe d trsf (pair ?? map fe))).
 intro;
 cases d;
 [ intros;
   simplify in H;
   simplify;
   intros 2;
   apply (bool_elim ? (occurs_in_trsf trsf str));
   [ intro;
     split
     [ split
       [ apply (check_id_map_occurs ????? H2)
       | apply (check_desc_flatEnv_occurs ????? H2)
       ]
     | apply (get_desc_env_eq_get_desc_flatEnv_occurs ?????? H2)
     ]
   | intro;
     cases (H str (check_desc_env_not_occurs ???? H2 H1));
     split
     [ split
       [ apply (check_id_map_not_occurs ????? H2 (proj1 ?? H3))
       | apply (check_desc_flatEnv_not_occurs ????? H2 (proj2 ?? H3))
       ]
     | rewrite > (get_desc_flatEnv_not_occurs ????? H2 (proj2 ?? H3));
       rewrite > (get_desc_env_not_occurs ???? H2);
       apply H4
     ]
   ]
 | intros;
   simplify in H;
   cases H;
   unfold env_to_flatEnv_inv_one_level in H1;
   split;
   [ intros 2;
     apply (bool_elim ? (occurs_in_trsf trsf str));
     [ intro;
       split
       [ split
         [ apply (check_id_map_occurs ????? H4)
         | apply (check_desc_flatEnv_occurs ????? H4)
         ]
       | apply (get_desc_env_eq_get_desc_flatEnv_occurs ?????? H4)
       ]
     | intro;
       split;
       [ split
         [ apply (check_id_map_not_occurs ????? H4 (proj1 ?? (proj1 ?? (H1 str (check_desc_env_not_occurs ???? H4 H3)))))
         | apply (check_desc_flatEnv_not_occurs ????? H4 (proj2 ?? (proj1 ?? (H1 str (check_desc_env_not_occurs ???? H4 H3)))))
         ]
       | rewrite > (get_desc_flatEnv_not_occurs ????? H4 (proj2 ?? (proj1 ?? (H1 str (check_desc_env_not_occurs ???? H4 H3)))));
         rewrite > (get_desc_env_not_occurs ???? H4);
         apply (proj2 ?? (H1 str (check_desc_env_not_occurs ???? H4 H3)))
       ]
     ]
   | change with (env_to_flatEnv_inv n (leave_env n (build_trasfEnv_env (S n) trsf e))
                 (leave_map n (fst ?? (build_trasfEnv_mapFe (S n) trsf (pair ?? map fe))))
                 (snd ?? (build_trasfEnv_mapFe (S n) trsf (pair ?? map fe))));
     rewrite > leave_map_build_trasfEnv_mapFe;
     rewrite > leave_env_build_trasfEnv;
     apply (leflatenv_to_inv ?????? H2);
     apply buildtrasfenvadd_to_le
   ]
 ].
qed.

lemma env_map_flatEnv_addNil_aux :
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv d
                     (build_trasfEnv_env d [] e)
                     (fst ?? (build_trasfEnv_mapFe d [] (pair ?? map fe)))
                     (snd ?? (build_trasfEnv_mapFe d [] (pair ?? map fe))).
 intros;
 simplify;
 apply H.
qed.

lemma env_map_flatEnv_addSingle_aux :
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe.∀name,const,desc.
  env_to_flatEnv_inv d e map fe →
  env_to_flatEnv_inv d
                     (add_desc_env d e name const desc)
                     (fst ?? (build_trasfEnv_mapFe d [ tripleT ??? name const desc ] (pair ?? map fe)))
                     (snd ?? (build_trasfEnv_mapFe d [ tripleT ??? name const desc ] (pair ?? map fe))).
 intros;
 apply (env_map_flatEnv_add_aux d e map fe [ tripleT ??? name const desc ]);
 apply H.
qed.

lemma env_map_flatEnv_addJoin_aux :
 ∀d.∀e:aux_env_type d.∀map:aux_map_type d.∀fe:aux_flatEnv_type.∀name,const,desc,trsf.
  env_to_flatEnv_inv d
                     (build_trasfEnv_env d trsf (add_desc_env d e name const desc))
                     map fe →
  env_to_flatEnv_inv d
                     (build_trasfEnv_env d ([ tripleT ??? name const desc ]@trsf) e)
                     map fe.
 intros;
 simplify;
 apply H.
qed.

(* ********************************************* *)

lemma newid_from_init :
 ∀d.∀e:aux_env_type d.∀name,const,desc.
  ast_id d (add_desc_env d e name const desc) const desc.
 intros;
 lapply (AST_ID d (add_desc_env d e name const desc) name ?);
 [ elim e;
   simplify;
   rewrite > (eq_to_eqstr ?? (refl_eq ??));
   simplify;
   apply I
 | cut (const = get_const_desc (get_desc_env d (add_desc_env d e name const desc) name) ∧
        desc = get_type_desc (get_desc_env d (add_desc_env d e name const desc) name));
   [ rewrite > (proj1 ?? Hcut) in ⊢ (? ? ? % ?);
     rewrite > (proj2 ?? Hcut) in ⊢ (? ? ? ? %);
     apply Hletin
   | split;
     [ elim e;
       simplify;
       rewrite > (eq_to_eqstr ?? (refl_eq ??));
       simplify;
       reflexivity
     | elim e;
       simplify;
       rewrite > (eq_to_eqstr ?? (refl_eq ??));
       simplify;
       reflexivity
     ]
   ]
 ].
qed.
