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

include "compiler/utility.ma".
include "freescale/word32.ma".

(* ************************* *)
(* dimensioni degli elementi *)
(* ************************* *)

(* usato per definire nell'ast *)
inductive ast_base_type : Type ≝
  AST_BASE_TYPE_BYTE8: ast_base_type
| AST_BASE_TYPE_WORD16: ast_base_type
| AST_BASE_TYPE_WORD32: ast_base_type.

inductive ast_type : Type ≝
  AST_TYPE_BASE: ast_base_type → ast_type
| AST_TYPE_ARRAY: ast_type → nat → ast_type
| AST_TYPE_STRUCT: ne_list ast_type → ast_type.

definition eq_ast_base_type ≝
λt1,t2:ast_base_type.match t1 with
 [ AST_BASE_TYPE_BYTE8 ⇒ match t2 with
  [ AST_BASE_TYPE_BYTE8 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD16 ⇒ match t2 with
  [ AST_BASE_TYPE_WORD16 ⇒ true | _ ⇒ false ]
 | AST_BASE_TYPE_WORD32 ⇒ match t2 with
  [ AST_BASE_TYPE_WORD32 ⇒ true | _ ⇒ false ]
 ].

lemma eqastbasetype_to_eq : ∀t1,t2:ast_base_type.(eq_ast_base_type t1 t2 = true) → (t1 = t2).
 unfold eq_ast_base_type;
 intros;
 elim t1 in H:(%);
 elim t2 in H:(%);
 normalize in H:(%);
 try reflexivity;
 destruct H.
qed.

lemma eq_to_eqastbasetype : ∀t1,t2.t1 = t2 → eq_ast_base_type t1 t2 = true.
 do 2 intro;
 elim t1 0;
 elim t2 0;
 normalize;
 intro;
 try destruct H;
 reflexivity.
qed.

definition eq_ast_type_aux ≝
λT:Type.λf:T → T → bool.
 let rec aux (nl1,nl2:ne_list T) on nl1 ≝
  match nl1 with
   [ ne_nil h ⇒ match nl2 with
    [ ne_nil h' ⇒ f h h'
    | ne_cons h' _ ⇒ false
    ]
   | ne_cons h t ⇒ match nl2 with
    [ ne_nil h' ⇒ false
    | ne_cons h' t' ⇒ (f h h') ⊗ (aux t t')
    ]
   ] in aux.

let rec eq_ast_type (t1,t2:ast_type) on t1 ≝
 match t1 with
  [ AST_TYPE_BASE bType1 ⇒ match t2 with
   [ AST_TYPE_BASE bType2 ⇒ eq_ast_base_type bType1 bType2 | _ ⇒ false ]
  | AST_TYPE_ARRAY subType1 dim1 ⇒ match t2 with
   [ AST_TYPE_ARRAY subType2 dim2 ⇒ (eq_ast_type subType1 subType2) ⊗ (eqb dim1 dim2) | _ ⇒ false ]
  | AST_TYPE_STRUCT nelSubType1 ⇒ match t2 with
   [ AST_TYPE_STRUCT nelSubType2 ⇒ eq_ast_type_aux ? eq_ast_type nelSubType1 nelSubType2
   | _ ⇒ false ]
  ].

lemma eq_ast_type_elim : 
 ∀P:ast_type → Prop.
  (∀x.P (AST_TYPE_BASE x)) → 
  (∀t:ast_type.∀n.(P t) → (P (AST_TYPE_ARRAY t n))) →
  (∀x.(P x) → (P (AST_TYPE_STRUCT (ne_nil ? x)))) →
  (∀x,l.(P x) → (P (AST_TYPE_STRUCT l)) → (P (AST_TYPE_STRUCT (ne_cons ? x l)))) →
  (∀t.(P t)).
 intros; 
 apply
  (let rec aux t ≝ 
    match t
     return λt.P t
    with
     [ AST_TYPE_BASE b ⇒ H b
     | AST_TYPE_ARRAY t n ⇒ H1 t n (aux t)
     | AST_TYPE_STRUCT l ⇒
      let rec aux_l (l:ne_list ast_type ) ≝
       match l
        return λl.P (AST_TYPE_STRUCT l)
       with
        [ ne_nil t => H2 t (aux t)
        | ne_cons hd tl => H3 hd tl (aux hd) (aux_l tl)
        ] in aux_l l
     ] in aux t);
qed.

lemma eqasttype_to_eq : ∀t1,t2:ast_type.(eq_ast_type t1 t2 = true) → (t1 = t2).
 intro;
 elim t1 using eq_ast_type_elim 0;
 [ 1: intros 2;
      elim t2 using eq_ast_type_elim 0;
      [ 1: intros;
           simplify in H;
           rewrite > (eqastbasetype_to_eq ?? H); 
           reflexivity
      | 2: simplify;
           intros;
           destruct H1
      | 3: simplify;
           intros;
           destruct H1
      | 4: simplify;
           intros;
           destruct H2
      ]
 | 2: intros 4;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H1
      | 2: simplify;
           intros;
           lapply (andb_true_true ?? H2) as H3;
           lapply (andb_true_true_r ?? H2) as H4;
           rewrite > (H ? H3);
           rewrite > (eqb_true_to_eq ?? H4);
           reflexivity
      | 3: simplify;
           intros;
           destruct H2
      | 4: simplify;
           intros;
           destruct H3
      ]
 | 3: intros 3;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H1
      | 2: simplify;
           intros;
           destruct H2
      | 3: intros;
           simplify in H2;
           rewrite > (H x1);
           [ reflexivity
           | apply H2
           ]
      | 4: intros;
           simplify in H3;
           destruct H3
      ]
 | 4: intros 5;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H2
      | 2: simplify;
           intros;
           destruct H3
      | 3: simplify;
           intros;
           destruct H3
      | 4: intros;
           simplify in H4;
           lapply (andb_true_true ?? H4) as H5;
           lapply (andb_true_true_r ?? H4) as H6;
           rewrite > (H ? H5);
           lapply depth=0 (H1 (AST_TYPE_STRUCT l1)) as K;
           destruct (K ?);
           [ apply H6
           | reflexivity
           ]
      ]
 ]. 
qed.

lemma eq_to_eqasttype : ∀t1,t2.t1 = t2 → eq_ast_type t1 t2 = true.
 intro;
 elim t1 using eq_ast_type_elim 0;
 [ 1: intros 2;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H;
           apply (eq_to_eqastbasetype x x (refl_eq ??))
      | 2: simplify;
           intros;
           destruct H1
      | 3: simplify;
           intros;
           destruct H1
      | 4: simplify;
           intros;
           destruct H2
      ]
 | 2: intros 4;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H1
      | 2: intros;
           simplify;
           destruct H2;
           rewrite > (H t (refl_eq ??));
           rewrite > (eq_to_eqb_true n n (refl_eq ??));
           reflexivity
      | 3: simplify;
           intros;
           destruct H2
      | 4: simplify;
           intros;
           destruct H3
      ]
 | 3: intros 3;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H1
      | 2: simplify;
           intros;
           destruct H2
      | 3: intros;
           simplify;
           destruct H2;
           rewrite > (H x (refl_eq ??));
           reflexivity
      | 4: simplify;
           intros;
           destruct H3
      ]
 | 4: intros 5;
      elim t2 using eq_ast_type_elim 0;
      [ 1: simplify;
           intros;
           destruct H2
      | 2: simplify;
           intros;
           destruct H3
      | 3: simplify;
           intros;
           destruct H3
      | 4: intros;
           simplify;
           destruct H4;
           rewrite > (H x (refl_eq ??));
           rewrite > (H1 (AST_TYPE_STRUCT l) (refl_eq ??));
           reflexivity
      ]
 ].
qed.

definition is_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ True | _ ⇒ False ].

definition isb_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ true | _ ⇒ false ].

lemma isbastbasetype_to_isastbasetype : ∀ast.isb_ast_base_type ast = true → is_ast_base_type ast.
 unfold isb_ast_base_type;
 unfold is_ast_base_type;
 intros;
 elim ast;
 [ normalize; autobatch |
   normalize; autobatch |
   normalize; autobatch ]
qed.

definition isnt_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ False | _ ⇒ True ].

definition isntb_ast_base_type ≝
λast:ast_type.match ast with [ AST_TYPE_BASE _ ⇒ false | _ ⇒ true ].

lemma isntbastbasetype_to_isntastbasetype : ∀ast.isntb_ast_base_type ast = true → isnt_ast_base_type ast.
 unfold isntb_ast_base_type;
 unfold isnt_ast_base_type;
 intros;
 elim ast;
 [ normalize; autobatch |
   normalize; autobatch |
   normalize; autobatch ]
qed.

definition eval_size_base_type ≝
λast:ast_base_type.match ast with
 [ AST_BASE_TYPE_BYTE8 ⇒ 1
 | AST_BASE_TYPE_WORD16 ⇒ 2
 | AST_BASE_TYPE_WORD32 ⇒ 4
 ].

let rec eval_size_type (ast:ast_type) on ast ≝
 match ast with
  [ AST_TYPE_BASE b ⇒ eval_size_base_type b
  | AST_TYPE_ARRAY sub_ast dim ⇒ (dim+1)*(eval_size_type sub_ast)
  | AST_TYPE_STRUCT nel_ast ⇒ fold_right_neList ?? (λt,x.(eval_size_type t)+x) O nel_ast
  ].
