(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti. C.Sacerdoti Coen.                          *)
(*      ||A||       E.Tassi. S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Code ported from the Coq theorem prover by Claudio Sacerdoti Coen *)
(* Original author: Claudio Sacerdoti Coen. for the Coq system       *)

include "datatypes/constructors.ma".
include "logic/coimplication.ma".
include "logic/connectives2.ma".

(* DEFINITIONS OF Relation_Class AND n-ARY Morphism_Theory *)

(* X will be used to distinguish covariant arguments whose type is an   *)
(* Asymmetric* relation from contravariant arguments of the same type *)
inductive X_Relation_Class (X: Type) : Type ≝
   SymmetricReflexive :
     ∀A,Aeq. symmetric A Aeq → reflexive ? Aeq → X_Relation_Class X
 | AsymmetricReflexive : X → ∀A,Aeq. reflexive A Aeq → X_Relation_Class X
 | SymmetricAreflexive : ∀A,Aeq. symmetric A Aeq → X_Relation_Class X
 | AsymmetricAreflexive : X → ∀A.∀Aeq : relation A. X_Relation_Class X
 | Leibniz : Type → X_Relation_Class X.

inductive variance : Set ≝
   Covariant : variance
 | Contravariant : variance.

definition Argument_Class ≝ X_Relation_Class variance.
definition Relation_Class ≝ X_Relation_Class unit.

inductive Reflexive_Relation_Class : Type :=
   RSymmetric :
     ∀A,Aeq. symmetric A Aeq → reflexive ? Aeq → Reflexive_Relation_Class
 | RAsymmetric :
     ∀A,Aeq. reflexive A Aeq → Reflexive_Relation_Class
 | RLeibniz : Type → Reflexive_Relation_Class.

inductive Areflexive_Relation_Class  : Type :=
 | ASymmetric : ∀A,Aeq. symmetric A Aeq → Areflexive_Relation_Class
 | AAsymmetric : ∀A.∀Aeq : relation A. Areflexive_Relation_Class.

definition relation_class_of_argument_class : Argument_Class → Relation_Class.
 intros (a); cases a;
  [ apply (SymmetricReflexive ? ? ? H H1)
  | apply (AsymmetricReflexive ? something ? ? H)
  | apply (SymmetricAreflexive ? ? ? H)
  | apply (AsymmetricAreflexive ? something ? r)
  | apply (Leibniz ? T)
  ]
qed.

definition carrier_of_relation_class : ∀X. X_Relation_Class X → Type.
 intros (X x); cases x (A o o o o A o o A o o o A o A); exact A.
qed.

definition relation_of_relation_class:
 ∀X,R. carrier_of_relation_class X R → carrier_of_relation_class X R → Prop.
intros 2; cases R; simplify; [1,2,3,4: assumption | apply (eq T) ]
qed.

lemma about_carrier_of_relation_class_and_relation_class_of_argument_class :
 ∀R.
  carrier_of_relation_class ? (relation_class_of_argument_class R) =
   carrier_of_relation_class ? R.
intro; cases R; reflexivity.
qed.

inductive nelistT (A : Type) : Type :=
   singl : A → nelistT A
 | cons : A → nelistT A → nelistT A.

definition Arguments := nelistT Argument_Class.

definition function_type_of_morphism_signature :
 Arguments → Relation_Class → Type.
  intros (In Out); elim In; 
  [ exact (carrier_of_relation_class ? a → carrier_of_relation_class ? Out)
  | exact (carrier_of_relation_class ? a → T)
  ]
qed. 

definition make_compatibility_goal_aux:
 ∀In,Out.∀f,g:function_type_of_morphism_signature In Out.Prop.
 intros 2; 
 elim In (a); simplify in f f1;
 generalize in match f1; clear f1;
 generalize in match f; clear f;
  [ elim a; simplify in f f1;
     [ exact (∀x1,x2. r x1 x2 → relation_of_relation_class ? Out (f x1) (f1 x2))
     | cases x;
        [ exact (∀x1,x2. r x1 x2 → relation_of_relation_class ? Out (f x1) (f1 x2))
        | exact (∀x1,x2. r x2 x1 → relation_of_relation_class ? Out (f x1) (f1 x2))
        ]
     | exact (∀x1,x2. r x1 x2 → relation_of_relation_class ? Out (f x1) (f1 x2))
     | cases x;
        [ exact (∀x1,x2. r x1 x2 → relation_of_relation_class ? Out (f x1) (f1 x2))
        | exact (∀x1,x2. r x2 x1 → relation_of_relation_class ? Out (f x1) (f1 x2))
        ]
     | exact (∀x. relation_of_relation_class ? Out (f x) (f1 x))
     ]
  | change with
     ((carrier_of_relation_class ? a → function_type_of_morphism_signature n Out) →
      (carrier_of_relation_class ? a → function_type_of_morphism_signature n Out) →
      Prop).
    elim a; simplify in f f1;
     [1,3: exact (∀x1,x2. r x1 x2 → R (f x1) (f1 x2))
     |2,4: cases x;
        [1,3: exact (∀x1,x2. r x1 x2 → R (f x1) (f1 x2))
        |2,4: exact (∀x1,x2. r x2 x1 → R (f x1) (f1 x2))
        ]
     | exact (∀x. R (f x) (f1 x))
     ]
  ]
qed. 

definition make_compatibility_goal :=
 λIn,Out,f. make_compatibility_goal_aux In Out f f.

record Morphism_Theory (In: Arguments) (Out: Relation_Class) : Type :=
 { Function : function_type_of_morphism_signature In Out;
   Compat : make_compatibility_goal In Out Function
 }.

definition list_of_Leibniz_of_list_of_types: nelistT Type → Arguments.
 intro;
 elim n;
  [ apply (singl ? (Leibniz ? a))
  | apply (cons ? (Leibniz ? a) a1)
  ]
qed.

(* every function is a morphism from Leibniz+ to Leibniz *)
definition morphism_theory_of_function :
 ∀In: nelistT Type.∀Out: Type.
  let In' := list_of_Leibniz_of_list_of_types In in
  let Out' := Leibniz ? Out in
   function_type_of_morphism_signature In' Out' →
    Morphism_Theory In' Out'.
  intros;
  apply (mk_Morphism_Theory ? ? f);
  unfold In' in f ⊢ %; clear In';
  unfold Out' in f ⊢ %; clear Out';
  generalize in match f; clear f;
  elim In;
   [ unfold make_compatibility_goal;
     whd; intros;
     reflexivity
   | simplify;
     intro;
     unfold In' in f;
     unfold Out' in f;
     exact (H (f1 x))
   ]
qed.

(* THE iff RELATION CLASS *)

definition Iff_Relation_Class : Relation_Class.
 apply (SymmetricReflexive unit ? iff);
  [ exact symmetric_iff
  | exact reflexive_iff
  ]
qed.

(* THE impl RELATION CLASS *)

definition impl \def \lambda A,B:Prop. A → B.

theorem impl_refl: reflexive ? impl.
 unfold reflexive;
 intros;
 unfold impl;
 intro;
 assumption.
qed.

definition Impl_Relation_Class : Relation_Class.
 unfold Relation_Class;
 apply (AsymmetricReflexive unit something ? impl);
 exact impl_refl.
qed.

(* UTILITY FUNCTIONS TO PROVE THAT EVERY TRANSITIVE RELATION IS A MORPHISM *)

definition equality_morphism_of_symmetric_areflexive_transitive_relation:
 ∀A: Type.∀Aeq: relation A.∀sym: symmetric ? Aeq.∀trans: transitive ? Aeq.
  let ASetoidClass := SymmetricAreflexive ? ? ? sym in
   (Morphism_Theory (cons ? ASetoidClass (singl ? ASetoidClass))
     Iff_Relation_Class).
 intros;
 apply mk_Morphism_Theory;
  [ exact Aeq
  | unfold make_compatibility_goal;
    simplify; unfold ASetoidClass; simplify;
    intros;
    split;
    unfold transitive in H;
    unfold symmetric in sym;
    intro;
      [ apply (H x2 x1 x3 ? ?);
          [apply (sym x1 x2 ?).
           apply (H1).
          |apply (H x1 x x3 ? ?);
            [apply (H3).
            |apply (H2).
            ]
          ]
      | apply (H x1 x3 x ? ?);
         [apply (H x1 x2 x3 ? ?);
            [apply (H1).
            |apply (H3).
            ]
         |apply (sym x x3 ?).
          apply (H2).
         ]
      ]
  ].
qed.

definition equality_morphism_of_symmetric_reflexive_transitive_relation:
 ∀A: Type.∀Aeq: relation A.∀refl: reflexive ? Aeq.∀sym: symmetric ? Aeq.
  ∀trans: transitive ? Aeq.
   let ASetoidClass := SymmetricReflexive ? ? ? sym refl in
    (Morphism_Theory (cons ? ASetoidClass (singl ? ASetoidClass)) Iff_Relation_Class).
 intros;
 apply mk_Morphism_Theory;
 normalize;
  [ exact Aeq
  | intros;
    split;
    intro;
    unfold transitive in H;
    unfold symmetric in sym;
    [ apply (H x2 x1 x3 ? ?);
        [apply (sym x1 x2 ?).
         apply (H1).
        |apply (H x1 x x3 ? ?);
          [apply (H3).
          |apply (H2).
          ]
        ]
    | apply (H x1 x2 x ? ?);
      [apply (H1).
      |apply (H x2 x3 x ? ?);
        [apply (H3).
        |apply (sym x x3 ?).
         apply (H x x3 x3 ? ?);
          [apply (H2).
          |apply (refl x3).
          ]
        ]
      ]
    ]
  ]
qed.

definition equality_morphism_of_asymmetric_areflexive_transitive_relation:
 ∀A: Type.∀Aeq: relation A.∀trans: transitive ? Aeq.
  let ASetoidClass1 := AsymmetricAreflexive ? Contravariant ? Aeq in
  let ASetoidClass2 := AsymmetricAreflexive ? Covariant ? Aeq in
   (Morphism_Theory (cons ? ASetoidClass1 (singl ? ASetoidClass2)) Impl_Relation_Class).
 intros;
 apply mk_Morphism_Theory;
 [ simplify;
   apply Aeq
 | simplify; unfold ASetoidClass1; simplify; unfold ASetoidClass2; simplify;
   intros;
   whd;
   intros;
   apply (H x2 x1 x3 ? ?);
    [apply (H1).
    |apply (H x1 x x3 ? ?);
      [apply (H3).
      |apply (H2).
      ]
    ]
 ].
qed.

definition equality_morphism_of_asymmetric_reflexive_transitive_relation:
 ∀A: Type.∀Aeq: relation A.∀refl: reflexive ? Aeq.∀trans: transitive ? Aeq.
  let ASetoidClass1 := AsymmetricReflexive ? Contravariant ? ? refl in
  let ASetoidClass2 := AsymmetricReflexive ? Covariant ? ? refl in
   (Morphism_Theory (cons ? ASetoidClass1 (singl ? ASetoidClass2)) Impl_Relation_Class).
 intros;
 apply mk_Morphism_Theory;
 [ simplify;
   apply Aeq
 | simplify; unfold ASetoidClass1; simplify; unfold ASetoidClass2; simplify;
   intros;
   whd;
   intro;
   apply (H x2 x1 x3 ? ?);
     [apply (H1).
     |apply (H x1 x x3 ? ?);
       [apply (H3).
       |apply (H2).
       ]
     ]
 ].
qed.

(* iff AS A RELATION *)

(*DA PORTARE:Add Relation Prop iff
 reflexivity proved by iff_refl
 symmetry proved by iff_sym
 transitivity proved by iff_trans
 as iff_relation.*)

(* every predicate is  morphism from Leibniz+ to Iff_Relation_Class *)
definition morphism_theory_of_predicate :
 ∀(In: nelistT Type).
  let In' := list_of_Leibniz_of_list_of_types In in
   function_type_of_morphism_signature In' Iff_Relation_Class →
    Morphism_Theory In' Iff_Relation_Class.
  intros;
  apply mk_Morphism_Theory;
  [ apply f
  | generalize in match f; clear f;
    unfold In'; clear In';
    elim In;
     [ normalize;
       intro;
       apply iff_refl
     | simplify;
       intro x;
       apply (H (f1 x))
     ]
  ].
qed.

(* impl AS A RELATION *)

theorem impl_trans: transitive ? impl.
 whd;
 unfold impl;
 intros;
 apply (H1 ?).apply (H ?).apply (H2).
 autobatch.
qed.

(*DA PORTARE: Add Relation Prop impl
 reflexivity proved by impl_refl
 transitivity proved by impl_trans
 as impl_relation.*)

(* THE CIC PART OF THE REFLEXIVE TACTIC (SETOID REWRITE) *)

inductive rewrite_direction : Type :=
   Left2Right: rewrite_direction
 | Right2Left: rewrite_direction.

definition variance_of_argument_class : Argument_Class → option variance.
 intros;
 elim a;
  [ apply None
  | apply (Some ? x)
  | apply None
  | apply (Some ? x)
  | apply None
  ]
qed.

definition opposite_direction :=
 λdir.
   match dir with
    [ Left2Right ⇒ Right2Left
    | Right2Left ⇒ Left2Right
    ].

lemma opposite_direction_idempotent:
 ∀dir. opposite_direction (opposite_direction dir) = dir.
  intros;
  elim dir;
  reflexivity.
qed.

inductive check_if_variance_is_respected :
 option variance → rewrite_direction → rewrite_direction →  Prop
:=
   MSNone : ∀dir,dir'. check_if_variance_is_respected (None ?) dir dir'
 | MSCovariant : ∀dir. check_if_variance_is_respected (Some ? Covariant) dir dir
 | MSContravariant :
     ∀dir.
      check_if_variance_is_respected (Some ? Contravariant) dir (opposite_direction dir).

definition relation_class_of_reflexive_relation_class:
 Reflexive_Relation_Class → Relation_Class.
 intro;
 elim r;
  [ apply (SymmetricReflexive ? ? ? H H1)
  | apply (AsymmetricReflexive ? something ? ? H)
  | apply (Leibniz ? T)
  ]
qed.

definition relation_class_of_areflexive_relation_class:
 Areflexive_Relation_Class → Relation_Class.
 intro;
 elim a;
  [ apply (SymmetricAreflexive ? ? ? H)
  | apply (AsymmetricAreflexive ? something ? r)
  ]
qed.

definition carrier_of_reflexive_relation_class :=
 λR.carrier_of_relation_class ? (relation_class_of_reflexive_relation_class R).

definition carrier_of_areflexive_relation_class :=
 λR.carrier_of_relation_class ? (relation_class_of_areflexive_relation_class R).

definition relation_of_areflexive_relation_class :=
 λR.relation_of_relation_class ? (relation_class_of_areflexive_relation_class R).

inductive Morphism_Context (Hole: Relation_Class) (dir:rewrite_direction) : Relation_Class → rewrite_direction →  Type :=
    App :
      ∀In,Out,dir'.
        Morphism_Theory In Out → Morphism_Context_List Hole dir dir' In →
           Morphism_Context Hole dir Out dir'
  | ToReplace : Morphism_Context Hole dir Hole dir
  | ToKeep :
     ∀S,dir'.
      carrier_of_reflexive_relation_class S →
        Morphism_Context Hole dir (relation_class_of_reflexive_relation_class S) dir'
 | ProperElementToKeep :
     ∀S,dir'.∀x: carrier_of_areflexive_relation_class S.
      relation_of_areflexive_relation_class S x x →
        Morphism_Context Hole dir (relation_class_of_areflexive_relation_class S) dir'
with Morphism_Context_List :
   rewrite_direction → Arguments → Type
:=
    fcl_singl :
      ∀S,dir',dir''.
       check_if_variance_is_respected (variance_of_argument_class S) dir' dir'' →
        Morphism_Context Hole dir (relation_class_of_argument_class S) dir' →
         Morphism_Context_List Hole dir dir'' (singl ? S)
 | fcl_cons :
      ∀S,L,dir',dir''.
       check_if_variance_is_respected (variance_of_argument_class S) dir' dir'' →
        Morphism_Context Hole dir (relation_class_of_argument_class S) dir' →
         Morphism_Context_List Hole dir dir'' L →
          Morphism_Context_List Hole dir dir'' (cons ? S L).

lemma Morphism_Context_rect2:
 ∀Hole,dir.
 ∀P:
  ∀r:Relation_Class.∀r0:rewrite_direction.Morphism_Context Hole dir r r0 → Type.
 ∀P0:
  ∀r:rewrite_direction.∀a:Arguments.Morphism_Context_List Hole dir r a → Type.
 (∀In,Out,dir'.
   ∀m:Morphism_Theory In Out.∀m0:Morphism_Context_List Hole dir dir' In.
    P0 dir' In m0 → P Out dir' (App Hole ? ? ? ? m m0)) →
 P Hole dir (ToReplace Hole dir) →
 (∀S:Reflexive_Relation_Class.∀dir'.∀c:carrier_of_reflexive_relation_class S.
   P (relation_class_of_reflexive_relation_class S) dir'
    (ToKeep Hole dir S dir' c)) →
 (∀S:Areflexive_Relation_Class.∀dir'.
   ∀x:carrier_of_areflexive_relation_class S.
    ∀r:relation_of_areflexive_relation_class S x x.
     P (relation_class_of_areflexive_relation_class S) dir'
      (ProperElementToKeep Hole dir S dir' x r)) →
 (∀S:Argument_Class.∀dir',dir''.
   ∀c:check_if_variance_is_respected (variance_of_argument_class S) dir' dir''.
    ∀m:Morphism_Context Hole dir (relation_class_of_argument_class S) dir'.
     P (relation_class_of_argument_class S) dir' m ->
      P0 dir'' (singl ? S) (fcl_singl ? ? S ? ? c m)) →
 (∀S:Argument_Class.∀L:Arguments.∀dir',dir''.
   ∀c:check_if_variance_is_respected (variance_of_argument_class S) dir' dir''.
    ∀m:Morphism_Context Hole dir (relation_class_of_argument_class S) dir'.
     P (relation_class_of_argument_class S) dir' m →
      ∀m0:Morphism_Context_List Hole dir dir'' L.
       P0 dir'' L m0 → P0 dir'' (cons ? S L) (fcl_cons ? ? S ? ? ? c m m0)) →
 ∀r:Relation_Class.∀r0:rewrite_direction.∀m:Morphism_Context Hole dir r r0.
  P r r0 m
≝
 λHole,dir,P,P0,f,f0,f1,f2,f3,f4.
 let rec
  F (rc:Relation_Class) (r0:rewrite_direction)
   (m:Morphism_Context Hole dir rc r0) on m : P rc r0 m
 ≝
  match m return λrc.λr0.λm0.P rc r0 m0 with
  [ App In Out dir' m0 m1 ⇒ f In Out dir' m0 m1 (F0 dir' In m1)
  | ToReplace ⇒ f0
  | ToKeep S dir' c ⇒ f1 S dir' c
  | ProperElementToKeep S dir' x r1 ⇒ f2 S dir' x r1
  ]
 and
  F0 (r:rewrite_direction) (a:Arguments)
   (m:Morphism_Context_List Hole dir r a) on m : P0 r a m
 ≝
  match m return λr.λa.λm0.P0 r a m0 with
  [ fcl_singl S dir' dir'' c m0 ⇒
      f3 S dir' dir'' c m0 (F (relation_class_of_argument_class S) dir' m0)
  | fcl_cons S L dir' dir'' c m0 m1 ⇒
      f4 S L dir' dir'' c m0 (F (relation_class_of_argument_class S) dir' m0)
        m1 (F0 dir'' L m1)
  ]
in F.

lemma Morphism_Context_List_rect2:
 ∀Hole,dir.
 ∀P:
  ∀r:Relation_Class.∀r0:rewrite_direction.Morphism_Context Hole dir r r0 → Type.
 ∀P0:
  ∀r:rewrite_direction.∀a:Arguments.Morphism_Context_List Hole dir r a → Type.
 (∀In,Out,dir'.
   ∀m:Morphism_Theory In Out.∀m0:Morphism_Context_List Hole dir dir' In.
    P0 dir' In m0 → P Out dir' (App Hole ? ? ? ? m m0)) →
 P Hole dir (ToReplace Hole dir) →
 (∀S:Reflexive_Relation_Class.∀dir'.∀c:carrier_of_reflexive_relation_class S.
   P (relation_class_of_reflexive_relation_class S) dir'
    (ToKeep Hole dir S dir' c)) →
 (∀S:Areflexive_Relation_Class.∀dir'.
   ∀x:carrier_of_areflexive_relation_class S.
    ∀r:relation_of_areflexive_relation_class S x x.
     P (relation_class_of_areflexive_relation_class S) dir'
      (ProperElementToKeep Hole dir S dir' x r)) →
 (∀S:Argument_Class.∀dir',dir''.
   ∀c:check_if_variance_is_respected (variance_of_argument_class S) dir' dir''.
    ∀m:Morphism_Context Hole dir (relation_class_of_argument_class S) dir'.
     P (relation_class_of_argument_class S) dir' m ->
      P0 dir'' (singl ? S) (fcl_singl ? ? S ? ? c m)) →
 (∀S:Argument_Class.∀L:Arguments.∀dir',dir''.
   ∀c:check_if_variance_is_respected (variance_of_argument_class S) dir' dir''.
    ∀m:Morphism_Context Hole dir (relation_class_of_argument_class S) dir'.
     P (relation_class_of_argument_class S) dir' m →
      ∀m0:Morphism_Context_List Hole dir dir'' L.
       P0 dir'' L m0 → P0 dir'' (cons ? S L) (fcl_cons ? ? S ? ? ? c m m0)) →
 ∀r:rewrite_direction.∀a:Arguments.∀m:Morphism_Context_List Hole dir r a.
  P0 r a m
≝
 λHole,dir,P,P0,f,f0,f1,f2,f3,f4.
 let rec
  F (rc:Relation_Class) (r0:rewrite_direction)
   (m:Morphism_Context Hole dir rc r0) on m : P rc r0 m
 ≝
  match m return λrc.λr0.λm0.P rc r0 m0 with
  [ App In Out dir' m0 m1 ⇒ f In Out dir' m0 m1 (F0 dir' In m1)
  | ToReplace ⇒ f0
  | ToKeep S dir' c ⇒ f1 S dir' c
  | ProperElementToKeep S dir' x r1 ⇒ f2 S dir' x r1
  ]
 and
  F0 (r:rewrite_direction) (a:Arguments)
   (m:Morphism_Context_List Hole dir r a) on m : P0 r a m
 ≝
  match m return λr.λa.λm0.P0 r a m0 with
  [ fcl_singl S dir' dir'' c m0 ⇒
      f3 S dir' dir'' c m0 (F (relation_class_of_argument_class S) dir' m0)
  | fcl_cons S L dir' dir'' c m0 m1 ⇒
      f4 S L dir' dir'' c m0 (F (relation_class_of_argument_class S) dir' m0)
        m1 (F0 dir'' L m1)
  ]
in F0.

definition product_of_arguments : Arguments → Type.
 intro;
 elim a;
  [ apply (carrier_of_relation_class ? a1)
  | apply (Prod (carrier_of_relation_class ? a1) T)
  ]
qed.

definition get_rewrite_direction: rewrite_direction → Argument_Class → rewrite_direction.
 intros (dir R);
 cases (variance_of_argument_class R) (a);
  [ exact dir
  | cases a;
     [ exact dir                      (* covariant *)
     | exact (opposite_direction dir) (* contravariant *)
     ]
  ]
qed.

definition directed_relation_of_relation_class:
 ∀dir:rewrite_direction.∀R: Relation_Class.
   carrier_of_relation_class ? R → carrier_of_relation_class ? R → Prop.
 intros;
 cases r;
  [ exact (relation_of_relation_class ? ? c c1)
  | apply (relation_of_relation_class ? ? c1 c)
  ]
qed.

definition directed_relation_of_argument_class:
 ∀dir:rewrite_direction.∀R: Argument_Class.
   carrier_of_relation_class ? R → carrier_of_relation_class ? R → Prop.
  intros (dir R c c1);
  rewrite < (about_carrier_of_relation_class_and_relation_class_of_argument_class R) in c c1;
  exact (directed_relation_of_relation_class dir (relation_class_of_argument_class R)  c c1).
qed.


definition relation_of_product_of_arguments:
 ∀dir:rewrite_direction.∀In.
  product_of_arguments In → product_of_arguments In → Prop.
 intros 2;
 elim In 0;
  [ simplify;
    intro;
    exact (directed_relation_of_argument_class (get_rewrite_direction r a) a)
  | intros;
    change in p with (Prod (carrier_of_relation_class variance a) (product_of_arguments n));
    change in p1 with (Prod (carrier_of_relation_class variance a) (product_of_arguments n));
    cases p (c p2);
    cases p1 (c1 p3);
   apply And;
    [ exact
      (directed_relation_of_argument_class (get_rewrite_direction r a) a c c1)
    | exact (R p2 p3)
    ]
  ]
qed. 

definition apply_morphism:
 ∀In,Out.∀m: function_type_of_morphism_signature In Out.
  ∀args: product_of_arguments In. carrier_of_relation_class ? Out.
 intro;
 elim In;
  [ exact (f p)
  | change in p with (Prod (carrier_of_relation_class variance a) (product_of_arguments n));
   elim p;
   change in f1 with (carrier_of_relation_class variance a → function_type_of_morphism_signature n Out);
   exact (f ? (f1 a1) b)
  ]
qed.

theorem apply_morphism_compatibility_Right2Left:
 ∀In,Out.∀m1,m2: function_type_of_morphism_signature In Out.
  ∀args1,args2: product_of_arguments In.
     make_compatibility_goal_aux ? ? m1 m2 →
      relation_of_product_of_arguments Right2Left ? args1 args2 →
        directed_relation_of_relation_class Right2Left ?
         (apply_morphism ? ? m2 args1)
         (apply_morphism ? ? m1 args2).
  intro;
  elim In;
   [ simplify in m1 m2 args1 args2 ⊢ %;
     change in H1 with
      (directed_relation_of_argument_class
        (get_rewrite_direction Right2Left a) a args1 args2);
     generalize in match H1; clear H1;
     generalize in match H; clear H;
     generalize in match args2; clear args2;
     generalize in match args1; clear args1;
     generalize in match m2; clear m2;
     generalize in match m1; clear m1;
     elim a 0; simplify;
      [ intros (T1 r Hs Hr m1 m2 args1 args2 H H1);
        apply H;
        exact H1
      | intros 8 (v T1 r Hr m1 m2 args1 args2);
        cases v; 
        simplify;
        intros (H H1);
        apply (H ? ? H1);
      | intros;
        apply H1;
        exact H2
      | intros 7 (v);
        cases v; simplify;
        intros (H H1);
        apply H;
        exact H1
      | intros;
        simplify in H1;
        rewrite > H1;
        apply H;
        exact H1
      ]
   | change in m1 with
      (carrier_of_relation_class variance a →
        function_type_of_morphism_signature n Out);
     change in m2 with
      (carrier_of_relation_class variance a →
        function_type_of_morphism_signature n Out);
     change in args1 with
      ((carrier_of_relation_class ? a) × (product_of_arguments n));
     change in args2 with
      ((carrier_of_relation_class ? a) × (product_of_arguments n));
     generalize in match H2; clear H2;
     elim args2 0; clear args2;
     elim args1; clear args1;
     simplify in H2;
     change in H2:(? ? %) with 
       (relation_of_product_of_arguments Right2Left n b b1);
     elim H2; clear H2;
     change with
      (relation_of_relation_class unit Out (apply_morphism n Out (m1 a2) b1)
        (apply_morphism n Out (m2 a1) b));
     generalize in match H3; clear H3;
     generalize in match a1; clear a1;
     generalize in match a2; clear a2;
     generalize in match H1; clear H1;
     generalize in match m2; clear m2;
     generalize in match m1; clear m1;
     elim a 0;
      [ intros (T1 r Hs Hr m1 m2 H1 t1 t3 H3);
        simplify in H3;
        change in H1 with
         (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
     | intro v;
       elim v 0;
       [ intros (T1 r Hr m1 m2 H1 t1 t3 H3);
         simplify in H3;
         change in H1 with
          (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
       | intros (T1 r Hr m1 m2 H1 t1 t3 H3);
         simplify in H3;
         change in H1 with
          (∀x1,x2:T1.r x2 x1 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
       ]
     | intros (T1 r Hs m1 m2 H1 t1 t3 H3);
       simplify in H3;
       change in H1 with
        (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
     | intro v;
       elim v 0;
        [ intros (T1 r m1 m2 H1 t1 t3 H3);
          simplify in H3;
          change in H1 with
           (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
        | intros (T1 r m1 m2 H1 t1 t3 H3);
          simplify in H3;
          change in H1 with
           (∀x1,x2:T1.r x2 x1 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
        ]
     | intros (T m1 m2 H1 t1 t3 H3);
       simplify in H3;
       change in H1 with
        (∀x:T. make_compatibility_goal_aux n Out (m1 x) (m2 x));
       rewrite > H3;
       simplify in H;
       apply H;
        [ apply H1 
        | assumption
        ]
     ] ;
     simplify in H;
     apply H;
      [1,3,5,7,9,11:
        apply H1;
        assumption
      |2,4,6,8,10,12:
        assumption
      ]
   ]
qed.

theorem apply_morphism_compatibility_Left2Right:
 ∀In,Out.∀m1,m2: function_type_of_morphism_signature In Out.
  ∀args1,args2: product_of_arguments In.
     make_compatibility_goal_aux ? ? m1 m2 →
      relation_of_product_of_arguments Left2Right ? args1 args2 →
        directed_relation_of_relation_class Left2Right ?
         (apply_morphism ? ? m1 args1)
         (apply_morphism ? ? m2 args2).
  intro; 
  elim In 0; simplify; intros;
   [ change in H1 with
      (directed_relation_of_argument_class
        (get_rewrite_direction Left2Right a) a args1 args2);
     generalize in match H1; clear H1;
     generalize in match H; clear H;
     generalize in match args2; clear args2;
     generalize in match args1; clear args1;
     generalize in match m2; clear m2;
     generalize in match m1; clear m1;
     elim a 0; simplify;
      [ intros (T1 r Hs Hr m1 m2 args1 args2 H H1);
        apply H;
        exact H1
      | intros 8 (v T1 r Hr m1 m2 args1 args2);
        cases v;
        intros (H H1);
        simplify in H1;
        apply H;
        exact H1
      | intros;
        apply H1;
        exact H2
      | intros 7 (v);
        cases v;
        intros (H H1);
        simplify in H1;
        apply H;
        exact H1
      | intros;
        simplify in H1;
        rewrite > H1;
        apply H;
        exact H1
      ]
   | change in m1 with
      (carrier_of_relation_class variance a →
        function_type_of_morphism_signature n Out);
     change in m2 with
      (carrier_of_relation_class variance a →
        function_type_of_morphism_signature n Out);
     change in args1 with
      ((carrier_of_relation_class ? a) × (product_of_arguments n));
     change in args2 with
      ((carrier_of_relation_class ? a) × (product_of_arguments n));
     generalize in match H2; clear H2;
     elim args2 0; clear args2;
     elim args1; clear args1;
     simplify in H2; change in H2:(? ? %) with
       (relation_of_product_of_arguments Left2Right n b b1); 
     elim H2; clear H2;
     change with
      (relation_of_relation_class unit Out (apply_morphism n Out (m1 a1) b)
        (apply_morphism n Out (m2 a2) b1));
     generalize in match H3; clear H3;
     generalize in match a2; clear a2;
     generalize in match a1; clear a1;
     generalize in match H1; clear H1;
     generalize in match m2; clear m2;
     generalize in match m1; clear m1;
     elim a 0;
      [ intros (T1 r Hs Hr m1 m2 H1 t1 t3 H3);
        change in H1 with
         (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
     | intro v;
       elim v 0;
       [ intros (T1 r Hr m1 m2 H1 t1 t3 H3);
         simplify in H3;
         change in H1 with
          (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
       | intros (T1 r Hr m1 m2 H1 t1 t3 H3);
         simplify in H3;
         change in H1 with
          (∀x1,x2:T1.r x2 x1 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
       ]
     | intros (T1 r Hs m1 m2 H1 t1 t3 H3);
       simplify in H3;
       change in H1 with
        (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
     | intro v;
       elim v 0;
        [ intros (T1 r m1 m2 H1 t1 t3 H3);
          simplify in H3;
          change in H1 with
           (∀x1,x2:T1.r x1 x2 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
        | intros (T1 r m1 m2 H1 t1 t3 H3);
          simplify in H3;
          change in H1 with
           (∀x1,x2:T1.r x2 x1 → make_compatibility_goal_aux n Out (m1 x1) (m2 x2));
        ]
     | intros (T m1 m2 H1 t1 t3 H3);
       simplify in H3;
       change in H1 with
        (∀x:T. make_compatibility_goal_aux n Out (m1 x) (m2 x));
       rewrite > H3;
       simplify in H;
       apply H;
        [ apply H1 
        | assumption
        ]
     ] ;
     simplify in H;
     apply H;
      [1,3,5,7,9,11:
        apply H1;
        assumption
      |2,4,6,8,10,12:
        assumption
      ]
   ]
qed.

definition interp :
 ∀Hole,dir,Out,dir'. carrier_of_relation_class ? Hole →
  Morphism_Context Hole dir Out dir' → carrier_of_relation_class ? Out.
 intros (Hole dir Out dir' H t).
 apply
  (Morphism_Context_rect2 Hole dir (λS,xx,yy. carrier_of_relation_class ? S)
    (λxx,L,fcl.product_of_arguments L));
  intros;
   [8: apply t
   |7: skip
   | exact (apply_morphism ? ? (Function ? ? m) p)
   | exact H
   | exact c
   | exact x
   | simplify;
     rewrite <
       (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
     exact c1
   | simplify;split;
      [ rewrite <
         (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
        exact c1
      | exact p
      ]
   ]
qed.


(*CSC: interp and interp_relation_class_list should be mutually defined. since
   the proof term of each one contains the proof term of the other one. However
   I cannot do that interactively (I should write the Fix by hand) *)
definition interp_relation_class_list :
 ∀Hole,dir,dir'.∀L: Arguments. carrier_of_relation_class ? Hole →
  Morphism_Context_List Hole dir dir' L → product_of_arguments L.
 intros (Hole dir dir' L H t);
 apply
  (Morphism_Context_List_rect2 Hole dir (λS,xx,yy.carrier_of_relation_class ? S)
    (λxx,L,fcl.product_of_arguments L));
 intros;
  [8: apply t
  |7: skip
  | exact (apply_morphism ? ? (Function ? ? m) p)
  | exact H
  | exact c
  | exact x
  | simplify;
     rewrite <
       (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
     exact c1
  | simplify; split;
     [ rewrite <
        (about_carrier_of_relation_class_and_relation_class_of_argument_class S);
       exact c1
     | exact p
     ]
  ]
qed.

(*
Theorem setoid_rewrite:
 ∀Hole dir Out dir' (E1 E2: carrier_of_relation_class Hole)
  (E: Morphism_Context Hole dir Out dir').
   (directed_relation_of_relation_class dir Hole E1 E2) →
    (directed_relation_of_relation_class dir' Out (interp E1 E) (interp E2 E)).
 intros.
 elim E using
   (@Morphism_Context_rect2 Hole dir
     (fun S dir'' E => directed_relation_of_relation_class dir'' S (interp E1 E) (interp E2 E))
     (fun dir'' L fcl =>
        relation_of_product_of_arguments dir'' ?
         (interp_relation_class_list E1 fcl)
         (interp_relation_class_list E2 fcl))); intros.
   change (directed_relation_of_relation_class dir'0 Out0
    (apply_morphism ? ? (Function m) (interp_relation_class_list E1 m0))
    (apply_morphism ? ? (Function m) (interp_relation_class_list E2 m0))).
   destruct dir'0.
     apply apply_morphism_compatibility_Left2Right.
       exact (Compat m).
       exact H0.
     apply apply_morphism_compatibility_Right2Left.
       exact (Compat m).
       exact H0.

   exact H.

   unfold interp. Morphism_Context_rect2.
   (*CSC: reflexivity used here*)
   destruct S; destruct dir'0; simpl; (apply r || reflexivity).

   destruct dir'0; exact r.

  destruct S; unfold directed_relation_of_argument_class; simpl in H0 |- *;
   unfold get_rewrite_direction; simpl.
     destruct dir'0; destruct dir'';
       (exact H0 ||
        unfold directed_relation_of_argument_class; simpl; apply s; exact H0).
     (* the following mess with generalize/clear/intros is to help Coq resolving *)
     (* second order unification problems.                                                                *)
     generalize m c H0; clear H0 m c; inversion c;
       generalize m c; clear m c; rewrite <- H1; rewrite <- H2; intros;
         (exact H3 || rewrite (opposite_direction_idempotent dir'0); apply H3).
     destruct dir'0; destruct dir'';
       (exact H0 ||
        unfold directed_relation_of_argument_class; simpl; apply s; exact H0).
(* the following mess with generalize/clear/intros is to help Coq resolving *)
     (* second order unification problems.                                                                *)
     generalize m c H0; clear H0 m c; inversion c;
       generalize m c; clear m c; rewrite <- H1; rewrite <- H2; intros;
         (exact H3 || rewrite (opposite_direction_idempotent dir'0); apply H3).
     destruct dir'0; destruct dir''; (exact H0 || hnf; symmetry; exact H0).

  change
    (directed_relation_of_argument_class (get_rewrite_direction dir'' S) S
       (eq_rect ? (fun T : Type => T) (interp E1 m) ?
         (about_carrier_of_relation_class_and_relation_class_of_argument_class S))
       (eq_rect ? (fun T : Type => T) (interp E2 m) ?
         (about_carrier_of_relation_class_and_relation_class_of_argument_class S)) /\
     relation_of_product_of_arguments dir'' ?
       (interp_relation_class_list E1 m0) (interp_relation_class_list E2 m0)).
   split.
     clear m0 H1; destruct S; simpl in H0 |- *; unfold get_rewrite_direction; simpl.
        destruct dir''; destruct dir'0; (exact H0 || hnf; apply s; exact H0).
        inversion c.
          rewrite <- H3; exact H0.
          rewrite (opposite_direction_idempotent dir'0); exact H0.
        destruct dir''; destruct dir'0; (exact H0 || hnf; apply s; exact H0).
        inversion c.
          rewrite <- H3; exact H0.
          rewrite (opposite_direction_idempotent dir'0); exact H0.
        destruct dir''; destruct dir'0; (exact H0 || hnf; symmetry; exact H0).
     exact H1.
Qed.

(* A FEW EXAMPLES ON iff *)

(* impl IS A MORPHISM *)

Add Morphism impl with signature iff ==> iff ==> iff as Impl_Morphism.
unfold impl; tautobatch.
Qed.

(* and IS A MORPHISM *)

Add Morphism and with signature iff ==> iff ==> iff as And_Morphism.
 tautobatch.
Qed.

(* or IS A MORPHISM *)

Add Morphism or with signature iff ==> iff ==> iff as Or_Morphism.
 tautobatch.
Qed.

(* not IS A MORPHISM *)

Add Morphism not with signature iff ==> iff as Not_Morphism.
 tautobatch.
Qed.

(* THE SAME EXAMPLES ON impl *)

Add Morphism and with signature impl ++> impl ++> impl as And_Morphism2.
 unfold impl; tautobatch.
Qed.

Add Morphism or with signature impl ++> impl ++> impl as Or_Morphism2.
 unfold impl; tautobatch.
Qed.

Add Morphism not with signature impl -→ impl as Not_Morphism2.
 unfold impl; tautobatch.
Qed.

*)
