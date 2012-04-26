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

include "algebra/groups.ma".
include "nat/relevant_equations.ma".

record finite_enumerable (T:Type) : Type≝
 { order: nat;
   repr: nat → T;
   index_of: T → nat;
   index_of_sur: ∀x.index_of x ≤ order;
   index_of_repr: ∀n. n≤order → index_of (repr n) = n;
   repr_index_of: ∀x. repr (index_of x) = x
 }.
 
notation "hvbox(C \sub i)" with precedence 89
for @{ 'repr $C $i }.

(* CSC: multiple interpretations in the same file are not considered in the
 right order
interpretation "Finite_enumerable representation" 'repr C i = (repr C ? i).*)
 
interpretation "Finite_enumerable order" 'card C = (order C ?).

record finite_enumerable_SemiGroup : Type≝
 { semigroup:> SemiGroup;
   is_finite_enumerable:> finite_enumerable semigroup
 }.

interpretation "Finite_enumerable representation" 'repr S i =
 (repr S (is_finite_enumerable S) i).

notation "hvbox(\iota e)" with precedence 65
for @{ 'index_of_finite_enumerable_semigroup $e }.

interpretation "Index_of_finite_enumerable representation"
 'index_of_finite_enumerable_semigroup e
=
 (index_of ? (is_finite_enumerable ?) e).


(* several definitions/theorems to be moved somewhere else *)

theorem pigeonhole:
 ∀n:nat.∀f:nat→nat.
  (∀x,y.x≤n → y≤n → f x = f y → x=y) →
  (∀m. m ≤ n → f m ≤ n) →
   ∀x. x≤n → ∃y.f y = x ∧ y ≤ n.
intro;
elim n;
[ apply (ex_intro ? ? O);
  split;
  [ rewrite < (le_n_O_to_eq ? H2);
    rewrite < (le_n_O_to_eq ? (H1 O ?));
    [ reflexivity
    | apply le_n
    ]
  | apply le_n
  ]
| clear n;
  letin f' ≝
   (λx.
    let fSn1 ≝f (S n1) in
     let fx ≝f x in
      match ltb fSn1 fx with
      [ true ⇒ pred fx
      | false ⇒ fx
      ]);
  cut (∀x,y. x ≤ n1 → y ≤ n1 → f' x = f' y → x=y);
  [ cut (∀x. x ≤ n1 → f' x ≤ n1);
    [ apply (nat_compare_elim (f (S n1)) x);
      [ intro;
        elim (H f' ? ? (pred x));
        [ simplify in H5;
          clear Hcut;
          clear Hcut1;
          unfold f' in H5;
          clear f';
          elim H5;
          clear H5;
          apply (ex_intro ? ? a);
          split;
          [ generalize in match (eq_f ? ? S ? ? H6);
            clear H6;
            intro;
            rewrite < S_pred in H5;
            [ generalize in match H4;
              clear H4;
              rewrite < H5;
              clear H5;
              apply (ltb_elim (f (S n1)) (f a));
              [ simplify;
                intros;
                rewrite < S_pred;
                [ reflexivity
                | apply (ltn_to_ltO ? ? H4)
                ]
              | simplify;
                intros;
                generalize in match (not_lt_to_le ? ? H4);
                clear H4;
                intro;
                generalize in match (le_n_m_to_lt_m_Sn_to_eq_n_m ? ? H6 H5);
                intro;
                generalize in match (H1 ? ? ? ? H4);
                [ intro;
                  generalize in match (le_n_m_to_lt_m_Sn_to_eq_n_m ? ? H6 H5);
                  intro;
                  generalize in match (H1 ? ? ? ? H9);
                  [ intro;
                    rewrite > H10 in H7;
                    elim (not_le_Sn_n ? H7)
                  | rewrite > H8;
                    apply le_n
                  | apply le_n
                  ]
                | apply le_S;
                  assumption
                | apply le_n
                ]
              ]
            | apply (ltn_to_ltO ? ? H4)
            ]
          | apply le_S;
            assumption
          ]
        | apply Hcut
        | apply Hcut1
        | apply le_S_S_to_le;
          rewrite < S_pred;
          [ assumption
          | apply (ltn_to_ltO ? ? H4)
          ]
        ]    
      | intros;
        apply (ex_intro ? ? (S n1));
        split;
        [ assumption
        | constructor 1
        ] 
      | intro;
        elim (H f' ? ? x);
        [ simplify in H5;
          clear Hcut;
          clear Hcut1;
          unfold f' in H5;
          clear f';
          elim H5;
          clear H5;
          apply (ex_intro ? ? a);
          split;
          [ generalize in match H4;
            clear H4;
            rewrite < H6;
            clear H6;
            apply (ltb_elim (f (S n1)) (f a));
            [ simplify;
              intros;
              generalize in match (lt_to_lt_S_S ? ? H5);
              intro;
              rewrite < S_pred in H6;
              [ elim (lt_n_m_to_not_lt_m_Sn ? ? H4 H6)
              | apply (ltn_to_ltO ? ? H4)
              ]
            | simplify;
              intros;
              reflexivity
            ]        
          | apply le_S;
            assumption
          ]
        | apply Hcut    
        | apply Hcut1
        | rewrite > (pred_Sn n1);
          simplify;
          generalize in match (H2 (S n1));
          intro;
          generalize in match (lt_to_le_to_lt ? ? ? H4 (H5 (le_n ?)));
          intro;
          unfold lt in H6;
          apply le_S_S_to_le;
          assumption
        ]
      ]
    | unfold f';
      simplify;
      intro;
      apply (ltb_elim (f (S n1)) (f x1));
      simplify;
      intros;
      [ generalize in match (H2 x1);
        intro;
        change in match n1 with (pred (S n1));
        apply le_to_le_pred;
        apply H6;
        apply le_S;
        assumption
      | generalize in match (H2 (S n1) (le_n ?));
        intro;
        generalize in match (not_lt_to_le ? ? H4);
        intro;
        generalize in match (transitive_le ? ? ? H7 H6);
        intro;
        cut (f x1 ≠ f (S n1));
        [ generalize in match (not_eq_to_le_to_lt ? ? Hcut1 H7);
          intro;
          unfold lt in H9;
          generalize in match (transitive_le ? ? ? H9 H6);
          intro;
          apply le_S_S_to_le;
          assumption
        | unfold Not;
          intro;
          generalize in match (H1 ? ? ? ? H9);
          [ intro;
            rewrite > H10 in H5;
            apply (not_le_Sn_n ? H5)
          | apply le_S;
            assumption
          | apply le_n
          ]
        ] 
      ]
    ]
  | intros 4;
    unfold f';
    simplify;
    apply (ltb_elim (f (S n1)) (f x1));
    simplify;
    apply (ltb_elim (f (S n1)) (f y));
    simplify;
    intros;
    [ cut (f x1 = f y);
      [ apply (H1 ? ? ? ? Hcut);
        apply le_S;
        assumption
      | apply eq_pred_to_eq;
        [ apply (ltn_to_ltO ? ? H7)
        | apply (ltn_to_ltO ? ? H6)
        | assumption
        ]
      ]         
    | (* pred (f x1) = f y absurd since y ≠ S n1 and thus f y ≠ f (S n1)
         so that f y < f (S n1) < f x1; hence pred (f x1) = f y is absurd *)
       cut (y < S n1);
       [ generalize in match (lt_to_not_eq ? ? Hcut);
         intro;
         cut (f y ≠ f (S n1));
         [ cut (f y < f (S n1));
           [ rewrite < H8 in Hcut2;
             unfold lt in Hcut2;
             unfold lt in H7;
             generalize in match (le_S_S ? ? Hcut2);
             intro;
             generalize in match (transitive_le ? ? ? H10 H7);
             intros;
             rewrite < (S_pred (f x1)) in H11;
              [ elim (not_le_Sn_n ? H11)
              | fold simplify ((f (S n1)) < (f x1)) in H7;
                apply (ltn_to_ltO ? ? H7)
              ]
           | apply not_eq_to_le_to_lt;
             [ assumption
             | apply not_lt_to_le;
               assumption
             ]
           ]
         | unfold Not;
           intro;
           apply H9;
           apply (H1 ? ? ? ? H10);
           [ apply lt_to_le;
             assumption
           | constructor 1
           ]
         ]
       | unfold lt;
         apply le_S_S;
         assumption
       ]
    | (* f x1 = pred (f y) absurd since it implies S (f x1) = f y and
         f x1 ≤ f (S n1) < f y = S (f x1) so that f x1 = f (S n1); by
         injectivity x1 = S n1 that is absurd since x1 ≤ n1 *)
       generalize in match (eq_f ? ? S ? ? H8);
       intro;
       rewrite < S_pred in H9;
       [ rewrite < H9 in H6;
         generalize in match (not_lt_to_le ? ? H7);
         intro;
         unfold lt in H6;
         generalize in match (le_S_S ? ? H10);
         intro;
         generalize in match (antisym_le ? ? H11 H6);
         intro;
         generalize in match (inj_S ? ? H12);
         intro;
         generalize in match (H1 ? ? ? ? H13);
         [ intro;
           rewrite > H14 in H4;
           elim (not_le_Sn_n ? H4)
         | apply le_S;
           assumption
         | apply le_n
         ]
       | apply (ltn_to_ltO ? ? H6) 
       ]
    | apply (H1 ? ? ? ? H8);
      apply le_S;
      assumption
    ]
  ]
].
qed.
(* demo *)
theorem finite_enumerable_SemiGroup_to_left_cancellable_to_right_cancellable_to_isMonoid:
 ∀G:finite_enumerable_SemiGroup.
  left_cancellable ? (op G) →
  right_cancellable ? (op G) →
   ∃e:G. IsMonoid (mk_PreMonoid G e).
intros;
letin f ≝(λn.ι(G \sub O · G \sub n));
cut (∀n.n ≤ order ? (is_finite_enumerable G) → ∃m.f m = n);
[ letin EX ≝(Hcut O ?);
  [ apply le_O_n
  | clearbody EX;
    clear Hcut;
    unfold f in EX;
    elim EX;
    clear EX;
    letin HH ≝(eq_f ? ? (repr ? (is_finite_enumerable G)) ? ? H2);
    clearbody HH;
    rewrite > (repr_index_of ? (is_finite_enumerable G)) in HH;
    apply (ex_intro ? ? (G \sub a));
    letin GOGO ≝(refl_eq ? (repr ? (is_finite_enumerable G) O));
    clearbody GOGO;
    rewrite < HH in GOGO;
    rewrite < HH in GOGO:(? ? % ?);
    rewrite > (op_is_associative ? G) in GOGO;
    letin GaGa ≝(H ? ? ? GOGO);
    clearbody GaGa;
    clear GOGO;
    constructor 1;
    [ simplify;
      apply (is_semi_group G)
    | unfold is_left_unit; intro;
      letin GaxGax ≝(refl_eq ? (G \sub a ·x));
      clearbody GaxGax; (* demo *)
      rewrite < GaGa in GaxGax:(? ? % ?);
      rewrite > (op_is_associative ? G) in GaxGax;
      apply (H ? ? ? GaxGax)
    | unfold is_right_unit; intro;
      letin GaxGax ≝(refl_eq ? (x·G \sub a));
      clearbody GaxGax;
      rewrite < GaGa in GaxGax:(? ? % ?);
      rewrite < (op_is_associative ? G) in GaxGax;
      apply (H1 ? ? ? GaxGax)
    ]
  ]
| intros;
  elim (pigeonhole (order ? G) f ? ? ? H2);
  [ apply (ex_intro ? ? a);
    elim H3;
    assumption
  | intros;
    simplify in H5;
    cut (G \sub (ι(G \sub O · G \sub x)) = G \sub (ι(G \sub O · G \sub y)));
    [ rewrite > (repr_index_of ? ? (G \sub O · G \sub x))  in Hcut;
      rewrite > (repr_index_of ? ? (G \sub O · G \sub y))  in Hcut;
      generalize in match (H ? ? ? Hcut);
      intro;
      generalize in match (eq_f ? ? (index_of ? G) ? ? H6);
      intro;
      rewrite > index_of_repr in H7;
      rewrite > index_of_repr in H7;
      assumption
    | apply eq_f;
      assumption
    ]
  | intros;
    unfold f;
    apply index_of_sur
  ] 
].
qed.
