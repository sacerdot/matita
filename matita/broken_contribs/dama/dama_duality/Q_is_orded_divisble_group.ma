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



include "Q/q.ma".
include "ordered_divisible_group.ma".

definition strong_decidable ≝
 λA:Prop.A ∨ ¬ A.

theorem strong_decidable_to_Not_Not_eq:
 ∀T:Type.∀eq: T → T → Prop.∀x,y:T.
  strong_decidable (x=y) → ¬x≠y → x=y.
 intros;
 cases s;
  [ assumption
  | elim (H H1) 
  ]
qed.

definition apartness_of_strong_decidable:
 ∀T:Type.(∀x,y:T.strong_decidable (x=y)) → apartness.
 intros;
 constructor 1;
  [ apply T
  | apply (λx,y:T.x ≠ y); 
  | simplify;
    intros 2;
    apply (H (refl_eq ??));
  | simplify;
    intros 4;
    apply H;
    symmetry;
    assumption
  | simplify;
    intros;
    elim (f x z);
     [ elim (f z y);
       [ elim H;
         transitivity z;
         assumption
       | right;
         assumption
       ]
     | left;
       assumption
     ]
  ]
qed.

theorem strong_decidable_to_strong_ext:
 ∀T:Type.∀sd:∀x,y:T.strong_decidable (x=y).
  ∀op:T→T. strong_ext (apartness_of_strong_decidable ? sd) op.
 intros 6;
 intro;
 apply a;
 apply eq_f;
 assumption;
qed.

theorem strong_decidable_to_transitive_to_cotransitive:
 ∀T:Type.∀le:T→T→Prop.(∀x,y:T.strong_decidable (le x y)) →
  transitive ? le → cotransitive ? (λx,y.¬ (le x y)).
 intros;
 whd;
 simplify;
 intros;
 elim (f x z);
  [ elim (f z y);
    [ elim H;
      apply (t ? z);
      assumption
    | right;
      assumption
    ]
  | left;
    assumption 
  ]
qed.
 
theorem reflexive_to_coreflexive:
 ∀T:Type.∀le:T→T→Prop.reflexive ? le → coreflexive ? (λx,y.¬(le x y)).
 intros;
 unfold;
 simplify;
 intros 2;
 apply H1;
 apply H;
qed.

definition ordered_set_of_strong_decidable:
 ∀T:Type.∀le:T→T→Prop.(∀x,y:T.strong_decidable (le x y)) →
  transitive ? le → reflexive ? le → excess.
 intros;
 constructor 1; 
 [ constructor 1;
   [ constructor 1;
     [ constructor 1;
       [ apply T
       | apply (λx,y.¬(le x y));
       | apply reflexive_to_coreflexive;
         assumption
       | apply strong_decidable_to_transitive_to_cotransitive;
         assumption]
     no ported to duality
  ]
qed.

definition abelian_group_of_strong_decidable:
 ∀T:Type.∀plus:T→T→T.∀zero:T.∀opp:T→T.
  (∀x,y:T.strong_decidable (x=y)) →
   associative ? plus (eq T) →
    commutative ? plus (eq T) →
     (∀x:T. plus zero x = x) →
      (∀x:T. plus (opp x) x = zero) →
       abelian_group.
 intros;
 constructor 1;
  [apply (apartness_of_strong_decidable ? f);]
 try assumption;
 [ change with (associative ? plus (λx,y:T.¬x≠y));
   simplify;
   intros;
   intro;
   apply H2;
   apply a;
 | intros 2;
   intro;
   apply a1;
   apply c;
 | intro;
   intro;
   apply a1;
   apply H
 | intro;
   intro;
   apply a1;
   apply H1
 | intros;
   apply strong_decidable_to_strong_ext;
   assumption
 ]
qed.

definition left_neutral ≝ λC:Type.λop.λe:C. ∀x:C. op e x = x.
definition left_inverse ≝ λC:Type.λop.λe:C.λinv:C→C. ∀x:C. op (inv x) x = e.

record nabelian_group : Type ≝
 { ncarr:> Type;
   nplus: ncarr → ncarr → ncarr;
   nzero: ncarr;
   nopp: ncarr → ncarr;
   nplus_assoc: associative ? nplus (eq ncarr);
   nplus_comm: commutative ? nplus (eq ncarr);
   nzero_neutral: left_neutral ? nplus nzero;
   nopp_inverse: left_inverse ? nplus nzero nopp
 }.

definition abelian_group_of_nabelian_group:
 ∀G:nabelian_group.(∀x,y:G.strong_decidable (x=y)) → abelian_group.
 intros;
 apply abelian_group_of_strong_decidable;
  [2: apply (nplus G)
  | skip
  | apply (nzero G)
  | apply (nopp G)
  | assumption
  | apply nplus_assoc;
  | apply nplus_comm;
  | apply nzero_neutral;
  | apply nopp_inverse
  ]
qed.

definition Z_abelian_group: abelian_group.
 apply abelian_group_of_nabelian_group;
  [ constructor 1;
     [ apply Z
     | apply Zplus
     | apply OZ
     | apply Zopp
     | whd;
       intros;
       symmetry;
       apply associative_Zplus
     | apply sym_Zplus
     | intro;
       reflexivity
     | intro;
       rewrite > sym_Zplus;
       apply Zplus_Zopp;
     ]
  | simplify;
    intros;
    unfold;
    generalize in match (eqZb_to_Prop x y);
    elim (eqZb x y);
    simplify in H;
     [ left ; assumption
     | right; assumption
     ]
  ]
qed.

record nordered_set: Type ≝
 { nos_carr:> Type;
   nos_le: nos_carr → nos_carr → Prop;
   nos_reflexive: reflexive ? nos_le;
   nos_transitive: transitive ? nos_le
 }.

definition excess_of_nordered_group:
 ∀O:nordered_set.(∀x,y:O. strong_decidable (nos_le ? x y)) → excess.
 intros;
 constructor 1;
  [ apply (nos_carr O)
  | apply (λx,y.¬(nos_le ? x y))
  | apply reflexive_to_coreflexive;
    apply nos_reflexive
  | apply strong_decidable_to_transitive_to_cotransitive;
     [ assumption
     | apply nos_transitive
     ]
  ]
qed.

lemma non_deve_stare_qui: reflexive ? Zle.
 intro;
 elim x;
  [ exact I
  |2,3: simplify;
    apply le_n;
  ]
qed.

axiom non_deve_stare_qui3: ∀x,y:Z. x < y → x ≤ y.

axiom non_deve_stare_qui4: ∀x,y:Z. x < y → y ≰ x.

definition Z_excess: excess.
 apply excess_of_nordered_group;
  [ constructor 1;
     [ apply Z
     | apply Zle
     | apply non_deve_stare_qui 
     | apply transitive_Zle
     ]
  | simplify;
    intros;
    unfold;
    generalize in match (Z_compare_to_Prop x y);
    cases (Z_compare x y); simplify; intro;
     [ left;
       apply non_deve_stare_qui3;
       assumption
     | left;
       rewrite > H;
       apply non_deve_stare_qui
     | right;
       apply non_deve_stare_qui4;
       assumption      
     ]
  ]
qed.