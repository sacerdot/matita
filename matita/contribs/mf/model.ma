(* (C) 2014 Luca Bressan *)

include "mTT.ma".

record is_Equiv (Sup: cl) (Eq: Sup → Sup → prop) : prop ≝
 { Rfl_: ∀x. Eq x x
 ; Sym_: ∀x,x'. Eq x x' → Eq x' x
 ; Tra_: ∀x,x',x''. Eq x x' → Eq x' x'' → Eq x x''
 }.

record ecl: Type[2] ≝ 
 { Sup:> cl
 ; Eq: Sup → Sup → prop
 ; is_ecl: is_Equiv Sup Eq
 }.
interpretation "Equality in Extensional Collections" 'eq a b = (Eq ? a b).

definition Rfl: ∀B: ecl. ∀x: B. x ≃ x ≝
 λB. Rfl_ … (is_ecl B).
interpretation "Reflexivity in Extensional Collections" 'rfl x = (Rfl ? x).

definition Sym: ∀B: ecl. ∀x,x': B. x ≃ x' → x' ≃ x ≝
 λB. Sym_ … (is_ecl B).
interpretation "Symmetry in Extensional Collections" 'sym d = (Sym ??? d).

definition Tra: ∀B: ecl. ∀x,x',x'': B. x ≃ x' → x' ≃ x'' → x ≃ x'' ≝
 λB. Tra_ … (is_ecl B).
interpretation "Transitivity in Extensional Collections" 'tra d d' = (Tra ???? d d').

record is_Subst (A: ecl)
                (dSup: A → ecl)
                (Subst: ∀x1,x2: A. x1 ≃ x2 → dSup x1 → dSup x2) : prop ≝
 { Pres_eq_:   ∀x1,x2: A. ∀d: x1 ≃ x2. ∀y,y': dSup x1.
                y ≃ y' → Subst … d y ≃ Subst … d y'
 ; Not_dep_:   ∀x1,x2: A. ∀d,d': x1 ≃ x2. ∀y: dSup x1.
                Subst … d y ≃ Subst … d' y
 ; Pres_id_:   ∀x: A. ∀y: dSup x.
                Subst … (ı x) y ≃ y
 ; Clos_comp_: ∀x1,x2,x3: A. ∀y: dSup x1. ∀d: x1 ≃ x2. ∀d': x2 ≃ x3.
                Subst … d' (Subst … d y) ≃ Subst … (d•d') y
 }.

record edcl (A: ecl) : Type[2] ≝ 
 { dSup:1> Sup A → ecl
 ; Subst: ∀x1,x2: Sup A. x1 ≃ x2 → Sup (dSup x1) → Sup (dSup x2)
 ; is_edcl: is_Subst A dSup Subst
 }.
interpretation "Substitution morphisms for Extensional Collections"
 'subst d y = (Subst ???? d y).

definition Pres_eq: ∀B: ecl. ∀C: edcl B. ∀x1,x2: B. ∀d: x1 ≃ x2. ∀y,y': C x1.
                     y ≃ y' → y∘d ≃ y'∘d ≝
 λB,C. Pres_eq_ … (is_edcl … C).
definition Not_dep: ∀B: ecl. ∀C: edcl B. ∀x1,x2: B. ∀d,d': x1 ≃ x2. ∀y: C x1.
                     y∘d ≃ y∘d' ≝
 λB,C. Not_dep_ … (is_edcl … C).
definition Pres_id: ∀B: ecl. ∀C: edcl B. ∀x: B. ∀y: C x.
                     y∘(ıx) ≃ y ≝
 λB,C. Pres_id_ … (is_edcl … C).
definition Clos_comp: ∀B: ecl. ∀C: edcl B. ∀x1,x2,x3: B. ∀y: C x1. ∀d: x1 ≃ x2. ∀d': x2 ≃ x3.
                       y∘d∘d' ≃ y∘d•d' ≝
 λB,C. Clos_comp_ … (is_edcl … C).

definition constant_edcl: ∀A: ecl. ecl → edcl A ≝
 λA,Y. mk_edcl … (λ_. Y) (λx1,x2,d,y. y) ?.
 % [ #x1 #x2 #d #y #y' #h @h
   | #x1 #x2 #_ #_ #y @(ıy)
   | #_ #y @(ıy)
   | #x1 #x2 #x3 #y #_ #_ @(ıy)
   ]
qed.

lemma inverse_Subst: ∀B: ecl. ∀C: edcl B. ∀x1,x2: B. ∀d: x1 ≃ x2. ∀y: C x2.
 y∘d⁻¹∘d ≃ y.
 #B #C #x1 #x2 #d #y
 @(Tra … (y∘d⁻¹∘d) (y∘d⁻¹•d) y)
 [ @Clos_comp
 | @(Tra … (y∘d⁻¹•d) (y∘ıx2) y)
   [ @Not_dep | @Pres_id ]
 ]
qed.

record is_equiv (sup: st) (eq: sup → sup → props) : props ≝
 { rfl_: ∀x. eq x x
 ; sym_: ∀x,x'. eq x x' → eq x' x
 ; tra_: ∀x,x',x''. eq x x' → eq x' x'' → eq x x''
 }.

record est: Type[1] ≝ 
 { sup:> st
 ; eq: sup → sup → props
 ; is_est: is_equiv sup eq
 }.
interpretation "Equality in Extensional Sets" 'eq a b = (eq ? a b).

definition rfl: ∀B: est. ∀x: B. x ≃ x ≝
 λB. rfl_ … (is_est B).
interpretation "Reflexivity in Extensional Sets" 'rfl x = (rfl ? x).

definition sym: ∀B: est. ∀x,x': B. x ≃ x' → x' ≃ x ≝
 λB. sym_ … (is_est B).
interpretation "Symmetry in Extensional Sets" 'sym d = (sym ??? d).

definition tra: ∀B: est. ∀x,x',x'': B. x ≃ x' → x' ≃ x'' → x ≃ x'' ≝
 λB. tra_ … (is_est B).
interpretation "Transitivity in Extensional Sets" 'tra d d' = (tra ???? d d').

definition est_into_ecl: est → ecl ≝ 
 λB. mk_ecl (sup B) (eq B) ?.
 % [ @rfl | @sym | @tra ]
qed.

record is_subst (A: est)
                (dsup: A → est)
                (subst: ∀x1,x2: A. x1 ≃ x2 → dsup x1 → dsup x2) : props ≝
 { pres_eq_:   ∀x1,x2: A. ∀d: x1 ≃ x2. ∀y,y': dsup x1.
                y ≃ y' → subst … d y ≃ subst … d y'
 ; not_dep_:   ∀x1,x2: A. ∀d1,d2: x1 ≃ x2. ∀y: dsup x1.
                subst … d1 y ≃ subst … d2 y
 ; pres_id_:   ∀x: sup A. ∀y: dsup x.
                subst … (ıx) y ≃ y
 ; clos_comp_: ∀x1,x2,x3: A. ∀y: dsup x1. ∀d1: x1 ≃ x2. ∀d2: x2 ≃ x3.
                subst … d2 (subst … d1 y) ≃ subst … (d1•d2) y
 }.

record edst (A: est) : Type[1] ≝ 
 { dsup:1> sup A → est
 ; subst: ∀x1,x2: sup A. x1 ≃ x2 → sup (dsup x1) → sup (dsup x2)
 ; is_edst: is_subst A dsup subst
 }.
interpretation "Substitution morphisms for Extensional Sets"
 'subst p a = (subst ???? p a).

definition pres_eq: ∀B: est. ∀C: edst B. ∀x1,x2: B. ∀d: x1 ≃ x2. ∀y,y': C x1.
                     y ≃ y' → y∘d ≃ y'∘d ≝
 λB,C. pres_eq_ … (is_edst … C).
definition not_dep: ∀B: est. ∀C: edst B. ∀x1,x2: B. ∀d,d': x1 ≃ x2. ∀y: C x1.
                     y∘d ≃ y∘d' ≝
 λB,C. not_dep_ … (is_edst … C).
definition pres_id: ∀B: est. ∀C: edst B. ∀x: B. ∀y: C x.
                     y∘(ıx) ≃ y ≝
 λB,C. pres_id_ … (is_edst … C).
definition clos_comp: ∀B: est. ∀C: edst B. ∀x1,x2,x3: B. ∀y: C x1. ∀d: x1 ≃ x2. ∀d': x2 ≃ x3.
                       y∘d∘d' ≃ y∘(d•d') ≝
 λB,C. clos_comp_ … (is_edst … C).

definition constant_edst: ∀A: est. est → edst A ≝
 λA,Y. mk_edst … (λ_. Y) (λx1,x2,d,y. y) ?.
 % [ #x1 #x2 #d #y #y' #h @h
   | #x1 #x2 #_ #_ #y @(ıy)
   | #_ #y @(ıy)
   | #x1 #x2 #x3 #y #_ #_ @(ıy)
   ]
qed.

lemma inverse_subst: ∀B: est. ∀C: edst B. ∀x1,x2: B. ∀d: x1 ≃ x2. ∀y: C x2.
 y∘d⁻¹∘d ≃ y.
 #B #C #x1 #x2 #d #y
 @tra [ @(y∘d⁻¹•d)
      | @clos_comp
      | @tra [ @(y∘ıx2) | @not_dep | @pres_id ]
      ]
qed.

lemma inverse_subst2: ∀B: est. ∀C: edst B. ∀x1,x2: B. ∀d: x1 ≃ x2. ∀y: C x1.
 y∘d∘d⁻¹ ≃ y.
 #B #C #x1 #x2 #d #y @tra [ @(y∘d•d⁻¹)
                          | @clos_comp
                          | @tra [ @(y∘(ıx1)) | @not_dep | @pres_id ]
                          ]
qed.

lemma eq_reflexivity: ∀B: est. ∀b1,b2: B. b1 = b2 → b1 ≃ b2.
 #B #b1 #b2 #h @(rewrite_l … b1 (λz. b1 ≃ z) (ıb1) … h)
qed.

definition eprop: Type[2] ≝ prop.

definition eprop_into_ecl: eprop → ecl ≝
 λP. mk_ecl P (λ_,_. ⊤) ?.
 % //
qed.

definition eprops: Type[1] ≝ props.

definition eprops_into_est: eprops → est ≝
 λP. mk_est P (λ_,_. ⊤) ?.
 % //
qed.

