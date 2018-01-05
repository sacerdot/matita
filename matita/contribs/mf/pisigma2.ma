(* (C) 2014 Luca Bressan *)

include "model.ma".

definition ePi: ∀B: ecl. edcl B → ecl ≝
 λB,C. mk_ecl
 (Σh: ∀y: Sup B. Sup (dSup … C y). ∀y1,y2: Sup B. ∀d: y1 ≃ y2. Subst … d (h y1) ≃ h y2)
 (λz,z'. ∀y: Sup B. Eq … ((Sig1 … z) y) ((Sig1 … z') y))
 ?.
 % [ #x #y @(ı…)
   | #x #x' #h #y @((h …)⁻¹)
   | #x #x' #x'' #h1 #h2 #y @((h1 …)•(h2 …))
   ]
qed.

interpretation "Properness of col morphisms" 'ap f d = (Sig2 ?? f ?? d).
interpretation "Support of col morphisms" 'sup_f f d = (Sig1 ?? f d).

definition eTo: ecl → ecl → ecl ≝
 λB,C. ePi B (constant_edcl B C).

definition Lift: ∀A,B: ecl. Sup (eTo A B) → edcl B → edcl A ≝
 λA,B,f,C.
 mk_edcl A (λa: Sup A. dSup … C (Sig1 … f a))
 (λx1,x2,d. Subst … (Sig2 … f … d)) ?.
 letin B' ≝ (constant_edcl A B)
 % [ #x1 #x2 #d #y #y' #e @(Pres_eq … e)
   | #x1 #x2 #d1 #d2 #y @Not_dep
   | #x #y
     cut (y∘(ı(f˙x)) ≃ y)
     [ @Pres_id
     | cut (y∘(f◽(ıx)) ≃ y∘ı(f˙x))
       [ @Not_dep
       | @Tra
       ]
     ]
   | #x1 #x2 #x3 #y #d1 #d2
     cut (y∘(f◽d1)∘(f◽d2) ≃ y∘(f◽d1)•(f◽d2))
     [ @Clos_comp
     | cut (Eq (C (f˙x3)) (y∘(f◽d1)•(f◽d2)) (y∘(f◽(d1•d2))))
       [ @Not_dep
       | #e1 #e2 @(e2•e1)
       ]
     ]
   ]
qed.

definition Shift: ∀B: ecl. edcl B → ecl → edcl B.
 #B #C #D %
 [ #b @(eTo (C b) D)
 | #x1 #x2 #d #f %
   [ #y @(f˙(y∘d⁻¹))
   | #y1 #y2 #e @(f◽…) @Pres_eq @e
   ]
 | %
   [ #x1 #x2 #d #f1 #f2 #h #y @(h (y∘d⁻¹))
   | #x1 #x2 #d1 #d2 #f #y @(f◽…) @Not_dep
   | #x #f #y @(f◽…) cut (y∘(ıx) ≃ y)
     [ @Pres_id
     | #h @Tra [ @(y∘(ıx)) | @Not_dep | @Pres_id ]
     ]
   | #x1 #x2 #x3 #f #d1 #d2 #y @(f◽…)
     @Tra [ @(y∘(d2⁻¹•d1⁻¹)) | @Clos_comp | @Not_dep ]
   ]
 ]
qed.

definition eSigma: ∀B: ecl. edcl B → ecl ≝ 
 λB,C. mk_ecl
 (Σy: B. C y)
 (λz,z'. ∃d: π1 z ≃ π1 z'. (π2 z)∘d ≃ π2 z')
 ?.
 % [ * #b #c %{ıb} @Pres_id
   | * #b #c * #b' #c' * #d #h %{(d⁻¹)}
     @Tra [ @(c∘d•d⁻¹)
          | @Tra [ @(c∘d∘d⁻¹) | @Pres_eq @(h⁻¹) | @Clos_comp ]
          | @Tra [ @(c∘ıb) | @Not_dep | @Pres_id ]
          ]
   | * #b #c * #b' #c' * #b'' #c'' * #d1 #h1 * #d2 #h2 %{(d1•d2)}
     @Tra [ @(c∘d1∘d2)
          | @Sym @Clos_comp
          | @Tra [ @(c'∘d2) | @Pres_eq @h1 | @h2 ]
          ]
   ]
qed.

definition eTimes: ecl → ecl → ecl ≝
 λB,C. eSigma B (constant_edcl B C).

definition mk_eSigma: ∀B: ecl. ∀C: edcl B. ePi B (Shift B C (eSigma B C)).
 #B #C %
 [ #b %
   [ #c @〈b, c〉
   | #c1 #c2 #d %{(ıb)}
     @Tra [ @c1 | @Pres_id | @d ]
   ]
 | #b1 #b2 #d #y %{d} @inverse_Subst
 ]
qed.

definition eSig1: ∀B: ecl. ∀C: edcl B. Sup (eTo (eSigma B C) B) ≝
 λB,C. 〈π1 …, ?〉.
 * #b1 #c1 * #b2 #c2 * #db #dc @db
qed.

definition eSig2: ∀B: ecl. ∀C: edcl B. Sup (ePi (eSigma B C) (Lift … (eSig1 …) C …)) ≝ 
 λB,C. 〈π2 …, ?〉.
 * #b1 #c1 * #b2 #c2 * #db #dc @dc
qed.

