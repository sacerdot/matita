(* (C) 2014 Luca Bressan *)

include "model.ma".

definition epi: ∀B: est. edst B → est ≝
 λB,C. mk_est
 (Σh: ∀y: sup B. sup (dsup … C y). ∀y1,y2: sup B. ∀d: y1 ≃ y2. subst … d (h y1) ≃ h y2)
 (λz,z'. ∀y: sup B. eq … ((sig1 … z) y) ((sig1 … z') y))
 ?.
 % [ #x #y @(ı…)
   | #x #x' #h #y @((h …)⁻¹)
   | #x #x' #x'' #h1 #h2 #y @((h1 …)•(h2 …))
   ]
qed.

interpretation "Properness of set morphisms" 'ap f d = (sig2 ?? f ?? d).
interpretation "Support of set morphisms" 'sup_f f d = (sig1 ?? f d).

definition eto: est → est → est ≝
 λB,C. epi B (constant_edst B C).

definition lift: ∀A,B: est. sup (eto A B) → edst B → edst A ≝
 λA,B,f,C.
 mk_edst A (λa: sup A. dsup … C (sig1 … f a))
 (λx1,x2,d. subst … (sig2 … f … d)) ?.
 letin B' ≝ (constant_edst A B)
 % [ #x1 #x2 #d #y #y' #e @(pres_eq … e)
   | #x1 #x2 #d1 #d2 #y @not_dep
   | #x #y
     cut (y∘(ı(f˙x)) ≃ y)
     [ @pres_id
     | cut (y∘(f◽(ıx)) ≃ y∘ı(f˙x))
       [ @not_dep
       | @tra
       ]
     ]
   | #x1 #x2 #x3 #y #d1 #d2
     cut (y∘(f◽d1)∘(f◽d2) ≃ y∘(f◽d1)•(f◽d2))
     [ @clos_comp
     | cut (y∘(f◽d1)•(f◽d2) ≃ y∘(f◽(d1•d2)))
       [ @not_dep
       | #e1 #e2 @(e2•e1)
       ]
     ]
   ]
qed.

definition shift: ∀B: est. edst B → est → edst B.
 #B #C #D %
 [ #b @(eto (C b) D)
 | #x1 #x2 #d #f %
   [ #y @(f˙(y∘d⁻¹))
   | #y1 #y2 #e @(f◽…) @pres_eq @e
   ]
 | %
   [ #x1 #x2 #d #f1 #f2 #h #y @(h (y∘d⁻¹))
   | #x1 #x2 #d1 #d2 #f #y @(f◽…) @not_dep
   | #x #f #y @(f◽…) cut (y∘(ıx) ≃ y)
     [ @pres_id
     | #h @tra [ @(y∘(ıx)) | @not_dep | @pres_id ]
     ]
   | #x1 #x2 #x3 #f #d1 #d2 #y @(f◽…)
     @tra [ @(y∘(d2⁻¹•d1⁻¹)) | @clos_comp | @not_dep ]
   ]
 ]
qed.

definition esigma: ∀B: est. edst B → est ≝ 
 λB,C. mk_est 
 (Σy: B. C y)
 (λz,z'. ∃d: π1 z ≃ π1 z'. (π2 z)∘d ≃ π2 z')
 ?.
 % [ * #b #c %{ıb} @pres_id
   | * #b #c * #b' #c' * #d #h %{(d⁻¹)}
     @tra [ @(c∘d•d⁻¹)
          | @tra [ @(c∘d∘d⁻¹) | @pres_eq @(h⁻¹) | @clos_comp ]
          | @tra [ @(c∘ıb) | @not_dep | @pres_id ]
          ]
   | * #b #c * #b' #c' * #b'' #c'' * #d1 #h1 * #d2 #h2 %{(d1•d2)}
     @tra [ @(c∘d1∘d2)
          | @sym @clos_comp
          | @tra [ @(c'∘d2) | @pres_eq @h1 | @h2 ]
          ]
   ]
qed.

definition etimes: est → est → est ≝
 λB,C. esigma B (constant_edst B C).

definition mk_esigma: ∀B: est. ∀C: edst B. epi B (shift B C (esigma B C)).
 #B #C %
 [ #b %
   [ #c @〈b, c〉
   | #c1 #c2 #d %{(ıb)}
     @tra [ @c1 | @pres_id | @d ]
   ]
 | #b1 #b2 #d #y %{d} @inverse_subst
 ]
qed.

definition esig1: ∀B: est. ∀C: edst B. sup (eto (esigma B C) B) ≝
 λB,C. 〈π1 …, ?〉.
 * #b1 #c1 * #b2 #c2 * #db #dc @db
qed.

definition esig2: ∀B: est. ∀C: edst B. sup (epi (esigma B C) (lift … (esig1 …) C …)) ≝ 
 λB,C. 〈π2 …, ?〉.
 * #b1 #c1 * #b2 #c2 * #db #dc @dc
qed.

