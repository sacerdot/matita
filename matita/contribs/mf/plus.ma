(* (C) 2014 Luca Bressan *)

include "model.ma".
include "pisigma.ma".

definition eplus: est → est → est ≝
 λB,C. mk_est
 (B+C)
 (λz,z'. (∃b: B. ∃b': B. (z = inl … b) ∧ ((z' = inl … b') ∧ (b ≃ b')))
         ∨ (∃c: C. ∃c': C. (z = inr … c) ∧ ((z' = inr … c') ∧ (c ≃ c'))))
 ?.
 % [ * #x [ %1 | %2 ] %{x} %{x} %
     [ 1,3: @(reflexivity …)
     | 2: @(mk_conj … (reflexivity …) (ıx)) 
     | 4: @(mk_conj … (reflexivity …) (ıx))
     ]
   | #z1 #z2 * * #x1 * #x2 * #h1 * #h2 #e [ %1 | %2 ] %{x2} %{x1} %
     [ 1,3: @h2
     | 2,4: % [ 1,3: @h1
              | 2,4: @(e⁻¹)
              ]
     ]
   | #z1 #z2 #z3 * * #x1 * #x12 * #h1 * #h12 #e12 * * #x23 * #x3 * #h23 * #h3 #e23
     [ %1 %{x1} %{x3} %
       [ @h1
       | % [ @h3
           | @(e12• 
               (rewrite_l … x23 (λz. z ≃ x3) e23 … 
                (injectivity_inl … (h12⁻¹•h23)⁻¹)))
           ]
       ]
     | @(falsum_rect_CProp0 … (plus_clash … (h12⁻¹•h23)))
     | @(falsum_rect_CProp0 … (plus_clash … ((h12⁻¹•h23)⁻¹)))
     | %2 %{x1} %{x3} %
       [ @h1
       | % [ @h3
           | @(e12•
               (rewrite_l … x23 (λz. z ≃ x3) e23 …
                (injectivity_inr … (h12⁻¹•h23)⁻¹)))
           ]
       ]
     ]
   ]
qed.

definition einl: ∀B,C: est. eto B (eplus B C) ≝
 λB,C. 〈inl …, ?〉.
 #x #y #h %1 %{x} %{y} % % [ % | @h ]
qed.

definition einr: ∀B,C: est. eto C (eplus B C) ≝
 λB,C. 〈inr …, ?〉.
 #x #y #h %2 %{x} %{y} % % [ % | @h ]
qed.

lemma injectivity_einl: ∀B,C: est. ∀b,b': B. (einl B C)˙b ≃ (einl B C)˙b' → b ≃ b'.
 #B #C #b #b' * * #z * #z' * #h1 * #h2 #h3
 [ @(rewrite_l … z (λw. w ≃ b')
     (rewrite_l … z' (λw. z ≃ w) h3 … (symmetry … (injectivity_inl … h2))) …
     (symmetry … (injectivity_inl … h1)))
 | @(falsum_rect_CProp0 … (plus_clash … h1))
 ]
qed.

lemma injectivity_einr: ∀B,C: est. ∀c,c': C. (einr B C)˙c ≃ (einr B C)˙c' → c ≃ c'.
 #B #C #c #c' * * #z * #z' * #h1 * #h2 #h3
 [ @(falsum_rect_CProp0 … (plus_clash … (symmetry … h1)))
 | @(rewrite_l … z (λw. w ≃ c')
     (rewrite_l … z' (λw. z ≃ w) h3 … (symmetry … (injectivity_inr … h2))) …
     (symmetry … (injectivity_inr … h1)))
 ]
qed.

definition edplus: ∀I: est. edst I → edst I → edst I.
 #I #B #C %
 [ @(λi. eplus (B i) (C i))
 | #i1 #i2 #e * #x [ @(inl … (x∘e)) | @(inr … (x∘e)) ]
 | % [ #i1 #i2 #e * #x1 * #x2 #h
       cases h * #z1 * #z2 * #h1 * #h2 #d
         [ 1: %1 %{(x1∘e)} %{(x2∘e)} % [ % | % [ % | @(pres_eq … (injectivity_einl … h)) ]]
         | 2,4: @(falsum_rect_CProp0 … (plus_clash … h1))
         | 3: @(falsum_rect_CProp0 … (plus_clash … h2⁻¹))
         | 5,7: @(falsum_rect_CProp0 … (plus_clash … h1⁻¹))
         | 6: @(falsum_rect_CProp0 … (plus_clash … h2))
         | 8: %2 %{(x1∘e)} %{(x2∘e)} % [ % | % [ % | @(pres_eq … (injectivity_einr … h)) ]]
         ]
     | #i1 #i2 #e1 #e2 * #x [ %1 | %2 ] %{(x∘e1)} %{(x∘e2)} %
       [ 1,3: % | 2,4: % [ 1,3: % | 2,4: @not_dep ]]
     | #i * #x [ %1 | %2 ] %{(x∘ıi)} %{x} %
       [ 1,3: % | 2,4: % [ 1,3: % | 2,4: @pres_id ]]
     | #i1 #i2 #i3 * #x #d1 #d2 [ %1 | %2 ] %{(x∘d1∘d2)} %{(x∘d1•d2)} %
       [ 1,3: % | 2,4: % [ 1,3: % | 2,4: @clos_comp ]]
     ]
 ]
qed.

