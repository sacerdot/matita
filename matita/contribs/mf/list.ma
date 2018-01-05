(* (C) 2014 Luca Bressan *)

include "model.ma".
include "pisigma.ma".

definition proj1: ∀C: est. ∀r: list (Σx. Σy. x ≃ y). list C ≝
 λC. lift_to_list … (π1 …).

definition proj2: ∀C: est. ∀r: list (Σx. Σy. x ≃ y). list C ≝
 λC. lift_to_list … (λz: Σx. Σy. x ≃ y. π1 (π2 z)).

definition elist: est → est ≝
 λC. mk_est
 (list C)
 (λz,z'. ∃l: list (Σx. Σy. x ≃ y). (proj1 … l = z) ∧ (proj2 … l = z'))
 ?.
 % [ @list_rect_CProp0 
     [ %{ϵ} % %
     | #l #c * #r * #h1 #h2
       %{⌈r, 〈c, 〈c, ıc〉〉⌉}
       % [ @(rewrite_l … ⌈proj1 … r, c⌉
             (λz. z = ⌈l, c⌉)
             (rewrite_l … (proj1 … r) (λz. ⌈proj1 … r, c⌉ = ⌈z, c⌉) (reflexivity …) … h1)
             … (reflexivity …))
         | @(rewrite_l … ⌈proj2 … r, c⌉
             (λz. z = ⌈l, c⌉)
             (rewrite_l … (proj2 … r) (λz. ⌈proj2 … r, c⌉ = ⌈z, c⌉) (reflexivity …) … h2)
             … (reflexivity …))
         ]
     ]
   | @list_rect_CProp0 
     [ *
       [ //
       | #l2' #c * *
         [ * #_ #abs @(falsum_rect_CProp0 … (list_clash … abs))
         | #r #s * normalize #abs @(falsum_rect_CProp0 … (list_clash … abs⁻¹))
         ]
       ]
     | #l1' #c1 #h *
       [ * *
         [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
         | #r #s * #_ normalize #abs @(falsum_rect_CProp0 … (list_clash … abs⁻¹))
         ]
       | #l2' #c2 * *
         [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
         | #r #s * #h1 #h2
           cut (∃l. (proj1 … l = l2') ∧ (proj2 … l = l1'))
           [ @(h l2') %{r} % [ @(injectivity_cons1 … h1) | @(injectivity_cons1 … h2) ]
           | * #r' * #h1' #h2' %{⌈r', 〈c2, 〈c1, ?〉〉⌉}
             [ cut (π1 (π2 s) = c2)
               [ cut (⌈proj2 … r, π1 (π2 s)⌉ = ⌈l2', c2⌉)
                 [ @(rewrite_l … (proj2 … ⌈r, s⌉)
                     (λz. z = ⌈l2', c2⌉) h2 … (reflexivity …))
                 | @injectivity_cons2
                 ]
               | #k2 cut (π1 s = c1)
                 [ cut (⌈proj1 … r, sig1 … s⌉ = ⌈l1', c1⌉)
                   [ @(rewrite_l … (proj1 … ⌈r, s⌉)
                       (λz. z = ⌈l1', c1⌉) h1 … (reflexivity …))
                   | @injectivity_cons2
                   ]
                 | #k1 cut (π1 (π2 s) ≃ π1 s)
                   [ @((π2 (π2 s))⁻¹)
                   | #e cut (c2 ≃ π1 s)
                     [ @(rewrite_l … (π1 (π2 s)) (λz. z ≃ π1 s) e … k2)
                     | #e' @(rewrite_l … (π1 s) (λz. c2 ≃ z) e' … k1)
                     ]
                   ]
                 ]
               ]
             | 
               % [ @(rewrite_l … (proj1 … r') (λz. ⌈proj1 … r', c2⌉ = ⌈z, c2⌉) (reflexivity …) … h1')
                 | @(rewrite_l … (proj2 … r') (λz. ⌈proj2 … r', c1⌉ = ⌈z, c1⌉) (reflexivity …) … h2')
                 ]
             ]
           ]
         ]
       ]
     ]
   | @list_rect_CProp0 
     [ *
       [ *
         [ //
         | #l3' #c3 #_ //
         ]
       | #l2 #c2 *
         [ #_ #_ %{ϵ} % %
         | #l3' #c3 * *
           [ * #_ #abs @(falsum_rect_CProp0 … (list_clash … abs))
           | #r1' #s1 * #abs @(falsum_rect_CProp0 … (list_clash … abs⁻¹))
           ]
         ]
       ]
     | #l1' #c1 #h *
       [ *
         [ * | #l3' #c3 * ] *
         [ 1,3: * #abs @(falsum_rect_CProp0 … (list_clash … abs))
         | 2,4: #r' #s * #_ #abs @(falsum_rect_CProp0 … (list_clash … abs⁻¹))
         ]
       | #l2' #c2 *
         [ #_ * *
           [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
           | #r' #s * #_ #abs @(falsum_rect_CProp0 … (list_clash … abs⁻¹))
           ]
         | #l3' #c3 * *
           [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
           | #r1 #s1 * #h1 #h2 * *
             [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
             | #r2 #s2 * #h3 #h4
               cut (⌈proj1 … r1, π1 s1⌉ = ⌈l1', c1⌉)
               [ @(rewrite_l … (proj1 … ⌈r1, s1⌉)
                   (λz. z = ⌈l1', c1⌉) h1 … (reflexivity …))
               | -h1 #h1
                 cut (⌈proj2 … r1, π1 (π2 s1)⌉ = ⌈l2', c2⌉)
                 [ @(rewrite_l … (proj2 … ⌈r1, s1⌉)
                     (λz. z = ⌈l2', c2⌉) h2 … (reflexivity …))
                 | -h2 #h2
                   cut (⌈proj1 … r2, π1 s2⌉ = ⌈l2', c2⌉)
                   [ @(rewrite_l … (proj1 … ⌈r2, s2⌉)
                       (λz. z = ⌈l2', c2⌉) h3 … (reflexivity …))
                   | -h3 #h3
                     cut (⌈proj2 … r2, π1 (π2 s2)⌉ = ⌈l3', c3⌉)
                     [ @(rewrite_l … (proj2 … ⌈r2, s2⌉)
                         (λz. z = ⌈l3', c3⌉) h4 … (reflexivity …))
                     | -h4 #h4
                       cut (∃l. (proj1 … l = l1') ∧ (proj2 … l = l3'))
                       [ @(h l2' l3')
                         [ %{r1} @(mk_conj … (injectivity_cons1 … h1) (injectivity_cons1 … h2))
                         | %{r2} @(mk_conj … (injectivity_cons1 … h3) (injectivity_cons1 … h4))
                         ]
                       | * #r * #e1 #e2 %{⌈r, 〈c1, 〈c3, ?〉〉⌉}
                         [ @(tra …
                             (rewrite_l … (π1 s1) (λz. z ≃ c2)
                              (rewrite_l … (π1 (π2 s1)) (λz. π1 s1 ≃ z) (π2 (π2 s1))
                                … (injectivity_cons2 … h2))
                              … (injectivity_cons2 … h1))
                             (rewrite_l … (π1 (π2 s2)) (λz. c2 ≃ z)
                               (rewrite_l … (π1 s2) (λz. z ≃ π1 (π2 s2)) (π2 (π2 s2))
                                … (injectivity_cons2 … h3))
                              … (injectivity_cons2 … h4)))
                         | %
                           [ @(rewrite_l … (proj1 … r) (λz. ⌈proj1 … r, c1⌉ = ⌈z, c1⌉) (reflexivity …) … e1)
                           | @(rewrite_l … (proj2 … r) (λz. ⌈proj2 … r, c3⌉ = ⌈z, c3⌉) (reflexivity …) … e2)
                           ]
                         ]
                       ]
                     ]
                   ]
                 ]
               ]
             ]
           ]
         ]
       ]
     ]
   ]
qed.

definition eepsilon: ∀C: est. elist C ≝ epsilon.

definition econs: ∀C: est. eto (elist C) (eto C (elist C)) ≝
 λC. 〈λl. 〈cons … l, ?〉, ?〉.
 [ #c1 #c2 #d
   cut (subst C (constant_edst C (elist C)) c1 c2 d ⌈l, c1⌉ = ⌈l, c1⌉)
   [ %
   | #h @(rewrite_l (list (sup C)) ⌈l, c1⌉ (λz. eq (elist C) z ⌈l, c2⌉) ?
          (subst C (constant_edst C (elist C)) c1 c2 d ⌈l, c1⌉) h)
     @(list_rect_CProp0 … l)
     [ %{⌈ϵ, 〈c1, 〈c2, d〉〉⌉} % %
     | #l' #c * *
       [ * #abs @(falsum_rect_CProp0 … (list_clash … abs))
       | #r' #s * #h1 #h2 %{⌈⌈r', 〈c, 〈c, ıc〉〉⌉, 〈c1, 〈c2, d〉〉⌉} %
         [ change with (⌈⌈proj1 … , ?⌉, ?⌉) in ⊢ (??%?);
           cut (proj1 … r' = l')
           [ @(injectivity_cons1 … h1)
           | #h @(rewrite_l ????? h) @reflexivity
           ]
         | @(rewrite_l … ⌈⌈proj2 … r', c⌉, c2⌉ (λz. z = ⌈⌈l', c⌉, c2⌉) ?
             (proj2 … ⌈⌈r', 〈c, 〈c, ıc〉〉⌉, 〈c1, 〈c2, d〉〉⌉) (reflexivity …))
           cut (proj2 … r' = l')
           [ @(injectivity_cons1 …
               (rewrite_l … (proj2 … ⌈r', s⌉) (λz. ⌈proj2 … r', sig1 … (sig2 … s)⌉ = z)
                (reflexivity …) ⌈l', c2⌉ h2))
           | #h @(rewrite_l … l' (λz. ⌈⌈z, c⌉, c2⌉ = ⌈⌈l', c⌉, c2⌉) (reflexivity …)
                  (proj2 C r') (symmetry … h))
           ]
         ]
       ]
     ]
   ]
 | #l1 #l2 * #r * #h1 #h2 #c %{⌈r, 〈c, 〈c, ıc〉〉⌉} %
   [ @(rewrite_l … l1 (λz. ⌈z, c⌉ = ⌈l1, c⌉) (reflexivity …) (proj1 … r) (symmetry … h1))
   | @(rewrite_l … l2 (λz. ⌈z, c⌉ = ⌈l2, c⌉) (reflexivity …) (proj2 … r) (symmetry … h2))
   ]
 ]
qed.

