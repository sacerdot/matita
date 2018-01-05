(* (C) 2014 Luca Bressan *)

include "model.ma".

definition eDe: est → est.
 #I %
 [ @(De I)
 | @De_rect_Type1
   [ #z @(z = c_unit …)
   | #i * [ 2: #i' @(i ≃ i') | 3,4: #_ #_ ] @falsum
   | #F1 #F2 #H1 #H2 * [ 3: #F1' #F2' @(H1 F1' ∧ H2 F2') | 2: #_ | 4: #_ #_ ] @falsum
   | #F1 #F2 #H1 #H2 * [ 4: #F1' #F2' @(H1 F1' ∧ H2 F2') | 2: #_ | 3: #_ #_ ] @falsum
   ]
 | %
   [ @De_rect_CProp0
     [ %
     | @rfl
     | #F1 #F2 #H1 #H2 % [ @H1 | @H2 ]
     | #F1 #F2 #H1 #H2 % [ @H1 | @H2 ]
     ]
   | @De_rect_CProp0
     [ * [ #_ % | #i #abs @(De_clash_unit_ev I i abs)
         | #F1 #F2 #abs @(De_clash_unit_times I F1 F2 abs)
         | #F1 #F2 #abs @(De_clash_unit_plus I F1 F2 abs) ]
     | #i * [ @falsum_rect_CProp0 | #i' @sym | 3,4: #F1' #F2' #abs @abs ]
     | #F1 #F2 #H1 #H2 * [ @falsum_rect_CProp0 | #i' #abs @abs 
                         | #F1' #F2' * #K1 #K2 % [ @H1 @K1 | @H2 @K2 ]
                         | #F1' #F2' #abs @abs ]
     | #F1 #F2 #H1 #H2 * [ @falsum_rect_CProp0 | #i' #abs @abs
                         | #F1' #F2' #abs @abs
                         | #F1' #F2' * #K1 #K2 % [ @H1 @K1 | @H2 @K2 ] ]
     ]
   | @De_rect_CProp0
     [ * [ #F'' #_ #h @h
         | #i' #F'' #abs @(falsum_rect_CProp0 … (De_clash_unit_ev I i' abs))
         | #F1' #F2' #F'' #abs @(falsum_rect_CProp0 … (De_clash_unit_times I F1' F2' abs))
         | #F1' #F2' #F'' #abs @(falsum_rect_CProp0 … (De_clash_unit_plus I F1' F2' abs))
         ]
     | #i * [ #F'' @falsum_rect_CProp0
            | #i' * [ #_ #abs @abs
                    | #i'' @tra
                    | 3,4: #F1'' #F2'' #_ #abs @abs
                    ]
            | 3,4: #F1' #F2' #F'' @falsum_rect_CProp0
            ]
     | #F1 #F2 #H1 #H2 * [ #F'' @falsum_rect_CProp0
                         | #i' #F'' @falsum_rect_CProp0
                         | #F1' #F2' * [ #_ #abs @abs
                                       | #i'' #_ #abs @abs
                                       | #F1'' #F2'' * #H11 #H12 * #H21 #H22 %
                                         [ @(H1 F1' F1'' H11 H21) | @(H2 F2' F2'' H12 H22) ]
                                       | #F1'' #F2'' #_ #abs @abs
                                       ]
                         | #F1' #F2' #F'' @falsum_rect_CProp0
                         ]
     | #F1 #F2 #H1 #H2 * [ #F'' @falsum_rect_CProp0
                         | #i' #F'' @falsum_rect_CProp0
                         | #F1' #F2' #F'' @falsum_rect_CProp0
                         | #F1' #F2' * [ #_ #abs @abs
                                       | #i'' #_ #abs @abs
                                       | #F1'' #F2'' #_ #abs @abs
                                       | #F1'' #F2'' * #H11 #H12 * #H21 #H22 %
                                         [ @(H1 F1' F1'' H11 H21) | @(H2 F2' F2'' H12 H22) ]
                                       ]
                         ]
     ]
   ]
 ]
qed.

