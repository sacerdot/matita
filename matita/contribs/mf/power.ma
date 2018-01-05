(* (C) 2014 Luca Bressan *)

include "model.ma".

definition fun_to_power_one: est → ecl ≝ 
 λB. mk_ecl
 (Σh: fun_to_props B. ∀y1,y2: B. eq … y1 y2 → (conj (h y1 → h y2) (h y2 → h y1)))
 (λz,z'. ∀y: B. conj ((Sig1 … z) y → (Sig1 … z') y)
                         (implies ((Sig1 … z') y) ((Sig1 … z) y)))
 ?.
 % [ #x #y % #h @h 
   | #x #x' #h #b % #k cases (h b) [ #_ #r | #r #_ ] @(r k) 
   | #x #x' #x'' #h1 #h2 #b cases (h1 b) #k10 #k01 cases (h2 b) #k21 #k12 %
     #r [ @(k21 (k10 r)) | @(k01 (k12 r)) ]
   ]
qed.

