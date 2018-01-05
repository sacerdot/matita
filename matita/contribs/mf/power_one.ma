(* (C) 2014 Luca Bressan *)

include "model.ma".

definition power_one: ecl ≝
 mk_ecl props (λz,z'. (z → z') ∧ (z' → z)) ?.
 % [ #x % #h @h
   | #x #y * #h1 #h2 % [ @h2 | @h1 ]
   | #x #y #z #h1 #h2 % cases h1 #hxy #hyx cases h2 #hyz #hzy
     [ #hx @(hyz (hxy hx))
     | #hz @(hyx (hzy hz))
     ]
   ]
qed.

definition dpower_one: ∀I: ecl. edcl I.
 #I %
 [ #i @power_one
 | #i1 #i2 #e #p @p
 | %
   [ #i1 #i2 #_ #y #y' #h @h
   | #i1 #i2 #_ #_ @Rfl
   | #i @Rfl
   | #i1 #i2 #i3 #y #_ #_ @Rfl
   ]
 ]
qed.

