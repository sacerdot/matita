(* (C) 2014 Luca Bressan *)

include "model.ma".
include "pisigma.ma".
include "pisigma2.ma".

definition en0: est ≝
 mk_est n0 (λz,z'. z = z') ?.
 % #x [ % | #y * % | #y #z #h * @h ]
qed.

definition en0_rect_Type0: ∀Q: edst en0. epi en0 Q ≝ 
 λQ. 〈n0_rect_Type0 …, ?〉.
 @(n0_rect_CProp0).
qed.

definition en0_rect_Type1: ∀Q: edcl (est_into_ecl en0). ePi … Q ≝ 
 λQ. 〈n0_rect_Type1 …, ?〉.
 @(n0_rect_CProp1).
qed.

definition edn0: ∀I: est. edst I ≝ λI. constant_edst I en0.

