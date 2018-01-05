(* (C) 2014 Luca Bressan *)

include "model.ma".
include "pisigma.ma".

definition en1: est ≝
 mk_est n1 (λz,z'. z = z') ?.
 % #x [ % | #y * % | #y #z * * % ]
qed.

definition estar: en1 ≝ ⋆.

definition en1_rect_Type0: ∀Q: edst en1. eto (Q estar) (epi en1 Q).
 #Q @(〈?, ?〉)
 [ #h @(〈n1_rect_Type0 (λw. Q w) h, ?〉)
   * * #d
   @(rewrite_l … h (λz. (subst … d z) ≃ z) … (n1_rect_Type0 … h estar) (reflexivity …))
   @tra [ @(h∘(ı…)) | @not_dep | @pres_id ]
 | #y1 #y2 #d * @d
 ]
qed.

definition edn1: ∀I: est. edst I ≝ λI. constant_edst I en1.

