include "reduction_old_preamble.ma".
definition test:
  〈〈x0,x0〉:〈x0,xF〉〉 = 
    ((succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
     〈〈x0,x0〉:〈x0,x0〉〉)))))))))))))))).
apply (refl_eq word16 〈〈x0,x0〉:〈x0,xF〉〉); 
qed.
