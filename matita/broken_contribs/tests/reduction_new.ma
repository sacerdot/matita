include "reduction_new_preamble.ma".

ndefinition test:
 〈〈x0,x0〉:〈x0,xF〉〉 =
    ((succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
    (succ_w16(succ_w16(succ_w16(succ_w16
     〈〈x0,x0〉:〈x0,x0〉〉)))))))))))))))).
napply (refl_eq word16 〈〈x0,x0〉:〈x0,xF〉〉); 
nqed.
