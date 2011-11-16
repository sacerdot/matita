include "Basic_2/reducibility/tpr.ma".

(* CONTEXT-FREE WEAK HEAD NORMAL TERMS **************************************)

definition twhnf: term → Prop ≝
   NF … tpr (thom …).

interpretation
   "context-free weak head normality (term)"
   'WHdNormal T = (twhnf T).

(* Basic properties *********************************************************)
