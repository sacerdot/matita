(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/test/prova".

include "LAMBDA-TYPES/LambdaDelta-1/preamble.ma".

alias id "Abst" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/B.ind#xpointer(1/1/2)".
alias id "Abbr" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/B.ind#xpointer(1/1/1)".
(*
alias id "B" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/B.ind#xpointer(1/1)".
*)
theorem not_abbr_abst:
 (Abbr\neq Abst)
.(* tactics: 7 *)
whd in \vdash (%).
intros 1 (H).
letin DEFINED \def (\lambda ee:B
 .match ee in B return \lambda _:B.Prop with 
  [Abbr\rArr True|Abst\rArr False|Void\rArr False]).(* extracted *)
cut (DEFINED Abbr) as ASSUMED;
[rewrite > H in ASSUMED:(%) as (H0)
|apply I
].
elim H0 using False_ind names 0.(* 2 C I 2 0 *)
qed.

alias id "Abbr" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/B.ind#xpointer(1/1/1)".
alias id "Abst" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/B.ind#xpointer(1/1/2)".
alias id "Appl" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/F.ind#xpointer(1/1/1)".
alias id "Bind" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/K.ind#xpointer(1/1/1)".
alias id "Cast" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/F.ind#xpointer(1/1/2)".
alias id "ex2_sym" = "cic:/matita/LAMBDA-TYPES/Level-1/Base/types/props/ex2_sym.con".
alias id "ex3_2_ind" = "cic:/matita/LAMBDA-TYPES/Level-1/Base/types/defs/ex3_2_ind.con".
alias id "Flat" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/K.ind#xpointer(1/1/2)".
alias id "lift" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/lift/defs/lift.con".
alias id "or3_ind" = "cic:/matita/LAMBDA-TYPES/Level-1/Base/types/defs/or3_ind.con".
alias id "pr0_beta" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/3)".
alias id "pr0" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1)".
alias id "pr0_comp" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/2)".
alias id "pr0_delta" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/5)".
alias id "pr0_epsilon" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/7)".
alias id "pr0_ind" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0_ind.con".
alias id "pr0_subst0_fwd" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/props/pr0_subst0_fwd.con".
alias id "pr0_upsilon" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/4)".
alias id "pr0_zeta" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/defs/pr0.ind#xpointer(1/1/6)".
alias id "s" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/s/defs/s.con".
alias id "subst0_both" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/defs/subst0.ind#xpointer(1/1/4)".
alias id "subst0" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/defs/subst0.ind#xpointer(1/1)".
alias id "subst0_confluence_neq" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/subst0/subst0_confluence_neq.con".
alias id "subst0_fst" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/defs/subst0.ind#xpointer(1/1/2)".
alias id "subst0_gen_head" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/fwd/subst0_gen_head.con".
alias id "subst0_gen_lift_ge" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/fwd/subst0_gen_lift_ge.con".
alias id "subst0_lift_ge_s" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/props/subst0_lift_ge_s.con".
alias id "subst0_snd" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/defs/subst0.ind#xpointer(1/1/3)".
alias id "subst0_subst0_back" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/subst0/subst0_subst0_back.con".
alias id "subst0_trans" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/subst0/subst0/subst0_trans.con".
alias id "T" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/T.ind#xpointer(1/1)".
alias id "THead" = "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/T/defs/T.ind#xpointer(1/1/3)".

inline procedural
   "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/pr0/props/pr0_subst0.con".
(*
inline procedural
   "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/ty3/pr3/ty3_sred_wcpr0_pr0.con".

inline procedural
   "cic:/Coq/Reals/RiemannInt/FTC_Riemann.con".
*)
