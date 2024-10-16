(*
lemma pippo (f):
      𝐬❨⫯f❩ ≐ ⫯𝐬❨f❩.
#f * // #p
<subst_push_succ
<subst_unwind_dapp <subst_unwind_dapp
<fbr_dapp_push_dx_succ <term_next_unfold
*)

(*
lemma pippo (t:𝕋) (f):
     (𝐬❨⫯f❩＠⧣❨t❩) ≐ ▼[𝐢]((⫯𝐬❨f❩)＠⧣❨t❩).
#t elim t -t
[ * //
| #b #t #IH #f 
  <subst_tapp_abst <subst_tapp_abst
  <unwind_unfold <subst_tapp_abst
  @term_eq_abst
  @subst_tapp_eq_repl



 #p #f
  <subst_tapp_lref <subst_tapp_lref
  <subst_push_succ <term_next_unfold


lemma unwind_abst (f) (b) (t):
      (𝛌b.▼[⫯f]t) ≐ ▼[f](𝛌b.t).
#f #b #t
<unwind_unfold <unwind_unfold <subst_tapp_abst
@term_eq_abst @subst_tapp_eq_repl //

*)
