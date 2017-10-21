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

include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/static/lsubf_lsubr.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Advanced properties ******************************************************)

(* Note: this replaces lemma 1400 concluding the "big tree" theorem *)
lemma frees_total: ∀L,T. ∃f. L ⊢ 𝐅*⦃T⦄ ≡ f.
#L #T @(fqup_wf_ind_eq (Ⓣ) … (⋆) L T) -L -T
#G0 #L0 #T0 #IH #G #L * *
[ /3 width=2 by frees_sort, ex_intro/
| cases L -L /3 width=2 by frees_atom, ex_intro/
  #L #I *
  [ cases I -I #I [2: #V ] #HG #HL #HT destruct
    [ elim (IH G L V) -IH
      /3 width=2 by frees_pair, fqu_fqup, fqu_lref_O, ex_intro/
    | -IH /3 width=2 by frees_unit, ex_intro/
    ]
  | #i #HG #HL #HT destruct
    elim (IH G L (#i)) -IH
    /3 width=2 by frees_lref, fqu_fqup, fqu_drop, ex_intro/
  ]
| /3 width=2 by frees_gref, ex_intro/
| #p #I #V #T #HG #HL #HT destruct
  elim (IH G L V) // #f1 #HV
  elim (IH G (L.ⓑ{I}V) T) -IH // #f2 #HT
  elim (sor_isfin_ex f1 (⫱f2))
  /3 width=6 by frees_fwd_isfin, frees_bind, isfin_tl, ex_intro/
| #I #V #T #HG #HL #HT destruct
  elim (IH G L V) // #f1 #HV
  elim (IH G L T) -IH // #f2 #HT
  elim (sor_isfin_ex f1 f2)
  /3 width=6 by frees_fwd_isfin, frees_flat, ex_intro/
]
qed-.

(* Advanced main properties *************************************************)

theorem frees_bind_void: ∀f1,L,V. L ⊢ 𝐅*⦃V⦄ ≡ f1 → ∀f2,T. L.ⓧ ⊢ 𝐅*⦃T⦄ ≡ f2 →
                         ∀f. f1 ⋓ ⫱f2 ≡ f → ∀p,I. L ⊢ 𝐅*⦃ⓑ{p,I}V.T⦄ ≡ f.
#f1 #L #V #Hf1 #f2 #T #Hf2 #f #Hf #p #I
elim (frees_total (L.ⓑ{I}V) T) #f0 #Hf0
lapply (lsubr_lsubf … Hf2 … Hf0) -Hf2 /2 width=5 by lsubr_unit/ #H02
elim (pn_split f2) * #g2 #H destruct
[ elim (lsubf_inv_push2 … H02) -H02 #g0 #Z #Y #H02 #H0 #H destruct
  lapply (lsubf_inv_refl … H02) -H02 #H02
  lapply (sor_eq_repl_fwd2 … Hf … H02) -g2 #Hf
  /2 width=5 by frees_bind/
| elim (lsubf_inv_unit2 … H02) -H02 * [ #g0 #Y #_ #_ #H destruct ]
  #z1 #g0 #z #Z #Y #X #H02 #Hz1 #Hz #H0 #H destruct
  lapply (lsubf_inv_refl … H02) -H02 #H02
  lapply (frees_mono … Hz1 … Hf1) -Hz1 #H1
  lapply (sor_eq_repl_back1 … Hz … H02) -g0 #Hz
  lapply (sor_eq_repl_back2 … Hz … H1) -z1 #Hz
  lapply (sor_comm … Hz) -Hz #Hz
  lapply (sor_mono … f Hz ?) // -Hz #H
  lapply (sor_inv_sle_sn … Hf) -Hf #Hf
  lapply (frees_eq_repl_back … Hf0 (⫯f) ?) /2 width=5 by eq_next/ -z #Hf0
  @(frees_bind … Hf1 Hf0) -Hf1 -Hf0 (**) (* constructor needed *)
  /2 width=1 by sor_sle_dx/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma frees_inv_bind_void: ∀f,p,I,L,V,T. L ⊢ 𝐅*⦃ⓑ{p,I}V.T⦄ ≡ f →
                           ∃∃f1,f2. L ⊢ 𝐅*⦃V⦄ ≡ f1 & L.ⓧ ⊢ 𝐅*⦃T⦄ ≡ f2 & f1 ⋓ ⫱f2 ≡ f.
#f #p #I #L #V #T #H
elim (frees_inv_bind … H) -H #f1 #f2 #Hf1 #Hf2 #Hf
elim (frees_total (L.ⓧ) T) #f0 #Hf0
lapply (lsubr_lsubf … Hf0 … Hf2) -Hf2 /2 width=5 by lsubr_unit/ #H20
elim (pn_split f0) * #g0 #H destruct
[ elim (lsubf_inv_push2 … H20) -H20 #g2 #I #Y #H20 #H2 #H destruct
  lapply (lsubf_inv_refl … H20) -H20 #H20
  lapply (sor_eq_repl_back2 … Hf … H20) -g2 #Hf
  /2 width=5 by ex3_2_intro/
| elim (lsubf_inv_unit2 … H20) -H20 * [ #g2 #Y #_ #_ #H destruct ]
  #z1 #z0 #g2 #Z #Y #X #H20 #Hz1 #Hg2 #H2 #H destruct
  lapply (lsubf_inv_refl … H20) -H20 #H0
  lapply (frees_mono … Hz1 … Hf1) -Hz1 #H1
  lapply (sor_eq_repl_back1 … Hg2 … H0) -z0 #Hg2
  lapply (sor_eq_repl_back2 … Hg2 … H1) -z1 #Hg2
  @(ex3_2_intro … Hf1 Hf0) -Hf1 -Hf0 (**) (* constructor needed *)
  /2 width=3 by sor_comm_23_idem/
]
qed-.
