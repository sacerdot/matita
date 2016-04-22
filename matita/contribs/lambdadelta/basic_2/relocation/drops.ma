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

include "basic_2/notation/relations/rdropstar_3.ma".
include "basic_2/notation/relations/rdropstar_4.ma".
include "basic_2/relocation/lreq.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Basic_1: includes: drop_skip_bind drop1_skip_bind *)
(* Basic_2A1: includes: drop_atom drop_pair drop_drop drop_skip
                        drop_refl_atom_O2 drop_drop_lt drop_skip_lt
*)
inductive drops (c:bool): rtmap → relation lenv ≝
| drops_atom: ∀f. (c = Ⓣ → 𝐈⦃f⦄) → drops c (f) (⋆) (⋆)
| drops_drop: ∀I,L1,L2,V,f. drops c f L1 L2 → drops c (⫯f) (L1.ⓑ{I}V) L2
| drops_skip: ∀I,L1,L2,V1,V2,f.
              drops c f L1 L2 → ⬆*[f] V2 ≡ V1 →
              drops c (↑f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation "uniform slicing (local environment)"
   'RDropStar i L1 L2 = (drops true (uni i) L1 L2).

interpretation "generic slicing (local environment)"
   'RDropStar c f L1 L2 = (drops c f L1 L2).

definition d_liftable1: relation2 lenv term → predicate bool ≝
                        λR,c. ∀L,K,f. ⬇*[c, f] L ≡ K →
                        ∀T,U. ⬆*[f] T ≡ U → R K T → R L U.

definition d_liftable2: predicate (lenv → relation term) ≝
                        λR. ∀K,T1,T2. R K T1 T2 → ∀L,c,f. ⬇*[c, f] L ≡ K →
                        ∀U1. ⬆*[f] T1 ≡ U1 → 
                        ∃∃U2. ⬆*[f] T2 ≡ U2 & R L U1 U2.

definition d_deliftable2_sn: predicate (lenv → relation term) ≝
                             λR. ∀L,U1,U2. R L U1 U2 → ∀K,c,f. ⬇*[c, f] L ≡ K →
                             ∀T1. ⬆*[f] T1 ≡ U1 →
                             ∃∃T2. ⬆*[f] T2 ≡ U2 & R K T1 T2.

definition dropable_sn: predicate (rtmap → relation lenv) ≝
                        λR. ∀L1,K1,c,f. ⬇*[c, f] L1 ≡ K1 → ∀L2,f2. R f2 L1 L2 →
                        ∀f1. f ⊚ f1 ≡ f2 →
                        ∃∃K2. R f1 K1 K2 & ⬇*[c, f] L2 ≡ K2.

definition dropable_dx: predicate (rtmap → relation lenv) ≝
                        λR. ∀L1,L2,f2. R f2 L1 L2 →
                        ∀K2,c,f. ⬇*[c, f] L2 ≡ K2 →  𝐔⦃f⦄ →
                        ∀f1. f ⊚ f1 ≡ f2 → 
                        ∃∃K1. ⬇*[c, f] L1 ≡ K1 & R f1 K1 K2.

definition dedropable_sn: predicate (rtmap → relation lenv) ≝
                          λR. ∀L1,K1,c,f. ⬇*[c, f] L1 ≡ K1 → ∀K2,f1. R f1 K1 K2 →
                          ∀f2. f ⊚ f1 ≡ f2 →
                          ∃∃L2. R f2 L1 L2 & ⬇*[c, f] L2 ≡ K2 & L1 ≡[f] L2.

(* Basic properties *********************************************************)

lemma drops_eq_repl_back: ∀L1,L2,c. eq_repl_back … (λf. ⬇*[c, f] L1 ≡ L2).
#L1 #L2 #c #f1 #H elim H -L1 -L2 -f1
[ /4 width=3 by drops_atom, isid_eq_repl_back/
| #I #L1 #L2 #V #f1 #_ #IH #f2 #H elim (eq_inv_nx … H) -H
  /3 width=3 by drops_drop/
| #I #L1 #L2 #V1 #v2 #f1 #_ #HV #IH #f2 #H elim (eq_inv_px … H) -H
  /3 width=3 by drops_skip, lifts_eq_repl_back/
]
qed-.

lemma drops_eq_repl_fwd: ∀L1,L2,c. eq_repl_fwd … (λf. ⬇*[c, f] L1 ≡ L2).
#L1 #L2 #c @eq_repl_sym /2 width=3 by drops_eq_repl_back/ (**) (* full auto fails *)
qed-.

lemma drops_inv_tls_at: ∀f,i1,i2. @⦃i1,f⦄ ≡ i2 →
                        ∀c, L1,L2. ⬇*[c,⫱*[i2]f] L1 ≡ L2 →
                        ⬇*[c,↑⫱*[⫯i2]f] L1 ≡ L2.
/3 width=3 by drops_eq_repl_fwd, at_inv_tls/ qed-.

(* Basic_2A1: includes: drop_FT *)
lemma drops_TF: ∀L1,L2,f. ⬇*[Ⓣ, f] L1 ≡ L2 → ⬇*[Ⓕ, f] L1 ≡ L2.
#L1 #L2 #f #H elim H -L1 -L2 -f
/3 width=1 by drops_atom, drops_drop, drops_skip/
qed.

(* Basic_2A1: includes: drop_gen *)
lemma drops_gen: ∀L1,L2,c,f. ⬇*[Ⓣ, f] L1 ≡ L2 → ⬇*[c, f] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drops_TF/
qed-.

(* Basic_2A1: includes: drop_T *)
lemma drops_F: ∀L1,L2,c,f. ⬇*[c, f] L1 ≡ L2 → ⬇*[Ⓕ, f] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drops_TF/
qed-.

(* Basic_2A1: includes: drop_refl *)
lemma drops_refl: ∀c,L,f. 𝐈⦃f⦄ → ⬇*[c, f] L ≡ L.
#c #L elim L -L /2 width=1 by drops_atom/
#L #I #V #IHL #f #Hf elim (isid_inv_gen … Hf) -Hf
/3 width=1 by drops_skip, lifts_refl/
qed.

(* Basic_2A1: includes: drop_split *)
lemma drops_split_trans: ∀L1,L2,f,c. ⬇*[c, f] L1 ≡ L2 → ∀f1,f2. f1 ⊚ f2 ≡ f → 𝐔⦃f1⦄ →
                         ∃∃L. ⬇*[c, f1] L1 ≡ L & ⬇*[c, f2] L ≡ L2.
#L1 #L2 #f #c #H elim H -L1 -L2 -f
[ #f #Hc #f1 #f2 #Hf #Hf1 @(ex2_intro … (⋆)) @drops_atom
  #H lapply (Hc H) -c
  #H elim (after_inv_isid3 … Hf H) -f //
| #I #L1 #L2 #V #f #HL12 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  [ #g1 #g2 #Hf #H1 #H2 destruct
    lapply (isuni_inv_push … Hf1 ??) -Hf1 [1,2: // ] #Hg1
    elim (IHL12 … Hf) -f
    /4 width=5 by drops_drop, drops_skip, lifts_refl, isuni_isid, ex2_intro/
  | #g1 #Hf #H destruct elim (IHL12 … Hf) -f
    /3 width=5 by ex2_intro, drops_drop, isuni_inv_next/
  ]
| #I #L1 #L2 #V1 #V2 #f #_ #HV21 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxp … Hf) -Hf [2,3: // ]
  #g1 #g2 #Hf #H1 #H2 destruct elim (lifts_split_trans … HV21 … Hf) -HV21
  elim (IHL12 … Hf) -f /3 width=5 by ex2_intro, drops_skip, isuni_fwd_push/
]
qed-.

lemma drops_split_div: ∀L1,L,f1,c. ⬇*[c, f1] L1 ≡ L → ∀f2,f. f1 ⊚ f2 ≡ f → 𝐔⦃f2⦄ →
                       ∃∃L2. ⬇*[Ⓕ, f2] L ≡ L2 & ⬇*[Ⓕ, f] L1 ≡ L2.
#L1 #L #f1 #c #H elim H -L1 -L -f1
[ #f1 #Hc #f2 #f #Hf #Hf2 @(ex2_intro … (⋆)) @drops_atom #H destruct
| #I #L1 #L #V #f1 #HL1 #IH #f2 #f #Hf #Hf2 elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g #Hg #H destruct elim (IH … Hg) -IH -Hg /3 width=5 by drops_drop, ex2_intro/
| #I #L1 #L #V1 #V #f1 #HL1 #HV1 #IH #f2 #f #Hf #Hf2
  elim (after_inv_pxx … Hf) -Hf [1,3: * |*: // ]
  #g2 #g #Hg #H2 #H0 destruct 
  [ lapply (isuni_inv_push … Hf2 ??) -Hf2 [1,2: // ] #Hg2 -IH
    lapply (after_isid_inv_dx … Hg … Hg2) -Hg #Hg
    /5 width=7 by drops_eq_repl_back, drops_F, drops_refl, drops_skip, lifts_eq_repl_back, isid_push, ex2_intro/
  | lapply (isuni_inv_next … Hf2 ??) -Hf2 [1,2: // ] #Hg2 -HL1 -HV1
    elim (IH … Hg) -f1 /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_1: includes: drop_gen_refl *)
(* Basic_2A1: includes: drop_inv_O2 *)
lemma drops_fwd_isid: ∀L1,L2,c,f. ⬇*[c, f] L1 ≡ L2 → 𝐈⦃f⦄ → L1 = L2.
#L1 #L2 #c #f #H elim H -L1 -L2 -f //
[ #I #L1 #L2 #V #f #_ #_ #H elim (isid_inv_next … H) //
| /5 width=5 by isid_inv_push, lifts_fwd_isid, eq_f3, sym_eq/
]
qed-.

fact drops_fwd_drop2_aux: ∀X,Y,c,f2. ⬇*[c, f2] X ≡ Y → ∀I,K,V. Y = K.ⓑ{I}V →
                          ∃∃f1,f. 𝐈⦃f1⦄ & f2 ⊚ ⫯f1 ≡ f & ⬇*[c, f] X ≡ K.
#X #Y #c #f2 #H elim H -X -Y -f2
[ #f2 #Ht2 #J #K #W #H destruct
| #I #L1 #L2 #V #f2 #_ #IHL #J #K #W #H elim (IHL … H) -IHL
  /3 width=7 by after_next, ex3_2_intro, drops_drop/
| #I #L1 #L2 #V1 #V2 #f2 #HL #_ #_ #J #K #W #H destruct
  lapply (isid_after_dx 𝐈𝐝 … f2) /3 width=9 by after_push, ex3_2_intro, drops_drop/
]
qed-.

lemma drops_fwd_drop2: ∀I,X,K,V,c,f2. ⬇*[c, f2] X ≡ K.ⓑ{I}V →
                       ∃∃f1,f. 𝐈⦃f1⦄ & f2 ⊚ ⫯f1 ≡ f & ⬇*[c, f] X ≡ K.
/2 width=5 by drops_fwd_drop2_aux/ qed-.

lemma drops_after_fwd_drop2: ∀I,X,K,V,c,f2. ⬇*[c, f2] X ≡ K.ⓑ{I}V →
                             ∀f1,f. 𝐈⦃f1⦄ → f2 ⊚ ⫯f1 ≡ f → ⬇*[c, f] X ≡ K.
#I #X #K #V #c #f2 #H #f1 #f #Hf1 #Hf elim (drops_fwd_drop2 … H) -H
#g1 #g #Hg1 #Hg #HK lapply (after_mono_eq … Hg … Hf ??) -Hg -Hf
/3 width=5 by drops_eq_repl_back, isid_inv_eq_repl, eq_next/
qed-.

(* Basic_1: was: drop_S *)
(* Basic_2A1: was: drop_fwd_drop2 *)
lemma drops_isuni_fwd_drop2: ∀I,X,K,V,c,f. 𝐔⦃f⦄ → ⬇*[c, f] X ≡ K.ⓑ{I}V → ⬇*[c, ⫯f] X ≡ K.
/3 width=7 by drops_after_fwd_drop2, after_isid_isuni/ qed-.

(* Forward lemmas with test for finite colength *****************************)

lemma drops_fwd_isfin: ∀L1,L2,f. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐅⦃f⦄.
#L1 #L2 #f #H elim H -L1 -L2 -f
/3 width=1 by isfin_next, isfin_push, isfin_isid/
qed-.

(* Basic inversion lemmas ***************************************************)

fact drops_inv_atom1_aux: ∀X,Y,c,f. ⬇*[c, f] X ≡ Y → X = ⋆ →
                          Y = ⋆ ∧ (c = Ⓣ → 𝐈⦃f⦄).
#X #Y #c #f * -X -Y -f
[ /3 width=1 by conj/
| #I #L1 #L2 #V #f #_ #H destruct
| #I #L1 #L2 #V1 #V2 #f #_ #_ #H destruct
]
qed-.

(* Basic_1: includes: drop_gen_sort *)
(* Basic_2A1: includes: drop_inv_atom1 *)
lemma drops_inv_atom1: ∀Y,c,f. ⬇*[c, f] ⋆ ≡ Y → Y = ⋆ ∧ (c = Ⓣ → 𝐈⦃f⦄).
/2 width=3 by drops_inv_atom1_aux/ qed-.

fact drops_inv_drop1_aux: ∀X,Y,c,f. ⬇*[c, f] X ≡ Y → ∀I,K,V,g. X = K.ⓑ{I}V → f = ⫯g →
                          ⬇*[c, g] K ≡ Y.
#X #Y #c #f * -X -Y -f
[ #f #Ht #J #K #W #g #H destruct
| #I #L1 #L2 #V #f #HL #J #K #W #g #H1 #H2 <(injective_next … H2) -g destruct //
| #I #L1 #L2 #V1 #V2 #f #_ #_ #J #K #W #g #_ #H2 elim (discr_push_next … H2)
]
qed-.

(* Basic_1: includes: drop_gen_drop *)
(* Basic_2A1: includes: drop_inv_drop1_lt drop_inv_drop1 *)
lemma drops_inv_drop1: ∀I,K,Y,V,c,f. ⬇*[c, ⫯f] K.ⓑ{I}V ≡ Y → ⬇*[c, f] K ≡ Y.
/2 width=7 by drops_inv_drop1_aux/ qed-.


fact drops_inv_skip1_aux: ∀X,Y,c,f. ⬇*[c, f] X ≡ Y → ∀I,K1,V1,g. X = K1.ⓑ{I}V1 → f = ↑g →
                          ∃∃K2,V2. ⬇*[c, g] K1 ≡ K2 & ⬆*[g] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
#X #Y #c #f * -X -Y -f
[ #f #Ht #J #K1 #W1 #g #H destruct
| #I #L1 #L2 #V #f #_ #J #K1 #W1 #g #_ #H2 elim (discr_next_push … H2)
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K1 #W1 #g #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_l *)
(* Basic_2A1: includes: drop_inv_skip1 *)
lemma drops_inv_skip1: ∀I,K1,V1,Y,c,f. ⬇*[c, ↑f] K1.ⓑ{I}V1 ≡ Y →
                       ∃∃K2,V2. ⬇*[c, f] K1 ≡ K2 & ⬆*[f] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
/2 width=5 by drops_inv_skip1_aux/ qed-.

fact drops_inv_skip2_aux: ∀X,Y,c,f. ⬇*[c, f] X ≡ Y → ∀I,K2,V2,g. Y = K2.ⓑ{I}V2 → f = ↑g →
                          ∃∃K1,V1. ⬇*[c, g] K1 ≡ K2 & ⬆*[g] V2 ≡ V1 & X = K1.ⓑ{I}V1.
#X #Y #c #f * -X -Y -f
[ #f #Ht #J #K2 #W2 #g #H destruct
| #I #L1 #L2 #V #f #_ #J #K2 #W2 #g #_ #H2 elim (discr_next_push … H2)
| #I #L1 #L2 #V1 #V2 #f #HL #HV #J #K2 #W2 #g #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_r *)
(* Basic_2A1: includes: drop_inv_skip2 *)
lemma drops_inv_skip2: ∀I,X,K2,V2,c,f. ⬇*[c, ↑f] X ≡ K2.ⓑ{I}V2 →
                       ∃∃K1,V1. ⬇*[c, f] K1 ≡ K2 & ⬆*[f] V2 ≡ V1 & X = K1.ⓑ{I}V1.
/2 width=5 by drops_inv_skip2_aux/ qed-.

fact drops_inv_TF_aux: ∀L1,L2,f. ⬇*[Ⓕ, f] L1 ≡ L2 → 𝐔⦃f⦄ →
                       ∀I,K,V. L2 = K.ⓑ{I}V →
                       ⬇*[Ⓣ, f] L1 ≡ K.ⓑ{I}V.
#L1 #L2 #f #H elim H -L1 -L2 -f
[ #f #_ #_ #J #K #W #H destruct
| #I #L1 #L2 #V #f #_ #IH #Hf #J #K #W #H destruct
  /4 width=3 by drops_drop, isuni_inv_next/
| #I #L1 #L2 #V1 #V2 #f #HL12 #HV21 #_ #Hf #J #K #W #H destruct
  lapply (isuni_inv_push … Hf ??) -Hf [1,2: // ] #Hf
  <(drops_fwd_isid … HL12) -K // <(lifts_fwd_isid … HV21) -V1
  /3 width=3 by drops_refl, isid_push/
]
qed-.

(* Basic_2A1: includes: drop_inv_FT *)
lemma drops_inv_TF: ∀I,L,K,V,f. ⬇*[Ⓕ, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                    ⬇*[Ⓣ, f] L ≡ K.ⓑ{I}V.
/2 width=3 by drops_inv_TF_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: includes: drop_inv_gen *)
lemma drops_inv_gen: ∀I,L,K,V,c,f. ⬇*[c, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                     ⬇*[Ⓣ, f] L ≡ K.ⓑ{I}V.
#I #L #K #V * /2 width=1 by drops_inv_TF/
qed-.

(* Basic_2A1: includes: drop_inv_T *)
lemma drops_inv_F: ∀I,L,K,V,c,f. ⬇*[Ⓕ, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                   ⬇*[c, f] L ≡ K.ⓑ{I}V.
#I #L #K #V * /2 width=1 by drops_inv_TF/
qed-.

(* Inversion lemmas with test for uniformity ********************************)

lemma drops_inv_isuni: ∀L1,L2,f. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐔⦃f⦄ →
                       (𝐈⦃f⦄ ∧ L1 = L2) ∨
                       ∃∃I,K,V,g. ⬇*[Ⓣ, g] K ≡ L2 & 𝐔⦃g⦄ & L1 = K.ⓑ{I}V & f = ⫯g.
#L1 #L2 #f * -L1 -L2 -f
[ /4 width=1 by or_introl, conj/
| /4 width=8 by isuni_inv_next, ex4_4_intro, or_intror/
| /7 width=6 by drops_fwd_isid, lifts_fwd_isid, isuni_inv_push, isid_push, or_introl, conj, eq_f3, sym_eq/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair1 *)
lemma drops_inv_pair1_isuni: ∀I,K,L2,V,c,f. 𝐔⦃f⦄ → ⬇*[c, f] K.ⓑ{I}V ≡ L2 →
                             (𝐈⦃f⦄ ∧ L2 = K.ⓑ{I}V) ∨
                             ∃∃g. 𝐔⦃g⦄ & ⬇*[c, g] K ≡ L2 & f = ⫯g.
#I #K #L2 #V #c #f #Hf #H elim (isuni_split … Hf) -Hf * #g #Hg #H0 destruct
[ lapply (drops_inv_skip1 … H) -H * #Y #X #HY #HX #H destruct
  <(drops_fwd_isid … HY Hg) -Y >(lifts_fwd_isid … HX Hg) -X
  /4 width=3 by isid_push, or_introl, conj/
| lapply (drops_inv_drop1 … H) -H /3 width=4 by ex3_intro, or_intror/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair2 *)
lemma drops_inv_pair2_isuni: ∀I,K,V,c,f,L1. 𝐔⦃f⦄ → ⬇*[c, f] L1 ≡ K.ⓑ{I}V →
                             (𝐈⦃f⦄ ∧ L1 = K.ⓑ{I}V) ∨
                             ∃∃I1,K1,V1,g. 𝐔⦃g⦄ & ⬇*[c, g] K1 ≡ K.ⓑ{I}V & L1 = K1.ⓑ{I1}V1 & f = ⫯g.
#I #K #V #c #f *
[ #Hf #H elim (drops_inv_atom1 … H) -H #H destruct
| #L1 #I1 #V1 #Hf #H elim (drops_inv_pair1_isuni … Hf H) -Hf -H *
  [ #Hf #H destruct /3 width=1 by or_introl, conj/
  | /3 width=8 by ex4_4_intro, or_intror/
  ]
]
qed-.

lemma drops_inv_pair2_isuni_next: ∀I,K,V,c,f,L1. 𝐔⦃f⦄ → ⬇*[c, ⫯f] L1 ≡ K.ⓑ{I}V →
                                  ∃∃I1,K1,V1. ⬇*[c, f] K1 ≡ K.ⓑ{I}V & L1 = K1.ⓑ{I1}V1.
#I #K #V #c #f #L1 #Hf #H elim (drops_inv_pair2_isuni … H) -H /2 width=3 by isuni_next/ -Hf *
[ #H elim (isid_inv_next … H) -H //
| /2 width=5 by ex2_3_intro/
]
qed-. 

(* Inversion lemmas with uniform relocations ********************************)

lemma drops_inv_succ: ∀L1,L2,l. ⬇*[⫯l] L1 ≡ L2 →
                      ∃∃I,K,V. ⬇*[l] K ≡ L2 & L1 = K.ⓑ{I}V.
#L1 #L2 #l #H elim (drops_inv_isuni … H) -H // *
[ #H elim (isid_inv_next … H) -H //
| /2 width=5 by ex2_3_intro/
]
qed-. 

(* Basic_2A1: removed theorems 12:
              drops_inv_nil drops_inv_cons d1_liftable_liftables
              drop_refl_atom_O2 drop_inv_pair1
              drop_inv_Y1 drop_Y1 drop_O_Y drop_fwd_Y2
              drop_fwd_length_minus2 drop_fwd_length_minus4
*)
(* Basic_1: removed theorems 53:
            drop1_gen_pnil drop1_gen_pcons drop1_getl_trans
            drop_ctail drop_skip_flat
            cimp_flat_sx cimp_flat_dx cimp_bind cimp_getl_conf
            drop_clear drop_clear_O drop_clear_S
            clear_gen_sort clear_gen_bind clear_gen_flat clear_gen_flat_r
            clear_gen_all clear_clear clear_mono clear_trans clear_ctail clear_cle
            getl_ctail_clen getl_gen_tail clear_getl_trans getl_clear_trans
            getl_clear_bind getl_clear_conf getl_dec getl_drop getl_drop_conf_lt
            getl_drop_conf_ge getl_conf_ge_drop getl_drop_conf_rev
            drop_getl_trans_lt drop_getl_trans_le drop_getl_trans_ge
            getl_drop_trans getl_flt getl_gen_all getl_gen_sort getl_gen_O
            getl_gen_S getl_gen_2 getl_gen_flat getl_gen_bind getl_conf_le
            getl_trans getl_refl getl_head getl_flat getl_ctail getl_mono
*)
