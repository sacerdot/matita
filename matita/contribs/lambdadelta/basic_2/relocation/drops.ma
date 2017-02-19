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

include "ground_2/relocation/rtmap_coafter.ma".
include "basic_2/notation/relations/rdropstar_3.ma".
include "basic_2/notation/relations/rdropstar_4.ma".
include "basic_2/relocation/lreq.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Basic_1: includes: drop_skip_bind drop1_skip_bind *)
(* Basic_2A1: includes: drop_atom drop_pair drop_drop drop_skip
                        drop_refl_atom_O2 drop_drop_lt drop_skip_lt
*)
inductive drops (b:bool): rtmap → relation lenv ≝
| drops_atom: ∀f. (b = Ⓣ → 𝐈⦃f⦄) → drops b (f) (⋆) (⋆)
| drops_drop: ∀f,I,L1,L2,V. drops b f L1 L2 → drops b (⫯f) (L1.ⓑ{I}V) L2
| drops_skip: ∀f,I,L1,L2,V1,V2.
              drops b f L1 L2 → ⬆*[f] V2 ≡ V1 →
              drops b (↑f) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation "uniform slicing (local environment)"
   'RDropStar i L1 L2 = (drops true (uni i) L1 L2).

interpretation "generic slicing (local environment)"
   'RDropStar b f L1 L2 = (drops b f L1 L2).

definition d_liftable1: predicate (relation2 lenv term) ≝
                        λR. ∀K,T. R K T → ∀b,f,L. ⬇*[b, f] L ≡ K →
                        ∀U. ⬆*[f] T ≡ U → R L U.

definition d_deliftable1: predicate (relation2 lenv term) ≝
                          λR. ∀L,U. R L U → ∀b,f,K. ⬇*[b, f] L ≡ K →
                          ∀T. ⬆*[f] T ≡ U → R K T.

definition d_liftable2: predicate (lenv → relation term) ≝
                        λR. ∀K,T1,T2. R K T1 T2 → ∀b,f,L. ⬇*[b, f] L ≡ K →
                        ∀U1. ⬆*[f] T1 ≡ U1 → 
                        ∃∃U2. ⬆*[f] T2 ≡ U2 & R L U1 U2.

definition d_deliftable2_sn: predicate (lenv → relation term) ≝
                             λR. ∀L,U1,U2. R L U1 U2 → ∀b,f,K. ⬇*[b, f] L ≡ K →
                             ∀T1. ⬆*[f] T1 ≡ U1 →
                             ∃∃T2. ⬆*[f] T2 ≡ U2 & R K T1 T2.

definition co_dropable_sn: predicate (rtmap → relation lenv) ≝
                           λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≡ K1 → 𝐔⦃f⦄ →
                           ∀f2,L2. R f2 L1 L2 → ∀f1. f ~⊚ f1 ≡ f2 →
                           ∃∃K2. R f1 K1 K2 & ⬇*[b, f] L2 ≡ K2.


definition co_dropable_dx: predicate (rtmap → relation lenv) ≝
                           λR. ∀f2,L1,L2. R f2 L1 L2 →
                           ∀b,f,K2. ⬇*[b, f] L2 ≡ K2 → 𝐔⦃f⦄ →
                           ∀f1. f ~⊚ f1 ≡ f2 → 
                           ∃∃K1. ⬇*[b, f] L1 ≡ K1 & R f1 K1 K2.

definition co_dedropable_sn: predicate (rtmap → relation lenv) ≝
                             λR. ∀b,f,L1,K1. ⬇*[b, f] L1 ≡ K1 → ∀f1,K2. R f1 K1 K2 →
                             ∀f2. f ~⊚ f1 ≡ f2 →
                             ∃∃L2. R f2 L1 L2 & ⬇*[b, f] L2 ≡ K2 & L1 ≡[f] L2.

(* Basic properties *********************************************************)

lemma drops_atom_F: ∀f. ⬇*[Ⓕ, f] ⋆ ≡ ⋆.
#f @drops_atom #H destruct
qed.

lemma drops_eq_repl_back: ∀b,L1,L2. eq_repl_back … (λf. ⬇*[b, f] L1 ≡ L2).
#b #L1 #L2 #f1 #H elim H -f1 -L1 -L2
[ /4 width=3 by drops_atom, isid_eq_repl_back/
| #f1 #I #L1 #L2 #V #_ #IH #f2 #H elim (eq_inv_nx … H) -H
  /3 width=3 by drops_drop/
| #f1 #I #L1 #L2 #V1 #v2 #_ #HV #IH #f2 #H elim (eq_inv_px … H) -H
  /3 width=3 by drops_skip, lifts_eq_repl_back/
]
qed-.

lemma drops_eq_repl_fwd: ∀b,L1,L2. eq_repl_fwd … (λf. ⬇*[b, f] L1 ≡ L2).
#b #L1 #L2 @eq_repl_sym /2 width=3 by drops_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Basic_2A1: includes: drop_FT *)
lemma drops_TF: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 → ⬇*[Ⓕ, f] L1 ≡ L2.
#f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by drops_atom, drops_drop, drops_skip/
qed.

(* Basic_2A1: includes: drop_gen *)
lemma drops_gen: ∀b,f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 → ⬇*[b, f] L1 ≡ L2.
* /2 width=1 by drops_TF/
qed-.

(* Basic_2A1: includes: drop_T *)
lemma drops_F: ∀b,f,L1,L2. ⬇*[b, f] L1 ≡ L2 → ⬇*[Ⓕ, f] L1 ≡ L2.
* /2 width=1 by drops_TF/
qed-.

(* Basic inversion lemmas ***************************************************)

fact drops_inv_atom1_aux: ∀b,f,X,Y. ⬇*[b, f] X ≡ Y → X = ⋆ →
                          Y = ⋆ ∧ (b = Ⓣ → 𝐈⦃f⦄).
#b #f #X #Y * -f -X -Y
[ /3 width=1 by conj/
| #f #I #L1 #L2 #V #_ #H destruct
| #f #I #L1 #L2 #V1 #V2 #_ #_ #H destruct
]
qed-.

(* Basic_1: includes: drop_gen_sort *)
(* Basic_2A1: includes: drop_inv_atom1 *)
lemma drops_inv_atom1: ∀b,f,Y. ⬇*[b, f] ⋆ ≡ Y → Y = ⋆ ∧ (b = Ⓣ → 𝐈⦃f⦄).
/2 width=3 by drops_inv_atom1_aux/ qed-.

fact drops_inv_drop1_aux: ∀b,f,X,Y. ⬇*[b, f] X ≡ Y → ∀g,I,K,V. X = K.ⓑ{I}V → f = ⫯g →
                          ⬇*[b, g] K ≡ Y.
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J #K #W #H destruct
| #f #I #L1 #L2 #V #HL #g #J #K #W #H1 #H2 <(injective_next … H2) -g destruct //
| #f #I #L1 #L2 #V1 #V2 #_ #_ #g #J #K #W #_ #H2 elim (discr_push_next … H2)
]
qed-.

(* Basic_1: includes: drop_gen_drop *)
(* Basic_2A1: includes: drop_inv_drop1_lt drop_inv_drop1 *)
lemma drops_inv_drop1: ∀b,f,I,K,Y,V. ⬇*[b, ⫯f] K.ⓑ{I}V ≡ Y → ⬇*[b, f] K ≡ Y.
/2 width=7 by drops_inv_drop1_aux/ qed-.

fact drops_inv_skip1_aux: ∀b,f,X,Y. ⬇*[b, f] X ≡ Y → ∀g,I,K1,V1. X = K1.ⓑ{I}V1 → f = ↑g →
                          ∃∃K2,V2. ⬇*[b, g] K1 ≡ K2 & ⬆*[g] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J #K1 #W1 #H destruct
| #f #I #L1 #L2 #V #_ #g #J #K1 #W1 #_ #H2 elim (discr_next_push … H2)
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K1 #W1 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_l *)
(* Basic_2A1: includes: drop_inv_skip1 *)
lemma drops_inv_skip1: ∀b,f,I,K1,V1,Y. ⬇*[b, ↑f] K1.ⓑ{I}V1 ≡ Y →
                       ∃∃K2,V2. ⬇*[b, f] K1 ≡ K2 & ⬆*[f] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
/2 width=5 by drops_inv_skip1_aux/ qed-.

fact drops_inv_skip2_aux: ∀b,f,X,Y. ⬇*[b, f] X ≡ Y → ∀g,I,K2,V2. Y = K2.ⓑ{I}V2 → f = ↑g →
                          ∃∃K1,V1. ⬇*[b, g] K1 ≡ K2 & ⬆*[g] V2 ≡ V1 & X = K1.ⓑ{I}V1.
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J #K2 #W2 #H destruct
| #f #I #L1 #L2 #V #_ #g #J #K2 #W2 #_ #H2 elim (discr_next_push … H2)
| #f #I #L1 #L2 #V1 #V2 #HL #HV #g #J #K2 #W2 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_r *)
(* Basic_2A1: includes: drop_inv_skip2 *)
lemma drops_inv_skip2: ∀b,f,I,X,K2,V2. ⬇*[b, ↑f] X ≡ K2.ⓑ{I}V2 →
                       ∃∃K1,V1. ⬇*[b, f] K1 ≡ K2 & ⬆*[f] V2 ≡ V1 & X = K1.ⓑ{I}V1.
/2 width=5 by drops_inv_skip2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

fact drops_fwd_drop2_aux: ∀b,f2,X,Y. ⬇*[b, f2] X ≡ Y → ∀I,K,V. Y = K.ⓑ{I}V →
                          ∃∃f1,f. 𝐈⦃f1⦄ & f2 ⊚ ⫯f1 ≡ f & ⬇*[b, f] X ≡ K.
#b #f2 #X #Y #H elim H -f2 -X -Y
[ #f2 #Hf2 #J #K #W #H destruct
| #f2 #I #L1 #L2 #V #_ #IHL #J #K #W #H elim (IHL … H) -IHL
  /3 width=7 by after_next, ex3_2_intro, drops_drop/
| #f2 #I #L1 #L2 #V1 #V2 #HL #_ #_ #J #K #W #H destruct
  lapply (after_isid_dx 𝐈𝐝 … f2) /3 width=9 by after_push, ex3_2_intro, drops_drop/
]
qed-.

lemma drops_fwd_drop2: ∀b,f2,I,X,K,V. ⬇*[b, f2] X ≡ K.ⓑ{I}V →
                       ∃∃f1,f. 𝐈⦃f1⦄ & f2 ⊚ ⫯f1 ≡ f & ⬇*[b, f] X ≡ K.
/2 width=5 by drops_fwd_drop2_aux/ qed-.

(* Properties with test for identity ****************************************)

(* Basic_2A1: includes: drop_refl *)
lemma drops_refl: ∀b,L,f. 𝐈⦃f⦄ → ⬇*[b, f] L ≡ L.
#b #L elim L -L /2 width=1 by drops_atom/
#L #I #V #IHL #f #Hf elim (isid_inv_gen … Hf) -Hf
/3 width=1 by drops_skip, lifts_refl/
qed.

(* Forward lemmas test for identity *****************************************)

(* Basic_1: includes: drop_gen_refl *)
(* Basic_2A1: includes: drop_inv_O2 *)
lemma drops_fwd_isid: ∀b,f,L1,L2. ⬇*[b, f] L1 ≡ L2 → 𝐈⦃f⦄ → L1 = L2.
#b #f #L1 #L2 #H elim H -f -L1 -L2 //
[ #f #I #L1 #L2 #V #_ #_ #H elim (isid_inv_next … H) //
| /5 width=5 by isid_inv_push, lifts_fwd_isid, eq_f3, sym_eq/
]
qed-.


lemma drops_after_fwd_drop2: ∀b,f2,I,X,K,V. ⬇*[b, f2] X ≡ K.ⓑ{I}V →
                             ∀f1,f. 𝐈⦃f1⦄ → f2 ⊚ ⫯f1 ≡ f → ⬇*[b, f] X ≡ K.
#b #f2 #I #X #K #V #H #f1 #f #Hf1 #Hf elim (drops_fwd_drop2 … H) -H
#g1 #g #Hg1 #Hg #HK lapply (after_mono_eq … Hg … Hf ??) -Hg -Hf
/3 width=5 by drops_eq_repl_back, isid_inv_eq_repl, eq_next/
qed-.

(* Forward lemmas with test for finite colength *****************************)

lemma drops_fwd_isfin: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐅⦃f⦄.
#f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by isfin_next, isfin_push, isfin_isid/
qed-.

(* Properties with test for uniformity **************************************)

lemma drops_isuni_ex: ∀f. 𝐔⦃f⦄ → ∀L. ∃K. ⬇*[Ⓕ, f] L ≡ K.
#f #H elim H -f /4 width=2 by drops_refl, drops_TF, ex_intro/
#f #_ #g #H #IH * /2 width=2 by ex_intro/
#L #I #V destruct
elim (IH L) -IH /3 width=2 by drops_drop, ex_intro/
qed-.

(* Inversion lemmas with test for uniformity ********************************)

lemma drops_inv_isuni: ∀f,L1,L2. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐔⦃f⦄ →
                       (𝐈⦃f⦄ ∧ L1 = L2) ∨
                       ∃∃g,I,K,V. ⬇*[Ⓣ, g] K ≡ L2 & 𝐔⦃g⦄ & L1 = K.ⓑ{I}V & f = ⫯g.
#f #L1 #L2 * -f -L1 -L2
[ /4 width=1 by or_introl, conj/
| /4 width=8 by isuni_inv_next, ex4_4_intro, or_intror/
| /7 width=6 by drops_fwd_isid, lifts_fwd_isid, isuni_inv_push, isid_push, or_introl, conj, eq_f3, sym_eq/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair1 *)
lemma drops_inv_pair1_isuni: ∀b,f,I,K,L2,V. 𝐔⦃f⦄ → ⬇*[b, f] K.ⓑ{I}V ≡ L2 →
                             (𝐈⦃f⦄ ∧ L2 = K.ⓑ{I}V) ∨
                             ∃∃g. 𝐔⦃g⦄ & ⬇*[b, g] K ≡ L2 & f = ⫯g.
#b #f #I #K #L2 #V #Hf #H elim (isuni_split … Hf) -Hf * #g #Hg #H0 destruct
[ lapply (drops_inv_skip1 … H) -H * #Y #X #HY #HX #H destruct
  <(drops_fwd_isid … HY Hg) -Y >(lifts_fwd_isid … HX Hg) -X
  /4 width=3 by isid_push, or_introl, conj/
| lapply (drops_inv_drop1 … H) -H /3 width=4 by ex3_intro, or_intror/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair2 *)
lemma drops_inv_pair2_isuni: ∀b,f,I,K,V,L1. 𝐔⦃f⦄ → ⬇*[b, f] L1 ≡ K.ⓑ{I}V →
                             (𝐈⦃f⦄ ∧ L1 = K.ⓑ{I}V) ∨
                             ∃∃g,I1,K1,V1. 𝐔⦃g⦄ & ⬇*[b, g] K1 ≡ K.ⓑ{I}V & L1 = K1.ⓑ{I1}V1 & f = ⫯g.
#b #f #I #K #V *
[ #Hf #H elim (drops_inv_atom1 … H) -H #H destruct
| #L1 #I1 #V1 #Hf #H elim (drops_inv_pair1_isuni … Hf H) -Hf -H *
  [ #Hf #H destruct /3 width=1 by or_introl, conj/
  | /3 width=8 by ex4_4_intro, or_intror/
  ]
]
qed-.

lemma drops_inv_pair2_isuni_next: ∀b,f,I,K,V,L1. 𝐔⦃f⦄ → ⬇*[b, ⫯f] L1 ≡ K.ⓑ{I}V →
                                  ∃∃I1,K1,V1. ⬇*[b, f] K1 ≡ K.ⓑ{I}V & L1 = K1.ⓑ{I1}V1.
#b #f #I #K #V #L1 #Hf #H elim (drops_inv_pair2_isuni … H) -H /2 width=3 by isuni_next/ -Hf *
[ #H elim (isid_inv_next … H) -H //
| /2 width=5 by ex2_3_intro/
]
qed-.

fact drops_inv_TF_aux: ∀f,L1,L2. ⬇*[Ⓕ, f] L1 ≡ L2 → 𝐔⦃f⦄ →
                       ∀I,K,V. L2 = K.ⓑ{I}V →
                       ⬇*[Ⓣ, f] L1 ≡ K.ⓑ{I}V.
#f #L1 #L2 #H elim H -f -L1 -L2
[ #f #_ #_ #J #K #W #H destruct
| #f #I #L1 #L2 #V #_ #IH #Hf #J #K #W #H destruct
  /4 width=3 by drops_drop, isuni_inv_next/
| #f #I #L1 #L2 #V1 #V2 #HL12 #HV21 #_ #Hf #J #K #W #H destruct
  lapply (isuni_inv_push … Hf ??) -Hf [1,2: // ] #Hf
  <(drops_fwd_isid … HL12) -K // <(lifts_fwd_isid … HV21) -V1
  /3 width=3 by drops_refl, isid_push/
]
qed-.

(* Basic_2A1: includes: drop_inv_FT *)
lemma drops_inv_TF: ∀f,I,L,K,V. ⬇*[Ⓕ, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                    ⬇*[Ⓣ, f] L ≡ K.ⓑ{I}V.
/2 width=3 by drops_inv_TF_aux/ qed-.

(* Basic_2A1: includes: drop_inv_gen *)
lemma drops_inv_gen: ∀b,f,I,L,K,V. ⬇*[b, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                     ⬇*[Ⓣ, f] L ≡ K.ⓑ{I}V.
* /2 width=1 by drops_inv_TF/
qed-.

(* Basic_2A1: includes: drop_inv_T *)
lemma drops_inv_F: ∀b,f,I,L,K,V. ⬇*[Ⓕ, f] L ≡ K.ⓑ{I}V → 𝐔⦃f⦄ →
                   ⬇*[b, f] L ≡ K.ⓑ{I}V.
* /2 width=1 by drops_inv_TF/
qed-.

(* Forward lemmas with test for uniformity **********************************)

(* Basic_1: was: drop_S *)
(* Basic_2A1: was: drop_fwd_drop2 *)
lemma drops_isuni_fwd_drop2: ∀b,f,I,X,K,V. 𝐔⦃f⦄ → ⬇*[b, f] X ≡ K.ⓑ{I}V → ⬇*[b, ⫯f] X ≡ K.
/3 width=7 by drops_after_fwd_drop2, after_isid_isuni/ qed-.

(* Inversion lemmas with uniform relocations ********************************)

lemma drops_inv_atom2: ∀b,L,f. ⬇*[b, f] L ≡ ⋆ →
                       ∃∃n,f1. ⬇*[b, 𝐔❴n❵] L ≡ ⋆ & 𝐔❴n❵ ⊚ f1 ≡ f.
#b #L elim L -L
[ /3 width=4 by drops_atom, after_isid_sn, ex2_2_intro/
| #L #I #V #IH #f #H elim (pn_split f) * #g #H0 destruct
  [ elim (drops_inv_skip1 … H) -H #K #W #_ #_ #H destruct
  | lapply (drops_inv_drop1 … H) -H #HL
    elim (IH … HL) -IH -HL /3 width=8 by drops_drop, after_next, ex2_2_intro/
  ]
]
qed-.

lemma drops_inv_succ: ∀l,L1,L2. ⬇*[⫯l] L1 ≡ L2 →
                      ∃∃I,K,V. ⬇*[l] K ≡ L2 & L1 = K.ⓑ{I}V.
#l #L1 #L2 #H elim (drops_inv_isuni … H) -H // *
[ #H elim (isid_inv_next … H) -H //
| /2 width=5 by ex2_3_intro/
]
qed-.

(* Properties with uniform relocations **************************************)

lemma drops_F_uni: ∀L,i. ⬇*[Ⓕ, 𝐔❴i❵] L ≡ ⋆ ∨ ∃∃I,K,V. ⬇*[i] L ≡ K.ⓑ{I}V.
#L elim L -L /2 width=1 by or_introl/
#L #I #V #IH * /4 width=4 by drops_refl, ex1_3_intro, or_intror/
#i elim (IH i) -IH /3 width=1 by drops_drop, or_introl/
* /4 width=4 by drops_drop, ex1_3_intro, or_intror/
qed-.  

(* Basic_2A1: includes: drop_split *)
lemma drops_split_trans: ∀b,f,L1,L2. ⬇*[b, f] L1 ≡ L2 → ∀f1,f2. f1 ⊚ f2 ≡ f → 𝐔⦃f1⦄ →
                         ∃∃L. ⬇*[b, f1] L1 ≡ L & ⬇*[b, f2] L ≡ L2.
#b #f #L1 #L2 #H elim H -f -L1 -L2
[ #f #H0f #f1 #f2 #Hf #Hf1 @(ex2_intro … (⋆)) @drops_atom
  #H lapply (H0f H) -b
  #H elim (after_inv_isid3 … Hf H) -f //
| #f #I #L1 #L2 #V #HL12 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  [ #g1 #g2 #Hf #H1 #H2 destruct
    lapply (isuni_inv_push … Hf1 ??) -Hf1 [1,2: // ] #Hg1
    elim (IHL12 … Hf) -f
    /4 width=5 by drops_drop, drops_skip, lifts_refl, isuni_isid, ex2_intro/
  | #g1 #Hf #H destruct elim (IHL12 … Hf) -f
    /3 width=5 by ex2_intro, drops_drop, isuni_inv_next/
  ]
| #f #I #L1 #L2 #V1 #V2 #_ #HV21 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxp … Hf) -Hf [2,3: // ]
  #g1 #g2 #Hf #H1 #H2 destruct elim (lifts_split_trans … HV21 … Hf) -HV21
  elim (IHL12 … Hf) -f /3 width=5 by ex2_intro, drops_skip, isuni_fwd_push/
]
qed-.

lemma drops_split_div: ∀b,f1,L1,L. ⬇*[b, f1] L1 ≡ L → ∀f2,f. f1 ⊚ f2 ≡ f → 𝐔⦃f2⦄ →
                       ∃∃L2. ⬇*[Ⓕ, f2] L ≡ L2 & ⬇*[Ⓕ, f] L1 ≡ L2.
#b #f1 #L1 #L #H elim H -f1 -L1 -L
[ #f1 #Hf1 #f2 #f #Hf #Hf2 @(ex2_intro … (⋆)) @drops_atom #H destruct
| #f1 #I #L1 #L #V #HL1 #IH #f2 #f #Hf #Hf2 elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g #Hg #H destruct elim (IH … Hg) -IH -Hg /3 width=5 by drops_drop, ex2_intro/
| #f1 #I #L1 #L #V1 #V #HL1 #HV1 #IH #f2 #f #Hf #Hf2
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

(* Properties with application **********************************************)

lemma drops_tls_at: ∀f,i1,i2. @⦃i1,f⦄ ≡ i2 →
                    ∀b,L1,L2. ⬇*[b,⫱*[i2]f] L1 ≡ L2 →
                    ⬇*[b,↑⫱*[⫯i2]f] L1 ≡ L2.
/3 width=3 by drops_eq_repl_fwd, at_inv_tls/ qed-.

lemma drops_split_trans_pair2: ∀b,f,I,L,K0,V. ⬇*[b, f] L ≡ K0.ⓑ{I}V → ∀n. @⦃O, f⦄ ≡ n →
                               ∃∃K,W. ⬇*[n]L ≡ K.ⓑ{I}W & ⬇*[b, ⫱*[⫯n]f] K ≡ K0 & ⬆*[⫱*[⫯n]f] V ≡ W.
#b #f #I #L #K0 #V #H #n #Hf
elim (drops_split_trans … H) -H [ |5: @(after_uni_dx … Hf) |2,3: skip ] /2 width=1 by after_isid_dx/ #Y #HLY #H
lapply (drops_tls_at … Hf … H) -H #H
elim (drops_inv_skip2 … H) -H #K #W #HK0 #HVW #H destruct
/3 width=5 by drops_inv_gen, ex3_2_intro/
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
