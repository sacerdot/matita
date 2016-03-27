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

include "ground_2/relocation/rtmap_isfin.ma".
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

interpretation "general slicing (local environment)"
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

(* Basic_2A1: includes: drop_refl *)
lemma drops_refl: ∀c,L,f. 𝐈⦃f⦄ → ⬇*[c, f] L ≡ L.
#c #L elim L -L /2 width=1 by drops_atom/
#L #I #V #IHL #f #Hf elim (isid_inv_gen … Hf) -Hf
/3 width=1 by drops_skip, lifts_refl/
qed.

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

(* forward lemmas with test for finite colength *****************************)

lemma drops_fwd_isfin: ∀L1,L2,f. ⬇*[Ⓣ, f] L1 ≡ L2 → 𝐅⦃f⦄.
#L1 #L2 #f #H elim H -L1 -L2 -f
/3 width=1 by isfin_next, isfin_push, isfin_isid/
qed-.

(* Basic_2A1: removed theorems 14:
              drops_inv_nil drops_inv_cons d1_liftable_liftables
              drop_refl_atom_O2
              drop_inv_O1_pair1 drop_inv_pair1 drop_inv_O1_pair2
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
