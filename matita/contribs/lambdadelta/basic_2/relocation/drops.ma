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

include "basic_2/notation/relations/rdropstar_4.ma".
include "basic_2/grammar/lenv.ma".
include "basic_2/relocation/lifts.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Basic_1: includes: drop_skip_bind drop1_skip_bind *)
(* Basic_2A1: includes: drop_atom drop_pair drop_drop drop_skip
                        drop_refl_atom_O2 drop_drop_lt drop_skip_lt
*)
inductive drops (s:bool): trace → relation lenv ≝
| drops_atom: ∀t. (s = Ⓕ → 𝐈⦃t⦄) → drops s (t) (⋆) (⋆)
| drops_drop: ∀I,L1,L2,V,t. drops s t L1 L2 → drops s (Ⓕ@t) (L1.ⓑ{I}V) L2
| drops_skip: ∀I,L1,L2,V1,V2,t.
              drops s t L1 L2 → ⬆*[t] V2 ≡ V1 →
              drops s (Ⓣ@t) (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation "general slicing (local environment)"
   'RDropStar s t L1 L2 = (drops s t L1 L2).

definition d_liftable1: relation2 lenv term → predicate bool ≝
                        λR,s. ∀L,K,t. ⬇*[s, t] L ≡ K →
                        ∀T,U. ⬆*[t] T ≡ U → R K T → R L U.

definition d_liftable2: predicate (lenv → relation term) ≝
                        λR. ∀K,T1,T2. R K T1 T2 → ∀L,s,t. ⬇*[s, t] L ≡ K →
                        ∀U1. ⬆*[t] T1 ≡ U1 → 
                        ∃∃U2. ⬆*[t] T2 ≡ U2 & R L U1 U2.

definition d_deliftable2_sn: predicate (lenv → relation term) ≝
                             λR. ∀L,U1,U2. R L U1 U2 → ∀K,s,t. ⬇*[s, t] L ≡ K →
                             ∀T1. ⬆*[t] T1 ≡ U1 →
                             ∃∃T2. ⬆*[t] T2 ≡ U2 & R K T1 T2.

definition dropable_sn: predicate (relation lenv) ≝
                        λR. ∀L1,K1,s,t. ⬇*[s, t] L1 ≡ K1 → ∀L2. R L1 L2 →
                        ∃∃K2. R K1 K2 & ⬇*[s, t] L2 ≡ K2.
(*
definition dropable_dx: predicate (relation lenv) ≝
                        λR. ∀L1,L2. R L1 L2 → ∀K2,s,m. ⬇[s, 0, m] L2 ≡ K2 →
                        ∃∃K1. ⬇[s, 0, m] L1 ≡ K1 & R K1 K2.
*)
(* Basic inversion lemmas ***************************************************)

fact drops_inv_atom1_aux: ∀X,Y,s,t. ⬇*[s, t] X ≡ Y → X = ⋆ →
                          Y = ⋆ ∧ (s = Ⓕ → 𝐈⦃t⦄).
#X #Y #s #t * -X -Y -t
[ /3 width=1 by conj/
| #I #L1 #L2 #V #t #_ #H destruct
| #I #L1 #L2 #V1 #V2 #t #_ #_ #H destruct
]
qed-.

(* Basic_1: includes: drop_gen_sort *)
(* Basic_2A1: includes: drop_inv_atom1 *)
lemma drops_inv_atom1: ∀Y,s,t. ⬇*[s, t] ⋆ ≡ Y → Y = ⋆ ∧ (s = Ⓕ → 𝐈⦃t⦄).
/2 width=3 by drops_inv_atom1_aux/ qed-.

fact drops_inv_drop1_aux: ∀X,Y,s,t. ⬇*[s, t] X ≡ Y → ∀I,K,V,tl. X = K.ⓑ{I}V → t = Ⓕ@tl →
                          ⬇*[s, tl] K ≡ Y.
#X #Y #s #t * -X -Y -t
[ #t #Ht #J #K #W #tl #H destruct
| #I #L1 #L2 #V #t #HL #J #K #W #tl #H1 #H2 destruct //
| #I #L1 #L2 #V1 #V2 #t #_ #_ #J #K #W #tl #_ #H2 destruct
]
qed-.

(* Basic_1: includes: drop_gen_drop *)
(* Basic_2A1: includes: drop_inv_drop1_lt drop_inv_drop1 *)
lemma drops_inv_drop1: ∀I,K,Y,V,s,t. ⬇*[s, Ⓕ@t] K.ⓑ{I}V ≡ Y → ⬇*[s, t] K ≡ Y.
/2 width=7 by drops_inv_drop1_aux/ qed-.


fact drops_inv_skip1_aux: ∀X,Y,s,t. ⬇*[s, t] X ≡ Y → ∀I,K1,V1,tl. X = K1.ⓑ{I}V1 → t = Ⓣ@tl →
                          ∃∃K2,V2. ⬇*[s, tl] K1 ≡ K2 & ⬆*[tl] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
#X #Y #s #t * -X -Y -t
[ #t #Ht #J #K1 #W1 #tl #H destruct
| #I #L1 #L2 #V #t #_ #J #K1 #W1 #tl #_ #H2 destruct
| #I #L1 #L2 #V1 #V2 #t #HL #HV #J #K1 #W1 #tl #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_l *)
(* Basic_2A1: includes: drop_inv_skip1 *)
lemma drops_inv_skip1: ∀I,K1,V1,Y,s,t. ⬇*[s, Ⓣ@t] K1.ⓑ{I}V1 ≡ Y →
                       ∃∃K2,V2. ⬇*[s, t] K1 ≡ K2 & ⬆*[t] V2 ≡ V1 & Y = K2.ⓑ{I}V2.
/2 width=5 by drops_inv_skip1_aux/ qed-.

fact drops_inv_skip2_aux: ∀X,Y,s,t. ⬇*[s, t] X ≡ Y → ∀I,K2,V2,tl. Y = K2.ⓑ{I}V2 → t = Ⓣ@tl →
                          ∃∃K1,V1. ⬇*[s, tl] K1 ≡ K2 & ⬆*[tl] V2 ≡ V1 & X = K1.ⓑ{I}V1.
#X #Y #s #t * -X -Y -t
[ #t #Ht #J #K2 #W2 #tl #H destruct
| #I #L1 #L2 #V #t #_ #J #K2 #W2 #tl #_ #H2 destruct
| #I #L1 #L2 #V1 #V2 #t #HL #HV #J #K2 #W2 #tl #H1 #H2 destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_r *)
(* Basic_2A1: includes: drop_inv_skip2 *)
lemma drops_inv_skip2: ∀I,X,K2,V2,s,t. ⬇*[s, Ⓣ@t] X ≡ K2.ⓑ{I}V2 →
                       ∃∃K1,V1. ⬇*[s, t] K1 ≡ K2 & ⬆*[t] V2 ≡ V1 & X = K1.ⓑ{I}V1.
/2 width=5 by drops_inv_skip2_aux/ qed-.

(* Basic properties *********************************************************)

(* Basic_2A1: includes: drop_FT *)
lemma drops_FT: ∀L1,L2,t. ⬇*[Ⓕ, t] L1 ≡ L2 → ⬇*[Ⓣ, t] L1 ≡ L2.
#L1 #L2 #t #H elim H -L1 -L2 -t
/3 width=1 by drops_atom, drops_drop, drops_skip/
qed.

(* Basic_2A1: includes: drop_gen *)
lemma drops_gen: ∀L1,L2,s,t. ⬇*[Ⓕ, t] L1 ≡ L2 → ⬇*[s, t] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drops_FT/
qed-.

(* Basic_2A1: includes: drop_T *)
lemma drops_T: ∀L1,L2,s,t. ⬇*[s, t] L1 ≡ L2 → ⬇*[Ⓣ, t] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drops_FT/
qed-.

(* Basic forward lemmas *****************************************************)

fact drops_fwd_drop2_aux: ∀X,Y,s,t2. ⬇*[s, t2] X ≡ Y → ∀I,K,V. Y = K.ⓑ{I}V →
                          ∃∃t1,t. 𝐈⦃t1⦄ & t2 ⊚ Ⓕ@t1 ≡ t & ⬇*[s, t] X ≡ K.
#X #Y #s #t2 #H elim H -X -Y -t2
[ #t2 #Ht2 #J #K #W #H destruct
| #I #L1 #L2 #V #t2 #_ #IHL #J #K #W #H elim (IHL … H) -IHL
  /3 width=5 by after_false, ex3_2_intro, drops_drop/
| #I #L1 #L2 #V1 #V2 #t2 #HL #_ #_ #J #K #W #H destruct
  elim (isid_after_dx t2) /3 width=5 by after_true, ex3_2_intro, drops_drop/
]
qed-.

(* Basic_1: includes: drop_S *)
(* Basic_2A1: includes: drop_fwd_drop2 *)
lemma drops_fwd_drop2: ∀I,X,K,V,s,t2. ⬇*[s, t2] X ≡ K.ⓑ{I}V →
                       ∃∃t1,t. 𝐈⦃t1⦄ & t2 ⊚ Ⓕ@t1 ≡ t & ⬇*[s, t] X ≡ K.
/2 width=5 by drops_fwd_drop2_aux/ qed-.

fact drops_after_fwd_drop2_aux: ∀X,Y,s,t2. ⬇*[s, t2] X ≡ Y → ∀I,K,V. Y = K.ⓑ{I}V →
                                ∀t1,t. 𝐈⦃t1⦄ → t2 ⊚ Ⓕ@t1 ≡ t → ⬇*[s, t] X ≡ K.
#X #Y #s #t2 #H elim H -X -Y -t2
[ #t2 #Ht2 #J #K #W #H destruct
| #I #L1 #L2 #V #t2 #_ #IHL #J #K #W #H #t1 #t #Ht1 #Ht elim (after_inv_false1 … Ht) -Ht
  /3 width=3 by drops_drop/
| #I #L1 #L2 #V1 #V2 #t2 #HL #_ #_ #J #K #W #H #t1 #t #Ht1 #Ht elim (after_inv_true1 … Ht) -Ht
  #u1 #u #b #H1 #H2 #Hu destruct >(after_isid_inv_dx … Hu) -Hu /2 width=1 by drops_drop/
]
qed-.

lemma drops_after_fwd_drop2: ∀I,X,K,V,s,t2. ⬇*[s, t2] X ≡ K.ⓑ{I}V →
                             ∀t1,t. 𝐈⦃t1⦄ → t2 ⊚ Ⓕ@t1 ≡ t → ⬇*[s, t] X ≡ K.
/2 width=9 by drops_after_fwd_drop2_aux/ qed-.

(* Basic_1: includes: drop_gen_refl *)
(* Basic_2A1: includes: drop_inv_O2 *)
lemma drops_fwd_isid: ∀L1,L2,s,t. ⬇*[s, t] L1 ≡ L2 → 𝐈⦃t⦄ → L1 = L2.
#L1 #L2 #s #t #H elim H -L1 -L2 -t //
[ #I #L1 #L2 #V #t #_ #_ #H elim (isid_inv_false … H)
| /5 width=3 by isid_inv_true, lifts_fwd_isid, eq_f3, sym_eq/
]
qed-.

(* Basic_2A1: removed theorems 13:
              drops_inv_nil drops_inv_cons d1_liftable_liftables
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
