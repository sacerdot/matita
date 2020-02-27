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

include "ground/xoa/ex_1_2.ma".
include "ground/xoa/ex_4_3.ma".
include "ground/relocation/rtmap_coafter.ma".
include "static_2/notation/relations/rdropstar_4.ma".
include "static_2/notation/relations/rdrop_3.ma".
include "static_2/relocation/seq.ma".
include "static_2/relocation/lifts_bind.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Basic_1: includes: drop_skip_bind drop1_skip_bind *)
(* Basic_2A1: includes: drop_atom drop_pair drop_drop drop_skip
                        drop_refl_atom_O2 drop_drop_lt drop_skip_lt
*)
inductive drops (b:bool): rtmap → relation lenv ≝
| drops_atom: ∀f. (b = Ⓣ → 𝐈❪f❫) → drops b (f) (⋆) (⋆)
| drops_drop: ∀f,I,L1,L2. drops b f L1 L2 → drops b (↑f) (L1.ⓘ[I]) L2
| drops_skip: ∀f,I1,I2,L1,L2.
              drops b f L1 L2 → ⇧*[f] I2 ≘ I1 →
              drops b (⫯f) (L1.ⓘ[I1]) (L2.ⓘ[I2])
.

interpretation "generic slicing (local environment)"
   'RDropStar b f L1 L2 = (drops b f L1 L2).

interpretation "uniform slicing (local environment)"
   'RDrop i L1 L2 = (drops true (uni i) L1 L2).

definition d_liftable1: predicate (relation2 lenv term) ≝
                        λR. ∀K,T. R K T → ∀b,f,L. ⇩*[b,f] L ≘ K →
                        ∀U. ⇧*[f] T ≘ U → R L U.

definition d_liftable1_isuni: predicate (relation2 lenv term) ≝
                              λR. ∀K,T. R K T → ∀b,f,L. ⇩*[b,f] L ≘ K → 𝐔❪f❫ →
                              ∀U. ⇧*[f] T ≘ U → R L U.

definition d_deliftable1: predicate (relation2 lenv term) ≝
                          λR. ∀L,U. R L U → ∀b,f,K. ⇩*[b,f] L ≘ K →
                          ∀T. ⇧*[f] T ≘ U → R K T.

definition d_deliftable1_isuni: predicate (relation2 lenv term) ≝
                                λR. ∀L,U. R L U → ∀b,f,K. ⇩*[b,f] L ≘ K → 𝐔❪f❫ →
                                ∀T. ⇧*[f] T ≘ U → R K T.

definition d_liftable2_sn: ∀C:Type[0]. ∀S:?→relation C.
                           predicate (lenv→relation C) ≝
                           λC,S,R. ∀K,T1,T2. R K T1 T2 → ∀b,f,L. ⇩*[b,f] L ≘ K →
                           ∀U1. S f T1 U1 →
                           ∃∃U2. S f T2 U2 & R L U1 U2.

definition d_deliftable2_sn: ∀C:Type[0]. ∀S:?→relation C.
                             predicate (lenv→relation C) ≝
                             λC,S,R. ∀L,U1,U2. R L U1 U2 → ∀b,f,K. ⇩*[b,f] L ≘ K →
                             ∀T1. S f T1 U1 →
                             ∃∃T2. S f T2 U2 & R K T1 T2.

definition d_liftable2_bi: ∀C:Type[0]. ∀S:?→relation C.
                           predicate (lenv→relation C) ≝
                           λC,S,R. ∀K,T1,T2. R K T1 T2 → ∀b,f,L. ⇩*[b,f] L ≘ K →
                           ∀U1. S f T1 U1 →
                           ∀U2. S f T2 U2 → R L U1 U2.

definition d_deliftable2_bi: ∀C:Type[0]. ∀S:?→relation C.
                             predicate (lenv→relation C) ≝
                             λC,S,R. ∀L,U1,U2. R L U1 U2 → ∀b,f,K. ⇩*[b,f] L ≘ K →
                             ∀T1. S f T1 U1 →
                             ∀T2. S f T2 U2 → R K T1 T2.

definition co_dropable_sn: predicate (?→relation lenv) ≝
                           λR. ∀b,f,L1,K1. ⇩*[b,f] L1 ≘ K1 → 𝐔❪f❫ →
                           ∀f2,L2. R f2 L1 L2 → ∀f1. f ~⊚ f1 ≘ f2 →
                           ∃∃K2. R f1 K1 K2 & ⇩*[b,f] L2 ≘ K2.

definition co_dropable_dx: predicate (?→relation lenv) ≝
                           λR. ∀f2,L1,L2. R f2 L1 L2 →
                           ∀b,f,K2. ⇩*[b,f] L2 ≘ K2 → 𝐔❪f❫ →
                           ∀f1. f ~⊚ f1 ≘ f2 →
                           ∃∃K1. ⇩*[b,f] L1 ≘ K1 & R f1 K1 K2.

definition co_dedropable_sn: predicate (?→relation lenv) ≝
                             λR. ∀b,f,L1,K1. ⇩*[b,f] L1 ≘ K1 → ∀f1,K2. R f1 K1 K2 →
                             ∀f2. f ~⊚ f1 ≘ f2 →
                             ∃∃L2. R f2 L1 L2 & ⇩*[b,f] L2 ≘ K2 & L1 ≡[f] L2.

(* Basic properties *********************************************************)

lemma drops_atom_F: ∀f. ⇩*[Ⓕ,f] ⋆ ≘ ⋆.
#f @drops_atom #H destruct
qed.

lemma drops_eq_repl_back: ∀b,L1,L2. eq_repl_back … (λf. ⇩*[b,f] L1 ≘ L2).
#b #L1 #L2 #f1 #H elim H -f1 -L1 -L2
[ /4 width=3 by drops_atom, isid_eq_repl_back/
| #f1 #I #L1 #L2 #_ #IH #f2 #H elim (eq_inv_nx … H) -H
  /3 width=3 by drops_drop/
| #f1 #I1 #I2 #L1 #L2 #_ #HI #IH #f2 #H elim (eq_inv_px … H) -H
  /3 width=3 by drops_skip, liftsb_eq_repl_back/
]
qed-.

lemma drops_eq_repl_fwd: ∀b,L1,L2. eq_repl_fwd … (λf. ⇩*[b,f] L1 ≘ L2).
#b #L1 #L2 @eq_repl_sym /2 width=3 by drops_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Basic_2A1: includes: drop_FT *)
lemma drops_TF: ∀f,L1,L2. ⇩*[Ⓣ,f] L1 ≘ L2 → ⇩*[Ⓕ,f] L1 ≘ L2.
#f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by drops_atom, drops_drop, drops_skip/
qed.

(* Basic_2A1: includes: drop_gen *)
lemma drops_gen: ∀b,f,L1,L2. ⇩*[Ⓣ,f] L1 ≘ L2 → ⇩*[b,f] L1 ≘ L2.
* /2 width=1 by drops_TF/
qed-.

(* Basic_2A1: includes: drop_T *)
lemma drops_F: ∀b,f,L1,L2. ⇩*[b,f] L1 ≘ L2 → ⇩*[Ⓕ,f] L1 ≘ L2.
* /2 width=1 by drops_TF/
qed-.

lemma d_liftable2_sn_bi: ∀C,S. (∀f,c. is_mono … (S f c)) →
                         ∀R. d_liftable2_sn C S R → d_liftable2_bi C S R.
#C #S #HS #R #HR #K #T1 #T2 #HT12 #b #f #L #HLK #U1 #HTU1 #U2 #HTU2
elim (HR … HT12 … HLK … HTU1) -HR -K -T1 #X #HTX #HUX
<(HS … HTX … HTU2) -T2 -U2 -b -f //
qed-.

lemma d_deliftable2_sn_bi: ∀C,S. (∀f. is_inj2 … (S f)) →
                           ∀R. d_deliftable2_sn C S R → d_deliftable2_bi C S R.
#C #S #HS #R #HR #L #U1 #U2 #HU12 #b #f #K #HLK #T1 #HTU1 #T2 #HTU2
elim (HR … HU12 … HLK … HTU1) -HR -L -U1 #X #HUX #HTX
<(HS … HUX … HTU2) -U2 -T2 -b -f //
qed-.

(* Basic inversion lemmas ***************************************************)

fact drops_inv_atom1_aux: ∀b,f,X,Y. ⇩*[b,f] X ≘ Y → X = ⋆ →
                          Y = ⋆ ∧ (b = Ⓣ → 𝐈❪f❫).
#b #f #X #Y * -f -X -Y
[ /3 width=1 by conj/
| #f #I #L1 #L2 #_ #H destruct
| #f #I1 #I2 #L1 #L2 #_ #_ #H destruct
]
qed-.

(* Basic_1: includes: drop_gen_sort *)
(* Basic_2A1: includes: drop_inv_atom1 *)
lemma drops_inv_atom1: ∀b,f,Y. ⇩*[b,f] ⋆ ≘ Y → Y = ⋆ ∧ (b = Ⓣ → 𝐈❪f❫).
/2 width=3 by drops_inv_atom1_aux/ qed-.

fact drops_inv_drop1_aux: ∀b,f,X,Y. ⇩*[b,f] X ≘ Y → ∀g,I,K. X = K.ⓘ[I] → f = ↑g →
                          ⇩*[b,g] K ≘ Y.
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J #K #H destruct
| #f #I #L1 #L2 #HL #g #J #K #H1 #H2 <(injective_next … H2) -g destruct //
| #f #I1 #I2 #L1 #L2 #_ #_ #g #J #K #_ #H2 elim (discr_push_next … H2)
]
qed-.

(* Basic_1: includes: drop_gen_drop *)
(* Basic_2A1: includes: drop_inv_drop1_lt drop_inv_drop1 *)
lemma drops_inv_drop1: ∀b,f,I,K,Y. ⇩*[b,↑f] K.ⓘ[I] ≘ Y → ⇩*[b,f] K ≘ Y.
/2 width=6 by drops_inv_drop1_aux/ qed-.

fact drops_inv_skip1_aux: ∀b,f,X,Y. ⇩*[b,f] X ≘ Y → ∀g,I1,K1. X = K1.ⓘ[I1] → f = ⫯g →
                          ∃∃I2,K2. ⇩*[b,g] K1 ≘ K2 & ⇧*[g] I2 ≘ I1 & Y = K2.ⓘ[I2].
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J1 #K1 #H destruct
| #f #I #L1 #L2 #_ #g #J1 #K1 #_ #H2 elim (discr_next_push … H2)
| #f #I1 #I2 #L1 #L2 #HL #HI #g #J1 #K1 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_l *)
(* Basic_2A1: includes: drop_inv_skip1 *)
lemma drops_inv_skip1: ∀b,f,I1,K1,Y. ⇩*[b,⫯f] K1.ⓘ[I1] ≘ Y →
                       ∃∃I2,K2. ⇩*[b,f] K1 ≘ K2 & ⇧*[f] I2 ≘ I1 & Y = K2.ⓘ[I2].
/2 width=5 by drops_inv_skip1_aux/ qed-.

fact drops_inv_skip2_aux: ∀b,f,X,Y. ⇩*[b,f] X ≘ Y → ∀g,I2,K2. Y = K2.ⓘ[I2] → f = ⫯g →
                          ∃∃I1,K1. ⇩*[b,g] K1 ≘ K2 & ⇧*[g] I2 ≘ I1 & X = K1.ⓘ[I1].
#b #f #X #Y * -f -X -Y
[ #f #Hf #g #J2 #K2 #H destruct
| #f #I #L1 #L2 #_ #g #J2 #K2 #_ #H2 elim (discr_next_push … H2)
| #f #I1 #I2 #L1 #L2 #HL #HV #g #J2 #K2 #H1 #H2 <(injective_push … H2) -g destruct
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: drop_gen_skip_r *)
(* Basic_2A1: includes: drop_inv_skip2 *)
lemma drops_inv_skip2: ∀b,f,I2,X,K2. ⇩*[b,⫯f] X ≘ K2.ⓘ[I2] →
                       ∃∃I1,K1. ⇩*[b,f] K1 ≘ K2 & ⇧*[f] I2 ≘ I1 & X = K1.ⓘ[I1].
/2 width=5 by drops_inv_skip2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

fact drops_fwd_drop2_aux: ∀b,f2,X,Y. ⇩*[b,f2] X ≘ Y → ∀I,K. Y = K.ⓘ[I] →
                          ∃∃f1,f. 𝐈❪f1❫ & f2 ⊚ ↑f1 ≘ f & ⇩*[b,f] X ≘ K.
#b #f2 #X #Y #H elim H -f2 -X -Y
[ #f2 #Hf2 #J #K #H destruct
| #f2 #I #L1 #L2 #_ #IHL #J #K #H elim (IHL … H) -IHL
  /3 width=7 by after_next, ex3_2_intro, drops_drop/
| #f2 #I1 #I2 #L1 #L2 #HL #_ #_ #J #K #H destruct
  lapply (after_isid_dx 𝐈𝐝 … f2) /3 width=9 by after_push, ex3_2_intro, drops_drop/
]
qed-.

lemma drops_fwd_drop2: ∀b,f2,I,X,K. ⇩*[b,f2] X ≘ K.ⓘ[I] →
                       ∃∃f1,f. 𝐈❪f1❫ & f2 ⊚ ↑f1 ≘ f & ⇩*[b,f] X ≘ K.
/2 width=4 by drops_fwd_drop2_aux/ qed-.

(* Properties with test for identity ****************************************)

(* Basic_2A1: includes: drop_refl *)
lemma drops_refl: ∀b,L,f. 𝐈❪f❫ → ⇩*[b,f] L ≘ L.
#b #L elim L -L /2 width=1 by drops_atom/
#L #I #IHL #f #Hf elim (isid_inv_gen … Hf) -Hf
/3 width=1 by drops_skip, liftsb_refl/
qed.

(* Forward lemmas test for identity *****************************************)

(* Basic_1: includes: drop_gen_refl *)
(* Basic_2A1: includes: drop_inv_O2 *)
lemma drops_fwd_isid: ∀b,f,L1,L2. ⇩*[b,f] L1 ≘ L2 → 𝐈❪f❫ → L1 = L2.
#b #f #L1 #L2 #H elim H -f -L1 -L2 //
[ #f #I #L1 #L2 #_ #_ #H elim (isid_inv_next … H) //
| /5 width=5 by isid_inv_push, liftsb_fwd_isid, eq_f2, sym_eq/
]
qed-.

lemma drops_after_fwd_drop2: ∀b,f2,I,X,K. ⇩*[b,f2] X ≘ K.ⓘ[I] →
                             ∀f1,f. 𝐈❪f1❫ → f2 ⊚ ↑f1 ≘ f → ⇩*[b,f] X ≘ K.
#b #f2 #I #X #K #H #f1 #f #Hf1 #Hf elim (drops_fwd_drop2 … H) -H
#g1 #g #Hg1 #Hg #HK lapply (after_mono_eq … Hg … Hf ??) -Hg -Hf
/3 width=5 by drops_eq_repl_back, isid_inv_eq_repl, eq_next/
qed-.

(* Forward lemmas with test for finite colength *****************************)

lemma drops_fwd_isfin: ∀f,L1,L2. ⇩*[Ⓣ,f] L1 ≘ L2 → 𝐅❪f❫.
#f #L1 #L2 #H elim H -f -L1 -L2
/3 width=1 by isfin_next, isfin_push, isfin_isid/
qed-.

(* Properties with test for uniformity **************************************)

lemma drops_isuni_ex: ∀f. 𝐔❪f❫ → ∀L. ∃K. ⇩*[Ⓕ,f] L ≘ K.
#f #H elim H -f /4 width=2 by drops_refl, drops_TF, ex_intro/
#f #_ #g #H #IH destruct * /2 width=2 by ex_intro/
#L #I elim (IH L) -IH /3 width=2 by drops_drop, ex_intro/
qed-.

(* Inversion lemmas with test for uniformity ********************************)

lemma drops_inv_isuni: ∀f,L1,L2. ⇩*[Ⓣ,f] L1 ≘ L2 → 𝐔❪f❫ →
                       (𝐈❪f❫ ∧ L1 = L2) ∨
                       ∃∃g,I,K. ⇩*[Ⓣ,g] K ≘ L2 & 𝐔❪g❫ & L1 = K.ⓘ[I] & f = ↑g.
#f #L1 #L2 * -f -L1 -L2
[ /4 width=1 by or_introl, conj/
| /4 width=7 by isuni_inv_next, ex4_3_intro, or_intror/
| /7 width=6 by drops_fwd_isid, liftsb_fwd_isid, isuni_inv_push, isid_push, or_introl, conj, eq_f2, sym_eq/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair1 *)
lemma drops_inv_bind1_isuni: ∀b,f,I,K,L2. 𝐔❪f❫ → ⇩*[b,f] K.ⓘ[I] ≘ L2 →
                             (𝐈❪f❫ ∧ L2 = K.ⓘ[I]) ∨
                             ∃∃g. 𝐔❪g❫ & ⇩*[b,g] K ≘ L2 & f = ↑g.
#b #f #I #K #L2 #Hf #H elim (isuni_split … Hf) -Hf * #g #Hg #H0 destruct
[ lapply (drops_inv_skip1 … H) -H * #Z #Y #HY #HZ #H destruct
  <(drops_fwd_isid … HY Hg) -Y >(liftsb_fwd_isid … HZ Hg) -Z
  /4 width=3 by isid_push, or_introl, conj/
| lapply (drops_inv_drop1 … H) -H /3 width=4 by ex3_intro, or_intror/
]
qed-.

(* Basic_2A1: was: drop_inv_O1_pair2 *)
lemma drops_inv_bind2_isuni: ∀b,f,I,K,L1. 𝐔❪f❫ → ⇩*[b,f] L1 ≘ K.ⓘ[I] →
                             (𝐈❪f❫ ∧ L1 = K.ⓘ[I]) ∨
                             ∃∃g,I1,K1. 𝐔❪g❫ & ⇩*[b,g] K1 ≘ K.ⓘ[I] & L1 = K1.ⓘ[I1] & f = ↑g.
#b #f #I #K *
[ #Hf #H elim (drops_inv_atom1 … H) -H #H destruct
| #L1 #I1 #Hf #H elim (drops_inv_bind1_isuni … Hf H) -Hf -H *
  [ #Hf #H destruct /3 width=1 by or_introl, conj/
  | /3 width=7 by ex4_3_intro, or_intror/
  ]
]
qed-.

lemma drops_inv_bind2_isuni_next: ∀b,f,I,K,L1. 𝐔❪f❫ → ⇩*[b,↑f] L1 ≘ K.ⓘ[I] →
                                  ∃∃I1,K1. ⇩*[b,f] K1 ≘ K.ⓘ[I] & L1 = K1.ⓘ[I1].
#b #f #I #K #L1 #Hf #H elim (drops_inv_bind2_isuni … H) -H /2 width=3 by isuni_next/ -Hf *
[ #H elim (isid_inv_next … H) -H //
| /2 width=4 by ex2_2_intro/
]
qed-.

fact drops_inv_TF_aux: ∀f,L1,L2. ⇩*[Ⓕ,f] L1 ≘ L2 → 𝐔❪f❫ →
                       ∀I,K. L2 = K.ⓘ[I] → ⇩*[Ⓣ,f] L1 ≘ K.ⓘ[I].
#f #L1 #L2 #H elim H -f -L1 -L2
[ #f #_ #_ #J #K #H destruct
| #f #I #L1 #L2 #_ #IH #Hf #J #K #H destruct
  /4 width=3 by drops_drop, isuni_inv_next/
| #f #I1 #I2 #L1 #L2 #HL12 #HI21 #_ #Hf #J #K #H destruct
  lapply (isuni_inv_push … Hf ??) -Hf [1,2: // ] #Hf
  <(drops_fwd_isid … HL12) -K // <(liftsb_fwd_isid … HI21) -I1
  /3 width=3 by drops_refl, isid_push/
]
qed-.

(* Basic_2A1: includes: drop_inv_FT *)
lemma drops_inv_TF: ∀f,I,L,K. ⇩*[Ⓕ,f] L ≘ K.ⓘ[I] → 𝐔❪f❫ → ⇩*[Ⓣ,f] L ≘ K.ⓘ[I].
/2 width=3 by drops_inv_TF_aux/ qed-.

(* Basic_2A1: includes: drop_inv_gen *)
lemma drops_inv_gen: ∀b,f,I,L,K. ⇩*[b,f] L ≘ K.ⓘ[I] → 𝐔❪f❫ → ⇩*[Ⓣ,f] L ≘ K.ⓘ[I].
* /2 width=1 by drops_inv_TF/
qed-.

(* Basic_2A1: includes: drop_inv_T *)
lemma drops_inv_F: ∀b,f,I,L,K. ⇩*[Ⓕ,f] L ≘ K.ⓘ[I] → 𝐔❪f❫ → ⇩*[b,f] L ≘ K.ⓘ[I].
* /2 width=1 by drops_inv_TF/
qed-.

(* Forward lemmas with test for uniformity **********************************)

(* Basic_1: was: drop_S *)
(* Basic_2A1: was: drop_fwd_drop2 *)
lemma drops_isuni_fwd_drop2: ∀b,f,I,X,K. 𝐔❪f❫ → ⇩*[b,f] X ≘ K.ⓘ[I] → ⇩*[b,↑f] X ≘ K.
/3 width=7 by drops_after_fwd_drop2, after_isid_isuni/ qed-.

(* Inversion lemmas with uniform relocations ********************************)

lemma drops_inv_atom2: ∀b,L,f. ⇩*[b,f] L ≘ ⋆ →
                       ∃∃n,f1. ⇩*[b,𝐔❨n❩] L ≘ ⋆ & 𝐔❨n❩ ⊚ f1 ≘ f.
#b #L elim L -L
[ /3 width=4 by drops_atom, after_isid_sn, ex2_2_intro/
| #L #I #IH #f #H elim (pn_split f) * #g #H0 destruct
  [ elim (drops_inv_skip1 … H) -H #J #K #_ #_ #H destruct
  | lapply (drops_inv_drop1 … H) -H #HL
    elim (IH … HL) -IH -HL /3 width=8 by drops_drop, after_next, ex2_2_intro/
  ]
]
qed-.

lemma drops_inv_succ: ∀L1,L2,i. ⇩[↑i] L1 ≘ L2 →
                      ∃∃I,K. ⇩[i] K ≘ L2 & L1 = K.ⓘ[I].
#L1 #L2 #i #H elim (drops_inv_isuni … H) -H // *
[ #H elim (isid_inv_next … H) -H //
| /2 width=4 by ex2_2_intro/
]
qed-.

(* Properties with uniform relocations **************************************)

lemma drops_F_uni: ∀L,i. ⇩*[Ⓕ,𝐔❨i❩] L ≘ ⋆ ∨ ∃∃I,K. ⇩[i] L ≘ K.ⓘ[I].
#L elim L -L /2 width=1 by or_introl/
#L #I #IH * /4 width=3 by drops_refl, ex1_2_intro, or_intror/
#i elim (IH i) -IH /3 width=1 by drops_drop, or_introl/
* /4 width=3 by drops_drop, ex1_2_intro, or_intror/
qed-.

(* Basic_2A1: includes: drop_split *)
lemma drops_split_trans: ∀b,f,L1,L2. ⇩*[b,f] L1 ≘ L2 → ∀f1,f2. f1 ⊚ f2 ≘ f → 𝐔❪f1❫ →
                         ∃∃L. ⇩*[b,f1] L1 ≘ L & ⇩*[b,f2] L ≘ L2.
#b #f #L1 #L2 #H elim H -f -L1 -L2
[ #f #H0f #f1 #f2 #Hf #Hf1 @(ex2_intro … (⋆)) @drops_atom
  #H lapply (H0f H) -b
  #H elim (after_inv_isid3 … Hf H) -f //
| #f #I #L1 #L2 #HL12 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxn … Hf) -Hf [1,3: * |*: // ]
  [ #g1 #g2 #Hf #H1 #H2 destruct
    lapply (isuni_inv_push … Hf1 ??) -Hf1 [1,2: // ] #Hg1
    elim (IHL12 … Hf) -f
    /4 width=5 by drops_drop, drops_skip, liftsb_refl, isuni_isid, ex2_intro/
  | #g1 #Hf #H destruct elim (IHL12 … Hf) -f
    /3 width=5 by ex2_intro, drops_drop, isuni_inv_next/
  ]
| #f #I1 #I2 #L1 #L2 #_ #HI21 #IHL12 #f1 #f2 #Hf #Hf1 elim (after_inv_xxp … Hf) -Hf [2,3: // ]
  #g1 #g2 #Hf #H1 #H2 destruct elim (liftsb_split_trans … HI21 … Hf) -HI21
  elim (IHL12 … Hf) -f /3 width=5 by ex2_intro, drops_skip, isuni_fwd_push/
]
qed-.

lemma drops_split_div: ∀b,f1,L1,L. ⇩*[b,f1] L1 ≘ L → ∀f2,f. f1 ⊚ f2 ≘ f → 𝐔❪f2❫ →
                       ∃∃L2. ⇩*[Ⓕ,f2] L ≘ L2 & ⇩*[Ⓕ,f] L1 ≘ L2.
#b #f1 #L1 #L #H elim H -f1 -L1 -L
[ #f1 #Hf1 #f2 #f #Hf #Hf2 @(ex2_intro … (⋆)) @drops_atom #H destruct
| #f1 #I #L1 #L #HL1 #IH #f2 #f #Hf #Hf2 elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g #Hg #H destruct elim (IH … Hg) -IH -Hg /3 width=5 by drops_drop, ex2_intro/
| #f1 #I1 #I #L1 #L #HL1 #HI1 #IH #f2 #f #Hf #Hf2
  elim (after_inv_pxx … Hf) -Hf [1,3: * |*: // ]
  #g2 #g #Hg #H2 #H0 destruct
  [ lapply (isuni_inv_push … Hf2 ??) -Hf2 [1,2: // ] #Hg2 -IH
    lapply (after_isid_inv_dx … Hg … Hg2) -Hg #Hg
    /5 width=7 by drops_eq_repl_back, drops_F, drops_refl, drops_skip, liftsb_eq_repl_back, isid_push, ex2_intro/
  | lapply (isuni_inv_next … Hf2 ??) -Hf2 [1,2: // ] #Hg2 -HL1 -HI1
    elim (IH … Hg) -f1 /3 width=3 by drops_drop, ex2_intro/
  ]
]
qed-.

(* Properties with application **********************************************)

lemma drops_tls_at: ∀f,i1,i2. @❪i1,f❫ ≘ i2 →
                    ∀b,L1,L2. ⇩*[b,⫱*[i2]f] L1 ≘ L2 →
                    ⇩*[b,⫯⫱*[↑i2]f] L1 ≘ L2.
/3 width=3 by drops_eq_repl_fwd, at_inv_tls/ qed-.

lemma drops_split_trans_bind2: ∀b,f,I,L,K0. ⇩*[b,f] L ≘ K0.ⓘ[I] → ∀i. @❪O,f❫ ≘ i →
                               ∃∃J,K. ⇩[i]L ≘ K.ⓘ[J] & ⇩*[b,⫱*[↑i]f] K ≘ K0 & ⇧*[⫱*[↑i]f] I ≘ J.
#b #f #I #L #K0 #H #i #Hf
elim (drops_split_trans … H) -H [ |5: @(after_uni_dx … Hf) |2,3: skip ] /2 width=1 by after_isid_dx/ #Y #HLY #H
lapply (drops_tls_at … Hf … H) -H #H
elim (drops_inv_skip2 … H) -H #J #K #HK0 #HIJ #H destruct
/3 width=5 by drops_inv_gen, ex3_2_intro/
qed-.

(* Properties with context-sensitive equivalence for terms ******************)

lemma ceq_lift_sn: d_liftable2_sn … liftsb ceq_ext.
#K #I1 #I2 #H <(ceq_ext_inv_eq … H) -I2
/2 width=3 by ex2_intro/ qed-.

lemma ceq_inv_lift_sn: d_deliftable2_sn … liftsb ceq_ext.
#L #J1 #J2 #H <(ceq_ext_inv_eq … H) -J2
/2 width=3 by ex2_intro/ qed-.

(* Note: d_deliftable2_sn cfull does not hold *)
lemma cfull_lift_sn: d_liftable2_sn … liftsb cfull.
#K #I1 #I2 #_ #b #f #L #_ #J1 #_ -K -I1 -b
elim (liftsb_total I2 f) /2 width=3 by ex2_intro/
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
