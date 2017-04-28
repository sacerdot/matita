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

include "ground_2/lib/star.ma".
include "basic_2/notation/relations/relationstarstar_4.ma".
include "basic_2/static/lfxs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

definition tc_lfxs (R): term → relation lenv ≝ LTC … (lfxs R).

interpretation "iterated extension on referred entries (local environment)"
   'RelationStarStar R T L1 L2 = (tc_lfxs R T L1 L2).

(* Basic properties *********************************************************)

lemma tc_lfxs_step_dx: ∀R,L1,L,T. L1 ⦻**[R, T] L →
                       ∀L2. L ⦻*[R, T] L2 → L1 ⦻**[R, T] L2.
#R #L1 #L2 #T #HL1 #L2 @step @HL1 (**) (* auto fails *)
qed-.

lemma tc_lfxs_step_sn: ∀R,L1,L,T. L1 ⦻*[R, T] L →
                       ∀L2. L ⦻**[R, T] L2 → L1 ⦻**[R, T] L2.
#R #L1 #L2 #T #HL1 #L2 @TC_strap @HL1 (**) (* auto fails *)
qed-.

lemma tc_lfxs_atom: ∀R,I. ⋆ ⦻**[R, ⓪{I}] ⋆.
/2 width=1 by inj/ qed.

lemma tc_lfxs_sort: ∀R,I,L1,L2,V1,V2,s.
                    L1 ⦻**[R, ⋆s] L2 → L1.ⓑ{I}V1 ⦻**[R, ⋆s] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #s #H elim H -L2
/3 width=4 by lfxs_sort, tc_lfxs_step_dx, inj/
qed.

lemma tc_lfxs_zero: ∀R. (∀L. reflexive … (R L)) →
                    ∀I,L1,L2,V. L1 ⦻**[R, V] L2 →
                    L1.ⓑ{I}V ⦻**[R, #0] L2.ⓑ{I}V.
#R #HR #I #L1 #L2 #V #H elim H -L2
/3 width=5 by lfxs_zero, tc_lfxs_step_dx, inj/
qed.

lemma tc_lfxs_lref: ∀R,I,L1,L2,V1,V2,i.
                    L1 ⦻**[R, #i] L2 → L1.ⓑ{I}V1 ⦻**[R, #⫯i] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #i #H elim H -L2
/3 width=4 by lfxs_lref, tc_lfxs_step_dx, inj/
qed.

lemma tc_lfxs_gref: ∀R,I,L1,L2,V1,V2,l.
                    L1 ⦻**[R, §l] L2 → L1.ⓑ{I}V1 ⦻**[R, §l] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #l #H elim H -L2
/3 width=4 by lfxs_gref, tc_lfxs_step_dx, inj/
qed.

lemma tc_lfxs_sym: ∀R. lexs_frees_confluent R cfull →
                   (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
                   ∀T. symmetric … (tc_lfxs R T).
#R #H1R #H2R #T #L1 #L2 #H elim H -L2
/4 width=3 by lfxs_sym, tc_lfxs_step_sn, inj/
qed-.

lemma tc_lfxs_co: ∀R1,R2. (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
                  ∀L1,L2,T. L1 ⦻**[R1, T] L2 → L1 ⦻**[R2, T] L2.
#R1 #R2 #HR #L1 #L2 #T #H elim H -L2
/4 width=5 by lfxs_co, tc_lfxs_step_dx, inj/
qed-.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: TC_lpx_sn_inv_atom1 *)
lemma tc_lfxs_inv_atom_sn: ∀R,I,Y2. ⋆ ⦻**[R, ⓪{I}] Y2 → Y2 = ⋆.
#R #I #Y2 #H elim H -Y2 /3 width=3 by inj, lfxs_inv_atom_sn/
qed-.

(* Basic_2A1: uses: TC_lpx_sn_inv_atom2 *)
lemma tc_lfxs_inv_atom_dx: ∀R,I,Y1. Y1 ⦻**[R, ⓪{I}] ⋆ → Y1 = ⋆.
#R #I #Y1 #H @(TC_ind_dx ??????? H) -Y1
/3 width=3 by inj, lfxs_inv_atom_dx/
qed-.

lemma tc_lfxs_inv_sort: ∀R,Y1,Y2,s. Y1 ⦻**[R, ⋆s] Y2 →
                        (Y1 = ⋆ ∧ Y2 = ⋆) ∨
                        ∃∃I,L1,L2,V1,V2. L1 ⦻**[R, ⋆s] L2 &
                                         Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R #Y1 #Y2 #s #H elim H -Y2
[ #Y2 #H elim (lfxs_inv_sort … H) -H *
  /4 width=8 by ex3_5_intro, inj, or_introl, or_intror, conj/
| #Y #Y2 #_ #H elim (lfxs_inv_sort … H) -H *
  [ #H #H2 * * /3 width=8 by ex3_5_intro, or_introl, or_intror, conj/
  | #I #L #L2 #V #V2 #HL2 #H #H2 * *
    [ #H1 #H0 destruct
    | #I0 #L1 #L0 #V1 #V0 #HL10 #H1 #H0 destruct
      /4 width=8 by ex3_5_intro, tc_lfxs_step_dx, or_intror/
    ]
  ]
] 
qed-.

lemma tc_lfxs_inv_gref: ∀R,Y1,Y2,l. Y1 ⦻**[R, §l] Y2 →
                        (Y1 = ⋆ ∧ Y2 = ⋆) ∨ 
                        ∃∃I,L1,L2,V1,V2. L1 ⦻**[R, §l] L2 &
                                         Y1 = L1.ⓑ{I}V1 & Y2 = L2.ⓑ{I}V2.
#R #Y1 #Y2 #l #H elim H -Y2
[ #Y2 #H elim (lfxs_inv_gref … H) -H *
  /4 width=8 by ex3_5_intro, inj, or_introl, or_intror, conj/
| #Y #Y2 #_ #H elim (lfxs_inv_gref … H) -H *
  [ #H #H2 * * /3 width=8 by ex3_5_intro, or_introl, or_intror, conj/
  | #I #L #L2 #V #V2 #HL2 #H #H2 * *
    [ #H1 #H0 destruct
    | #I0 #L1 #L0 #V1 #V0 #HL10 #H1 #H0 destruct
      /4 width=8 by ex3_5_intro, tc_lfxs_step_dx, or_intror/
    ]
  ]
] 
qed-.

lemma tc_lfxs_inv_bind: ∀R. (∀L. reflexive … (R L)) →
                        ∀p,I,L1,L2,V,T. L1 ⦻**[R, ⓑ{p,I}V.T] L2 →
                        L1 ⦻**[R, V] L2 ∧ L1.ⓑ{I}V ⦻**[R, T] L2.ⓑ{I}V.
#R #HR #p #I #L1 #L2 #V #T #H elim H -L2
[ #L2 #H elim (lfxs_inv_bind … V ? H) -H /3 width=1 by inj, conj/
| #L #L2 #_ #H * elim (lfxs_inv_bind … V ? H) -H /3 width=3 by tc_lfxs_step_dx, conj/
]
qed-.

lemma tc_lfxs_inv_flat: ∀R,I,L1,L2,V,T. L1 ⦻**[R, ⓕ{I}V.T] L2 →
                        L1 ⦻**[R, V] L2 ∧ L1 ⦻**[R, T] L2.
#R #I #L1 #L2 #V #T #H elim H -L2
[ #L2 #H elim (lfxs_inv_flat … H) -H /3 width=1 by inj, conj/
| #L #L2 #_ #H * elim (lfxs_inv_flat … H) -H /3 width=3 by tc_lfxs_step_dx, conj/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma tc_lfxs_inv_sort_pair_sn: ∀R,I,Y2,L1,V1,s. L1.ⓑ{I}V1 ⦻**[R, ⋆s] Y2 →
                                ∃∃L2,V2. L1 ⦻**[R, ⋆s] L2 & Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #s #H elim (tc_lfxs_inv_sort … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma tc_lfxs_inv_sort_pair_dx: ∀R,I,Y1,L2,V2,s. Y1 ⦻**[R, ⋆s] L2.ⓑ{I}V2 →
                                ∃∃L1,V1. L1 ⦻**[R, ⋆s] L2 & Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #s #H elim (tc_lfxs_inv_sort … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma tc_lfxs_inv_gref_pair_sn: ∀R,I,Y2,L1,V1,l. L1.ⓑ{I}V1 ⦻**[R, §l] Y2 →
                                ∃∃L2,V2. L1 ⦻**[R, §l] L2 & Y2 = L2.ⓑ{I}V2.
#R #I #Y2 #L1 #V1 #l #H elim (tc_lfxs_inv_gref … H) -H *
[ #H destruct
| #J #Y1 #L2 #X1 #V2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma tc_lfxs_inv_gref_pair_dx: ∀R,I,Y1,L2,V2,l. Y1 ⦻**[R, §l] L2.ⓑ{I}V2 →
                                ∃∃L1,V1. L1 ⦻**[R, §l] L2 & Y1 = L1.ⓑ{I}V1.
#R #I #Y1 #L2 #V2 #l #H elim (tc_lfxs_inv_gref … H) -H *
[ #_ #H destruct
| #J #L1 #Y2 #V1 #X2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma tc_lfxs_fwd_pair_sn: ∀R,I,L1,L2,V,T. L1 ⦻**[R, ②{I}V.T] L2 → L1 ⦻**[R, V] L2.
#R #I #L1 #L2 #V #T #H elim H -L2
/3 width=5 by lfxs_fwd_pair_sn, tc_lfxs_step_dx, inj/
qed-.

lemma tc_lfxs_fwd_bind_dx: ∀R. (∀L. reflexive … (R L)) →
                           ∀p,I,L1,L2,V,T. L1 ⦻**[R, ⓑ{p,I}V.T] L2 →
                           L1.ⓑ{I}V ⦻**[R, T] L2.ⓑ{I}V.
#R #HR #p #I #L1 #L2 #V #T #H elim (tc_lfxs_inv_bind … H) -H //
qed-.

lemma tc_lfxs_fwd_flat_dx: ∀R,I,L1,L2,V,T. L1 ⦻**[R, ⓕ{I}V.T] L2 → L1 ⦻**[R, T] L2.
#R #I #L1 #L2 #V #T #H elim (tc_lfxs_inv_flat … H) -H //
qed-.

(* Basic_2A1: removed theorems 2:
              TC_lpx_sn_inv_pair1 TC_lpx_sn_inv_pair2
*)
