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
include "static_2/notation/relations/relationstar_4.ma".
include "static_2/static/rex.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

definition rexs (R): term → relation lenv ≝ CTC … (rex R).

interpretation "iterated extension on referred entries (local environment)"
   'RelationStar R T L1 L2 = (rexs R T L1 L2).

(* Basic properties *********************************************************)

lemma rexs_step_dx: ∀R,L1,L,T. L1 ⪤*[R,T] L →
                    ∀L2. L ⪤[R,T] L2 → L1 ⪤*[R,T] L2.
#R #L1 #L2 #T #HL1 #L2 @step @HL1 (**) (* auto fails *)
qed-.

lemma rexs_step_sn: ∀R,L1,L,T. L1 ⪤[R,T] L →
                    ∀L2. L ⪤*[R,T] L2 → L1 ⪤*[R,T] L2.
#R #L1 #L2 #T #HL1 #L2 @TC_strap @HL1 (**) (* auto fails *)
qed-.

lemma rexs_atom: ∀R,I. ⋆ ⪤*[R,⓪{I}] ⋆.
/2 width=1 by inj/ qed.

lemma rexs_sort: ∀R,I,L1,L2,V1,V2,s.
                 L1 ⪤*[R,⋆s] L2 → L1.ⓑ{I}V1 ⪤*[R,⋆s] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #s #H elim H -L2
/3 width=4 by rex_sort, rexs_step_dx, inj/
qed.

lemma rexs_pair: ∀R. (∀L. reflexive … (R L)) →
                 ∀I,L1,L2,V. L1 ⪤*[R,V] L2 →
                 L1.ⓑ{I}V ⪤*[R,#0] L2.ⓑ{I}V.
#R #HR #I #L1 #L2 #V #H elim H -L2
/3 width=5 by rex_pair, rexs_step_dx, inj/
qed.

lemma rexs_unit: ∀R,f,I,L1,L2. 𝐈⦃f⦄ → L1 ⪤[cext2 R,cfull,f] L2 →
                 L1.ⓤ{I} ⪤*[R,#0] L2.ⓤ{I}.
/3 width=3 by rex_unit, inj/ qed.

lemma rexs_lref: ∀R,I,L1,L2,V1,V2,i.
                 L1 ⪤*[R,#i] L2 → L1.ⓑ{I}V1 ⪤*[R,#↑i] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #i #H elim H -L2
/3 width=4 by rex_lref, rexs_step_dx, inj/
qed.

lemma rexs_gref: ∀R,I,L1,L2,V1,V2,l.
                 L1 ⪤*[R,§l] L2 → L1.ⓑ{I}V1 ⪤*[R,§l] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #V2 #l #H elim H -L2
/3 width=4 by rex_gref, rexs_step_dx, inj/
qed.

lemma rexs_co: ∀R1,R2. (∀L,T1,T2. R1 L T1 T2 → R2 L T1 T2) →
               ∀L1,L2,T. L1 ⪤*[R1,T] L2 → L1 ⪤*[R2,T] L2.
#R1 #R2 #HR #L1 #L2 #T #H elim H -L2
/4 width=5 by rex_co, rexs_step_dx, inj/
qed-.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: TC_lpx_sn_inv_atom1 *)
lemma rexs_inv_atom_sn: ∀R,I,Y2. ⋆ ⪤*[R,⓪{I}] Y2 → Y2 = ⋆.
#R #I #Y2 #H elim H -Y2 /3 width=3 by inj, rex_inv_atom_sn/
qed-.

(* Basic_2A1: uses: TC_lpx_sn_inv_atom2 *)
lemma rexs_inv_atom_dx: ∀R,I,Y1. Y1 ⪤*[R,⓪{I}] ⋆ → Y1 = ⋆.
#R #I #Y1 #H @(TC_ind_dx ??????? H) -Y1
/3 width=3 by inj, rex_inv_atom_dx/
qed-.

lemma rexs_inv_sort: ∀R,Y1,Y2,s. Y1 ⪤*[R,⋆s] Y2 →
                     ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
                      | ∃∃I1,I2,L1,L2. L1 ⪤*[R,⋆s] L2 &
                                       Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
#R #Y1 #Y2 #s #H elim H -Y2
[ #Y2 #H elim (rex_inv_sort … H) -H *
  /4 width=8 by ex3_4_intro, inj, or_introl, or_intror, conj/
| #Y #Y2 #_ #H elim (rex_inv_sort … H) -H *
  [ #H #H2 * * /3 width=7 by ex3_4_intro, or_introl, or_intror, conj/
  | #I #I2 #L #L2 #HL2 #H #H2 * *
    [ #H1 #H0 destruct
    | #I1 #I0 #L1 #L0 #HL10 #H1 #H0 destruct
      /4 width=7 by ex3_4_intro, rexs_step_dx, or_intror/
    ]
  ]
]
qed-.

lemma rexs_inv_gref: ∀R,Y1,Y2,l. Y1 ⪤*[R,§l] Y2 →
                     ∨∨ ∧∧ Y1 = ⋆ & Y2 = ⋆
                      | ∃∃I1,I2,L1,L2. L1 ⪤*[R,§l] L2 &
                                       Y1 = L1.ⓘ{I1} & Y2 = L2.ⓘ{I2}.
#R #Y1 #Y2 #l #H elim H -Y2
[ #Y2 #H elim (rex_inv_gref … H) -H *
  /4 width=8 by ex3_4_intro, inj, or_introl, or_intror, conj/
| #Y #Y2 #_ #H elim (rex_inv_gref … H) -H *
  [ #H #H2 * * /3 width=7 by ex3_4_intro, or_introl, or_intror, conj/
  | #I #I2 #L #L2 #HL2 #H #H2 * *
    [ #H1 #H0 destruct
    | #I1 #I0 #L1 #L0 #HL10 #H1 #H0 destruct
      /4 width=7 by ex3_4_intro, rexs_step_dx, or_intror/
    ]
  ]
]
qed-.

lemma rexs_inv_bind: ∀R. (∀L. reflexive … (R L)) →
                     ∀p,I,L1,L2,V,T. L1 ⪤*[R,ⓑ{p,I}V.T] L2 →
                     ∧∧ L1 ⪤*[R,V] L2 & L1.ⓑ{I}V ⪤*[R,T] L2.ⓑ{I}V.
#R #HR #p #I #L1 #L2 #V #T #H elim H -L2
[ #L2 #H elim (rex_inv_bind … V ? H) -H /3 width=1 by inj, conj/
| #L #L2 #_ #H * elim (rex_inv_bind … V ? H) -H /3 width=3 by rexs_step_dx, conj/
]
qed-.

lemma rexs_inv_flat: ∀R,I,L1,L2,V,T. L1 ⪤*[R,ⓕ{I}V.T] L2 →
                     ∧∧ L1 ⪤*[R,V] L2 & L1 ⪤*[R,T] L2.
#R #I #L1 #L2 #V #T #H elim H -L2
[ #L2 #H elim (rex_inv_flat … H) -H /3 width=1 by inj, conj/
| #L #L2 #_ #H * elim (rex_inv_flat … H) -H /3 width=3 by rexs_step_dx, conj/
]
qed-.

(* Advanced inversion lemmas ************************************************)

lemma rexs_inv_sort_bind_sn: ∀R,I1,Y2,L1,s. L1.ⓘ{I1} ⪤*[R,⋆s] Y2 →
                             ∃∃I2,L2. L1 ⪤*[R,⋆s] L2 & Y2 = L2.ⓘ{I2}.
#R #I1 #Y2 #L1 #s #H elim (rexs_inv_sort … H) -H *
[ #H destruct
| #Z #I2 #Y1 #L2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma rexs_inv_sort_bind_dx: ∀R,I2,Y1,L2,s. Y1 ⪤*[R,⋆s] L2.ⓘ{I2} →
                             ∃∃I1,L1. L1 ⪤*[R,⋆s] L2 & Y1 = L1.ⓘ{I1}.
#R #I2 #Y1 #L2 #s #H elim (rexs_inv_sort … H) -H *
[ #_ #H destruct
| #I1 #Z #L1 #Y2 #Hs #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma rexs_inv_gref_bind_sn: ∀R,I1,Y2,L1,l. L1.ⓘ{I1} ⪤*[R,§l] Y2 →
                             ∃∃I2,L2. L1 ⪤*[R,§l] L2 & Y2 = L2.ⓘ{I2}.
#R #I1 #Y2 #L1 #l #H elim (rexs_inv_gref … H) -H *
[ #H destruct
| #Z #I2 #Y1 #L2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

lemma rexs_inv_gref_bind_dx: ∀R,I2,Y1,L2,l. Y1 ⪤*[R,§l] L2.ⓘ{I2} →
                             ∃∃I1,L1. L1 ⪤*[R,§l] L2 & Y1 = L1.ⓘ{I1}.
#R #I2 #Y1 #L2 #l #H elim (rexs_inv_gref … H) -H *
[ #_ #H destruct
| #I1 #Z #L1 #Y2 #Hl #H1 #H2 destruct /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma rexs_fwd_pair_sn: ∀R,I,L1,L2,V,T. L1 ⪤*[R,②{I}V.T] L2 → L1 ⪤*[R,V] L2.
#R #I #L1 #L2 #V #T #H elim H -L2
/3 width=5 by rex_fwd_pair_sn, rexs_step_dx, inj/
qed-.

lemma rexs_fwd_bind_dx: ∀R. (∀L. reflexive … (R L)) →
                        ∀p,I,L1,L2,V,T. L1 ⪤*[R,ⓑ{p,I}V.T] L2 →
                        L1.ⓑ{I}V ⪤*[R,T] L2.ⓑ{I}V.
#R #HR #p #I #L1 #L2 #V #T #H elim (rexs_inv_bind … H) -H //
qed-.

lemma rexs_fwd_flat_dx: ∀R,I,L1,L2,V,T. L1 ⪤*[R,ⓕ{I}V.T] L2 → L1 ⪤*[R,T] L2.
#R #I #L1 #L2 #V #T #H elim (rexs_inv_flat … H) -H //
qed-.

(* Basic_2A1: removed theorems 2:
              TC_lpx_sn_inv_pair1 TC_lpx_sn_inv_pair2
*)
