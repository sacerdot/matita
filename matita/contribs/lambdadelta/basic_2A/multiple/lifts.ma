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

include "ground/relocation/mr2_at.ma".
include "ground/relocation/mr2_plus.ma".
include "basic_2A/notation/relations/rliftstar_3.ma".
include "basic_2A/substitution/lift.ma".

(* GENERIC TERM RELOCATION **************************************************)

inductive lifts: mr2 â relation term â
| lifts_nil : âT. lifts (ð) T T
| lifts_cons: âT1,T,T2,cs,l,m.
              â¬[l,m] T1 â¡ T â lifts cs T T2 â lifts (â¨l, mâ©â cs) T1 T2
.

interpretation "generic relocation (term)"
   'RLiftStar cs T1 T2 = (lifts cs T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lifts_inv_nil_aux: âT1,T2,cs. â¬*[cs] T1 â¡ T2 â cs = ð â T1 = T2.
#T1 #T2 #cs * -T1 -T2 -cs //
#T1 #T #T2 #l #m #cs #_ #_ #H destruct
qed-.

lemma lifts_inv_nil: âT1,T2. â¬*[ð] T1 â¡ T2 â T1 = T2.
/2 width=3 by lifts_inv_nil_aux/ qed-.

fact lifts_inv_cons_aux: âT1,T2,cs. â¬*[cs] T1 â¡ T2 â
                         âl,m,tl. cs = â¨l, mâ©â tl â
                         ââT. â¬[l, m] T1 â¡ T & â¬*[tl] T â¡ T2.
#T1 #T2 #cs * -T1 -T2 -cs
[ #T #l #m #tl #H destruct
| #T1 #T #T2 #cs #l #m #HT1 #HT2 #l0 #m0 #tl #H destruct
  /2 width=3 by ex2_intro/
qed-.

lemma lifts_inv_cons: âT1,T2,l,m,cs. â¬*[â¨l, mâ©â cs] T1 â¡ T2 â
                      ââT. â¬[l, m] T1 â¡ T & â¬*[cs] T â¡ T2.
/2 width=3 by lifts_inv_cons_aux/ qed-.

lemma lifts_inv_sort1: âT2,k,cs. â¬*[cs] âk â¡ T2 â T2 = âk.
#T2 #k #cs elim cs -cs
[ #H <(lifts_inv_nil â¦ H) -H //
| #l #m #cs #IH #H
  elim (lifts_inv_cons â¦ H) -H #X #H
  >(lift_inv_sort1 â¦ H) -H /2 width=1 by/
]
qed-.

lemma lifts_inv_lref1: âT2,cs,i1. â¬*[cs] #i1 â¡ T2 â
                       ââi2. @âªi1, csâ« â i2 & T2 = #i2.
#T2 #cs elim cs -cs
[ #i1 #H <(lifts_inv_nil â¦ H) -H /2 width=3 by at_nil, ex2_intro/
| #l #m #cs #IH #i1 #H
  elim (lifts_inv_cons â¦ H) -H #X #H1 #H2
  elim (lift_inv_lref1 â¦ H1) -H1 * #Hli1 #H destruct
  elim (IH â¦ H2) -IH -H2 /3 width=3 by at_lt, at_ge, ex2_intro/
]
qed-.

lemma lifts_inv_gref1: âT2,p,cs. â¬*[cs] Â§p â¡ T2 â T2 = Â§p.
#T2 #p #cs elim cs -cs
[ #H <(lifts_inv_nil â¦ H) -H //
| #l #m #cs #IH #H
  elim (lifts_inv_cons â¦ H) -H #X #H
  >(lift_inv_gref1 â¦ H) -H /2 width=1 by/
]
qed-.

lemma lifts_inv_bind1: âa,I,T2,cs,V1,U1. â¬*[cs] â{a,I} V1. U1 â¡ T2 â
                       ââV2,U2. â¬*[cs] V1 â¡ V2 & â¬*[cs + 1] U1 â¡ U2 &
                                T2 = â{a,I} V2. U2.
#a #I #T2 #cs elim cs -cs
[ #V1 #U1 #H
  <(lifts_inv_nil â¦ H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #l #m #cs #IHcs #V1 #U1 #H
  elim (lifts_inv_cons â¦ H) -H #X #H #HT2
  elim (lift_inv_bind1 â¦ H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHcs â¦ HT2) -IHcs -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

lemma lifts_inv_flat1: âI,T2,cs,V1,U1. â¬*[cs] â{I} V1. U1 â¡ T2 â
                       ââV2,U2. â¬*[cs] V1 â¡ V2 & â¬*[cs] U1 â¡ U2 &
                                T2 = â{I} V2. U2.
#I #T2 #cs elim cs -cs
[ #V1 #U1 #H
  <(lifts_inv_nil â¦ H) -H /2 width=5 by ex3_2_intro, lifts_nil/
| #l #m #cs #IHcs #V1 #U1 #H
  elim (lifts_inv_cons â¦ H) -H #X #H #HT2
  elim (lift_inv_flat1 â¦ H) -H #V #U #HV1 #HU1 #H destruct
  elim (IHcs â¦ HT2) -IHcs -HT2 #V2 #U2 #HV2 #HU2 #H destruct
  /3 width=5 by ex3_2_intro, lifts_cons/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma lifts_simple_dx: âT1,T2,cs. â¬*[cs] T1 â¡ T2 â ðâ¦T1â¦ â ðâ¦T2â¦.
#T1 #T2 #cs #H elim H -T1 -T2 -cs /3 width=5 by lift_simple_dx/
qed-.

lemma lifts_simple_sn: âT1,T2,cs. â¬*[cs] T1 â¡ T2 â ðâ¦T2â¦ â ðâ¦T1â¦.
#T1 #T2 #cs #H elim H -T1 -T2 -cs /3 width=5 by lift_simple_sn/
qed-.

(* Basic properties *********************************************************)

lemma lifts_bind: âa,I,T2,V1,V2,cs. â¬*[cs] V1 â¡ V2 â
                  âT1. â¬*[cs + 1] T1 â¡ T2 â
                  â¬*[cs] â{a,I} V1. T1 â¡ â{a,I} V2. T2.
#a #I #T2 #V1 #V2 #cs #H elim H -V1 -V2 -cs
[ #V #T1 #H >(lifts_inv_nil â¦ H) -H //
| #V1 #V #V2 #cs #l #m #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons â¦ H) -H /3 width=3 by lift_bind, lifts_cons/
]
qed.

lemma lifts_flat: âI,T2,V1,V2,cs. â¬*[cs] V1 â¡ V2 â
                  âT1. â¬*[cs] T1 â¡ T2 â
                  â¬*[cs] â{I} V1. T1 â¡ â{I} V2. T2.
#I #T2 #V1 #V2 #cs #H elim H -V1 -V2 -cs
[ #V #T1 #H >(lifts_inv_nil â¦ H) -H //
| #V1 #V #V2 #cs #l #m #HV1 #_ #IHV #T1 #H
  elim (lifts_inv_cons â¦ H) -H /3 width=3 by lift_flat, lifts_cons/
]
qed.

lemma lifts_total: âcs,T1. âT2. â¬*[cs] T1 â¡ T2.
#cs elim cs -cs /2 width=2 by lifts_nil, ex_intro/
#l #m #cs #IH #T1 elim (lift_total T1 l m)
#T #HT1 elim (IH T) -IH /3 width=4 by lifts_cons, ex_intro/
qed.
