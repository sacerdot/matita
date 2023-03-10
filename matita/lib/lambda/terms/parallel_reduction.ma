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

include "lambda/terms/size.ma".
include "lambda/terms/sequential_reduction.ma".

include "lambda/notation/relations/parred_2.ma".

include "lambda/xoa/ex_4_3.ma".

(* PARALLEL REDUCTION (SINGLE STEP) *****************************************)

(* Note: the application "(A B)" is represented by "@B.A"
         as for sequential reduction
*)
inductive pred: relation term โ
| pred_vref: โi. pred (#i) (#i)
| pred_abst: โA1,A2. pred A1 A2 โ pred (๐.A1) (๐.A2) 
| pred_appl: โB1,B2,A1,A2. pred B1 B2 โ pred A1 A2 โ pred (@B1.A1) (@B2.A2)
| pred_beta: โB1,B2,A1,A2. pred B1 B2 โ pred A1 A2 โ pred (@B1.๐.A1) ([โB2]A2)
.

interpretation "parallel reduction"
    'ParRed M N = (pred M N).

lemma pred_refl: reflexive โฆ pred.
#M elim M -M // /2 width=1/
qed.

lemma pred_inv_vref: โM,N. M โค N โ โi. #i = M โ #i = N.
#M #N * -M -N //
[ #A1 #A2 #_ #i #H destruct
| #B1 #B2 #A1 #A2 #_ #_ #i #H destruct
| #B1 #B2 #A1 #A2 #_ #_ #i #H destruct
]
qed-.

lemma pred_inv_abst: โM,N. M โค N โ โA. ๐.A = M โ
                     โโC. A โค C & ๐.C = N.
#M #N * -M -N
[ #i #A0 #H destruct
| #A1 #A2 #HA12 #A0 #H destruct /2 width=3/
| #B1 #B2 #A1 #A2 #_ #_ #A0 #H destruct
| #B1 #B2 #A1 #A2 #_ #_ #A0 #H destruct
]
qed-.

lemma pred_inv_appl: โM,N. M โค N โ โB,A. @B.A = M โ
                     (โโD,C. B โค D & A โค C & @D.C = N) โจ
                     โโA0,D,C0. B โค D & A0 โค C0 & ๐.A0 = A & [โD]C0 = N.
#M #N * -M -N
[ #i #B0 #A0 #H destruct
| #A1 #A2 #_ #B0 #A0 #H destruct
| #B1 #B2 #A1 #A2 #HB12 #HA12 #B0 #A0 #H destruct /3 width=5/
| #B1 #B2 #A1 #A2 #HB12 #HA12 #B0 #A0 #H destruct /3 width=7/
]
qed-.

lemma pred_lift: liftable pred.
#h #M1 #M2 #H elim H -M1 -M2 normalize // /2 width=1/
#B1 #B2 #A1 #A2 #_ #_ #IHB12 #IHC12 #d <dsubst_lift_le // /2 width=1/
qed.

lemma pred_inv_lift: deliftable_sn pred.
#h #N1 #N2 #H elim H -N1 -N2 /2 width=3/
[ #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst โฆ H) -H #A1 #HAC1 #H
  elim (IHC12 โฆ HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro โฆ (๐.A2)) // /2 width=1/
| #D1 #D2 #C1 #C2 #_ #_ #IHD12 #IHC12 #d #M1 #H
  elim (lift_inv_appl โฆ H) -H #B1 #A1 #HBD1 #HAC1 #H
  elim (IHD12 โฆ HBD1) -D1 #B2 #HB12 #HBD2
  elim (IHC12 โฆ HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro โฆ (@B2.A2)) // /2 width=1/
| #D1 #D2 #C1 #C2 #_ #_ #IHD12 #IHC12 #d #M1 #H
  elim (lift_inv_appl โฆ H) -H #B1 #M #HBD1 #HM #H1
  elim (lift_inv_abst โฆ HM) -HM #A1 #HAC1 #H
  elim (IHD12 โฆ HBD1) -D1 #B2 #HB12 #HBD2
  elim (IHC12 โฆ HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro โฆ ([โB2]A2)) /2 width=1/
]
qed-.

lemma pred_dsubst: dsubstable pred.
#N1 #N2 #HN12 #M1 #M2 #H elim H -M1 -M2
[ #i #d elim (lt_or_eq_or_gt i d) #Hid
  [ >(dsubst_vref_lt โฆ Hid) >(dsubst_vref_lt โฆ Hid) //
  | destruct >dsubst_vref_eq >dsubst_vref_eq /2 width=1/
  | >(dsubst_vref_gt โฆ Hid) >(dsubst_vref_gt โฆ Hid) //
  ]
| normalize /2 width=1/
| normalize /2 width=1/
| normalize #B1 #B2 #A1 #A2 #_ #_ #IHB12 #IHC12 #d
  >dsubst_dsubst_ge // /2 width=1/
]
qed.

lemma pred_conf1_vref: โi. pw_confluent โฆ pred (#i).
#i #M1 #H1 #M2 #H2
<(pred_inv_vref โฆ H1) -H1 [3: // |2: skip ] (**) (* simplify line *)
<(pred_inv_vref โฆ H2) -H2 [3: // |2: skip ] (**) (* simplify line *)
/2 width=3/
qed-.

lemma pred_conf1_abst: โA. pw_confluent โฆ pred A โ pw_confluent โฆ pred (๐.A).
#A #IH #M1 #H1 #M2 #H2
elim (pred_inv_abst โฆ H1 โฆ) -H1 [3: // |2: skip ] #A1 #HA1 #H destruct (**) (* simplify line *)
elim (pred_inv_abst โฆ H2 โฆ) -H2 [3: // |2: skip ] #A2 #HA2 #H destruct (**) (* simplify line *)
elim (IH โฆ HA1 โฆ HA2) -A /3 width=3/
qed-.

lemma pred_conf1_appl_beta: โB,B1,B2,C,C2,M1.
                            (โM0. |M0| < |B|+|๐.C|+1 โ  pw_confluent ? pred M0) โ (**) (* ? needed in place of โฆ *)
                            B โค B1 โ B โค B2 โ ๐.C โค M1 โ C โค C2 โ
                            โโM. @B1.M1 โค M & [โB2]C2 โค M.
#B #B1 #B2 #C #C2 #M1 #IH #HB1 #HB2 #H1 #HC2
elim (pred_inv_abst โฆ H1 โฆ) -H1 [3: // |2: skip ] #C1 #HC1 #H destruct (**) (* simplify line *)
elim (IH B โฆ HB1 โฆ HB2) -HB1 -HB2 //
elim (IH C โฆ HC1 โฆ HC2) normalize // -B -C /3 width=5/
qed-.

theorem pred_conf: confluent โฆ pred.
#M @(f_ind โฆ size โฆ M) -M #n #IH * normalize
[ /2 width=3 by pred_conf1_vref/
| /3 width=4 by pred_conf1_abst/
| #B #A #H #M1 #H1 #M2 #H2 destruct
  elim (pred_inv_appl โฆ H1 โฆ) -H1 [5: // |2,3: skip ] * (**) (* simplify line *)
  elim (pred_inv_appl โฆ H2 โฆ) -H2 [5,10: // |2,3,7,8: skip ] * (**) (* simplify line *) 
  [ #B2 #A2 #HB2 #HA2 #H2 #B1 #A1 #HB1 #HA1 #H1 destruct
    elim (IH A โฆ HA1 โฆ HA2) -HA1 -HA2 //
    elim (IH B โฆ HB1 โฆ HB2) // -A -B /3 width=5/
  | #C #B2 #C2 #HB2 #HC2 #H2 #HM2 #B1 #N #HB1 #H #HM1 destruct
    @(pred_conf1_appl_beta โฆ IH) // (**) (* /2 width=7 by pred_conf1_appl_beta/ does not work *)
  | #B2 #N #B2 #H #HM2 #C #B1 #C1 #HB1 #HC1 #H1 #HM1 destruct
    @ex2_commute @(pred_conf1_appl_beta โฆ IH) //
  | #C #B2 #C2 #HB2 #HC2 #H2 #HM2 #C0 #B1 #C1 #HB1 #HC1 #H1 #HM1 destruct
    elim (IH B โฆ HB1 โฆ HB2) -HB1 -HB2 //
    elim (IH C โฆ HC1 โฆ HC2) normalize // -B -C /3 width=5/
  ]
]
qed-.

lemma sred_pred: โM,N. M โฆ N โ M โค N.
#M #N #H elim H -M -N /2 width=1/
qed.
