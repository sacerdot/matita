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

include "static_2/syntax/lveq_length.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

(* Main inversion lemmas ****************************************************)

theorem lveq_inv_bind: โK1,K2. K1 โโง*[๐,๐] K2 โ
                       โI1,I2,m1,m2. K1.โ[I1] โโง*[m1,m2] K2.โ[I2] โ
                       โงโง ๐ = m1 & ๐ = m2.
#K1 #K2 #HK #I1 #I2 #m1 #m2 #H
lapply (lveq_fwd_length_eq โฆ HK) -HK #HK
elim (lveq_inj_length โฆ H) -H /3 width=1 by conj/
qed-.

theorem lveq_inj: โL1,L2,n1,n2. L1 โโง*[n1,n2] L2 โ
                  โm1,m2. L1 โโง*[m1,m2] L2 โ
                  โงโง n1 = m1 & n2 = m2.
#L1 #L2 #n1 #n2 #Hn #m1 #m2 #Hm
elim (lveq_fwd_length โฆ Hn) -Hn #H1 #H2 destruct
elim (lveq_fwd_length โฆ Hm) -Hm #H1 #H2 destruct
/2 width=1 by conj/
qed-.

theorem lveq_inj_void_sn_ge: โK1,K2. |K2| โค |K1| โ
                             โn1,n2. K1 โโง*[n1,n2] K2 โ
                             โm1,m2. K1.โง โโง*[m1,m2] K2 โ
                             โงโง โn1 = m1 & ๐ = m2 & ๐ = n2.
#L1 #L2 #HL #n1 #n2 #Hn #m1 #m2 #Hm
elim (lveq_fwd_length โฆ Hn) -Hn #H1 #H2 destruct
elim (lveq_fwd_length โฆ Hm) -Hm #H1 #H2 destruct
>length_bind <nminus_succ_dx
<(nminus_succ_sn โฆ HL) <(nle_inv_eq_zero_minus โฆ HL)
/2 width=1 by and3_intro/
qed-.

theorem lveq_inj_void_dx_le: โK1,K2. |K1| โค |K2| โ
                             โn1,n2. K1 โโง*[n1,n2] K2 โ
                             โm1,m2. K1 โโง*[m1,m2] K2.โง โ
                             โงโง โn2 = m2 & ๐ = m1 & ๐ = n1.
/3 width=5 by lveq_inj_void_sn_ge, lveq_sym/ qed-. (* auto: 2x lveq_sym *)
