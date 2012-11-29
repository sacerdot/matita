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

include "redex_pointer.ma".
include "multiplicity.ma".

(* LABELLED SEQUENTIAL REDUCTION (ONE STEP) *********************************)

(* Note: the application "(A B)" is represented by "@B.A" following:
         F. Kamareddine and R.P. Nederpelt: "A useful λ-notation".
         Theoretical Computer Science 155(1), Elsevier (1996), pp. 85-109.
*)
inductive lsred: rpointer → relation term ≝
| lsred_beta   : ∀A,D. lsred (◊) (@D.𝛌.A) ([⬐D]A)
| lsred_abst   : ∀p,A,C. lsred p A C → lsred p (𝛌.A) (𝛌.C) 
| lsred_appl_sn: ∀p,B,D,A. lsred p B D → lsred (true::p) (@B.A) (@D.A)
| lsred_appl_dx: ∀p,B,A,C. lsred p A C → lsred (false::p) (@B.A) (@B.C)
.

interpretation "labelled sequential reduction"
    'LablSeqRed M p N = (lsred p M N).

(* Note: we do not use → since it is reserved by CIC *)
notation "hvbox( M break ⇀ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'LablSeqRed $M $p $N }.

theorem lsred_fwd_mult: ∀p,M,N. M ⇀[p] N → #{N} < #{M} * #{M}.
#p #M #N #H elim H -p -M -N
[ #A #D @(le_to_lt_to_lt … (#{A}*#{D})) //
  normalize /3 width=1 by lt_minus_to_plus_r, lt_times/ (**) (* auto: too slow without trace *) 
| //
| #p #B #D #A #_ #IHBD
  @(lt_to_le_to_lt … (#{B}*#{B}+#{A})) [ /2 width=1/ ] -D -p
| #p #B #A #C #_ #IHAC
  @(lt_to_le_to_lt … (#{B}+#{A}*#{A})) [ /2 width=1/ ] -C -p
]
@(transitive_le … (#{B}*#{B}+#{A}*#{A})) [ /2 width=1/ ]
>distributive_times_plus normalize /2 width=1/
qed-.
