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

include "delayed_updating/substitution/lift.ma".
include "ground/notation/relations/ringeq_3.ma".

(* LIFT FOR PATH ***********************************************************)

definition lift_exteq (A): relation2 (lift_continuation A) (lift_continuation A) ≝
           λk1,k2. ∀f,p. k1 f p = k2 f p.

interpretation
  "extensional equivalence (lift continuation)"
  'RingEq A k1 k2 = (lift_exteq A k1 k2).

(* Constructions with lift_exteq ********************************************)

lemma lift_eq_repl_sn (A) (p) (k1) (k2) (f):
      k1 ≗{A} k2 → ↑❨k1, f, p❩ = ↑❨k2, f, p❩.
#A #p @(path_ind_lift … p) -p [| #n | #n #l0 #q ]
[ #k1 #k2 #f #Hk <lift_empty <lift_empty //
|*: #IH #k1 #k2 #f #Hk /2 width=1 by/
]
qed-.

(* Advanced constructions ***************************************************)

lemma lift_lcons_alt (A) (k) (f) (p) (l):
      ↑❨λg,p2. k g (l◗p2), f, p❩ = ↑{A}❨λg,p2. k g ((l◗𝐞)●p2), f, p❩.
#A #k #f #p #l
@lift_eq_repl_sn #p2 #g // (**) (* auto fails with typechecker failure *)
qed.

lemma lift_append_rcons_sn (A) (k) (f) (p1) (p) (l):
      ↑❨λg,p2. k g (p1●l◗p2), f, p❩ = ↑{A}❨λg,p2. k g (p1◖l●p2), f, p❩.
#A #k #f #p1 #p #l
@lift_eq_repl_sn #p2 #g
<list_append_rcons_sn //
qed.

(* Advanced constructions with proj_path ************************************)

lemma lift_path_append_sn (p) (f) (q):
      q●↑[f]p = ↑❨(λg,p. proj_path g (q●p)), f, p❩.
#p @(path_ind_lift … p) -p // [ #n #l #p |*: #p ] #IH #f #q
[ <lift_d_lcons_sn <lift_d_lcons_sn <IH -IH //
| <lift_L_sn <lift_L_sn >lift_lcons_alt >lift_append_rcons_sn
  <IH <IH -IH <list_append_rcons_sn //
| <lift_A_sn <lift_A_sn >lift_lcons_alt >lift_append_rcons_sn
  <IH <IH -IH <list_append_rcons_sn //
| <lift_S_sn <lift_S_sn >lift_lcons_alt >lift_append_rcons_sn
  <IH <IH -IH <list_append_rcons_sn //
]
qed.

lemma lift_path_lcons (f) (p) (l):
      l◗↑[f]p = ↑❨(λg,p. proj_path g (l◗p)), f, p❩.
#f #p #l
>lift_lcons_alt <lift_path_append_sn //
qed.

lemma lift_path_L_sn (f) (p):
      (𝗟◗↑[⫯f]p) = ↑[f](𝗟◗p).
// qed.

lemma lift_path_A_sn (f) (p):
      (𝗔◗↑[f]p) = ↑[f](𝗔◗p).
// qed.

lemma lift_path_S_sn (f) (p):
      (𝗦◗↑[f]p) = ↑[f](𝗦◗p).
// qed.
