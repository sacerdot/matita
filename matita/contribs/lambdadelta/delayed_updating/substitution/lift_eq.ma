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
(*
include "ground/relocation/tr_uni_compose.ma".
include "ground/relocation/tr_compose_compose.ma".
include "ground/relocation/tr_compose_eq.ma".
*)
include "ground/relocation/tr_pap_eq.ma".
include "ground/relocation/tr_pn_eq.ma".
include "ground/lib/stream_tls_eq.ma".

(* LIFT FOR PATH ***********************************************************)

definition lift_exteq (A): relation2 (lift_continuation A) (lift_continuation A) ≝
           λk1,k2. ∀f1,f2,p. f1 ≗ f2 → k1 f1 p = k2 f2 p.

interpretation
  "extensional equivalence (lift continuation)"
  'RingEq A k1 k2 = (lift_exteq A k1 k2).

(* Constructions with lift_exteq ********************************************)

lemma lift_eq_repl (A) (p) (k1) (k2):
      k1 ≗{A} k2 → stream_eq_repl … (λf1,f2. ↑❨k1, f1, p❩ = ↑❨k2, f2, p❩).
#A #p elim p -p [| * [ #n ] #q #IH ]
#k1 #k2 #Hk #f1 #f2 #Hf
[ <lift_empty <lift_empty /2 width=1 by/
| <lift_d_sn <lift_d_sn <(tr_pap_eq_repl … Hf)
  /3 width=3 by stream_tls_eq_repl, compose_repl_fwd_sn/
| /3 width=1 by/
| /3 width=1 by tr_push_eq_repl/
| /3 width=1 by/
| /3 width=1 by/
]
qed-.

(* Advanced constructions ***************************************************)

lemma lift_lcons_alt (A) (k) (f) (p) (l): k ≗ k →
      ↑❨λg,p2. k g (l◗p2), f, p❩ = ↑{A}❨λg,p2. k g ((l◗𝐞)●p2), f, p❩.
#A #k #f #p #l #Hk
@lift_eq_repl // #g1 #g2 #p2 #Hg @Hk -Hk // (**) (* auto fail *)
qed.

lemma lift_append_rcons_sn (A) (k) (f) (p1) (p) (l): k ≗ k →
      ↑❨λg,p2. k g (p1●l◗p2), f, p❩ = ↑{A}❨λg,p2. k g (p1◖l●p2), f, p❩.
#A #k #f #p1 #p #l #Hk
@lift_eq_repl // #g1 #g2 #p2 #Hg
<list_append_rcons_sn @Hk -Hk // (**) (* auto fail *)
qed.

(* Advanced constructions with proj_path ************************************)

lemma proj_path_proper:
      proj_path ≗ proj_path.
// qed.

lemma lift_path_eq_repl (p):
      stream_eq_repl … (λf1,f2. ↑[f1]p = ↑[f2]p).
/2 width=1 by lift_eq_repl/ qed.

lemma lift_path_append_sn (p) (f) (q):
      q●↑[f]p = ↑❨(λg,p. proj_path g (q●p)), f, p❩.
#p elim p -p // * [ #n ] #p #IH #f #q
[ <lift_d_sn <lift_d_sn
| <lift_m_sn <lift_m_sn
| <lift_L_sn <lift_L_sn
| <lift_A_sn <lift_A_sn
| <lift_S_sn <lift_S_sn
] 
>lift_lcons_alt // >lift_append_rcons_sn //
<IH <IH -IH <list_append_rcons_sn //
qed.

lemma lift_path_lcons (f) (p) (l):
      l◗↑[f]p = ↑❨(λg,p. proj_path g (l◗p)), f, p❩.
#f #p #l
>lift_lcons_alt <lift_path_append_sn //
qed.

lemma lift_path_d_sn (f) (p) (n):
      (𝗱(f＠⧣❨n❩)◗↑[⇂*[n]f]p) = ↑[f](𝗱n◗p).
// qed.

lemma lift_path_m_sn (f) (p):
      (𝗺◗↑[f]p) = ↑[f](𝗺◗p).
// qed.

lemma lift_path_L_sn (f) (p):
      (𝗟◗↑[⫯f]p) = ↑[f](𝗟◗p).
// qed.

lemma lift_path_A_sn (f) (p):
      (𝗔◗↑[f]p) = ↑[f](𝗔◗p).
// qed.

lemma lift_path_S_sn (f) (p):
      (𝗦◗↑[f]p) = ↑[f](𝗦◗p).
// qed.
(* COMMENT 

(* Advanced constructions with proj_rmap and stream_tls *********************)

lemma lift_rmap_tls_d_dx (f) (p) (m) (n):
      ⇂*[m+n]↑[p]f ≗ ⇂*[m]↑[p◖𝗱n]f.
#f #p #m #n
<lift_rmap_d_dx >nrplus_inj_dx
/2 width=1 by tr_tls_compose_uni_dx/
qed.
*)
