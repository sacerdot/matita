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
include "ground/relocation/tr_pap_pap.ma".
include "ground/relocation/tr_pap_eq.ma".
include "ground/relocation/tr_pn_eq.ma".
include "ground/lib/stream_tls_eq.ma".

(* LIFT FOR PATH ************************************************************)

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

lemma lift_path_append (p2) (p1) (f):
      (↑[f]p1)●(↑[↑[p1]f]p2) = ↑[f](p1●p2).
#p2 #p1 elim p1 -p1 //
* [ #n1 ] #p1 #IH #f
[ <lift_path_d_sn <lift_path_d_sn <IH //
| <lift_path_m_sn <lift_path_m_sn <IH //
| <lift_path_L_sn <lift_path_L_sn <IH //
| <lift_path_A_sn <lift_path_A_sn <IH //
| <lift_path_S_sn <lift_path_S_sn <IH //
]
qed.

lemma lift_path_d_dx (f) (p) (n):
      (↑[f]p)◖𝗱((↑[p]f)＠⧣❨n❩) = ↑[f](p◖𝗱n).
#f #p #n <lift_path_append //
qed.

lemma lift_path_m_dx (f) (p):
      (↑[f]p)◖𝗺 = ↑[f](p◖𝗺).
#f #p <lift_path_append //
qed.

lemma lift_path_L_dx (f) (p):
      (↑[f]p)◖𝗟 = ↑[f](p◖𝗟).
#f #p <lift_path_append //
qed.

lemma lift_path_A_dx (f) (p):
      (↑[f]p)◖𝗔 = ↑[f](p◖𝗔).
#f #p <lift_path_append //
qed.

lemma lift_path_S_dx (f) (p):
      (↑[f]p)◖𝗦 = ↑[f](p◖𝗦).
#f #p <lift_path_append //
qed.

(* Advanced inversions ******************************************************)

lemma lift_path_inv_empty (f) (p):
      (𝐞) = ↑[f]p → 𝐞 = p.
#f * // * [ #n ] #p
[ <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
qed-.

lemma lift_path_inv_d_sn (f) (p) (q) (k):
      (𝗱k◗q) = ↑[f]p →
      ∃∃r,h. k = f＠⧣❨h❩ & q = ↑[⇂*[h]f]r & 𝗱h◗r = p.
#f * [| * [ #n ] #p ] #q #k
[ <lift_path_empty
| <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
/2 width=5 by ex3_2_intro/
qed-.

lemma lift_path_inv_m_sn (f) (p) (q):
      (𝗺◗q) = ↑[f]p →
      ∃∃r. q = ↑[f]r & 𝗺◗r = p.
#f * [| * [ #n ] #p ] #q
[ <lift_path_empty
| <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_path_inv_L_sn (f) (p) (q):
      (𝗟◗q) = ↑[f]p →
      ∃∃r. q = ↑[⫯f]r & 𝗟◗r = p.
#f * [| * [ #n ] #p ] #q
[ <lift_path_empty
| <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_path_inv_A_sn (f) (p) (q):
      (𝗔◗q) = ↑[f]p →
      ∃∃r. q = ↑[f]r & 𝗔◗r = p.
#f * [| * [ #n ] #p ] #q
[ <lift_path_empty
| <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_path_inv_S_sn (f) (p) (q):
      (𝗦◗q) = ↑[f]p →
      ∃∃r. q = ↑[f]r & 𝗦◗r = p.
#f * [| * [ #n ] #p ] #q
[ <lift_path_empty
| <lift_path_d_sn
| <lift_path_m_sn
| <lift_path_L_sn
| <lift_path_A_sn
| <lift_path_S_sn
] #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_path_inv_append_dx (q2) (q1) (p) (f):
      q1●q2 = ↑[f]p →
      ∃∃p1,p2. q1 = ↑[f]p1 & q2 = ↑[↑[p1]f]p2 & p1●p2 = p.
#q2 #q1 elim q1 -q1
[| * [ #n1 ] #q1 #IH ] #p #f
[ <list_append_empty_sn #H0 destruct
  /2 width=5 by ex3_2_intro/
| <list_append_lcons_sn #H0
  elim (lift_path_inv_d_sn … H0) -H0 #r1 #m1 #_ #_ #H0 #_ -IH
    elim (eq_inv_list_empty_append … H0) -H0 #_ #H0 destruct
    elim Hq2 -Hq2 //
  | elim (lift_path_inv_m_sn … H)
  | elim (lift_path_inv_L_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗟◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (lift_path_inv_A_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗔◗p1)) //
    <structure_append <Hr1 -Hr1 //
  | elim (lift_path_inv_S_sn … H) -H #r1 #s1 #Hr1 #Hs1 #H0 destruct
    elim (IH … Hs1) -IH -Hs1 // -Hq2 #p1 #p2 #H1 #H2 #H3 destruct
    @(ex3_2_intro … (r1●𝗦◗p1)) //
    <structure_append <Hr1 -Hr1 //
  ]
]
qed-.

(* Main inversions **********************************************************)

theorem lift_path_inj (q:path) (p) (f):
        ↑[f]q = ↑[f]p → q = p.
#q elim q -q [| * [ #k ] #q #IH ] #p #f
[ <lift_path_empty #H0
  <(lift_path_inv_empty … H0) -H0 //
| <lift_path_d_sn #H0
  elim (lift_path_inv_d_sn … H0) -H0 #r #h #H0
  <(tr_pap_inj ????? H0) -h [1,3: // ] #Hr #H0 destruct
| <lift_path_m_sn #H0
  elim (lift_path_inv_m_sn … H0) -H0 #r #Hr #H0 destruct
| <lift_path_L_sn #H0
  elim (lift_path_inv_L_sn … H0) -H0 #r #Hr #H0 destruct
| <lift_path_A_sn #H0
  elim (lift_path_inv_A_sn … H0) -H0 #r #Hr #H0 destruct
| <lift_path_S_sn #H0
  elim (lift_path_inv_S_sn … H0) -H0 #r #Hr #H0 destruct
]
<(IH … Hr) -r -IH //
qed-.

(* COMMENT 

(* Advanced constructions with proj_rmap and stream_tls *********************)

lemma lift_rmap_tls_d_dx (f) (p) (m) (n):
      ⇂*[m+n]↑[p]f ≗ ⇂*[m]↑[p◖𝗱n]f.
#f #p #m #n
<lift_rmap_d_dx >nrplus_inj_dx
/2 width=1 by tr_tls_compose_uni_dx/
qed.

*)
