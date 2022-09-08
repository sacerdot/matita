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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/circled_times_1.ma".
include "ground/xoa/ex_3_2.ma".

(* STRUCTURE FOR PATH *******************************************************)

rec definition structure (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
   match l with
   [ label_d k    ⇒ structure q
   | label_d2 k d ⇒ structure q
   | label_m      ⇒ structure q
   | label_L      ⇒ (structure q)◖𝗟
   | label_A      ⇒ (structure q)◖𝗔
   | label_S      ⇒ (structure q)◖𝗦
   ]
].

interpretation
  "structure (path)"
  'CircledTimes p = (structure p).

(* Basic constructions ******************************************************)

lemma structure_empty:
      𝐞 = ⊗𝐞.
// qed.

lemma structure_d_dx (p) (k):
      ⊗p = ⊗(p◖𝗱k).
// qed.

lemma structure_d2_dx (p) (k) (d):
      ⊗p = ⊗(p◖𝗱❨k,d❩).
// qed.

lemma structure_m_dx (p):
      ⊗p = ⊗(p◖𝗺).
// qed.

lemma structure_L_dx (p):
      (⊗p)◖𝗟 = ⊗(p◖𝗟).
// qed.

lemma structure_A_dx (p):
      (⊗p)◖𝗔 = ⊗(p◖𝗔).
// qed.

lemma structure_S_dx (p):
      (⊗p)◖𝗦 = ⊗(p◖𝗦).
// qed.

(* Main constructions *******************************************************)

theorem structure_idem (p):
        ⊗p = ⊗⊗p.
#p elim p -p //
* [ #k | #k #d ] #p #IH //
qed.

theorem structure_append (p) (q):
        ⊗p●⊗q = ⊗(p●q).
#p #q elim q -q //
* [ #k | #k #d ] #q #IH //
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma structure_d_sn (p) (k):
      ⊗p = ⊗(𝗱k◗p).
#p #k <structure_append //
qed.

lemma structure_d2_sn (p) (k) (d):
      ⊗p = ⊗(𝗱❨k,d❩◗p).
#p #k #d <structure_append //
qed.

lemma structure_m_sn (p):
      ⊗p = ⊗(𝗺◗p).
#p <structure_append //
qed.

lemma structure_L_sn (p):
      (𝗟◗⊗p) = ⊗(𝗟◗p).
#p <structure_append //
qed.

lemma structure_A_sn (p):
      (𝗔◗⊗p) = ⊗(𝗔◗p).
#p <structure_append //
qed.

lemma structure_S_sn (p):
      (𝗦◗⊗p) = ⊗(𝗦◗p).
#p <structure_append //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_d_dx_structure (h) (q) (p):
      q◖𝗱h = ⊗p → ⊥.
#h #q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0 /2 width=1 by/
| <structure_d2_dx #H0 /2 width=1 by/
| <structure_m_dx #H0 /2 width=1 by/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_d2_dx_structure (d) (h) (q) (p):
      q◖𝗱❨h,d❩ = ⊗p → ⊥.
#d #h #q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0 /2 width=1 by/
| <structure_d2_dx #H0 /2 width=1 by/
| <structure_m_dx #H0 /2 width=1 by/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_m_dx_structure (q) (p):
      q◖𝗺 = ⊗p → ⊥.
#q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0 /2 width=1 by/
| <structure_d2_dx #H0 /2 width=1 by/
| <structure_m_dx #H0 /2 width=1 by/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_L_dx_structure (q) (p):
      q◖𝗟 = ⊗p →
      ∃∃r1,r2. q = ⊗r1 & 𝐞 = ⊗r2 & r1●𝗟◗r2 = p.
#q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_d2_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_m_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_L_dx #H0 destruct -IH
  /2 width=5 by ex3_2_intro/
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_A_dx_structure (q) (p):
      q◖𝗔 = ⊗p →
      ∃∃r1,r2. q = ⊗r1 & 𝐞 = ⊗r2 & r1●𝗔◗r2 = p.
#q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_d2_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_m_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct -IH
  /2 width=5 by ex3_2_intro/
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_S_dx_structure (q) (p):
      q◖𝗦 = ⊗p →
      ∃∃r1,r2. q = ⊗r1 & 𝐞 = ⊗r2 & r1●𝗦◗r2 = p.
#q #p elim p -p [| * [ #k | #k #d ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_d2_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_m_dx #H0
  elim IH -IH // -H0 #r1 #r2 #H1 #H0 #H2 destruct
  /2 width=5 by ex3_2_intro/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct -IH
  /2 width=5 by ex3_2_intro/
]
qed-.

(* Main inversions **********************************************************)

theorem eq_inv_append_structure (p) (q) (r):
        p●q = ⊗r →
        ∃∃r1,r2.p = ⊗r1 & q = ⊗r2 & r1●r2 = r.
#p #q elim q -q [| * [ #k | #k #d ] #q #IH ] #r
[ <list_append_empty_sn #H0 destruct
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_d_dx_structure … H0)
| #H0 elim (eq_inv_d2_dx_structure … H0)
| #H0 elim (eq_inv_m_dx_structure … H0)
| #H0 elim (eq_inv_L_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH … Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro … s1 (s2●𝗟◗r2)) //
  <structure_append <structure_L_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_A_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH … Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro … s1 (s2●𝗔◗r2)) //
  <structure_append <structure_A_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_S_dx_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH … Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro … s1 (s2●𝗦◗r2)) //
  <structure_append <structure_S_sn <Hr2 -Hr2 //
]
qed-.

(* Inversions with path_lcons ***********************************************)

lemma eq_inv_d_sn_structure (h) (q) (p):
      (𝗱h◗q) = ⊗p → ⊥.
#h #q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_d_dx_structure … H0)
qed-.

lemma eq_inv_d2_sn_structure (d) (h) (q) (p):
      (𝗱❨h,d❩◗q) = ⊗p → ⊥.
#d #h #q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_d2_dx_structure … H0)
qed-.

lemma eq_inv_m_sn_structure (q) (p):
      (𝗺 ◗q) = ⊗p → ⊥.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_m_dx_structure … H0)
qed-.

lemma eq_inv_L_sn_structure (q) (p):
      (𝗟◗q) = ⊗p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ⊗r2 & r1●𝗟◗r2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_L_dx_structure … H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro … s1 (s2●r2)) // -s1
<structure_append <H2 -s2 //
qed-.

lemma eq_inv_A_sn_structure (q) (p):
      (𝗔◗q) = ⊗p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ⊗r2 & r1●𝗔◗r2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_A_dx_structure … H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro … s1 (s2●r2)) // -s1
<structure_append <H2 -s2 //
qed-.

lemma eq_inv_S_sn_structure (q) (p):
      (𝗦◗q) = ⊗p →
      ∃∃r1,r2. 𝐞 = ⊗r1 & q = ⊗r2 & r1●𝗦◗r2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure … H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_S_dx_structure … H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro … s1 (s2●r2)) // -s1
<structure_append <H2 -s2 //
qed-.
