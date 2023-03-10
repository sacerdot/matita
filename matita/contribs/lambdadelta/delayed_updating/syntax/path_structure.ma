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

rec definition structure (p) on p ā
match p with
[ list_empty     ā š
| list_lcons l q ā
   match l with
   [ label_d k ā structure q
   | label_m   ā structure q
   | label_L   ā (structure q)āš
   | label_A   ā (structure q)āš
   | label_S   ā (structure q)āš¦
   ]
].

interpretation
  "structure (path)"
  'CircledTimes p = (structure p).

(* Basic constructions ******************************************************)

lemma structure_empty:
      š = āš.
// qed.

lemma structure_d_dx (p) (k):
      āp = ā(pāš±k).
// qed.

lemma structure_m_dx (p):
      āp = ā(pāšŗ).
// qed.

lemma structure_L_dx (p):
      (āp)āš = ā(pāš).
// qed.

lemma structure_A_dx (p):
      (āp)āš = ā(pāš).
// qed.

lemma structure_S_dx (p):
      (āp)āš¦ = ā(pāš¦).
// qed.

(* Main constructions *******************************************************)

theorem structure_idem (p):
        āp = āāp.
#p elim p -p //
* [ #k ] #p #IH //
qed.

theorem structure_append (p) (q):
        āpāāq = ā(pāq).
#p #q elim q -q //
* [ #k ] #q #IH //
<list_append_lcons_sn //
qed.

(* Constructions with path_lcons ********************************************)

lemma structure_d_sn (p) (k):
      āp = ā(š±kāp).
#p #k <structure_append //
qed.

lemma structure_m_sn (p):
      āp = ā(šŗāp).
#p <structure_append //
qed.

lemma structure_L_sn (p):
      (šāāp) = ā(šāp).
#p <structure_append //
qed.

lemma structure_A_sn (p):
      (šāāp) = ā(šāp).
#p <structure_append //
qed.

lemma structure_S_sn (p):
      (š¦āāp) = ā(š¦āp).
#p <structure_append //
qed.

(* Basic inversions *********************************************************)

lemma eq_inv_d_dx_structure (h) (q) (p):
      qāš±h = āp ā ā„.
#h #q #p elim p -p [| * [ #k ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0 /2 width=1 by/
| <structure_m_dx #H0 /2 width=1 by/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_m_dx_structure (q) (p):
      qāšŗ = āp ā ā„.
#q #p elim p -p [| * [ #k ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0 /2 width=1 by/
| <structure_m_dx #H0 /2 width=1 by/
| <structure_L_dx #H0 destruct
| <structure_A_dx #H0 destruct
| <structure_S_dx #H0 destruct
]
qed-.

lemma eq_inv_L_dx_structure (q) (p):
      qāš = āp ā
      āār1,r2. q = ār1 & š = ār2 & r1āšār2 = p.
#q #p elim p -p [| * [ #k ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
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
      qāš = āp ā
      āār1,r2. q = ār1 & š = ār2 & r1āšār2 = p.
#q #p elim p -p [| * [ #k ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
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
      qāš¦ = āp ā
      āār1,r2. q = ār1 & š = ār2 & r1āš¦ār2 = p.
#q #p elim p -p [| * [ #k ] #p #IH ]
[ <structure_empty #H0 destruct
| <structure_d_dx #H0
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
        pāq = ār ā
        āār1,r2.p = ār1 & q = ār2 & r1ār2 = r.
#p #q elim q -q [| * [ #k ] #q #IH ] #r
[ <list_append_empty_sn #H0 destruct
  /2 width=5 by ex3_2_intro/
| #H0 elim (eq_inv_d_dx_structure ā¦ H0)
| #H0 elim (eq_inv_m_dx_structure ā¦ H0)
| #H0 elim (eq_inv_L_dx_structure ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH ā¦ Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <structure_append <structure_L_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_A_dx_structure ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH ā¦ Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āšār2)) //
  <structure_append <structure_A_sn <Hr2 -Hr2 //
| #H0 elim (eq_inv_S_dx_structure ā¦ H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  elim (IH ā¦ Hr1) -IH -Hr1 #s1 #s2 #H1 #H2 #H3 destruct
  @(ex3_2_intro ā¦ s1 (s2āš¦ār2)) //
  <structure_append <structure_S_sn <Hr2 -Hr2 //
]
qed-.

(* Inversions with path_lcons ***********************************************)

lemma eq_inv_d_sn_structure (h) (q) (p):
      (š±hāq) = āp ā ā„.
#h #q #p >list_cons_comm #H0
elim (eq_inv_append_structure ā¦ H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_d_dx_structure ā¦ H0)
qed-.

lemma eq_inv_m_sn_structure (q) (p):
      (šŗ āq) = āp ā ā„.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure ā¦ H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_m_dx_structure ā¦ H0)
qed-.

lemma eq_inv_L_sn_structure (q) (p):
      (šāq) = āp ā
      āār1,r2. š = ār1 & q = ār2 & r1āšār2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure ā¦ H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_L_dx_structure ā¦ H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro ā¦ s1 (s2ār2)) // -s1
<structure_append <H2 -s2 //
qed-.

lemma eq_inv_A_sn_structure (q) (p):
      (šāq) = āp ā
      āār1,r2. š = ār1 & q = ār2 & r1āšār2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure ā¦ H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_A_dx_structure ā¦ H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro ā¦ s1 (s2ār2)) // -s1
<structure_append <H2 -s2 //
qed-.

lemma eq_inv_S_sn_structure (q) (p):
      (š¦āq) = āp ā
      āār1,r2. š = ār1 & q = ār2 & r1āš¦ār2 = p.
#q #p >list_cons_comm #H0
elim (eq_inv_append_structure ā¦ H0) -H0 #r1 #r2
<list_cons_comm #H0 #H1 #H2 destruct
elim (eq_inv_S_dx_structure ā¦ H0) -H0 #s1 #s2 #H1 #H2 #H3 destruct
@(ex3_2_intro ā¦ s1 (s2ār2)) // -s1
<structure_append <H2 -s2 //
qed-.
