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

include "Domain/defs.ma".

(* SUBSETS
   - We use predicative subsets encoded as propositional functions
     according to Sambin/Valentini "Toolbox".
*)

record Subset (D:Domain): Type ≝ {
   subset       :1> D → Prop;
   ces_subset_fw:   ∀d1,d2. subset d1 → ces ? d1 d2 → subset d2;
   ces_subset_bw:   ∀d1,d2. subset d1 → ces ? d2 d1 → subset d2
}.

(* subset membership (epsilon) ********************************************)

definition sin: ∀D. Subset D → D → Prop ≝
   λD. λU:Subset D. λd. cin D d ∧ U d.

theorem sin_i: ∀D. ∀U:Subset D. ∀d. cin D d → U d → sin ? U d.
 unfold sin; intros; autobatch.
qed.

theorem sin_e1: ∀D. ∀U:Subset D. ∀d. sin ? U d → cin D d.
 intros; decompose; autobatch.
qed.

theorem sin_e2: ∀D. ∀U:Subset D. ∀d. sin ? U d → U d.
 intros; decompose; autobatch.
qed.

(* the domain built upon a subset *****************************************)

theorem ces_sin_fw: ∀D,U,d1,d2. sin D U d1 → ces ? d1 d2 → sin D U d2.
 intros; 
 apply sin_i; 
 [ autobatch
 | apply (ces_subset_fw D U d1); [ apply sin_e2; autobatch | autobatch ] (**)
 ]. 
qed.

theorem ces_sin_bw: ∀D,U,d1,d2. sin D U d1 → ces ? d2 d1 → sin D U d2.
 intros; 
 apply sin_i; 
 [ autobatch
 | apply (ces_subset_bw D U d1); [ apply sin_e2; autobatch | autobatch ] (**)
 ]. 
qed.

definition domain_of_subset: ∀D. Subset D → Domain ≝
   λD:Domain. λU.
   mk_Domain (mk_Class D (sin D U) (ces D) (ces_sin_fw ? ?) (ces_sin_bw ? ?)).

coercion domain_of_subset.

(* subset top (full subset) ***********************************************)

definition stop: ∀D. Subset D ≝
   λD. mk_Subset D (true_f ?) (true_fw ? ?) (true_bw ? ?).

coercion stop nocomposites.

(* subset bottom (empty subset) *******************************************)

definition sbot: ∀D. Subset D ≝
   λD. mk_Subset D (false_f ?) (false_fw ? ?) (false_bw ? ?).

(* subset and (binary intersection) ***************************************)

theorem ces_sand_fw:
   ∀D. ∀U1,U2:Subset D. ∀d1,d2. U1 d1 ∧ U2 d1 → ces ? d1 d2 → U1 d2 ∧ U2 d2.
 intros; decompose; apply conj;
 [ apply (ces_subset_fw D U1 d1); autobatch (**)
 | apply (ces_subset_fw D U2 d1); autobatch
 ].
qed.

theorem ces_sand_bw:
   ∀D. ∀U1,U2:Subset D. ∀d1,d2. U1 d1 ∧ U2 d1 → ces ? d2 d1 → U1 d2 ∧ U2 d2.
 intros; decompose; apply conj;
 [ apply (ces_subset_bw D U1 d1); autobatch (**)
 | apply (ces_subset_bw D U2 d1); autobatch
 ].
qed.

definition sand: ∀D. Subset D → Subset D → Subset D ≝
   λD,U1,U2. 
   mk_Subset D (λd. U1 d ∧ U2 d) (ces_sand_fw ? U1 U2) (ces_sand_bw ? U1 U2).

(* subset or (binary union) ***********************************************)

theorem ces_sor_fw:
   ∀D. ∀U1,U2:Subset D. ∀d1,d2. U1 d1 ∨ U2 d1 → ces ? d1 d2 → U1 d2 ∨ U2 d2.
 intros; decompose;
 [ apply or_introl; apply (ces_subset_fw D U1 d1); autobatch (**)
 | apply or_intror; apply (ces_subset_fw D U2 d1); autobatch
 ].
qed.

theorem ces_sor_bw:
   ∀D. ∀U1,U2:Subset D. ∀d1,d2. U1 d1 ∨ U2 d1 → ces ? d2 d1 → U1 d2 ∨ U2 d2.
 intros; decompose;
 [ apply or_introl; apply (ces_subset_bw D U1 d1); autobatch (**)
 | apply or_intror; apply (ces_subset_bw D U2 d1); autobatch
 ].
qed.

definition sor: ∀D. Subset D → Subset D → Subset D ≝
   λD,U1,U2. 
   mk_Subset D (λd. U1 d ∨ U2 d) (ces_sor_fw ? U1 U2) (ces_sor_bw ? U1 U2).

(* subset less or equal (inclusion) ***************************************)

definition sle: ∀D. Subset D → Subset D → Prop ≝
   λD. λU1,U2:Subset D. \iforall d. U1 d → U2 d. 

(* subset overlap *********************************************************)

definition sover: ∀D. Subset D → Subset D → Prop ≝
   λD. λU1,U2:Subset D. \iexists d. U1 d ∧ U2 d. 

(* the class of the subsets of a domain ***********************************)

definition power: Domain → Class ≝
   λD. mk_Class (Subset D) (true_f ?) (sle ?) (true_fw ? ?) (true_bw ? ?). 
