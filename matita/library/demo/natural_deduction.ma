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

include "didactic/support/natural_deduction.ma".

lemma RAA_to_EM : A ∨ ¬ A.

  apply rule (prove (A ∨ ¬ A));
  
  apply rule (RAA [H] ⊥);
  apply rule (¬#e (¬A) A);
    [ apply rule (¬#i [H1] ⊥);
      apply rule (¬#e (¬(A∨¬A)) (A∨¬A));
      [ apply rule (discharge [H]);
      | apply rule (∨#i_l A);
        apply rule (discharge [H1]);
      ]
    | apply rule (RAA [H2] ⊥);
      apply rule (¬#e (¬(A∨¬A)) (A∨¬A));
      [ apply rule (discharge [H]);
      | apply rule (∨#i_r (¬A));
        apply rule (discharge [H2]);
      ]
    ]
qed.

lemma RA_to_EM1 : A ∨ ¬ A.

  apply rule (prove (A ∨ ¬ A));
  
  apply rule (RAA [H] ⊥);
  apply rule (¬#e (¬¬A) (¬A));
    [ apply rule (¬#i [H2] ⊥);
      apply rule (¬#e (¬(A∨¬A)) (A∨¬A));
      [ apply rule (discharge [H]);
      | apply rule (∨#i_r (¬A));
        apply rule (discharge [H2]);
      ]
    | apply rule (¬#i [H1] ⊥);
      apply rule (¬#e (¬(A∨¬A)) (A∨¬A));
      [ apply rule (discharge [H]);
      | apply rule (∨#i_l A);
        apply rule (discharge [H1]);
      ]
    ]
qed.

lemma ex1 : (A ⇒ E) ∨ B ⇒ A ∧ C ⇒ (E ∧ C) ∨ B.

 apply rule (prove ((A⇒E)∨B⇒A∧C⇒E∧C∨B));
   
 apply rule (⇒#i [H] (A∧C⇒E∧C∨B));
 apply rule (⇒#i [K] (E∧C∨B));
 apply rule (∨#e ((A⇒E)∨B) [C1] (E∧C∨B) [C2] (E∧C∨B));
[ apply rule (discharge [H]);
| apply rule (∨#i_l (E∧C));
  apply rule (∧#i E C);
  [ apply rule (⇒#e (A⇒E) A);
    [ apply rule (discharge [C1]);
    | apply rule (∧#e_l (A∧C)); apply rule (discharge [K]);
    ]
  | apply rule (∧#e_r (A∧C)); apply rule (discharge [K]);
  ]
| apply rule (∨#i_r B); apply rule (discharge [C2]);
]
qed.

