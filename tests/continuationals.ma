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


include "coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "trans_equal" = "cic:/Coq/Init/Logic/trans_equal.con".
alias id "refl_equal" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)".
alias id "Z" = "cic:/Coq/ZArith/BinInt/Z.ind#xpointer(1/1)".

theorem semicolon: \forall p:Prop.p\to p\land p.
intros (p); split; assumption.
qed.

theorem branch:\forall x:nat.x=x.
intros (n);
elim n
[ reflexivity;
| reflexivity ].
qed.

theorem pos:\forall x:Z.x=x.
intros (n);
elim n;
[ 3: reflexivity;
| 2: reflexivity;
| reflexivity ]
qed.

theorem dot:\forall x:Z.x=x.
intros (x).
elim x.
reflexivity. reflexivity. reflexivity.
qed.

theorem dot_slice:\forall x:Z.x=x.
intros (x).
elim x;
[ elim x. reflexivity. reflexivity. reflexivity;
| reflexivity
| reflexivity ];
qed.

theorem focus:\forall x:Z.x=x.
intros (x); elim x.
focus 16 17;
  reflexivity;
unfocus.
reflexivity.
qed.

theorem skip:\forall x:nat.x=x. 
intros (x).
apply trans_equal;
[ 2: apply (refl_equal nat x);
| skip
| reflexivity
]
qed.

theorem skip_focus:\forall x:nat.x=x.
intros (x).
apply trans_equal;
[ focus 18; apply (refl_equal nat x); unfocus;
| skip  
| reflexivity ]
qed.
