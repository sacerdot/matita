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

include "lambda/sn.ma".

let rec substc M l on l ≝ match l with
   [ nil ⇒ M
   | cons A D ⇒ lift (substc M D)[0≝A] 0 1
   ]. 

notation "M [ l ]" non associative with precedence 90 for @{'Substc $M $l}.

interpretation "Substc" 'Substc M l = (substc M l).

theorem substc_sort: ∀n,l. (Sort n)[l] = Sort n.
#n #l (elim l) -l // #A #D #IH normalize >IH -IH. normalize //
qed.

(* REDUCIBILITY CANDIDATES ****************************************************)

(* nautral terms *)
inductive neutral: T → Prop ≝
   | neutral_sort: ∀n.neutral (Sort n)
   | neutral_rel: ∀i.neutral (Rel i)
   | neutral_app: ∀M,N.neutral (App M N)
.

(* the reducibility candidates (r.c.) *)
record RC : Type[0] ≝ {
   mem : T → Prop;
   cr1 : ∀t. mem t → SN t;
   sat0: ∀l,n. all mem l → mem (Appl (Sort n) l);
   sat1: ∀l,i. all mem l → mem (Appl (Rel i) l);
   sat2: ∀F,A,B,l. mem B → mem A → 
         mem (Appl F[0:=A] l) → mem (Appl (Lambda B F) (A::l))
}.

interpretation "membership (reducibility candidate)" 'mem A R = (mem R A).

(* the r.c. of all s.n. terms *)
definition snRC: RC ≝ mk_RC SN ….
/2/ qed. 

(* the carrier of the r.c. of a (dependent) product type *)
definition dep_mem ≝ λRA,RB,M. ∀N. N ∈ RA → App M N ∈ RB.

(* the r.c. of a (dependent) product type *)
axiom depRC: RC → RC → RC.
(* FG 
 * ≝ λRA,RB. mk_RC (dev_mem RA RB) ?.
 *)

(* a generalization of mem on lists *)
let rec memc H l on l : Prop ≝ match l with
   [ nil ⇒ True
   | cons A D ⇒ match H with
      [ nil      ⇒ A ∈ snRC ∧ memc H D
      | cons R K ⇒ A ∈ R ∧ memc K D
      ]
   ].

interpretation "componentwise membership (context of reducibility candidates)" 'mem l H = (memc H l).

(* the r.c. associated to a type *)
let rec trc H t on t : RC ≝ match t with
   [ Sort _     ⇒ snRC
   | Rel i      ⇒ nth i … H snRC
   | App _ _    ⇒ snRC (* FG ??? *)
   | Lambda _ _ ⇒ snRC
   | Prod A B   ⇒ depRC (trc H A) (trc (trc H A :: H) B)
   | D _        ⇒ snRC (* FG ??? *)
   ].

notation "hvbox(〚T〛 _ term 90 E)" non associative with precedence 50 for @{'InterpE $T $E}.

interpretation "interpretation of a type" 'InterpE t H = (trc H t).

(* the r.c. context associated to a context *)
let rec trcc H G on G : list RC ≝ match G with
   [ nil      ⇒ H
   | cons A D ⇒ 〚A〛_(trcc H D) :: trcc H D
   ].

interpretation "interpretation of a context" 'InterpE G H = (trcc H G).

theorem tj_trc: ∀G,A,B. G ⊢A:B → ∀H,l. l ∈ 〚G〛_(H) → 
                A[l] ∈ 〚B[l]〛_〚G〛_(H).
#G #A #B #tjAB (elim tjAB) -G A B tjAB
   [ #i #j #_ #H #l #_ >substc_sort >substc_sort @(sn_sort (nil ?)) //
   | #G #B #n #tjB #IH #H #l (elim l) -l (normalize) 
     [ #_
     | #C #D #IHl #mem (elim mem) -mem #mem #memc 
(* 
theorem tj_sn: ∀G,A,B. G ⊢A:B → SN A.
#G #A #B #tjAB lapply (tj_trc … tjAB (nil ?) (nil ?)) -tjAB (normalize) /3/
qed.
*)