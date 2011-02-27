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

include "lambda/rc_sat.ma".

(* THE EVALUATION *************************************************************)

(* The interpretation of a type t as a r.c. denoted by 〚t〛.
 * For the "conv" rule we need 〚M〛 ≈ 〚N〛 when M and N are convertible, so:
 * 1) 〚(λB.M N)〛 ≈ 〚N[0≝N]〛 implies that 〚(M N)〛 and 〚λB.M〛 are evaluated by
 *    stacking the application arguments like a reduction machine does
 * 2) ∀M,N. 〚D M〛 ≈ 〚D N〛, implies that 〚D M〛 must be a constant.
 *)
let rec ev E K t on t : RC ≝ match t with (* E: environment, K: stack *)
   [ Sort _     ⇒ snRC                               (* from λ→ *)
   | Rel i      ⇒ nth i … E snRC                     (* from F *)
   | App M N    ⇒ ev E (ev E ([]) N :: K) M          (* machine-like push *)
   | Lambda _ M ⇒ ev (hd … K snRC :: E) (tail … K) M (* machine-like pop *)
   | Prod N M   ⇒ let C ≝ (ev E ([]) N) in
                  depRC C (ev (C :: E) K M)          (* from λ→ and F *)
   | D _        ⇒ snRC                               (* see note 2 above *)
   ].

interpretation "interpretation of a type" 'Eval2 t E K = (ev E K t).

(* extensional equality of the interpretations *)
definition eveq: T → T → Prop ≝ λt1,t2. ∀E,K. 〚t1〛_[E, K] ≅ 〚t2〛_[E, K].

interpretation 
   "extensional equality of the type interpretations"
   'napart t1 t2 = (eveq t1 t2).

(* The interpretation of a context of types as a context of r.c.'s *)
let rec cev E G on G : list RC ≝ match G with
   [ nil      ⇒ E
   | cons t F ⇒ let D ≝ cev E F in 〚t〛_[D,[]] :: D
   ].

interpretation "interpretation of a context" 'Eval1 G E = (cev E G).

theorem ev_app: ∀M,N,E,K. 〚App M N〛_[E, K] = 〚M〛_[E, 〚N〛_[E,[]]::K].
// qed.

theorem ev_lambda: ∀M,N,E,K.
                   〚Lambda N M〛_[E, K] = 〚M〛_[hd … K snRC :: E, tail … K].
// qed.

theorem ev_prod: ∀M,N,E,K.
                 〚Prod N M〛_[E,K] = depRC (〚N〛_[E,[]]) (〚M〛_[〚N〛_[E,[]]::E,K]).
// qed.

theorem ev_repl: ∀t,E1,E2,K1,K2. E1 ≅ E2 → K1 ≅ K2 → 〚t〛_[E1,K1] ≅ 〚t〛_[E2,K2].
#t (elim t) /5/
qed.

theorem ev_rel_lt: ∀K,D,E,i. (S i) ≤ |E| → 〚Rel i〛_[E @ D, K] = 〚Rel i〛_[E,K].
#K #D #E (elim E) -E [1: #i #Hie (elim (not_le_Sn_O i)) #Hi (elim (Hi Hie)) ]
#C #F #IHE #i (elim i) -i // #i #_ #Hie @IHE @le_S_S_to_le @Hie
qed.

theorem ev_rel_ge: ∀K,D,E,i. (S i) ≰ |E| →
                   〚Rel i〛_[E @ D, K] = 〚Rel (i-|E|)〛_[D,K].
#K #D #E (elim E) -E [ normalize // ]
#C #F #IHE #i (elim i) -i [1: -IHE #Hie (elim Hie) -Hie #Hie (elim (Hie ?)) /2/ ]
normalize #i #_ #Hie @IHE /2/
qed.

theorem ev_app_repl: ∀M1,M2,N1,N2. M1 ≈ M2 → N1 ≈ N2 →
                     App M1 N1 ≈ App M2 N2.
#M1 #M2 #N1 #N2 #IHM #IHN #E #K >ev_app (@transitive_rceq) /3/
qed.

theorem ev_lambda_repl: ∀N1,N2,M1,M2. N1 ≈ N2 → M1 ≈ M2 →
                        Lambda N1 M1 ≈ Lambda N2 M2.
#N1 #N2 #M1 #M2 #IHN #IHM #E #K >ev_lambda (@transitive_rceq) //
qed.

theorem ev_prod_repl: ∀N1,N2,M1,M2. N1 ≈ N2 → M1 ≈ M2 →
                      Prod N1 M1 ≈ Prod N2 M2.
#N1 #N2 #M1 #M2 #IHN #IHM #E #K >ev_prod @dep_repl //
(@transitive_rceq) [2: @IHM | skip ] /3/
qed. 

(* weakeing and thinning lemma for the type interpretation *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
theorem ev_lift: ∀E,Ep,t,Ek,K.
                 〚lift t (|Ek|) (|Ep|)〛_[Ek @ Ep @ E, K] ≅ 〚t〛_[Ek @ E, K].
#E #Ep #t (elim t) -t
   [ #n >lift_sort /by SAT0_sort/
   | #i #Ek #K @(leb_elim (S i) (|Ek|)) #Hik
     [ >(lift_rel_lt … Hik) >(ev_rel_lt … Hik) >(ev_rel_lt … Hik) //
     | >(lift_rel_ge … Hik) >(ev_rel_ge … Hik) <associative_append
       >(ev_rel_ge …) (>length_append)
       [ >arith2 // @not_lt_to_le /2/ | @(arith3 … Hik) ]
     ]
   | #M #N #IHM #IHN #Ek #K >lift_app >ev_app (@transitive_rceq) /3/
   | #N #M #IHN #IHM #Ek #K >lift_lambda >ev_lambda (@transitive_rceq)
     [2: >commutative_plus @(IHM (? :: ?)) | skip ] //
   | #N #M #IHN #IHM #Ek #K >lift_prod >ev_prod (@dep_repl) //
     (@transitive_rceq) [2: >commutative_plus @(IHM (? :: ?)) | skip ] /3/
   | //
   ]
qed.

(*
theorem tj_ev: ∀G,A,B. G ⊢A:B → ∀H,l. l ∈ 〚G〛_(H) → A[l] ∈ 〚B[l]〛_〚G〛_(H).
#G #A #B #tjAB (elim tjAB) -G A B tjAB
   [ #i #j #_ #H #l #_ >substc_sort >substc_sort /2 by SAT0_sort/
   | #G #B #n #tjB #IH #H #l (elim l) -l (normalize) 
     [ #_ /2 by SAT1_rel/
     | #C #D #IHl #mem (elim mem) -mem #mem #memc
       >lift_0 >delift // >lift_0 

*)
(* 
theorem tj_sn: ∀G,A,B. G ⊢A:B → SN A.
#G #A #B #tjAB lapply (tj_trc … tjAB (nil ?) (nil ?)) -tjAB (normalize) /3/
qed.
*)

(*
theorem tev_rel_S: ∀i,R,H. 〚Rel (S i)〛_(R::H) = 〚Rel i〛_(H).
// qed.
*)
(*
theorem append_cons: ∀(A:Type[0]). ∀(l1,l2:list A). ∀a.
                     (a :: l1) @ l2 = a :: (l1 @ l2).
// qed.
*)