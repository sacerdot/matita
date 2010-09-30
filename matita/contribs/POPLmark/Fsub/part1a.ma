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

include "Fsub/defn.ma".

(*** Lemma A.1 (Reflexivity) ***)
theorem JS_Refl : ∀T,G.(G ⊢ T) → G ⊢ ♦ → G ⊢ T ⊴  T.
intros 3; elim H;try autobatch;
apply SA_All; [ autobatch | intros;autobatch depth=4 size=10]
qed.

(*
 * A slightly more general variant to lemma A.2.2, where weakening isn't
 * defined as concatenation of any two disjoint environments, but as
 * set inclusion.
 *)

lemma JS_weakening : ∀G,T,U.G ⊢ T ⊴ U → ∀H.H ⊢ ♦ → G ⊆ H → H ⊢ T ⊴ U.
intros 4; elim H;try autobatch depth=4 size=7;
apply (SA_All ? ? ? ? ? (H2 ? H6 H7));
intros; autobatch depth=6 width=4 size=13;
qed.

inverter JS_indinv for JSubtype (%?%).

theorem narrowing:∀X,G,G1,U,P,M,N.
  G1 ⊢ P ⊴ U → (∀G2,T.G2@G1 ⊢ U ⊴ T → G2@G1 ⊢ P ⊴ T) → G ⊢ M ⊴ N →
  ∀l.G=l@ !X ⊴ U::G1 → l@ !X ⊴ P::G1 ⊢ M ⊴ N.
intros 10.elim H2; destruct;
 [letin x \def fv_env. letin y ≝incl. autobatch depth=4 size=8.
 | autobatch depth=4 size=7;
 | elim (decidable_eq_nat X n)
    [apply (SA_Trans_TVar ? ? ? P); destruct;
      [ autobatch
      | lapply (WFE_bound_bound X t1 U ? ? H3); autobatch]
    | apply (SA_Trans_TVar ? ? ? t1); autobatch]
 | autobatch
 | apply SA_All;
    [ autobatch
    | intros; apply (H6 ? ? (mk_bound true X1 t2::l1)); autobatch]]
qed.

lemma JS_trans_prova: ∀T,G1.(G1 ⊢ T) →
      ∀G,R,U.fv_env G1 ⊆ fv_env G → G ⊢ R ⊴ T → G ⊢ T ⊴ U → G ⊢ R ⊴ U.
intros 3;elim H;clear H;
  [elim H3 using JS_indinv;destruct;autobatch
  |inversion H3; intros; destruct; assumption
  |*:elim H6 using JS_indinv;destruct;
    [1,3: autobatch
    |*: inversion H7; intros; destruct;
      [1,2: autobatch depth=4 width=4 size=9
      | apply SA_Top
         [ assumption
         | apply WFT_Forall;intros;autobatch depth=4]
      | apply SA_All
         [ autobatch
         | intros;apply (H4 X);simplify;
            [4: apply (narrowing X (mk_bound true X t::G) ? ? ? ? ? H11 ? ? [])
               [intros;apply H2;try unfold;intros;autobatch; 
               |*:autobatch]
            |3:apply incl_cons;apply H5
            |*:autobatch]]]]]
qed.

theorem JS_trans : ∀G,T,U,V.G ⊢ T ⊴ U → G ⊢ U ⊴ V → G ⊢ T ⊴ V.
intros 5; apply (JS_trans_prova ? G); autobatch depth=2.
qed.

theorem JS_narrow : ∀G1,G2,X,P,Q,T,U.
                       G2 @ !X ⊴ Q :: G1 ⊢ T ⊴ U → G1 ⊢ P ⊴ Q →
                       G2 @ !X ⊴ P :: G1 ⊢ T ⊴ U.
intros;apply (narrowing ? ? ? ? ? ? ? H1 ? H) [|autobatch]
intros;apply (JS_trans ? ? ? ? ? H2);apply (JS_weakening ? ? ? H1);autobatch.
qed.