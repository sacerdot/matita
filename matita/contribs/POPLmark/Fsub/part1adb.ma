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

include "Fsub/defndb.ma".
include "nat/lt_arith.ma".
include "nat/le_arith.ma".

(*** Lemma A.1 (Reflexivity) ***)
theorem JS_Refl : ∀T,G.WFType G T → WFEnv G → G ⊢ T ⊴  T.
intros 3;elim H;autobatch depth=4 size=7;
qed.

(*
 * A slightly more general variant to lemma A.2.2, where weakening isn't
 * defined as concatenation of any two disjoint environments, but as
 * set inclusion.
 *)

lemma JS_weakening : ∀G,T,U.G ⊢ T ⊴ U → ∀H.WFEnv H → 
                     ∀f. injective nat nat f → 
                     (∀n:ℕ.n<length bound G→f n<length bound H) →
                     incl G H f → H ⊢ perm T f ⊴ perm U f.
intros 4; elim H;
 [apply SA_Top
  [assumption
  |apply (WFT_env_incl ?? H2);assumption]
 |simplify;apply SA_Refl_TVar
  [assumption
  |change in ⊢ (? ? %) with (perm (TVar n) f);autobatch width=4]
 |simplify;lapply (H4 ? H6 ? H7);
  lapply (H9 ? n H1)
  [assumption
  |rewrite > H2 in Hletin1;simplify in Hletin1;
   cut (∃t.nth bound H5 (mk_bound true Top) (f n) = mk_bound true t)
   [elim Hcut;rewrite > H10 in Hletin1;simplify in Hletin1;destruct;
    rewrite > Hcut1 in Hletin;apply (SA_Trans_TVar ?????? Hletin);autobatch
   |elim (nth bound H5 (mk_bound true Top) (f n)) in Hletin1;
    elim b in H10;simplify in H10;destruct;exists [apply t2]
    reflexivity]
  |*:assumption]
 |simplify;autobatch width=5 size=11
 |simplify;apply (SA_All ? ? ? ? ? (H2 ? H6 ?? H8 H9))
  [assumption
  |apply H4
   [autobatch depth=4 width=4 size=8
   |change in ⊢ (???%) with (flift f 1);autobatch;
   |intro;cases n;simplify;intros;autobatch depth=4
   |change in ⊢ (???%) with (flift f 1);autobatch]]]
qed.

inverter JS_indinv for JSubtype (%?%).

theorem narrowing:∀G,G1,U,P,M,N.
  G1 ⊢ P ⊴ U →  
  (∀G2,S,T.
    G2@G1 ⊢ S ⊴ lift U (length ? G2) O →
    G2@G1 ⊢ lift U (length ? G2) O ⊴ T → 
    G2@G1 ⊢ S ⊴ T) → 
  G ⊢ M ⊴ N →
  ∀l.G=l@(mk_bound true U::G1) → l@(mk_bound true P::G1) ⊢ M ⊴ N.
intros 9;elim H2;destruct;try autobatch depth=4 size=7;
elim (decidable_eq_nat n (length ? l1))
[apply (SA_Trans_TVar ??? P);
 [elim l1 in n H7
  [rewrite > H7;simplify;autobatch
  |rewrite > H8;simplify;apply le_S_S;apply H7;reflexivity]
 |elim l1 in n H4 H7
  [rewrite > H7;reflexivity
  |rewrite > H8;simplify;apply H4
   [rewrite > H8 in H7;apply H7
   |reflexivity]]
 |cut (U = t1)
  [change in ⊢ (? (? ? ? %) ? ?) with ([mk_bound true P]@G1);
   cut (S n = length ? (l1@[mk_bound true P]))
   [rewrite > Hcut1;rewrite < associative_append;apply H1;rewrite < Hcut1;
    rewrite > Hcut;rewrite > associative_append;
    [do 2 rewrite > lift_perm2;rewrite < Hcut;
     apply (JS_weakening ??? H)
     [simplify;autobatch
     |autobatch
     |intros;simplify;change in ⊢ (??(??%)) with (l1@[⊴P]@G1);
      rewrite < associative_append;
      rewrite > length_append;rewrite < Hcut1;rewrite < sym_plus;
      autobatch
     |applyS incl_append]
    |apply H6;reflexivity]
   |elim l1 in n H7
    [simplify;rewrite > H7;reflexivity
    |simplify;rewrite > H8;rewrite < H7
     [simplify;apply refl_eq
     |skip
     |reflexivity]]]
  |elim l1 in n H7 H4;destruct;
   [simplify in H4;destruct;reflexivity
   |simplify in H7;apply H4
    [2:apply H7
    |skip
    |reflexivity]]]]
|apply (SA_Trans_TVar ??? t1)
 [cut (length ? (l1@⊴ P :: G1) = length ? (l1@⊴U::G1))
  [rewrite > Hcut;assumption
  |elim l1;simplify;autobatch]
 |rewrite < H4;elim l1 in n H7 0
  [simplify;intro;cases n1;intros
   [elim H7;reflexivity
   |reflexivity]
  |simplify;intros 4;elim n1
   [simplify;reflexivity
   |simplify;apply H7;intro;elim H9;autobatch]]
 |apply H6;reflexivity]]
qed.

lemma JS_trans_prova: ∀T,G,R,U,f.G ⊢ R ⊴ perm T f → G ⊢ perm T f ⊴ U → G ⊢ R ⊴ U.
intro;elim T;
  [simplify in H;simplify in H1;elim H using JS_indinv;destruct;autobatch
  |simplify in H1;inversion H1; intros; destruct; assumption
  |simplify in H2;elim H2 using JS_indinv;intros;destruct;
   [autobatch
   |simplify in H3;inversion H3;intros;destruct;autobatch depth=4 size=7]
  |simplify in H2;elim H2 using JS_indinv;intros;destruct;
   [autobatch
   |simplify in H3;inversion H3;intros;destruct;
    [apply SA_Top;autobatch
    |apply SA_All
     [apply (H ???? H8 H4);assumption
     |apply H1
      [2:apply (narrowing (mk_bound true (perm t f)::G) G ???? H8 ? H6 [])
       [intros;rewrite > lift_perm2 in H12;rewrite > lift_perm2 in H13;
        rewrite > perm_compose in H12; rewrite > perm_compose in H13;
        apply H
        [2,3:autobatch]
       |reflexivity]
      |3:assumption]]]]]
qed.

theorem JS_trans : ∀G,T,U,V.G ⊢ T ⊴ U → G ⊢ U ⊴ V → G ⊢ T ⊴ V.
intros 4;rewrite > (perm_id ? 0) in ⊢ (???% → ??%? → ?);
intros;autobatch;
qed.

theorem JS_narrow : ∀G1,G2,P,Q,T,U.
                       (G2 @ (mk_bound true Q :: G1)) ⊢ T ⊴ U → G1 ⊢ P ⊴ Q →
                       (G2 @ (mk_bound true P :: G1)) ⊢ T ⊴ U.
intros; apply (narrowing ? ? ? ? ? ? H1 ? H) [|autobatch]
intros;autobatch;
qed.