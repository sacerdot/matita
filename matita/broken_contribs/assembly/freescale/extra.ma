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

(* ********************************************************************** *)
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "nat/div_and_mod.ma".
include "nat/primes.ma".
include "list/list.ma".
include "datatypes/constructors.ma".
include "logic/connectives.ma".

(* BOOLEANI *)

(* ridefinizione degli operatori booleani, per evitare l'overloading di quelli normali *)
definition not_bool ≝
λb:bool.match b with [ true ⇒ false | false ⇒ true ].

definition and_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ b2 | false ⇒ false ].

definition or_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ true | false ⇒ b2 ].

definition xor_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ not_bool b2
 | false ⇒ b2 ].

definition eq_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ b2
 | false ⇒ not_bool b2 ].

lemma eqbool_switch : ∀b1,b2.eq_bool b1 b2 = eq_bool b2 b1.
 do 2 intro;
 elim b1; elim b2;
 reflexivity.
qed.

lemma andbool_switch : ∀b1,b2.and_bool b1 b2 = and_bool b2 b1.
 do 2 intro;
 elim b1; elim b2;
 reflexivity.
qed.

lemma orbool_switch : ∀b1,b2.or_bool b1 b2 = or_bool b2 b1.
 do 2 intro;
 elim b1; elim b2;
 reflexivity.
qed.

lemma xorbool_switch : ∀b1,b2.xor_bool b1 b2 = xor_bool b2 b1.
 do 2 intro;
 elim b1; elim b2;
 reflexivity.
qed.


lemma orb_false_false :
 ∀b1,b2:bool.((or_bool b1 b2) = false) → b1 = false.
 intros 2;
 elim b1 0;
 elim b2;
 simplify in H;
 try destruct H;
 reflexivity.
qed.

lemma orb_false_false_r :
 ∀b1,b2:bool.((or_bool b1 b2) = false) → b2 = false.
 intros 2;
 elim b1 0;
 elim b2;
 simplify in H;
 try destruct H;
 reflexivity.
qed.

lemma eqbool_to_eq : ∀b1,b2:bool.(eq_bool b1 b2 = true) → (b1 = b2).
 unfold eq_bool;
 intros;
 elim b1 in H:(%);
 elim b2 in H:(%);
 normalize in H:(%);
 try reflexivity;
 destruct H.
qed.

lemma eq_to_eqbool : ∀b1,b2.b1 = b2 → eq_bool b1 b2 = true.
 do 2 intro;
 elim b1 0;
 elim b2 0;
 intro;
 normalize in H:(%);
 try destruct H;
 reflexivity.
qed.

(* \ominus *)
notation "hvbox(⊖ a)" non associative with precedence 36
 for @{ 'not_bool $a }.
interpretation "not_bool" 'not_bool x = (not_bool x).

(* \otimes *)
notation "hvbox(a break ⊗ b)" left associative with precedence 35
 for @{ 'and_bool $a $b }.
interpretation "and_bool" 'and_bool x y = (and_bool x y).

(* \oplus *)
notation "hvbox(a break ⊕ b)" left associative with precedence 34
 for @{ 'or_bool $a $b }.
interpretation "or_bool" 'or_bool x y = (or_bool x y).

(* \odot *)
notation "hvbox(a break ⊙ b)" left associative with precedence 33
 for @{ 'xor_bool $a $b }.
interpretation "xor_bool" 'xor_bool x y = (xor_bool x y).

(* ProdT e' gia' definito, aggiungo Prod3T e Prod4T e Prod5T *)

inductive Prod3T (T1:Type) (T2:Type) (T3:Type) : Type ≝
tripleT : T1 → T2 → T3 → Prod3T T1 T2 T3.

definition fst3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ tripleT x _ _ ⇒ x ].

definition snd3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ tripleT _ x _ ⇒ x ].

definition thd3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ tripleT _ _ x ⇒ x ].

inductive Prod4T (T1:Type) (T2:Type) (T3:Type) (T4:Type) : Type ≝
quadrupleT : T1 → T2 → T3 → T4 → Prod4T T1 T2 T3 T4.

definition fst4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadrupleT x _ _ _ ⇒ x ].

definition snd4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadrupleT _ x _ _ ⇒ x ].

definition thd4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadrupleT _ _ x _ ⇒ x ].

definition fth4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadrupleT _ _ _ x ⇒ x ].

inductive Prod5T (T1:Type) (T2:Type) (T3:Type) (T4:Type) (T5:Type) : Type ≝
quintupleT : T1 → T2 → T3 → T4 → T5 → Prod5T T1 T2 T3 T4 T5.

definition fst5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintupleT x _ _ _ _ ⇒ x ].

definition snd5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintupleT _ x _ _ _ ⇒ x ].

definition thd5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintupleT _ _ x _ _ ⇒ x ].

definition frth5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintupleT _ _ _ x _ ⇒ x ].

definition ffth5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintupleT _ _ _ _ x ⇒ x ].

(* OPTIOTN MAP *)

(* option map = match ... with [ None ⇒ None ? | Some .. ⇒ .. ] *)
definition opt_map ≝
λT1,T2:Type.λt:option T1.λf:T1 → option T2.
 match t with [ None ⇒ None ? | Some x ⇒ (f x) ].

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

axiom mod_plus: ∀a,b,m. (a + b) \mod m = (a \mod m + b \mod m) \mod m.
axiom mod_mod: ∀a,n,m. n∣m → a \mod n = a \mod n \mod m.
axiom eq_mod_times_n_m_m_O: ∀n,m. O < m → n * m \mod m = O.
axiom eq_mod_to_eq_plus_mod: ∀a,b,c,m. a \mod m = b \mod m → (a+c) \mod m = (b+c) \mod m.
axiom eq_mod_times_times_mod: ∀a,b,n,m. m = a*n → (a*b) \mod m = a * (b \mod n).
axiom divides_to_eq_mod_mod_mod: ∀a,n,m. n∣m → a \mod m \mod n = a \mod n.
axiom le_to_le_plus_to_le : ∀a,b,c,d.b\leq d\rarr a+b\leq c+d\rarr a\leq c.
axiom or_lt_le : ∀n,m. n < m ∨ m ≤ n.

lemma le_to_lt: ∀n,m. n ≤ m → n < S m.
 intros;
 unfold;autobatch.
qed.

alias num (instance 0) = "natural number".
definition nat_of_bool ≝
 λb:bool.match b return λ_.nat with [ true ⇒ 1 | false ⇒ 0 ].

theorem lt_trans: ∀x,y,z. x < y → y < z → x < z.
 unfold lt;
 intros;
 autobatch.
qed.

lemma leq_m_n_to_eq_div_n_m_S: ∀n,m:nat. 0 < m → m ≤ n → ∃z. n/m = S z.
 intros;
 unfold div;
 apply (ex_intro ? ? (div_aux (pred n) (n-m) (pred m)));
 cut (∃w.m = S w);
  [ elim Hcut;
    rewrite > H2;
    rewrite > H2 in H1;
    clear Hcut; clear H2; clear H;
    simplify;
    unfold in ⊢ (? ? % ?);
    cut (∃z.n = S z);
     [ elim Hcut; clear Hcut;
       rewrite > H in H1;
       rewrite > H; clear m;
       change in ⊢ (? ? % ?)  with
        (match leb (S a1) a with
         [ true ⇒ O
         | false ⇒ S (div_aux a1 ((S a1) - S a) a)]);
       cut (S a1 ≰ a);
        [ apply (leb_elim (S a1) a);
           [ intro;
             elim (Hcut H2)
           | intro;
             simplify;
             reflexivity
           ]
        | intro;
          autobatch
        ]
     | elim H1; autobatch
     ]
  | exists;[apply (pred m);]autobatch
  ].
qed.

axiom daemon: False.
