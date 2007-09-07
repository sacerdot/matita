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

set "baseuri" "cic:/matita/test/russell/".

include "nat/orders.ma".
include "list/list.ma".
include "datatypes/constructors.ma".

inductive sigma (A:Type) (P:A → Prop) : Type ≝
 sig_intro: ∀a:A. P a → sigma A P.

interpretation "sigma" 'exists \eta.x =
  (cic:/matita/test/russell/sigma.ind#xpointer(1/1) _ x).
 
definition inject ≝ λP.λa:list nat.λp:P a. sig_intro ? P ? p.

coercion cic:/matita/test/russell/inject.con 0 1.

definition eject ≝ λP.λc: ∃n:list nat.P n. match c with [ sig_intro w _ ⇒ w].

coercion cic:/matita/test/russell/eject.con.
  
alias symbol "exists" (instance 2) = "exists".
lemma tl : ∀l:list nat. l ≠ [] → ∃l1.∃a.a :: l1 = l.
letin program ≝ 
  (λl:list nat. λH:l ≠ [].match l with [ nil ⇒ λH.[] | cons x l1 ⇒ λH.l1] H);
letin program_spec ≝ (program : ∀l:list nat. l ≠ [] → ∃l1.∃a.a :: l1 = l);
 [ generalize in match H; cases l; [intros (h1); cases (h1 ?); reflexivity]
   intros; apply (ex_intro ? ? n); apply eq_f; reflexivity; ]
exact program_spec;
qed.

alias symbol "exists" (instance 3) = "exists".
lemma tl2 : ∀l:∃l:list nat. l ≠ []. ∃l1.∃a.a :: l1 = l.
letin program ≝ 
  (λl:list nat. match l with [ nil ⇒ [] | cons x l1 ⇒ l1]);
letin program_spec ≝ 
  (program : ∀l:∃l:list nat. l ≠ []. ∃l1.∃a.a :: l1 = l);
  [ autobatch; | generalize in match H; clear H; cases s; simplify;
    intros; cases (H H1); ]
exact program_spec.
qed.

definition nat_return := λn:nat. Some ? n.

coercion cic:/matita/test/russell/nat_return.con.

definition raise_exn := None nat.

definition try_with :=
 λx,e. match x with [ None => e | Some (x : nat) => x].

lemma hd : list nat → option nat :=
  λl.match l with [ nil ⇒ raise_exn | cons x _ ⇒ nat_return x ].
  
axiom f : nat -> nat.

definition bind ≝ λf:nat->nat.λx.
  match x with [None ⇒ raise_exn| Some x ⇒ nat_return(f x)].

include "datatypes/bool.ma".
include "list/sort.ma".
include "nat/compare.ma".

definition inject_opt ≝ λP.λa:option nat.λp:P a. sig_intro ? P ? p.

coercion cic:/matita/test/russell/inject_opt.con 0 1.

definition eject_opt ≝ λP.λc: ∃n:option nat.P n. match c with [ sig_intro w _ ⇒ w].

coercion cic:/matita/test/russell/eject_opt.con.

definition find :
 ∀p:nat → bool.
  ∀l:list nat. sigma ? (λres:option nat.
   match res with
    [ None ⇒ ∀y. mem ? eqb y l = true → p y = false
    | Some x ⇒ mem ? eqb x l = true ∧ p x = true ]).
letin program ≝
 (λp.
  let rec aux l ≝
   match l with
    [ nil ⇒ raise_exn
    | cons x l ⇒ match p x with [ true ⇒ nat_return x | false ⇒ aux l ]
    ]
  in
   aux);
apply
 (program : ∀p:nat → bool.
  ∀l:list nat. ∃res:option nat.
   match res with
    [ None ⇒ ∀y:nat. (mem nat eqb y l = true : Prop) → p y = false
    | Some (x:nat) ⇒ mem nat eqb x l = true ∧ p x = true ]);
clear program;
 [ cases (aux l1); clear aux;
   simplify in ⊢ (match % in option return ? with [None⇒?|Some⇒?]);
   generalize in match H2; clear H2;
   cases a;
    [ simplify;
      intros 2;
      apply (eqb_elim y n);
       [ intros;
         autobatch
       | intros;
         apply H2;
         simplify in H4;
         exact H4
       ]
    | simplify;
      intros;
      cases H2; clear H2;
      split;
       [ elim (eqb n1 n);
         simplify;
         autobatch
       | assumption
       ]
    ]
 | unfold nat_return; simplify;
   split;
    [ rewrite > eqb_n_n;
      reflexivity
    | assumption
    ]
 | unfold raise_exn; simplify;
   intros;
   change in H1 with (false = true);
   destruct H1 
 ]
qed.