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

(* we may define mem as in the following lemma and get rid of it *)
definition find_spec ≝
  λl,p.λres:option nat.
   match res with
    [ None ⇒ ∀y. mem ? eqb y l = true → p y = false
    | Some x ⇒ mem ? eqb x l = true ∧ 
               p x = true ∧ 
               ∀y.mem ? eqb y l = true → p y = true → x ≠ y → 
                    ∃l1,l2,l3.l = l1 @ [x] @ l2 @ [y] @ l3].

lemma mem_x_to_ex_l1_l2 : ∀l,x.mem ? eqb x l = true → ∃l1,l2.l = l1 @ [x] @ l2.
intros 2; elim l (H hd tl IH H); [destruct H]
generalize in match H; clear H;
simplify; apply (eqb_elim x hd); simplify; intros;
[1:clear IH; rewrite < H; apply (ex_intro ? ? []); 
|2:lapply(IH H1); clear H1 IH; decompose; rewrite > H2; clear H2]
simplify; autobatch;
qed.

definition if : ∀A:Type.bool → A → A → A ≝ 
 λA,b,t,f. match b with [ true ⇒ t | false ⇒ f].
 
notation < "'If' \nbsp b \nbsp 'Then' \nbsp t \nbsp 'Else' \nbsp f" for @{ 'if $b $t $f }.
notation > "'If' b 'Then' t 'Else' f" for @{ 'if $b $t $f }.
interpretation "if" 'if a b c = (cic:/matita/test/russell/if.con _ a b c). 

definition sigma_find_spec : ∀p,l. sigma ? (λres.find_spec l p res).
(* define the find function *) 
letin find ≝ (λp. 
  let rec aux l ≝
    match l with
    [ nil ⇒ raise_exn
    | cons x l ⇒ If p x Then nat_return x Else aux l]
    in aux);
(* manca una delta?! *) unfold if in find;
apply (find: ∀p.∀l.sigma ? (λres.find_spec l p res)); clear find;
(* l = x::tl ∧ p x = false *)
[1: cases (aux l1); clear aux;
    generalize in match H2; clear H2; cases a; clear a; simplify;
    [1: intros 2; apply (eqb_elim y n); intros (Eyn); [rewrite > Eyn; assumption]
        apply H3; simplify in H2; assumption;
    |2: intros; decompose; repeat split; [2: assumption]; intros;
        [1: cases (eqb n1 n); simplify; autobatch;
        |2: generalize in match (refl_eq ? (eqb y n)); generalize in ⊢ (? ? ? %→?); 
            intro; cases b; clear b; intro Eyn; rewrite > Eyn in H3; simplify in H3;
            [1: rewrite > (eqb_true_to_eq ? ? Eyn) in H6; rewrite > H1 in H6; destruct H6;
            |2: lapply H4; try assumption; decompose; clear H4; rewrite > H8;
                simplify; autobatch depth = 4;]]]
(* l = x::tl ∧ p x = true *)
|2: unfold find_spec; unfold nat_return; simplify; repeat split; [2: assumption]
    [1: rewrite > eqb_n_n; reflexivity
    |2: intro; generalize in match (refl_eq ? (eqb y n)); generalize in ⊢ (? ? ? %→?);
        intro; cases b; clear b; intro Eyn; rewrite > Eyn; 
        [1: rewrite > (eqb_true_to_eq ? ? Eyn);] clear Eyn; simplify; intros;
        [1: cases H4; reflexivity
        |2: lapply (mem_x_to_ex_l1_l2 ? ? H2); decompose; rewrite > H6;
            apply (ex_intro ? ? []); simplify; autobatch;]]
(* l = [] *)
|3: unfold raise_exn; simplify; intros; destruct H1;]
qed.
