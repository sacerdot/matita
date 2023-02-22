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

include "nat/plus.ma".
include "nat/compare.ma".
include "list/sort.ma".
include "datatypes/constructors.ma".

inductive Formula : Type ≝
   FTrue: Formula
 | FFalse: Formula
 | FAtom: nat → Formula
 | FAnd: Formula → Formula → Formula
 | FOr: Formula → Formula → Formula
 | FNot: Formula → Formula.

definition interp ≝ nat → bool.

let rec eval (interp:interp) F on F : bool ≝
 match F with
  [ FTrue ⇒ true
  | FFalse ⇒ false
  | FAtom n ⇒ interp n
  | FAnd f1 f2 ⇒ eval interp f1 ∧ eval interp f2
  | FOr f1 f2 ⇒ eval interp f1 ∨ eval interp f2
  | FNot f ⇒ ¬ eval interp f
  ].

inductive not_nf : Formula → Prop ≝
   NTrue: not_nf FTrue
 | NFalse: not_nf FFalse
 | NAtom: ∀n. not_nf (FAtom n)
 | NAnd: ∀f1,f2. not_nf f1 → not_nf f2 → not_nf (FAnd f1 f2)
 | NOr: ∀f1,f2. not_nf f1 → not_nf f2 → not_nf (FOr f1 f2)
 | NNot: ∀n.not_nf (FNot (FAtom n)).

let rec negate F ≝
 match F with
  [ FTrue ⇒ FFalse
  | FFalse ⇒ FTrue
  | FAtom n ⇒ FNot (FAtom n)
  | FAnd f1 f2 ⇒ FOr (negate f1) (negate f2)
  | FOr f1 f2 ⇒ FAnd (negate f1) (negate f2)
  | FNot f ⇒ elim_not f]
and elim_not F ≝
 match F with
  [ FTrue ⇒ FTrue
  | FFalse ⇒ FFalse
  | FAtom n ⇒ FAtom n
  | FAnd f1 f2 ⇒ FAnd (elim_not f1) (elim_not f2)
  | FOr f1 f2 ⇒ FOr (elim_not f1) (elim_not f2)
  | FNot f ⇒ negate f
  ].

theorem not_nf_elim_not: ∀F.not_nf (elim_not F) ∧ not_nf (negate F).
 intros;
 elim F;
  [1,2,3: simplify; autobatch
  |4,5:
   simplify;
   elim H; clear H;
   elim H1; clear H1;
   split;
   autobatch
  |elim H; clear H;
   split;
   [ assumption 
   | assumption
   ]
  ]
qed.

theorem demorgan1: ∀b1,b2:bool. (¬ (b1 ∧ b2)) = ¬ b1 ∨ ¬ b2.
 intros;
 elim b1;
 simplify;
 reflexivity.
qed.

theorem demorgan2: ∀b1,b2:bool. (¬ (b1 ∨ b2)) = ¬ b1 ∧ ¬ b2.
 intros;
 elim b1;
 simplify;
 reflexivity.
qed.

theorem eq_notb_notb_b_b: ∀b:bool. (¬ ¬ b) = b.
 intro;
 elim b;
 reflexivity.
qed.

theorem eq_eval_elim_not_eval:
 ∀i,F. eval i (elim_not F) = eval i F ∧ eval i (negate F) = eval i (FNot F).
 intros;
 elim F;
  [1,2,3: split; reflexivity
  |4,5:
   simplify;
   elim H; clear H;
   elim H1; clear H1;
   split;
    [1,3: autobatch
    |replace with ((eval i (FNot f) ∨ eval i (FNot f1)) = ¬ (eval i f ∧ eval i f1));
     [ simplify;
       autobatch
     | autobatch
     ]
    |replace with ((eval i (FNot f) ∧ eval i (FNot f1)) = ¬ (eval i f ∨ eval i f1));
     [ simplify;
       autobatch
     | autobatch
     ]
    ]
  |elim H; clear H;
   split;
    [ assumption
    | change with (eval i (elim_not f) = ¬ ¬ eval i f);
      autobatch
    ]
  ]
qed.

definition sequent ≝ (list Formula) × (list Formula).

inductive derive: sequent → Prop ≝
   ExchangeL: ∀l,l1,l2,f. derive 〈f::l1@l2,l〉 → derive 〈l1 @ [f] @ l2,l〉
 | ExchangeR: ∀l,l1,l2,f. derive 〈l,f::l1@l2〉 → derive 〈l,l1 @ [f] @ l2〉
 | Axiom: ∀l1,l2,f. derive 〈f::l1, f::l2〉
 | TrueR: ∀l1,l2. derive 〈l1,FTrue::l2〉
 | FalseL: ∀l1,l2. derive 〈FFalse::l1,l2〉
 | AndR: ∀l1,l2,f1,f2.
    derive 〈l1,f1::l2〉 → derive 〈l1,f2::l2〉 →
     derive 〈l1,FAnd f1 f2::l2〉
 | AndL: ∀l1,l2,f1,f2.
    derive 〈f1 :: f2 :: l1,l2〉 → derive 〈FAnd f1 f2 :: l1,l2〉
 | OrL: ∀l1,l2,f1,f2.
    derive 〈f1::l1,l2〉 → derive 〈f2::l1,l2〉 →
     derive 〈FOr f1 f2 :: l1,l2〉
 | OrR: ∀l1,l2,f1,f2.
    derive 〈l1,f1 :: f2 :: l2〉 → derive 〈l1,FOr f1 f2 :: l2〉
 | NotR: ∀l1,l2,f.
    derive 〈f::l1,l2〉 → derive 〈l1,FNot f :: l2〉
 | NotL: ∀l1,l2,f.
    derive 〈l1,f::l2〉 → derive 〈FNot f :: l1,l2〉.

let rec and_of_list l ≝
 match l with
  [ nil ⇒ FTrue
  | cons F l' ⇒ FAnd F (and_of_list l')
  ].

let rec or_of_list l ≝
 match l with
  [ nil ⇒ FFalse
  | cons F l' ⇒ FOr F (or_of_list l')
  ].

definition formula_of_sequent ≝
 λs.match s with [pair l1 l2 ⇒ FOr (FNot (and_of_list l1)) (or_of_list l2)].

definition is_tautology ≝
 λF. ∀i. eval i F = true.
 
axiom assoc_orb: associative ? orb.
axiom symm_orb: symmetric ? orb.
axiom orb_not_b_b: ∀b:bool. (¬b ∨ b) = true.
axiom distributive_orb_andb: distributive ? orb andb.
axiom symm_andb: symmetric ? andb.
axiom associative_andb: associative ? andb.
axiom distributive_andb_orb: distributive ? andb orb.

lemma andb_true: ∀x.(true ∧ x) = x. intro; reflexivity. qed. 

lemma and_of_list_permut:
 ∀i,f,l1,l2. eval i (and_of_list (l1 @ (f::l2))) = eval i (and_of_list (f :: l1 @ l2)).
 intros;
 elim l1;
  [ simplify;
    reflexivity
  | simplify in H ⊢ %;
    rewrite > H;
    autobatch paramodulation
  ]
qed. 

lemma or_of_list_permut:
 ∀i,f,l1,l2. eval i (or_of_list (l1 @ (f::l2))) = eval i (or_of_list (f :: l1 @ l2)).
 intros;
 elim l1;
  [ simplify;
    reflexivity
  | simplify in H ⊢ %;
    rewrite > H;
    autobatch paramodulation
  ]
qed. 

theorem soundness: ∀F. derive F → is_tautology (formula_of_sequent F).
 intros;
 elim H;
  [ simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    rewrite > and_of_list_permut;
    simplify;
    autobatch
  | simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    rewrite > or_of_list_permut;
    simplify;
    autobatch
  | simplify;
    intro;
    rewrite > demorgan1;
    rewrite < assoc_orb;
    rewrite > assoc_orb in ⊢ (? ? (? % ?) ?);
    rewrite > symm_orb in ⊢ (? ? (? (? ? %) ?) ?);
    rewrite < assoc_orb;
    rewrite > orb_not_b_b;
    reflexivity
  | simplify;
    intros;
    rewrite > symm_orb;
    reflexivity
  | simplify;
    intros;
    reflexivity
  | simplify in H2 H4 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    lapply (H4 i); clear H4;
    rewrite > symm_orb in ⊢ (? ? (? ? %) ?);
    rewrite > distributive_orb_andb;
    demodulate.
    reflexivity.
    (*
    autobatch paramodulation
      by distributive_orb_andb,symm_orb,symm_orb, 
         Hletin, Hletin1,andb_true.
    *)
  | simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    pump 100. pump 100.
    demodulate.
    reflexivity. 
    (* autobatch paramodulation by andb_assoc, Hletin. *) 
  | simplify in H2 H4 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    lapply (H4 i); clear H4;
    rewrite > symm_andb;
    rewrite > distributive_andb_orb;
    rewrite > demorgan2;
    rewrite > symm_orb;
    rewrite > distributive_orb_andb;
    demodulate.
    reflexivity.
    (* autobatch paramodulation by symm_andb,symm_orb,andb_true,Hletin,Hletin1. *)
  | simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    autobatch paramodulation;
  | simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    autobatch paramodulation
  | simplify in H2 ⊢ %;
    intros;
    lapply (H2 i); clear H2;
    autobatch paramodulation
  ]
qed.

alias num (instance 0) = "natural number".
let rec size F ≝
 match F with
  [ FTrue ⇒ 0
  | FFalse ⇒ 0
  | FAtom n ⇒ 0
  | FAnd f1 f2 ⇒ S (size f1 + size f2)
  | FOr f1 f2 ⇒ S (size f1 + size f2)
  | FNot f ⇒ S (size f)
  ].

let rec sizel l ≝
 match l with
  [ nil ⇒ 0
  | cons F l' ⇒ size F + sizel l'
  ].

definition size_of_sequent ≝
 λS.match S with [ pair l r ⇒ sizel l + sizel r].

axiom weakeningR:
 ∀l1,l2,F. derive 〈l1,l2〉 → derive 〈l1,F::l2〉.

definition same_atom : Formula → Formula → bool.
 intros;
 elim f;
  [3: elim f1;
       [3: apply (eqb n n1)
       |*: apply false
       ]
  |*: apply false
  ]
qed.

definition symmetricb ≝
 λA:Type.λeq:A → A → bool. ∀x,y. eq x y = eq y x.

theorem symmetricb_eqb: symmetricb ? eqb.
 intro;
 elim x;
 elim y;
  [1,2,3: reflexivity
  | simplify;
    autobatch
  ]
qed.

theorem symmetricb_same_atom: symmetricb ? same_atom.
 intro;
 elim x;
  [3:
    elim y;
     [3:
       simplify;
       apply symmetricb_eqb
     |*: reflexivity
     ]
  |*: elim y; reflexivity
  ]
qed.

definition transitiveb ≝
 λA:Type.λeq:A → A → bool.
  ∀x,y,z. eq x y = true → eq y z = eq x z.

theorem transitiveb_same_atom: transitiveb ? same_atom.
 intro;
 elim x 0;
  [3:
    intros 2;
    elim y 0;
     [3:
       intros 3;
       simplify in H;
       rewrite > (eqb_true_to_eq ? ? H);
       reflexivity
     |1,2:
       intros;
       simplify in H;
       destruct H
     |4,5:
       intros;
       simplify in H2;
       destruct H2
     | intros;
       simplify in H1;
       destruct H1
     ]
  |1,2:
    intros;
    simplify in H;
    destruct H
  |4,5:
    intros;
    simplify in H2;
    destruct H2
  | intros;
    simplify in H1;
    destruct H1
  ]
qed.

theorem eq_to_eq_mem:
 ∀A.∀eq: A → A → bool.transitiveb ? eq →
  ∀x,y,l.eq x y = true → mem ? eq x l = mem ? eq y l.
 intros;
 elim l;
  [ reflexivity
  | simplify;
    rewrite > (H ? ? ? H1);
    rewrite > H2;
    reflexivity
  ]
qed.

theorem mem_to_exists_l1_l2:
 ∀A,eq,n,l. (∀x,y. eq x y = true → x = y) → mem A eq n l = true → ∃l1,l2. l = l1 @ (n :: l2).
 intros 4;
 elim l;
  [ simplify in H1;
    destruct H1
  | simplify in H2;
    apply (bool_elim ? (eq n a));
    intro;
     [ apply (ex_intro ? ? []);
       apply (ex_intro ? ? l1);
       simplify;
       rewrite > (H1 ? ? H3);
       reflexivity
     | rewrite > H3 in H2;
       simplify in H2;
       elim (H H1 H2);
       elim H4;
       rewrite > H5;
       apply (ex_intro ? ? (a::a1));
       apply (ex_intro ? ? a2);
       simplify;
       reflexivity
     ]
  ]
qed.

lemma same_atom_to_eq: ∀f1,f2. same_atom f1 f2 = true → f1=f2.
 intro;
 elim f1;
  [1,2:
    simplify in H;
    destruct H
  | elim f2 in H ⊢ %;
     [1,2:
       simplify in H;
       destruct H
     | simplify in H;
       rewrite > (eqb_true_to_eq ? ? H);
       reflexivity
     |4,5:
       simplify in H2;
       destruct H2
     | simplify in H1;
       destruct H1
     ]
  |4,5:
    simplify in H2;
    destruct H2
  |6:
    simplify in H1;
    destruct H1
  ]
qed.

lemma same_atom_to_exists: ∀f1,f2. same_atom f1 f2 = true → ∃n. f1 = FAtom n.
 intro;
 elim f1;
  [1,2:
    simplify in H;
    destruct H
  | autobatch
  |4,5:
    simplify in H2;
    destruct H2
  | simplify in H1;
    destruct H1
  ]
qed.

lemma mem_same_atom_to_exists:
 ∀f,l. mem ? same_atom f l = true → ∃n. f = FAtom n.
 intros 2;
 elim l;
  [ simplify in H;
    destruct H
  | simplify in H1;
    apply (bool_elim ? (same_atom f a));
    intros;
     [ elim (same_atom_to_exists ? ? H2);
       autobatch
     | rewrite > H2 in H1;
       simplify in H1;
       elim (H H1);
       autobatch
     ]
  ]
qed.
  
lemma look_for_axiom:
 ∀l1,l2.
  (∃n,ll1,ll2,lr1,lr2. l1 = ll1 @ (FAtom n :: ll2) ∧ l2 = lr1 @ (FAtom n :: lr2))
  ∨ ∀n1. (mem ? same_atom (FAtom n1) l1 ∧ mem ? same_atom (FAtom n1) l2) = false.
 intro;
 elim l1 1; clear l1;
  [ intros;
    right;
    intros;
    simplify;
    reflexivity
  | intros;
    generalize in match (refl_eq ? (mem ? same_atom a l2));
    elim (mem ? same_atom a l2) in ⊢ (? ? ? %→?);
     [ left;
       elim (mem_to_exists_l1_l2 ? ? ? ? same_atom_to_eq H1);
       elim H2; clear H2;
       elim (mem_same_atom_to_exists ? ? H1);
       rewrite > H2 in H3;
       apply (ex_intro ? ? a3);
       rewrite > H2;
       apply (ex_intro ? ? []);
       simplify;
       autobatch depth=5
     | elim (H l2);
        [ left;
          decompose;
          apply (ex_intro ? ? a1);
          apply (ex_intro ? ? (a::a2));
          simplify;
          apply (ex_intro ? ? a3);
          apply (ex_intro ? ? a4);
          autobatch depth=4
        | right;
          intro;
          apply (bool_elim ? (same_atom a (FAtom n1)));
           [ intro;
             rewrite > (eq_to_eq_mem ? ? transitiveb_same_atom ? ? ? H3) in H1;
             rewrite > H1;
             autobatch
           | intro;
             change in ⊢ (? ? (? % ?) ?) with
              (match same_atom (FAtom n1) a with
                [true ⇒ true
                |false ⇒ mem ? same_atom (FAtom n1) l
                ]);
             rewrite > symmetricb_same_atom;
             rewrite > H3;
             simplify;
             apply H2
           ]
        ]
     ]
  ]
qed.

lemma eq_plus_n_m_O_to_eq_m_O: ∀n,m.n+m=0 → m=0.
 intros 2;
 elim n;
  [ assumption
  | simplify in H1;
    destruct H1
  ]
qed.

lemma not_eq_nil_append_cons: ∀A.∀l1,l2.∀x:A.¬ [] = l1 @ (x :: l2).
 intros;
 elim l1;
 simplify;
 intro;
  [ destruct H
  | destruct H1
  ]
qed.

(*lemma foo: ∀x,l.
 (¬eval
   (λn:nat
    .match eqb n x with 
     [true⇒true|false⇒mem Formula same_atom (FAtom n) l]) (and_of_list l)) =
 (¬eval
   (λn:nat.mem Formula same_atom (FAtom n) l) (and_of_list l)).
 intros;
 elim l;
  [ reflexivity
  | simplify in ⊢ (? ? (? (? ? %)) ?);
    change in ⊢ (? ? (? %) ?) with
     (eval (λn:nat
      .match eqb n x in bool return λb:bool.bool with 
       [true⇒true|false⇒mem Formula same_atom (FAtom n) (t::l1)]) t
      ∧
      eval (λn:nat
      .match eqb n x in bool return λb:bool.bool with 
       [true⇒true|false⇒mem Formula same_atom (FAtom n) (t::l1)])
      (and_of_list l1));
    

  ]
qed.*)

axiom daemon: False.

lemma sizel_0_no_axiom_is_tautology:
 ∀l1,l2. size_of_sequent 〈l1,l2〉 = 0 → is_tautology (formula_of_sequent 〈l1,l2〉) →
  (∀n. (mem ? same_atom (FAtom n) l1 ∧ mem ? same_atom (FAtom n) l2) = false) →   
   (∃ll1,ll2. l1 = ll1 @ (FFalse :: ll2)) ∨ (∃ll1,ll2. l2 = ll1 @ (FTrue :: ll2)).
 intros;
 lapply (H1 (λn.mem ? same_atom (FAtom n) l1)); clear H1;
 simplify in Hletin;  
 elim l1 in Hletin H2 H ⊢ % 0;
  [ intros;
    simplify in H2;
    elim l2 in H2 H1 H ⊢ % 0;
     [ intros;
       simplify in H2;
       destruct H2
     | simplify;
       intro;
       elim a;
        [ right;
          apply (ex_intro ? ? []);
          simplify;
          autobatch
        | simplify in H3;
          simplify in H1;
          elim H;
           [ elim H4;
             elim H5;
             elim (not_eq_nil_append_cons ? ? ? ? H6)
           | elim H4;
             right;
             apply (ex_intro ? ? (FFalse::a1));
             simplify;
             elim H5;
             apply (ex_intro ? ? a2);
             autobatch
           |3,4: autobatch
           | assumption
           ]
        | simplify in H1 H3;
          elim (H H1 H2 H3); clear H;
           [ elim H4;
             elim H;
             elim (not_eq_nil_append_cons ? ? ? ? H5)
           | right;
             elim H4;
             apply (ex_intro ? ? (FAtom n::a1));
             simplify;
             elim H;
             autobatch
           ]
        |4,5:
          simplify in H3;
          destruct H3
        | simplify in H2;
          destruct H2
        ]
     ]
  | intro;
     elim a;
     [ elim H;
        [ left;
          elim H4;
          apply (ex_intro ? ? (FTrue::a1));
          simplify;
          elim H5;
          autobatch
        | right;
          assumption
        | assumption
        | lapply (H2 n); clear H2;
          simplify in Hletin;
          assumption
        | simplify in H3;
          assumption
        ] 
     | left;
       apply (ex_intro ? ? []);
       simplify;
       autobatch
     | elim H;
        [ left;
          elim H4;
          apply (ex_intro ? ? (FAtom n::a1));
          simplify;
          elim H5;
          autobatch
        | right;
          assumption
        | assumption
        | lapply (H2 n1); clear H2;
          simplify in Hletin;
          elim (eqb n1 n) in Hletin ⊢ %;
           [ simplify in H2;
             rewrite > H2;
             autobatch
           | simplify in H2;
             assumption
           ]
        | simplify in H2;
          lapply (H2 n); clear H2;
          rewrite > eqb_n_n in Hletin;
          simplify in Hletin;
          simplify in H3;
          rewrite > eqb_n_n in H3;
          simplify in H3;
(*
          elim l in H3 H1 H ⊢ % 0;
           [ elim l2 0;
              [ intros;
                simplify in H2;
                destruct H2
              | intros;
                simplify in H4 ⊢ %;
                simplify in H;
                rewrite > H;
                 [ autobatch
                 | intros;
                   apply H1;
                 | simplify in H2;
                   apply (eq_plus_n_m_O_to_eq_m_O ? ? H2)
                 | 
                 ]
                    
                 [ autobatch
                 | elim t1 in H4 H2 ⊢ %;
                    [
                    |
                    |
                    |4,5:
                      simplify in H5;
                      destruct H5
                    | simplify in H4;
                      destruct H4
                    ] 
                 ]
              ]
           |
           ]
*) elim daemon
        ]
     |4,5:
       simplify in H3;
       destruct H3
     | simplify in H2;
       destruct H2
     ]
  ]
qed.

lemma completeness_base:
 ∀S. size_of_sequent S = 0 → is_tautology (formula_of_sequent S) → derive S.
 intro;
 elim S 1; clear S;
 simplify in ⊢ (?→%→?);
 intros;
 elim (look_for_axiom a b);
  [ decompose;
    rewrite > H2; clear H2;
    rewrite > H4; clear H4;
    apply (ExchangeL ? a2 a3 (FAtom a1));
    apply (ExchangeR ? a4 a5 (FAtom a1));
    apply Axiom 
  | elim (sizel_0_no_axiom_is_tautology a b H H1 H2);
     [ decompose;
       rewrite > H3;
       apply (ExchangeL ? a1 a2 FFalse);
       apply FalseL
     | decompose;
       rewrite > H3;
       apply (ExchangeR ? a1 a2 FTrue);
       apply TrueR
     ]
  ]
qed.

(*
lemma completeness_step:
 ∀l1,l2,n. size_of_sequent 〈l1,l2〉 = S n →
   (∃ll1,ll2,f. l1 = ll1 @ (f::ll2) ∧ size f > 0) ∨
   (∃ll1,ll2,f. l2 = ll1 @ (f::ll2) ∧ size f > 0).
 intros 3;
 elim l1 0;
  [ elim l2 0;
     [ intros;
       simplify in H;
       destruct H 
     | intros 3;
       elim t;
        [ elim (H H1);
           [ left;
             assumption
           | right;
             decompose;
             apply (ex_intro ? ? (FTrue::a));
             simplify;
             autobatch depth=5
           ]
        | elim (H H1);
           [ left;
             assumption
           | right;
             decompose;
             apply (ex_intro ? ? (FFalse::a));
             simplify;
             autobatch depth=5
           ]
        | elim (H H1);
           [ left;
             assumption
           | right;
             decompose;
             apply (ex_intro ? ? (FAtom n1::a));
             simplify;
             autobatch depth=5
           ]
        | right;
          apply (ex_intro ? ? []);
          simplify;
          apply (ex_intro ? ? l);
          apply (ex_intro ? ? (FAnd f f1));
          simplify;
          split;
           [ reflexivity
           | unfold gt;
             autobatch
           ]
        | right;
          apply (ex_intro ? ? []);
          simplify;
          apply (ex_intro ? ? l);
          apply (ex_intro ? ? (FOr f f1));
          simplify;
          split;
           [ reflexivity
           | unfold gt;
             autobatch
           ]
        | right;
          apply (ex_intro ? ? []);
          simplify;
          apply (ex_intro ? ? l);
          apply (ex_intro ? ? (FNot f));
          simplify;
          split;
           [ reflexivity
           | unfold gt;
             autobatch
           ]
        ]
     ]
  | intros 2;
    elim t;
     [1,2:(*,2,3:*)
       elim (H H1);
       decompose;
        [ left;
          autobatch depth=5
        | right;
          autobatch depth=5
        ]
     | left;
       apply (ex_intro ? ? []);
       simplify;
       apply (ex_intro ? ? l);
       apply (ex_intro ? ? (FAnd f f1));
       unfold gt;
       simplify;
       autobatch
     | left;
       apply (ex_intro ? ? []);
       simplify;
       apply (ex_intro ? ? l);
       apply (ex_intro ? ? (FOr f f1));
       unfold gt;
       simplify;
       autobatch
     | left;
       apply (ex_intro ? ? []);
       simplify;
       apply (ex_intro ? ? l);
       apply (ex_intro ? ? (FNot f));
       unfold gt;
       simplify;
       autobatch
     ]
  ]
qed.

theorem completeness: ∀S. is_tautology (formula_of_sequent S) → derive S.
 intro;
 generalize in match (refl_eq ? (size_of_sequent S));
 elim (size_of_sequent S) in ⊢ (? ? ? %→?);
  [ apply completeness_base;
    assumption
  | 
  ]
qed. 
 
 elim F;
  [ autobatch
  | simplify in H;
    lapply (H (λx.true));
    destruct Hletin
  | simplify in H;
    lapply (H (λx.false));
    destruct Hletin
  | apply AndR;
     [ apply H;
       intro;
       lapply (H2 i); clear H2;
       simplify in Hletin;
       autobatch
     | apply H1;
       intro;
       lapply (H2 i); clear H2;
       simplify in Hletin;
       autobatch
     ]
  | apply OrR;
    simplify in H2;
  | apply NotR;
    simplify in H1;
*)
