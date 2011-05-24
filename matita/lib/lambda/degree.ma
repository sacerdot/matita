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

include "lambda/ext_lambda.ma".

(* DEGREE ASSIGNMENT **********************************************************)

(* The degree of a term *******************************************************)

(* degree assigned to the term t in the environment L *)
let rec deg L t on t ≝ match t with
   [ Sort i     ⇒ i + 3
   | Rel i      ⇒ (nth i … L 0) - 1
   | App m _    ⇒ deg L m 
   | Lambda n m ⇒ let l ≝ deg L n in deg (l::L) m
   | Prod n m   ⇒ let l ≝ deg L n in deg (l::L) m
   | D m        ⇒ deg L m
   ].

interpretation "degree assignment (term)" 'IInt1 t L = (deg L t).

lemma deg_app: ∀m,n,L. ║App m n║_[L] = ║m║_[L].
// qed.

lemma deg_lambda: ∀n,m,L. ║Lambda n m║_[L] = ║m║_[║n║_[L]::L].
// qed.

lemma deg_prod: ∀n,m,L. ║Prod n m║_[L] = ║m║_[║n║_[L]::L].
// qed.

lemma deg_rel_lt: ∀LK,L,i. (S i) ≤ |L| → ║Rel i║_[L @ LK] = ║Rel i║_[L].
#LK #L elim L -L [1: #i #Hie elim (not_le_Sn_O i) #Hi elim (Hi Hie) ]
#l #L #IHL #i elim i -i // #i #_ #Hie @IHL @le_S_S_to_le @Hie
qed.

lemma deg_rel_not_le: ∀K,L,i. (S i) ≰ |L| →
                      ║Rel i║_[L @ K] = ║Rel (i-|L|)║_[K].
#K #L elim L -L [ normalize // ]
#l #L #IHL #i elim i -i [1: -IHL #Hie elim Hie -Hie #Hie; elim (Hie ?) /2/ ]
normalize #i #_ #Hie @IHL /2/
qed.

(* weakeing and thinning lemma for the degree assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma deg_lift: ∀p,L,Lp. p = |Lp| → ∀t,k,Lk. k = |Lk| →
                ║lift t k p║_[Lk @ Lp @ L] = ║t║_[Lk @ L].
#p #L #Lp #HLp #t elim t -t //
   [ #i #k #Lk #HLk @(leb_elim (S i) k) #Hik
     [ >(lift_rel_lt … Hik) >HLk in Hik #Hik
       >(deg_rel_lt … Hik) >(deg_rel_lt … Hik) //
     | >(lift_rel_not_le … Hik) >HLk in Hik #Hik
       >(deg_rel_not_le … Hik) <associative_append
       >(deg_rel_not_le …) >length_append >HLp;
       [ >arith2 // @not_lt_to_le /2/ | @(arith3 … Hik) ]
     ]
   | #m #n #IHm #_ #k #Lk #HLk >lift_app >deg_app /3/
   | #n #m #IHn #IHm #k #Lk #HLk >lift_lambda >deg_lambda
     >IHn // >(IHm … (? :: ?)) // >commutative_plus /2/
   | #n #m #IHn #IHm #k #Lk #HLk >lift_prod >deg_prod
     >IHn // >(IHm … (? :: ?)) // >commutative_plus /2/
   | #m #IHm #k #Lk #HLk >IHm //
   ]
qed.

lemma deg_lift_1: ∀t,N,L. ║lift t 0 1║_[N :: L] = ║t║_[L].
#t #N #L >(deg_lift ?? ([?]) … ([]) …) //
qed.

(* substitution lemma for the degree assignment *)
(* NOTE: >commutative_plus comes from |a::b| ↦ S |b| rather than |b| + 1 *)
lemma deg_subst: ∀v,L,t,k,Lk. k = |Lk| → 
                 ║t[k≝v]║_[Lk @ L] = ║t║_[Lk @ ║v║_[L]+1::L].
#v #L #t elim t -t //
   [ #i #k #Lk #HLk @(leb_elim (S i) k) #H1ik
     [ >(subst_rel1 … H1ik) >HLk in H1ik #H1ik
       >(deg_rel_lt … H1ik) >(deg_rel_lt … H1ik) //
     | @(eqb_elim i k) #H2ik
       [ >H2ik in H1ik -H2ik i #H1ik >subst_rel2 >HLk in H1ik #H1ik
         >(deg_rel_not_le … H1ik) <minus_n_n >(deg_lift ? ? ? ? ? ? ([])) normalize //
       | lapply (arith4 … H1ik H2ik) -H1ik H2ik #Hik >(subst_rel3 … Hik)
         >deg_rel_not_le; [2: /2/ ] <(associative_append ? ? ([?]) ?)
         >deg_rel_not_le >length_append >commutative_plus;
         [ <minus_plus // | <HLk -HLk Lk @not_le_to_not_le_S_S /3/ ]
       ]
     ]
   | #m #n #IHm #_ #k #Lk #HLk >subst_app >deg_app /3/
   | #n #m #IHn #IHm #k #Lk #HLk >subst_lambda > deg_lambda
     >IHn // >commutative_plus in ⊢ (??(? ? %)?) >(IHm … (? :: ?)) /2/
   | #n #m #IHn #IHm #k #Lk #HLk >subst_prod > deg_prod
     >IHn // >commutative_plus in ⊢ (??(? ? %)?) >(IHm … (? :: ?)) /2/
   | #m #IHm #k #Lk #HLk >IHm //
   ]
qed.

lemma deg_subst_0: ∀t,v,L. ║t[0≝v]║_[L] = ║t║_[║v║_[L]+1::L].
#t #v #L >(deg_subst ???? ([])) //
qed.

(* The degree context  ********************************************************)

(* degree context assigned to the type context G *)
let rec Deg G ≝ match G with
   [ nil      ⇒ nil …
   | cons t F ⇒ let H ≝ Deg F in ║t║_[H] :: H
   ].

interpretation "degree assignment (type context)" 'IInt G = (Deg G).
