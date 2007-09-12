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

set "baseuri" "cic:/matita/Fsub/part1a/".
include "Fsub/defn.ma".

(*** Lemma A.1 (Reflexivity) ***)

theorem JS_Refl : ∀T,G.WFType G T → WFEnv G → G ⊢ T ⊴  T.
intros 3;elim H
  [apply (SA_Refl_TVar l n H2 H1);
  |apply (SA_Top l Top H1 (WFT_Top l));
  |apply (SA_Arrow l t t1 t t1 (H2 H5) (H4 H5))
  |apply (SA_All ? ? ? ? ? (H2 H5));intros;apply (H4 X H6)
     [intro;apply H6;apply (fv_WFT (Forall t t1) X l)
        [apply (WFT_Forall ? ? ? H1 H3)
        |simplify;autobatch]
     |autobatch]]
qed.

(* 
 * A slightly more general variant to lemma A.2.2, where weakening isn't
 * defined as concatenation of any two disjoint environments, but as
 * set inclusion.
 *)
 
lemma JS_weakening : \forall G,T,U.(JSubtype G T U) \to
                      \forall H.(WFEnv H) \to (incl ? G H) \to (JSubtype H T U).
intros 4;elim H
  [apply (SA_Top ? ? H4);lapply (incl_bound_fv ? ? H5);
   apply (WFT_env_incl ? ? H2 ? Hletin)
  |apply (SA_Refl_TVar ? ? H4);lapply (incl_bound_fv ? ? H5);
   apply (Hletin ? H2)
  |lapply (H3 ? H5 H6);lapply (H6 ? H1);
   apply (SA_Trans_TVar ? ? ? ? Hletin1 Hletin)
  |lapply (H2 ? H6 H7);lapply (H4 ? H6 H7);
   apply (SA_Arrow ? ? ? ? ? Hletin Hletin1)
  |lapply (H2 ? H6 H7);apply (SA_All ? ? ? ? ? Hletin);intros;apply H4
     [unfold;intro;apply H8;lapply (incl_bound_fv ? ? H7);apply (Hletin1 ? H9)
     |apply WFE_cons
        [1,2:assumption
        |apply (JS_to_WFT1 ? ? ? Hletin)]
     |unfold;intros;elim (in_cons_case ? ? ? ? H9)
        [rewrite > H10;apply in_Base
        |elim H10;apply (in_Skip ? ? ? ? ? H11);apply (H7 ? H12)]]]
qed.

lemma decidable_eq_Typ : \forall S,T:Typ.(S = T) ∨ (S ≠ T).
intro;elim S
  [elim T
     [elim (decidable_eq_nat n n1)
        [rewrite > H;left;reflexivity
        |right;intro;destruct H1;apply (H Hcut)]
     |2,3:right;intro;destruct H
     |*:right;intro;destruct H2]
  |elim T
     [2:elim (decidable_eq_nat n n1)
        [rewrite > H;left;reflexivity
        |right;intro;destruct H1;apply (H Hcut)]
     |1,3:right;intro;destruct H
     |*:right;intro;destruct H2]
  |elim T
     [3:left;reflexivity
     |1,2:right;intro;destruct H
     |*:right;intro;destruct H2]
  |elim T
     [1,2,3:right;intro;destruct H2
     |elim (H t2)
        [rewrite > H4;elim (H1 t3)
           [rewrite > H5;left;reflexivity
           |right;intro;apply H5;destruct H6;assumption]
        |right;intro;apply H4;destruct H5;assumption]
     |right;intro;destruct H4]
  |elim T
     [1,2,3:right;intro;destruct H2
     |right;intro;destruct H4
     |elim (H t2)
        [rewrite > H4;elim (H1 t3)
           [rewrite > H5;left;reflexivity
           |right;intro;apply H5;destruct H6;assumption]
        |right;intro;apply H4;destruct H5;assumption]]]
qed.

lemma decidable_eq_bound: ∀b1,b2:bound.(b1 = b2) ∨ (b1 ≠ b2).
intros;elim b1;elim b2;elim (decidable_eq_nat n n1)
  [rewrite < H;elim (decidable_eq_Typ t t1)
     [rewrite < H1;elim (bool_to_decidable_eq b b3)
        [rewrite > H2;left;reflexivity
        |right;intro;destruct H3;apply (H2 Hcut)]
     |right;intro;destruct H2;apply (H1 Hcut1)]
  |right;intro;destruct H1;apply (H Hcut1)]
qed.     

(* Lemma A.3 (Transitivity and Narrowing) *)

lemma JS_trans_narrow : \forall Q.
  (\forall G,T,U.
     (JSubtype G T Q) \to (JSubtype G Q U) \to 
     (JSubtype G T U)) \land
  (\forall G,H,X,P,M,N.
     (JSubtype (H @ ((mk_bound true X Q) :: G)) M N) \to
     (JSubtype G P Q) \to
     (JSubtype (H @ ((mk_bound true X P) :: G)) M N)).
apply Typ_len_ind;intros 2;
cut (\forall G,T,P. 
           (JSubtype G T U) \to 
           (JSubtype G U P) \to 
           (JSubtype G T P))
  [split
     [assumption
     |cut (\forall G,M,N.(JSubtype G M N) \to
           \forall G1,X,G2,P.
              (G = G2 @ ((mk_bound true X U) :: G1)) \to 
              (JSubtype G1 P U) \to 
              (JSubtype (G2 @ ((mk_bound true X P) :: G1)) M N))
        [intros;apply (Hcut1 ? ? ? H2 ? ? ? ? ? H3);reflexivity
        |intros;cut (incl ? (fv_env (G2 @ ((mk_bound true X U)::G1)))
                    (fv_env (G2 @ ((mk_bound true X P)::G1))))
           [intros;generalize in match H2;generalize in match Hcut1;
            generalize in match Hcut;generalize in match G2;elim H1
              [apply SA_Top
                 [rewrite > H8 in H4;lapply (JS_to_WFT1 ? ? ? H3);
                  apply (WFE_Typ_subst ? ? ? ? ? ? ? H4 Hletin)
                 |rewrite > H8 in H5;apply (WFT_env_incl ? ? H5 ? H7)]
              |apply SA_Refl_TVar
                 [rewrite > H8 in H4;apply (WFE_Typ_subst ? ? ? ? ? ? ? H4);
                  apply (JS_to_WFT1 ? ? ? H3)
                 |rewrite > H8 in H5;apply (H7 ? H5)]
              |elim (decidable_eq_nat X n)
                 [apply (SA_Trans_TVar ? ? ? P)
                    [rewrite < H10;elim l1
                      [simplify;constructor 1
                      |simplify;elim (decidable_eq_bound (mk_bound true X P) t2)
                         [rewrite < H12;apply in_Base
                         |apply (in_Skip ? ? ? ? ? H12);assumption]]
                   |apply H7
                      [lapply (H6 ? H7 H8 H9);lapply (JS_to_WFE ? ? ? Hletin);
                       apply (JS_weakening ? ? ? H3 ? Hletin1);unfold;intros;
                       elim l1
                         [simplify;
                          elim (decidable_eq_bound x (mk_bound true X P))
                            [rewrite < H12;apply in_Base
                            |apply (in_Skip ? ? ? ? ? H12);assumption]
                         |simplify;elim (decidable_eq_bound x t2)
                            [rewrite < H13;apply in_Base
                            |apply (in_Skip ? ? ? ? ? H13);assumption]]
                      |lapply (WFE_bound_bound true n t1 U ? ? H4)
                         [apply (JS_to_WFE ? ? ? H5)
                         |rewrite < Hletin;apply (H6 ? H7 H8 H9)
                         |rewrite > H9;rewrite > H10;elim l1;simplify
                            [constructor 1
                            |elim (decidable_eq_bound (mk_bound true n U) t2)
                               [rewrite > H12;apply in_Base
                               |apply (in_Skip ? ? ? ? ? H12);assumption]]]]]
                |apply (SA_Trans_TVar ? ? ? t1)
                   [rewrite > H9 in H4;
                    apply (lookup_env_extends ? ? ? ? ? ? ? ? ? ? H4);
                    unfold;intro;apply H10;symmetry;assumption
                   |apply (H6 ? H7 H8 H9)]]
             |apply SA_Arrow
                [apply (H5 ? H8 H9 H10)
                |apply (H7 ? H8 H9 H10)]
             |apply SA_All
                [apply (H5 ? H8 H9 H10)
                |intros;apply (H7 ? ? (mk_bound true X1 t2::l1) H8)
                   [rewrite > H10;cut ((fv_env (l1@(mk_bound true X P::G1))) =
                                       (fv_env (l1@(mk_bound true X U::G1))))
                      [unfold;intro;apply H11;rewrite > Hcut2;assumption
                      |elim l1
                         [simplify;reflexivity
                         |elim t4;simplify;rewrite > H12;reflexivity]]
                   |simplify;apply (incl_nat_cons ? ? ? H9)
                   |simplify;rewrite < H10;reflexivity]]]
          |cut ((fv_env (G2@(mk_bound true X U::G1))) =
                (fv_env (G2@(mk_bound true X P::G1))))
             [rewrite > Hcut1;unfold;intros;assumption
             |elim G2
                [simplify;reflexivity
                |elim t;simplify;rewrite > H4;reflexivity]]]]]
  |intros 4;generalize in match H;elim H1
     [inversion H5
        [intros;rewrite < H8;apply (SA_Top ? ? H2 H3)
        |intros;destruct H9
        |intros;destruct H10
        |*:intros;destruct H11]
     |assumption
     |apply (SA_Trans_TVar ? ? ? ? H2);apply (H4 H5 H6)
     |inversion H7
        [intros;apply (SA_Top ? ? H8);rewrite < H10;apply WFT_Arrow
           [apply (JS_to_WFT2 ? ? ? H2)
           |apply (JS_to_WFT1 ? ? ? H4)]
        |intros;destruct H11
        |intros;destruct H12
        |intros;destruct H13;apply SA_Arrow
              [rewrite > H12 in H2;rewrite < Hcut in H8;
               lapply (H6 t2)
                 [elim Hletin;apply (H15 ? ? ? H8 H2)
                 |apply (t_len_arrow1 t2 t3)]
              |rewrite > H12 in H4;rewrite < Hcut1 in H10;
               lapply (H6 t3)
                 [elim Hletin;apply (H15 ? ? ? H4 H10)
                 |apply (t_len_arrow2 t2 t3)]]
           |intros;destruct H13]
     |inversion H7
        [intros;apply (SA_Top ? ? H8);rewrite < H10;apply WFT_Forall
           [apply (JS_to_WFT2 ? ? ? H2)
           |intros;lapply (H4 ? H13);lapply (JS_to_WFT1 ? ? ? Hletin);
            apply (WFT_env_incl ? ? Hletin1);simplify;unfold;intros;
            assumption]
        |intros;destruct H11
        |intros;destruct H12
        |intros;destruct H13
        |intros;destruct H13;subst;apply SA_All
           [lapply (H6 t4)
              [elim Hletin;apply (H12 ? ? ? H8 H2)
              |apply t_len_forall1]
           |intros;(*destruct H12;*)subst;
            lapply (H6 (subst_type_nat t5 (TFree X) O))
              [elim Hletin;apply H13
                 [lapply (H6 t4)
                    [elim Hletin1;apply (H16 l1 [] X t6);
                       [simplify;apply H4;assumption
                       |assumption]
                    |apply t_len_forall1]
                 |apply (H10 ? H12)]
              |rewrite < eq_t_len_TFree_subst;
               apply t_len_forall2]]]]]
qed.

theorem JS_trans : \forall G,T,U,V.(JSubtype G T U) \to 
                                   (JSubtype G U V) \to
                                   (JSubtype G T V).
intros;elim JS_trans_narrow;autobatch;
qed.

theorem JS_narrow : \forall G1,G2,X,P,Q,T,U.
                       (JSubtype (G2 @ (mk_bound true X Q :: G1)) T U) \to
                       (JSubtype G1 P Q) \to
                       (JSubtype (G2 @ (mk_bound true X P :: G1)) T U).
intros;elim JS_trans_narrow;autobatch;
qed.
