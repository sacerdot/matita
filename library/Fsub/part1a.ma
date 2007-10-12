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

set "baseuri" "cic:/matita/test/Fsub/part1a/".
include "Fsub/defn.ma".

(*** Lemma A.1 (Reflexivity) ***)
theorem JS_Refl : ∀T,G.WFType G T → WFEnv G → G ⊢ T ⊴  T.
intros 3.elim H
  [apply SA_Refl_TVar [apply H2|assumption]
  |apply SA_Top [assumption|apply WFT_Top]
  |apply (SA_Arrow ? ? ? ? ? (H2 H5) (H4 H5))
  |apply (SA_All ? ? ? ? ? (H2 H5));intros;apply (H4 ? H6)
     [intro;apply H6;apply (fv_WFT ? ? ? (WFT_Forall ? ? ? H1 H3));
      simplify;autobatch
     |autobatch]]
qed.

(*
 * A slightly more general variant to lemma A.2.2, where weakening isn't
 * defined as concatenation of any two disjoint environments, but as
 * set inclusion.
 *)

lemma JS_weakening : ∀G,T,U.G ⊢ T ⊴ U → ∀H.WFEnv H → incl ? G H → H ⊢ T ⊴ U.
intros 4;elim H
  [apply (SA_Top ? ? H4);apply (WFT_env_incl ? ? H2 ? (incl_bound_fv ? ? H5))
  |apply (SA_Refl_TVar ? ? H4);apply (incl_bound_fv ? ? H5 ? H2)
  |apply (SA_Trans_TVar ? ? ? ? ? (H3 ? H5 H6));apply H6;assumption
  |apply (SA_Arrow ? ? ? ? ? (H2 ? H6 H7) (H4 ? H6 H7))
  |apply (SA_All ? ? ? ? ? (H2 ? H6 H7));intros;apply H4
     [unfold;intro;apply H8;apply (incl_bound_fv ? ? H7 ? H9)
     |apply (WFE_cons ? ? ? ? H6 H8);autobatch
     |unfold;intros;inversion H9;intros
        [destruct H11;rewrite > Hcut;apply in_Base
        |destruct H13;rewrite < Hcut1 in H10;apply in_Skip;apply (H7 ? H10)]]]
qed.

theorem narrowing:∀X,G,G1,U,P,M,N.
  G1 ⊢ P ⊴ U → (∀G2,T.G2@G1 ⊢ U ⊴ T → G2@G1 ⊢ P ⊴ T) → G ⊢ M ⊴ N →
  ∀l.G=l@(mk_bound true X U::G1) → l@(mk_bound true X P::G1) ⊢ M ⊴ N.
intros 10.elim H2
  [apply SA_Top
    [rewrite > H5 in H3;
     apply (WFE_Typ_subst ? ? ? ? ? ? ? H3 (JS_to_WFT1 ? ? ? H))
    |rewrite > H5 in H4;apply (WFT_env_incl ? ? H4);apply incl_fv_env]
  |apply SA_Refl_TVar
    [rewrite > H5 in H3;apply (WFE_Typ_subst ? ? ? ? ? ? ? H3);
     apply (JS_to_WFT1 ? ? ? H)
    |rewrite > H5 in H4;rewrite < fv_env_extends;apply H4]
  |elim (decidable_eq_nat X n)
    [apply (SA_Trans_TVar ? ? ? P)
      [rewrite < H7;elim l1;simplify
        [constructor 1|constructor 2;assumption]
      |rewrite > append_cons;apply H1;
       lapply (WFE_bound_bound true n t1 U ? ? H3)
        [apply (JS_to_WFE ? ? ? H4)
        |rewrite < Hletin;rewrite < append_cons;apply (H5 ? H6)
        |rewrite < H7;rewrite > H6;elim l1;simplify
          [constructor 1|constructor 2;assumption]]]
    |apply (SA_Trans_TVar ? ? ? t1)
      [rewrite > H6 in H3;apply (lookup_env_extends ? ? ? ? ? ? ? ? ? ? H3);
       unfold;intro;apply H7;symmetry;assumption
      |apply (H5 ? H6)]]
  |apply (SA_Arrow ? ? ? ? ? (H4 ? H7) (H6 ? H7))
  |apply (SA_All ? ? ? ? ? (H4 ? H7));intros;
   apply (H6 ? ? (mk_bound true X1 t2::l1))
      [rewrite > H7;rewrite > fv_env_extends;apply H8
      |simplify;rewrite < H7;reflexivity]]
qed.

lemma JS_trans_prova: ∀T,G1.WFType G1 T →
∀G,R,U.incl ? (fv_env G1) (fv_env G) → G ⊢ R ⊴ T → G ⊢ T ⊴ U → G ⊢ R ⊴ U.
intros 3;elim H;clear H; try autobatch;
  [rewrite > (JSubtype_Top ? ? H3);autobatch
  |generalize in match H7;generalize in match H4;generalize in match H2;
   generalize in match H5;clear H7 H4 H2 H5;
   generalize in match (refl_eq ? (Arrow t t1));
   elim H6 in ⊢ (? ? ? %→%); clear H6; intros; subst;
    [apply (SA_Trans_TVar ? ? ? ? H);apply (H4 ? ? H8 H9);autobatch
    |inversion H11;intros; subst; autobatch depth=4 width=4 size=9;
    ]
  |generalize in match H7;generalize in match H4;generalize in match H2;
   generalize in match H5;clear H7 H4 H2 H5;
   generalize in match (refl_eq ? (Forall t t1));elim H6 in ⊢ (? ? ? %→%);subst
     [apply (SA_Trans_TVar ? ? ? ? H);apply (H4 ? H7 H8 H9 H10);reflexivity
     |inversion H11;intros;subst
        [apply SA_Top
           [autobatch
              |apply WFT_Forall
                 [autobatch
                 |intros;lapply (H4 ? H13);autobatch]]
           |apply SA_All
              [autobatch paramodulation
              |intros;apply (H10 X)
                 [intro;apply H15;apply H8;assumption
                 |intro;apply H15;apply H8;apply (WFT_to_incl ? ? ? H3);
                  assumption
                 |simplify;autobatch
                 |apply (narrowing X (mk_bound true X t::l2) 
                         ? ? ? ? ? H7 ? ? [])
                    [intros;apply H9
                       [unfold;intros;lapply (H8 ? H17);rewrite > fv_append;
                        autobatch
                       |apply (JS_weakening ? ? ? H7)
                          [autobatch
                          |unfold;intros;autobatch]
                       |assumption]
                    |*:autobatch]
                 |autobatch]]]]]
qed.

theorem JS_trans : ∀G,T,U,V.G ⊢ T ⊴ U → G ⊢ U ⊴ V → G ⊢ T ⊴ V.
intros 5;apply (JS_trans_prova ? G);autobatch;
qed.

theorem JS_narrow : ∀G1,G2,X,P,Q,T,U.
                       (G2 @ (mk_bound true X Q :: G1)) ⊢ T ⊴ U → G1 ⊢ P ⊴ Q →
                       (G2 @ (mk_bound true X P :: G1)) ⊢ T ⊴ U.
intros;apply (narrowing ? ? ? ? ? ? ? H1 ? H) [|autobatch]
intros;apply (JS_trans ? ? ? ? ? H2);apply (JS_weakening ? ? ? H1);
     [autobatch|unfold;intros;autobatch]
qed.
