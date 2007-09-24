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
intros 3;elim H;clear H
  [apply (JS_trans_TFree ? ? ? H3 ? H4)
  |rewrite > (JSubtype_Top ? ? H3);apply SA_Top;autobatch
  |cut (∃T.T = Arrow t t1) as Htriv
     [elim Htriv;clear Htriv;rewrite < H in H6;rewrite < H in H7;
      generalize in match H7;generalize in match H4;generalize in match H2;
      generalize in match H5;generalize in match H;clear H7 H4 H2 H5 H;elim H6
        [1,2:destruct H4
        |apply (SA_Trans_TVar ? ? ? ? H);apply (H4 H5 H7 H8 H9);assumption
        |inversion H11;intros
           [apply SA_Top;rewrite < H14;autobatch
           |destruct H15
           |destruct H16
           |destruct H17;apply SA_Arrow;rewrite < H16;destruct H7
              [apply H9
                 [autobatch
                 |rewrite < Hcut2;rewrite > Hcut;rewrite > H16;assumption
                 |rewrite < Hcut2;assumption]
              |apply H10
                 [autobatch
                 |rewrite < Hcut3;rewrite < Hcut1;rewrite < H16;assumption
                 |rewrite > H16;rewrite < Hcut3;rewrite > Hcut1;assumption]]
           |destruct H17]
        |destruct H7]
     |apply (ex_intro ? ? (Arrow t t1));reflexivity]
  |cut (∃T.T = Forall t t1) as Htriv
     [elim Htriv;clear Htriv;rewrite < H in H7;rewrite < H in H6.
      generalize in match H7;generalize in match H4;generalize in match H2;
      generalize in match H5;generalize in match H;clear H7 H4 H2 H5 H;
      elim H6
        [1,2:destruct H4
        |apply (SA_Trans_TVar ? ? ? ? H);apply (H4 H5 H7 H8 H9 H10)
        |destruct H7
        |inversion H11;intros
           [apply SA_Top
              [assumption
              |rewrite < H14;apply WFT_Forall
                 [autobatch
                 |intros;lapply (H4 ? H17);autobatch]]
           |destruct H15
           |destruct H16
           |destruct H17
           |destruct H17;apply SA_All;destruct H7
              [rewrite < H16;apply H9;
                 [autobatch
                 |rewrite < Hcut2;rewrite > Hcut;rewrite > H16;assumption
                 |rewrite < Hcut2. assumption]
              |intros;apply (H10 X)
                 [intro;apply H19;rewrite < H16;apply H8;assumption
                 |intro;apply H19;rewrite < H16;apply H8;
                  apply (WFT_to_incl ? ? ? H3);assumption
                 |simplify;apply incl_cons;rewrite < H16;assumption
                 |apply (narrowing X ((mk_bound true X t6)::l2) 
                            ? ? ? ? ? H12 ? ? [])
                    [intros;apply H9
                       [unfold;intros;lapply (H8 ? H21);rewrite < H16;
                        rewrite > fv_append;autobatch
                       |rewrite < Hcut2;rewrite > Hcut;
                        apply (JS_weakening ? ? ? H12)
                          [autobatch
                          |unfold;intros;autobatch]
                       |rewrite < Hcut2;rewrite > Hcut;assumption]
                    |rewrite < Hcut;rewrite < Hcut3;rewrite < H16;apply H4;
                     rewrite > H16;assumption
                    |reflexivity]
                 |rewrite < Hcut3;rewrite > Hcut1;apply H14;assumption]]]]
     |apply (ex_intro ? ? (Forall t t1));reflexivity]]
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
