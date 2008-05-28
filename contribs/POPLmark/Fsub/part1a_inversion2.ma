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

include "Fsub/defn2.ma".

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
        [destruct H11;apply in_list_head
        |destruct H13;apply in_list_cons;apply (H7 ? H10)]]]
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

lemma JSubtype_inv:
 ∀G:list bound.∀T1,T:Typ.
  ∀P:list bound → Typ → Prop.
   (∀t. WFEnv G → WFType G t → T=Top → P G t) →
   (∀n. T=TFree n → P G (TFree n)) →
   (∀n,t1.
    (mk_bound true n t1) ∈ G → G ⊢ t1 ⊴ T → P G t1 → P G (TFree n)) →
   (∀s1,s2,t1,t2. G ⊢ t1 ⊴ s1 → G ⊢ s2 ⊴ t2 → T=Arrow t1 t2 → P G (Arrow s1 s2)) →
   (∀s1,s2,t1,t2. G ⊢ t1 ⊴ s1 →
    (∀X. ¬(X ∈ fv_env G) → (mk_bound true X t1)::G ⊢ subst_type_nat s2 (TFree X) O ⊴ subst_type_nat t2 (TFree X) O)
      → T=Forall t1 t2 → P G (Forall s1 s2)) →
    G ⊢ T1 ⊴ T → P G T1.
 intros;
 generalize in match (refl_eq ? T);
 generalize in match (refl_eq ? G);
 elim H5 in ⊢ (? ? ? % → ? ? ? % → %);
  [1,2: destruct; autobatch
  | rewrite < H9 in H6 H7 H8 ⊢ %;
    rewrite < H10 in H7 H8;
    autobatch
  | rewrite < H10 in H6 H8 ⊢ %;
    autobatch
  | rewrite < H10 in H6 H8 ⊢ %;
    apply (H4 t t1 t2 t3); assumption
  ]
qed.


lemma JS_trans_prova: ∀T,G1.WFType G1 T →
∀G,R,U.incl ? (fv_env G1) (fv_env G) → G ⊢ R ⊴ T → G ⊢ T ⊴ U → G ⊢ R ⊴ U.
intros 3;elim H;clear H; try autobatch;
  [ apply (JSubtype_inv ? ? ? ? ? ? ? ? ? H3); intros; destruct; autobatch
  | inversion H3; intros; destruct; assumption
  |*: apply (JSubtype_inv ? ? ? ? ? ? ? ? ? H6); intros; destruct;
    [1,3: autobatch
    |*: inversion H7; intros; destruct;
      [1,2: autobatch depth=4 width=4 size=9
      | apply SA_Top
         [ assumption
         | apply WFT_Forall;
            [ autobatch
            | intros;lapply (H8 ? H11);
              autobatch]]
      | apply SA_All
         [ autobatch
         | intros;apply (H4 X);
            [intro; autobatch;
            |intro;  apply H13;apply H5; apply (WFT_to_incl ? ? ? H3);
             assumption
            |simplify;autobatch
            |apply (narrowing X (mk_bound true X t::G) ? ? ? ? ? H9 ? ? [])
               [intros;apply H2
                  [unfold;intros;lapply (H5 ? H15);rewrite > fv_append;
                   autobatch
                  |apply (JS_weakening ? ? ? H9)
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
