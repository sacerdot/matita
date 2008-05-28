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
intros 3; elim H;
 [1,2,3: autobatch
 | apply SA_All;
    [ autobatch
    | intros; apply (H4 ? H6);
       [ intro; apply H6; apply (fv_WFT ? ? ? (WFT_Forall ? ? ? H1 H3));
         simplify; autobatch
       | autobatch]]]
qed.

(*
 * A slightly more general variant to lemma A.2.2, where weakening isn't
 * defined as concatenation of any two disjoint environments, but as
 * set inclusion.
 *)

lemma JS_weakening : ∀G,T,U.G ⊢ T ⊴ U → ∀H.WFEnv H → incl ? G H → H ⊢ T ⊴ U.
intros 4; elim H;
 [1,2,3,4: autobatch depth=4 width=4 size=7
 | apply (SA_All ? ? ? ? ? (H2 ? H6 H7));intros;
   apply H4
     [ intro; autobatch
     | apply WFE_cons; autobatch
     | unfold;intros; elim (in_list_cons_case ? ? ? ? H9); destruct; autobatch]]
qed.

lemma JSubtype_inv:
 ∀G:list bound.∀T1,T:Typ.
  ∀P:list bound → Typ → Typ → Prop.
   (∀t. WFEnv G → WFType G t → T=Top → P G t Top) →
   (∀n. WFEnv G → n ∈ fv_env G → T=TFree n → P G (TFree n) (TFree n)) →
   (∀n,t1,t.
    (mk_bound true n t1) ∈ G → G ⊢ t1 ⊴ t → P G t1 t → T=t → P G (TFree n) T) →
   (∀s1,s2,t1,t2. G ⊢ t1 ⊴ s1 → G ⊢ s2 ⊴ t2 → T=Arrow t1 t2 → P G (Arrow s1 s2) (Arrow t1 t2)) →
   (∀s1,s2,t1,t2. G ⊢ t1 ⊴ s1 →
    (∀X. ¬(X ∈ fv_env G) → (mk_bound true X t1)::G ⊢ subst_type_nat s2 (TFree X) O ⊴ subst_type_nat t2 (TFree X) O)
      → T=Forall t1 t2 → P G (Forall s1 s2) (Forall t1 t2)) →
    G ⊢ T1 ⊴ T → P G T1 T.
 intros;
 generalize in match (refl_eq ? T);
 generalize in match (refl_eq ? G);
 elim H5 in ⊢ (? ? ? % → ? ? ? % → %); destruct; 
  [1,2,3,4: autobatch depth=10 width=10 size=8
  | apply H4; first [assumption | autobatch]]
qed.

theorem narrowing:∀X,G,G1,U,P,M,N.
  G1 ⊢ P ⊴ U → (∀G2,T.G2@G1 ⊢ U ⊴ T → G2@G1 ⊢ P ⊴ T) → G ⊢ M ⊴ N →
  ∀l.G=l@(mk_bound true X U::G1) → l@(mk_bound true X P::G1) ⊢ M ⊴ N.
intros 10.elim H2; destruct;
 [1,2,4: autobatch width=10 depth=10 size=8
 | elim (decidable_eq_nat X n)
    [apply (SA_Trans_TVar ? ? ? P); destruct;
      [ autobatch
      | rewrite > append_cons; apply H1;
        lapply (WFE_bound_bound true X t1 U ? ? H3); destruct;
          [1,3: autobatch
          | rewrite < append_cons; autobatch
          ]]
    | apply (SA_Trans_TVar ? ? ? t1)
      [ apply (lookup_env_extends ? ? ? ? ? ? ? ? ? ? H3);
        intro; autobatch
      | autobatch]]
 | apply SA_All;
    [ autobatch
    | intros;
      apply (H6 ? ? (mk_bound true X1 t2::l1))
      [ rewrite > fv_env_extends; autobatch
      | autobatch]]]
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
intros 5; autobatch.
qed.

theorem JS_narrow : ∀G1,G2,X,P,Q,T,U.
                       (G2 @ (mk_bound true X Q :: G1)) ⊢ T ⊴ U → G1 ⊢ P ⊴ Q →
                       (G2 @ (mk_bound true X P :: G1)) ⊢ T ⊴ U.
intros; apply (narrowing ? ? ? ? ? ? ? H1 ? H) [|autobatch]
intros;apply (JS_trans ? ? ? ? ? H2);apply (JS_weakening ? ? ? H1);
     [autobatch|unfold;intros;autobatch]
qed.
