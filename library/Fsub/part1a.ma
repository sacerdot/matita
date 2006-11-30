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
include "library/logic/equality.ma".
include "library/nat/nat.ma".
include "library/datatypes/bool.ma".
include "library/nat/compare.ma".
include "Fsub/defn.ma".

theorem JS_Refl : \forall T,G.(WFType G T) \to (WFEnv G) \to (JSubtype G T T).
apply Typ_len_ind;intro;elim U
  [(* FIXME *) generalize in match H1;intro;inversion H1
     [intros;destruct H6
     |intros;destruct H5
     |intros;destruct H9
     |intros;destruct H9]
  |apply (SA_Refl_TVar ? ? H2);(*FIXME*)generalize in match H1;intro;
   inversion H1
     [intros;destruct H6;rewrite > Hcut;assumption
     |intros;destruct H5
     |intros;destruct H9
     |intros;destruct H9]
  |apply (SA_Top ? ? H2 H1)
  |cut ((WFType G t) \land (WFType G t1))
     [elim Hcut;apply SA_Arrow
        [apply H2
           [apply t_len_arrow1
           |assumption
           |assumption]
        |apply H2
           [apply t_len_arrow2
           |assumption
           |assumption]]
     |(*FIXME*)generalize in match H3;intro;inversion H3
        [intros;destruct H8
        |intros;destruct H7
        |intros;destruct H11;rewrite > Hcut;rewrite > Hcut1;split;assumption
        |intros;destruct H11]]
  |elim (fresh_name ((fv_type t1) @ (fv_env G)));
   cut ((\lnot (in_list ? a (fv_type t1))) \land
        (\lnot (in_list ? a (fv_env G))))
     [elim Hcut;cut (WFType G t)
        [apply (SA_All2 ? ? ? ? ? a ? H7 H6 H6)
           [apply H2
              [apply t_len_forall1
              |assumption
              |assumption]
           |apply H2
              [rewrite > subst_O_nat;rewrite < eq_t_len_TFree_subst;
               apply t_len_forall2
              |(*FIXME*)generalize in match H3;intro;inversion H3
                 [intros;destruct H11
                 |intros;destruct H10
                 |intros;destruct H14
                 |intros;destruct H14;rewrite < Hcut2 in H11;
                  rewrite < Hcut3 in H11;rewrite < H13;rewrite < H13 in H11;
                  apply (H11 ? H7 H6)]
              |apply WFE_cons;assumption]]
        |(*FIXME*)generalize in match H3;intro;inversion H3
           [intros;destruct H11
           |intros;destruct H10
           |intros;destruct H14
           |intros;destruct H14;rewrite > Hcut1;assumption]]
     |split;unfold;intro;apply H5;apply natinG_or_inH_to_natinGH;auto]]
qed.

lemma env_append_weaken : \forall G,H.(WFEnv (H @ G)) \to
                             (incl ? G (H @ G)).
intros 2;elim H
  [simplify;unfold;intros;assumption
  |simplify in H2;simplify;unfold;intros;apply in_Skip;apply H1
     [apply (WFE_consG_WFE_G ? ? H2)
     |assumption]]
qed.

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
        [assumption
        |assumption
        |lapply (incl_bound_fv ? ? H7);apply (WFT_env_incl ? ? ? ? Hletin1);
         apply (JS_to_WFT1 ? ? ? H1)]
     |unfold;intros;inversion H9
        [intros;lapply (inj_head ? ? ? ? H11);rewrite > Hletin1;apply in_Base
        |intros;lapply (inj_tail ? ? ? ? ? H13);rewrite < Hletin1 in H10;
         apply in_Skip;apply (H7 ? H10)]]]
qed.

lemma fv_env_extends : \forall H,x,B,C,T,U,G.
                          (fv_env (H @ ((mk_bound B x T) :: G))) = 
                          (fv_env (H @ ((mk_bound C x U) :: G))).
intros;elim H
  [simplify;reflexivity
  |elim s;simplify;rewrite > H1;reflexivity]
qed.

lemma WFE_Typ_subst : \forall H,x,B,C,T,U,G.
                      (WFEnv (H @ ((mk_bound B x T) :: G))) \to (WFType G U) \to
                      (WFEnv (H @ ((mk_bound C x U) :: G))).
intros 7;elim H 0
  [simplify;intros;(*FIXME*)generalize in match H1;intro;inversion H1
     [intros;lapply (nil_cons ? G (mk_bound B x T));lapply (Hletin H4);
      elim Hletin1
     |intros;lapply (inj_tail ? ? ? ? ? H8);lapply (inj_head ? ? ? ? H8);
      destruct Hletin1;rewrite < Hletin in H6;rewrite < Hletin in H4;
      rewrite < Hcut1 in H6;apply (WFE_cons ? ? ? ? H4 H6 H2)]
  |intros;simplify;generalize in match H2;elim s;simplify in H4;
   inversion H4
     [intros;absurd (mk_bound b n t::l@(mk_bound B x T::G)=Empty)
        [assumption
        |apply nil_cons]
     |intros;lapply (inj_tail ? ? ? ? ? H9);lapply (inj_head ? ? ? ? H9);
      destruct Hletin1;apply WFE_cons
        [apply H1
           [rewrite > Hletin;assumption
           |assumption]
        |rewrite > Hcut1;generalize in match H7;rewrite < Hletin;
         rewrite > (fv_env_extends ? x B C T U);intro;assumption
        |rewrite < Hletin in H8;rewrite > Hcut2;
         apply (WFT_env_incl ? ? H8);rewrite > (fv_env_extends ? x B C T U);
         unfold;intros;assumption]]]
qed.

lemma lookup_env_extends : \forall G,H,B,C,D,T,U,V,x,y.
            (in_list ? (mk_bound D y V) (H @ ((mk_bound C x U) :: G))) \to
            (y \neq x) \to
            (in_list ? (mk_bound D y V) (H @ ((mk_bound B x T) :: G))).
intros 10;elim H
  [simplify in H1;(*FIXME*)generalize in match H1;intro;inversion H1
     [intros;lapply (inj_head ? ? ? ? H5);rewrite < H4 in Hletin;
      destruct Hletin;absurd (y = x) [symmetry;assumption|assumption]
     |intros;simplify;lapply (inj_tail ? ? ? ? ? H7);rewrite > Hletin;
      apply in_Skip;assumption]
  |(*FIXME*)generalize in match H2;intro;inversion H2
     [intros;simplify in H6;lapply (inj_head ? ? ? ? H6);rewrite > Hletin;
      simplify;apply in_Base
     |simplify;intros;lapply (inj_tail ? ? ? ? ? H8);rewrite > Hletin in H1;
      rewrite > H7 in H1;apply in_Skip;apply (H1 H5 H3)]]
qed.

lemma t_len_pred: \forall T,m.(S (t_len T)) \leq m \to (t_len T) \leq (pred m).
intros 2;elim m
  [elim (not_le_Sn_O ? H)
  |simplify;apply (le_S_S_to_le ? ? H1)]
qed.

lemma pred_m_lt_m : \forall m,T.(t_len T) \leq m \to (pred m) < m.
intros 2;elim m 0
  [elim T
     [simplify in H;elim (not_le_Sn_n ? H)
     |simplify in H;elim (not_le_Sn_n ? H)
     |simplify in H;elim (not_le_Sn_n ? H)
     |simplify in H2;elim (not_le_Sn_O ? H2)
     |simplify in H2;elim (not_le_Sn_O ? H2)]
  |intros;simplify;unfold;constructor 1]
qed.

lemma WFE_bound_bound : \forall B,x,T,U,G. (WFEnv G) \to
                                  (in_list ? (mk_bound B x T) G) \to
                                  (in_list ? (mk_bound B x U) G) \to T = U.
intros 6;elim H
  [lapply (in_list_nil ? ? H1);elim Hletin
  |inversion H6
     [intros;rewrite < H7 in H8;lapply (inj_head ? ? ? ? H8);
      rewrite > Hletin in H5;inversion H5
        [intros;rewrite < H9 in H10;lapply (inj_head ? ? ? ? H10);
         destruct Hletin1;symmetry;assumption
        |intros;lapply (inj_tail ? ? ? ? ? H12);rewrite < Hletin1 in H9;
         rewrite < H11 in H9;lapply (boundinenv_natinfv x e)
           [destruct Hletin;rewrite < Hcut1 in Hletin2;lapply (H3 Hletin2);
            elim Hletin3
           |apply ex_intro
              [apply B|apply ex_intro [apply T|assumption]]]]
     |intros;lapply (inj_tail ? ? ? ? ? H10);rewrite < H9 in H7;
      rewrite < Hletin in H7;(*FIXME*)generalize in match H5;intro;inversion H5
        [intros;rewrite < H12 in H13;lapply (inj_head ? ? ? ? H13);
         destruct Hletin1;rewrite < Hcut1 in H7;
         lapply (boundinenv_natinfv n e)
           [lapply (H3 Hletin2);elim Hletin3
           |apply ex_intro
              [apply B|apply ex_intro [apply U|assumption]]]
        |intros;apply (H2 ? H7);rewrite > H14;lapply (inj_tail ? ? ? ? ? H15);
         rewrite > Hletin1;assumption]]]
qed.         

lemma JS_trans_narrow : \forall n.
  (\forall G,T,Q,U.
     (t_len Q) \leq n \to (JSubtype G T Q) \to (JSubtype G Q U) \to 
     (JSubtype G T U)) \land
  (\forall G,H,X,P,Q,M,N.
     (t_len Q) \leq n \to 
     (JSubtype (H @ ((mk_bound true X Q) :: G)) M N) \to
     (JSubtype G P Q) \to
     (JSubtype (H @ ((mk_bound true X P) :: G)) M N)).
intro;apply (nat_elim1 n);intros 2;
cut (\forall G,T,Q.(JSubtype G T Q) \to 
        \forall U.(t_len Q \leq m) \to (JSubtype G Q U) \to (JSubtype G T U))
  [cut (\forall G,M,N.(JSubtype G M N) \to
           \forall G1,X,Q,G2,P.
              (G = G2 @ ((mk_bound true X Q) :: G1)) \to (t_len Q) \leq m \to
              (JSubtype G1 P Q) \to 
              (JSubtype (G2 @ ((mk_bound true X P) :: G1)) M N))
     [split
        [intros;apply (Hcut ? ? ? H2 ? H1 H3)
        |intros;apply (Hcut1 ? ? ? H3 ? ? ? ? ? ? H2 H4);reflexivity]
     |intros 9;cut (incl ? (fv_env (G2 @ ((mk_bound true X Q)::G1)))
                   (fv_env (G2 @ ((mk_bound true X P)::G1))))
        [intros;
(*                 [rewrite > H6 in H2;lapply (JS_to_WFT1 ? ? ? H8);
                  apply (WFE_Typ_subst ? ? ? ? ? ? ? H2 Hletin) *)
         generalize in match Hcut1;generalize in match H2;
         generalize in match H1;generalize in match H4;
         generalize in match G1;generalize in match G2;elim H1
           [apply SA_Top
              [rewrite > H9 in H5;lapply (JS_to_WFT1 ? ? ? H7);
               apply (WFE_Typ_subst ? ? ? ? ? ? ? H5 Hletin)
              |rewrite > H9 in H6;apply (WFT_env_incl ? ? H6);elim l
                 [simplify;unfold;intros;assumption
                 |simplify;apply (incl_nat_cons ? ? ? H11)]]
           |apply SA_Refl_TVar
              [rewrite > H9 in H5;lapply (JS_to_WFT1 ? ? ? H7);
               apply (WFE_Typ_subst ? ? ? ? ? ? ? H5 Hletin)
              |apply H10;rewrite < H9;assumption]           
           |elim (decidable_eq_nat X n1)
              [apply (SA_Trans_TVar ? ? ? P)
                 [rewrite < H12;elim l
                    [simplify;apply in_Base
                    |simplify;apply in_Skip;assumption]
                 |lapply (JS_to_WFE ? ? ? H9);rewrite > H10 in Hletin;
                  rewrite > H10 in H5;
                  lapply (WFE_bound_bound ? ? ? Q ? Hletin H5)
                    [lapply (H7 ? ? H8 H6 H10 H11);rewrite > Hletin1 in Hletin2;
                     apply (Hcut ? ? ? ? ? H3 Hletin2);
                     lapply (JS_to_WFE ? ? ? Hletin2);
                     apply (JS_weakening ? ? ? H8 ? Hletin3);unfold;intros;
                     elim l;simplify;apply in_Skip;assumption
                    |rewrite > H12;elim l
                       [simplify;apply in_Base
                       |simplify;apply in_Skip;assumption]]]
              |rewrite > H10 in H5;apply (SA_Trans_TVar ? ? ? t1)
                 [apply (lookup_env_extends ? ? ? ? ? ? ? ? ? ? H5);unfold;
                  intro;apply H12;symmetry;assumption
                 |apply (H7 ? ? H8 H6 H10 H11)]]
           |apply SA_Arrow
              [apply (H6 ? ? H9 H5 H11 H12)
              |apply (H8 ? ? H9 H7 H11 H12)]
           |apply SA_All
              [apply (H6 ? ? H9 H5 H11 H12)
              |intros;apply (H8 ? ? (mk_bound true X1 t2::l) l1)
                 [unfold;intro;apply H13;rewrite > H11 in H14;apply (H12 ? H14)
                 |assumption
                 |apply H7;rewrite > H11;unfold;intro;apply H13;apply (H12 ? H14)
                 |simplify;rewrite < H11;reflexivity
                 |simplify;apply incl_nat_cons;assumption]]]
        |elim G2 0
           [simplify;unfold;intros;assumption
           |intro;elim s 0;simplify;intros;apply incl_nat_cons;assumption]]]
  |intros 4;(*generalize in match H1;*)elim H1
     [inversion H5
        [intros;rewrite < H8;apply (SA_Top ? ? H2 H3)
        |intros;destruct H9
        |intros;destruct H10
        |intros;destruct H11
        |intros;destruct H11]
     |assumption
     |apply (SA_Trans_TVar ? ? ? ? H2);apply (H4 ? H5 H6)
     |inversion H7
        [intros;apply (SA_Top ? ? H8);rewrite < H10;apply WFT_Arrow
           [apply (JS_to_WFT2 ? ? ? H2)
           |apply (JS_to_WFT1 ? ? ? H4)]
        |intros;destruct H11
        |intros;destruct H12
        |intros;destruct H13;elim (H (pred m))
           [apply SA_Arrow
              [rewrite > H12 in H2;rewrite < Hcut in H8;
               apply (H15 ? ? ? ? ? H8 H2);lapply (t_len_arrow1 t2 t3);
               unfold in Hletin;lapply (trans_le ? ? ? Hletin H6);
               apply (t_len_pred ? ? Hletin1)
              |rewrite > H12 in H4;rewrite < Hcut1 in H10;
               apply (H15 ? ? ? ? ? H4 H10);lapply (t_len_arrow2 t2 t3);
               unfold in Hletin;lapply (trans_le ? ? ? Hletin H6);
               apply (t_len_pred ? ? Hletin1)]
           |apply (pred_m_lt_m ? ? H6)]
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
        |intros;destruct H13;elim (H (pred m))
           [elim (fresh_name ((fv_env e1) @ (fv_type t1) @ (fv_type t7)));
            cut ((\lnot (in_list ? a (fv_env e1))) \land 
                 (\lnot (in_list ? a (fv_type t1))) \land
                 (\lnot (in_list ? a (fv_type t7))))
              [elim Hcut2;elim H18;clear Hcut2 H18;apply (SA_All2 ? ? ? ? ? a)
                 [rewrite < Hcut in H8;rewrite > H12 in H2;
                  apply (H15 ? ? ? ? ? H8 H2);lapply (t_len_forall1 t2 t3);
                  unfold in Hletin;lapply (trans_le ? ? ? Hletin H6);
                  apply (t_len_pred ? ? Hletin1)
                 |assumption
                 |assumption
                 |assumption
                 |lapply (H10 ? H20);rewrite > H12 in H5;
                  lapply (H5 ? H20 (subst_type_O t5 (TFree a)))
                    [apply (H15 ? ? ? ? ? ? Hletin)
                       [rewrite < Hcut1;rewrite > subst_O_nat;
                        rewrite < eq_t_len_TFree_subst;
                        lapply (t_len_forall2 t2 t3);unfold in Hletin2;
                        lapply (trans_le ? ? ? Hletin2 H6);
                        apply (t_len_pred ? ? Hletin3)
                       |rewrite < Hcut in H8;
                        apply (H16 e1 (nil ?) a t6 t2 ? ? ? Hletin1 H8);
                        lapply (t_len_forall1 t2 t3);unfold in Hletin2;
                        lapply (trans_le ? ? ? Hletin2 H6);
                        apply (t_len_pred ? ? Hletin3)]
                    |rewrite > subst_O_nat;rewrite < eq_t_len_TFree_subst;
                     lapply (t_len_forall2 t2 t3);unfold in Hletin1;
                     lapply (trans_le ? ? ? Hletin1 H6);
                     apply (trans_le ? ? ? ? Hletin2);constructor 2;
                     constructor 1
                    |rewrite > Hcut1;rewrite > H12 in H4;
                     lapply (H4 ? H20);rewrite < Hcut1;apply JS_Refl
                       [apply (JS_to_WFT2 ? ? ? Hletin1)
                       |apply (JS_to_WFE ? ? ? Hletin1)]]]
              |split
                 [split
                    [unfold;intro;apply H17;
                     apply (natinG_or_inH_to_natinGH ? (fv_env e1));right;
                     assumption
                    |unfold;intro;apply H17;
                     apply (natinG_or_inH_to_natinGH 
                               ((fv_type t1) @ (fv_type t7)));left;
                     apply natinG_or_inH_to_natinGH;right;assumption]
                 |unfold;intro;apply H17;
                  apply (natinG_or_inH_to_natinGH 
                            ((fv_type t1) @ (fv_type t7)));left;
                  apply natinG_or_inH_to_natinGH;left;assumption]]
           |apply (pred_m_lt_m ? ? H6)]]]]
qed.

theorem JS_trans : \forall G,T,U,V.(JSubtype G T U) \to 
                                   (JSubtype G U V) \to
                                   (JSubtype G T V).
intros;elim (JS_trans_narrow (t_len U));apply (H2 ? ? ? ? ? H H1);constructor 1;
qed.

theorem JS_narrow : \forall G1,G2,X,P,Q,T,U.
                       (JSubtype (G2 @ (mk_bound true X Q :: G1)) T U) \to
                       (JSubtype G1 P Q) \to
                       (JSubtype (G2 @ (mk_bound true X P :: G1)) T U).
intros;elim (JS_trans_narrow (t_len Q));apply (H3 ? ? ? ? ? ? ? ? H H1);
constructor 1;
qed.