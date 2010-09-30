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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/comp_ext.ma".
include "num/bool_lemmas.ma".

(* ******** *)
(* COMPOSTI *)
(* ******** *)

nrecord comp_num (T:Type) : Type ≝
 {
 cnH: T;
 cnL: T
 }.

(* operatore = *)
ndefinition eq_cn ≝
λT.λfeq:T → T → bool.
λcn1,cn2:comp_num T.
 (feq (cnH ? cn1) (cnH ? cn2)) ⊗ (feq (cnL ? cn1) (cnL ? cn2)).

nlemma cn_destruct_1 :
∀T.∀x1,x2,y1,y2:T.
 mk_comp_num T x1 y1 = mk_comp_num T x2 y2 → x1 = x2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_comp_num ? x2 y2 with [ mk_comp_num a _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma cn_destruct_2 :
∀T.∀x1,x2,y1,y2:T.
 mk_comp_num T x1 y1 = mk_comp_num T x2 y2 → y1 = y2.
 #T; #x1; #x2; #y1; #y2; #H;
 nchange with (match mk_comp_num ? x2 y2 with [ mk_comp_num _ b ⇒ y1 = b ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma symmetric_eqcn :
∀T.∀feq:T → T → bool.
 (symmetricT T bool feq) →
 (symmetricT (comp_num T) bool (eq_cn T feq)).
 #T; #feq; #H;
 #b1; nelim b1; #e1; #e2;
 #b2; nelim b2; #e3; #e4;
 nchange with (((feq e1 e3)⊗(feq e2 e4)) = ((feq e3 e1)⊗(feq e4 e2)));
 nrewrite > (H e1 e3);
 nrewrite > (H e2 e4);
 napply refl_eq.
nqed.

nlemma eqcn_to_eq :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(feq x y = true) → (x = y)) →
 (∀b1,b2:comp_num T.
  ((eq_cn T feq b1 b2 = true) → (b1 = b2))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 nchange in ⊢ (% → ?) with (((feq e1 e3)⊗(feq e2 e4)) = true);
 #H1;
 nrewrite < (H … (andb_true_true_l … H1));
 nrewrite < (H … (andb_true_true_r … H1));
 napply refl_eq.
nqed.

nlemma eq_to_eqcn :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(x = y) → (feq x y = true)) →
 (∀b1,b2:comp_num T.
  ((b1 = b2) → (eq_cn T feq b1 b2 = true))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 #H1;
 nrewrite < (cn_destruct_1 … H1);
 nrewrite < (cn_destruct_2 … H1);
 nchange with (((feq e1 e1)⊗(feq e2 e2)) = true);
 nrewrite > (H e1 e1 (refl_eq …));
 nrewrite > (H e2 e2 (refl_eq …)); 
 nnormalize;
 napply refl_eq.
nqed.

nlemma decidable_cn_aux1 :
∀T.∀e1,e2,e3,e4:T.e1 ≠ e3 → (mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4).
 #T; #e1; #e2; #e3; #e4;
 nnormalize; #H; #H1;
 napply (H (cn_destruct_1 … H1)).
nqed.

nlemma decidable_cn_aux2 :
∀T.∀e1,e2,e3,e4:T.e2 ≠ e4 → (mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4).
 #T; #e1; #e2; #e3; #e4;
 nnormalize; #H; #H1;
 napply (H (cn_destruct_2 … H1)).
nqed.

nlemma decidable_cn :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀b1,b2:comp_num T.
    (decidable (b1 = b2))).
 #T; #H;
 #b1; nelim b1; #e1; #e2;
 #b2; nelim b2; #e3; #e4;
 nnormalize;
 napply (or2_elim (e1 = e3) (e1 ≠ e3) ? (H e1 e3) …);
 ##[ ##2: #H1; napply (or2_intro2 … (decidable_cn_aux1 T e1 e2 e3 e4 H1))
 ##| ##1: #H1; napply (or2_elim (e2 = e4) (e2 ≠ e4) ? (H e2 e4) …);
          ##[ ##2: #H2; napply (or2_intro2 … (decidable_cn_aux2 T e1 e2 e3 e4 H2))
          ##| ##1: #H2; nrewrite > H1; nrewrite > H2;
                        napply (or2_intro1 … (refl_eq ? (mk_comp_num T e3 e4)))
          ##]
 ##]
nqed.

nlemma neqcn_to_neq :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(feq x y = false) → (x ≠ y)) →
 (∀b1,b2:comp_num T.
  ((eq_cn T feq b1 b2 = false) → (b1 ≠ b2))).
 #T; #feq; #H; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 nchange with ((((feq e1 e3) ⊗ (feq e2 e4)) = false) → ?);
 #H1;
 napply (or2_elim ((feq e1 e3) = false) ((feq e2 e4) = false) ? (andb_false2 … H1) …);
 ##[ ##1: #H2; napply (decidable_cn_aux1 … (H … H2))
 ##| ##2: #H2; napply (decidable_cn_aux2 … (H … H2))
 ##]
nqed.

nlemma cn_destruct :
∀T.(∀x,y:T.decidable (x = y)) →
   (∀e1,e2,e3,e4:T.
    ((mk_comp_num T e1 e2) ≠ (mk_comp_num T e3 e4)) →
    ((e1 ≠ e3) ∨ (e2 ≠ e4))).
 #T; #H; #e1; #e2; #e3; #e4;
 nnormalize; #H1;
 napply (or2_elim (e1 = e3) (e1 ≠ e3) ? (H e1 e3) …);
 ##[ ##2: #H2; napply (or2_intro1 … H2)
 ##| ##1: #H2; napply (or2_elim (e2 = e4) (e2 ≠ e4) ? (H e2 e4) …);
          ##[ ##2: #H3; napply (or2_intro2 … H3)
          ##| ##1: #H3; nrewrite > H2 in H1:(%);
                   nrewrite > H3;
                   #H1; nelim (H1 (refl_eq …))
          ##]
 ##]
nqed.

nlemma neq_to_neqcn :
∀T.∀feq:T → T → bool.
 (∀x,y:T.(x ≠ y) → (feq x y = false)) →
 (∀x,y:T.decidable (x = y)) →
 (∀b1,b2:comp_num T.
  ((b1 ≠ b2) → (eq_cn T feq b1 b2 = false))).
 #T; #feq; #H; #H1; #b1; #b2;
 nelim b1; #e1; #e2;
 nelim b2; #e3; #e4;
 #H2; nchange with (((feq e1 e3) ⊗ (feq e2 e4)) = false);
 napply (or2_elim (e1 ≠ e3) (e2 ≠ e4) ? (cn_destruct T H1 e1 e2 e3 e4 … H2) …);
 ##[ ##1: #H3; nrewrite > (H … H3); nnormalize; napply refl_eq
 ##| ##2: #H3; nrewrite > (H … H3);
          nrewrite > (symmetric_andbool (feq e1 e3) false);
          nnormalize; napply refl_eq
 ##]
nqed.

nlemma cn_is_comparable : comparable → comparable.
 #T; @ (comp_num T)
  (* zero *)
  ##[ napply (mk_comp_num ? (zeroc ?) (zeroc ?))
  (* forall *)
  ##| napply (λP.forallc T
              (λh.forallc T
               (λl.P (mk_comp_num ? h l))))
  (* eq *)
  ##| napply (eq_cn ? (eqc T))
  (* eqc_to_eq *)
  ##| napply (eqcn_to_eq … (eqc_to_eq T))
  (* eq_to_eqc *)
  ##| napply (eq_to_eqcn … (eq_to_eqc T))
  (* neqc_to_neq *)
  ##| napply (neqcn_to_neq … (neqc_to_neq T))
  (* neq_to_neqc *)
  ##| napply (neq_to_neqcn … (neq_to_neqc T));
      napply (decidable_c T)
  (* decidable_c *)
  ##| napply (decidable_cn … (decidable_c T))
  (* symmetric_eqc *)
  ##| napply (symmetric_eqcn … (symmetric_eqc T))
  ##]
nqed.

nlemma cn_is_comparable_ext : comparable_ext → comparable_ext.
 #T; nelim T; #c;
 #ltc; #lec; #gtc; #gec; #andc; #orc; #xorc;
 #getMSBc; #setMSBc; #clrMSBc; #getLSBc; #setLSBc; #clrLSBc;
 #rcrc; #shrc; #rorc; #rclc; #shlc; #rolc; #notc;
 #plusc_dc_dc; #plusc_d_dc; #plusc_dc_d; #plusc_d_d; #plusc_dc_c; #plusc_d_c;
 #predc; #succc; #complc; #absc; #inrangec;
 napply (mk_comparable_ext);
  ##[ napply (cn_is_comparable c)
  (* lt *)
  ##| napply (λx,y.(ltc (cnH ? x) (cnH ? y)) ⊕
                   (((eqc c) (cnH ? x) (cnH ? y)) ⊗ (ltc (cnL ? x) (cnL ? y))))
  (* le *)
  ##| napply (λx,y.(ltc (cnH ? x) (cnH ? y)) ⊕
                    (((eqc c) (cnH ? x) (cnH ? y)) ⊗ (lec (cnL ? x) (cnL ? y))))
  (* gt *)
  ##| napply (λx,y.(gtc (cnH ? x) (cnH ? y)) ⊕
                   (((eqc c) (cnH ? x) (cnH ? y)) ⊗ (gtc (cnL ? x) (cnL ? y))))
  (* ge *)
  ##| napply (λx,y.(gtc (cnH ? x) (cnH ? y)) ⊕
                   (((eqc c) (cnH ? x) (cnH ? y)) ⊗ (gec (cnL ? x) (cnL ? y))))
  (* and *)
  ##| napply (λx,y.mk_comp_num ? (andc (cnH ? x) (cnH ? y))
                                 (andc (cnL ? x) (cnL ? y)))
  (* or *)
  ##| napply (λx,y.mk_comp_num ? (orc (cnH ? x) (cnH ? y))
                                 (orc (cnL ? x) (cnL ? y)))
  (* xor *)
  ##| napply (λx,y.mk_comp_num ? (xorc (cnH ? x) (cnH ? y))
                                 (xorc (cnL ? x) (cnL ? y)))
  (* getMSB *)
  ##| napply (λx.getMSBc (cnH ? x))
  (* setMSB *)
  ##| napply (λx.mk_comp_num ? (setMSBc (cnH ? x)) (cnL ? x))
  (* clrMSB *)
  ##| napply (λx.mk_comp_num ? (clrMSBc (cnH ? x)) (cnL ? x))
  (* getLSB *)
  ##| napply (λx.getLSBc (cnL ? x))
  (* setLSB *)
  ##| napply (λx.mk_comp_num ? (cnH ? x) (setLSBc (cnL ? x)))
  (* clrLSB *)
  ##| napply (λx.mk_comp_num ? (cnH ? x) (clrLSBc (cnL ? x)))
  (* rcr *)
  ##| napply (λcy,x.match rcrc cy (cnH ? x) with
              [ pair cy' cnh' ⇒ match rcrc cy' (cnL ? x) with
              [ pair cy'' cnl' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* shr *)
  ##| napply (λx.match shrc (cnH ? x) with
              [ pair cy' cnh' ⇒ match rcrc cy' (cnL ? x) with
              [ pair cy'' cnl' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* ror *)
  ##| napply (λx.match shrc (cnH ? x) with
              [ pair cy' cnh' ⇒ match rcrc cy' (cnL ? x) with
              [ pair cy'' cnl' ⇒ mk_comp_num ?
               (match cy'' with [ true ⇒ setMSBc
                                | false ⇒ λh.h ] cnh') cnl']])
  (* rcl *)
  ##| napply (λcy,x.match rclc cy (cnL ? x) with
              [ pair cy' cnl' ⇒ match rclc cy' (cnH ? x) with
              [ pair cy'' cnh' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* shl *)
  ##| napply (λx.match shlc (cnL ? x) with
              [ pair cy' cnl' ⇒ match rclc cy' (cnH ? x) with
              [ pair cy'' cnh' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* rol *)
  ##| napply (λx.match shlc (cnL ? x) with
              [ pair cy' cnl' ⇒ match rclc cy' (cnH ? x) with
              [ pair cy'' cnh' ⇒ mk_comp_num ?
               cnh' (match cy'' with [ true ⇒ setLSBc
                                     | false ⇒ λh.h ] cnl')]])
  (* not *)
  ##| napply (λx.mk_comp_num ? (notc (cnH ? x)) (notc (cnL ? x)))
  (* plus_dc_dc *)
  ##| napply (λcy,x,y.match plusc_dc_dc cy (cnL ? x) (cnL ? y) with
              [ pair cy' cnl' ⇒ match plusc_dc_dc cy' (cnH ? x) (cnH ? y) with
              [ pair cy'' cnh' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* plus_d_dc *)
  ##| napply (λx,y.match plusc_d_dc (cnL ? x) (cnL ? y) with
              [ pair cy' cnl' ⇒ match plusc_dc_dc cy' (cnH ? x) (cnH ? y) with
              [ pair cy'' cnh' ⇒ pair … cy'' (mk_comp_num ? cnh' cnl')]])
  (* plus_dc_d *)
  ##| napply (λcy,x,y.match plusc_dc_dc cy (cnL ? x) (cnL ? y) with
              [ pair cy' cnl' ⇒ mk_comp_num ? (plusc_dc_d cy' (cnH ? x) (cnH ? y)) cnl'])
  (* plus_d_d *)
  ##| napply (λx,y.match plusc_d_dc (cnL ? x) (cnL ? y) with
              [ pair cy' cnl' ⇒ mk_comp_num ? (plusc_dc_d cy' (cnH ? x) (cnH ? y)) cnl'])
  (* plus_dc_c *)
  ##| napply (λcy,x,y.plusc_dc_c (plusc_dc_c cy (cnL ? x) (cnL ? y))
                                 (cnH ? x) (cnH ? y))
  (* plus_d_c *)
  ##| napply (λx,y.plusc_dc_c (plusc_d_c (cnL ? x) (cnL ? y))
                              (cnH ? x) (cnH ? y))
  (* pred *)
  ##| napply (λx.match (eqc c) (zeroc c) (cnL ? x) with
              [ true ⇒ mk_comp_num ? (predc (cnH ? x)) (predc (cnL ? x))
              | false ⇒ mk_comp_num ? (cnH ? x) (predc (cnL ? x)) ])
  (* succ *)
  ##| napply (λx.match (eqc c) (predc (zeroc c)) (cnL ? x) with
              [ true ⇒ mk_comp_num ? (succc (cnH ? x)) (succc (cnL ? x))
              | false ⇒ mk_comp_num ? (cnH ? x) (succc (cnL ? x)) ])
  (* compl *)
  ##| napply (λx.(match (eqc c) (zeroc c) (cnL ? x) with
               [ true ⇒ mk_comp_num ? (complc (cnH ? x)) (complc (cnL ? x))
              | false ⇒ mk_comp_num ? (notc (cnH ? x)) (complc (cnL ? x)) ]))
  (* abs *)
  ##| napply (λx.match getMSBc (cnH ? x) with
              [ true ⇒ match (eqc c) (zeroc c) (cnL ? x) with
               [ true ⇒ mk_comp_num ? (complc (cnH ? x)) (complc (cnL ? x))
               | false ⇒ mk_comp_num ? (notc (cnH ? x)) (complc (cnL ? x)) ]
              | false ⇒ x ])
  (* inrange *)
  ##| napply (λx,inf,sup.
              match (ltc (cnH ? inf) (cnH ? sup)) ⊕
                    (((eqc c) (cnH ? inf) (cnH ? sup)) ⊗ (lec (cnL ? inf) (cnL ? sup))) with
               [ true ⇒ and_bool | false ⇒ or_bool ]
              ((ltc (cnH ? inf) (cnH ? x)) ⊕
              (((eqc c) (cnH ? inf) (cnH ? x)) ⊗ (lec (cnL ? inf) (cnL ? x))))
              ((ltc (cnH ? x) (cnH ? sup)) ⊕
              (((eqc c) (cnH ? x) (cnH ? sup)) ⊗ (lec (cnL ? x) (cnL ? sup)))))
  ##]
nqed.

ndefinition zeroc ≝ λx:comparable_ext.zeroc (comp_base x).
ndefinition forallc ≝ λx:comparable_ext.forallc (comp_base x).
ndefinition eqc ≝ λx:comparable_ext.eqc (comp_base x).
ndefinition eqc_to_eq ≝ λx:comparable_ext.eqc_to_eq (comp_base x).
ndefinition eq_to_eqc ≝ λx:comparable_ext.eq_to_eqc (comp_base x).
ndefinition neqc_to_neq ≝ λx:comparable_ext.neqc_to_neq (comp_base x).
ndefinition neq_to_neqc ≝ λx:comparable_ext.neq_to_neqc (comp_base x).
ndefinition decidable_c ≝ λx:comparable_ext.decidable_c (comp_base x).
ndefinition symmetric_eqc ≝ λx:comparable_ext.symmetric_eqc (comp_base x).


unification hint 0 ≔ S: comparable;
         T ≟ (carr S),
         X ≟ (cn_is_comparable S)
 (*********************************************) ⊢
         carr X ≡ comp_num T.
