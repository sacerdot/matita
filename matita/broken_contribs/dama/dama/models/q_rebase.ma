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

include "dama/russell_support.ma".
include "models/q_copy.ma".
(*
definition rebase_spec ≝ 
 λl1,l2:q_f.λp:q_f × q_f. 
   And3
    (same_bases (bars (\fst p)) (bars (\snd p)))
    (same_values l1 (\fst p)) 
    (same_values l2 (\snd p)).

inductive rebase_cases : list bar → list bar → (list bar) × (list bar) → Prop ≝
| rb_fst_full  : ∀b,h1,xs.
   rebase_cases (〈b,h1〉::xs) [] 〈〈b,h1〉::xs,〈b,〈OQ,OQ〉〉::copy xs〉
| rb_snd_full  : ∀b,h1,ys.
   rebase_cases [] (〈b,h1〉::ys) 〈〈b,〈OQ,OQ〉〉::copy ys,〈b,h1〉::ys〉  
| rb_all_full  : ∀b,h1,h2,h3,h4,xs,ys,r1,r2.
   \snd(\last ▭ (〈b,h1〉::xs)) = \snd(\last ▭ (〈b,h3〉::r1)) →
   \snd(\last ▭ (〈b,h2〉::ys)) = \snd(\last ▭ (〈b,h4〉::r2)) →
   rebase_cases (〈b,h1〉::xs) (〈b,h2〉::ys) 〈〈b,h3〉::r1,〈b,h4〉::r2〉
| rb_all_full_l  : ∀b1,b2,h1,h2,xs,ys,r1,r2.
   \snd(\last ▭ (〈b1,h1〉::xs)) = \snd(\last ▭ (〈b1,h1〉::r1)) →
   \snd(\last ▭ (〈b2,h2〉::ys)) = \snd(\last ▭ (〈b1,h2〉::r2)) →
   b1 < b2 →
   rebase_cases (〈b1,h1〉::xs) (〈b2,h2〉::ys) 〈〈b1,h1〉::r1,〈b1,〈OQ,OQ〉〉::r2〉 
| rb_all_full_r  : ∀b1,b2,h1,h2,xs,ys,r1,r2.
   \snd(\last ▭ (〈b1,h1〉::xs)) = \snd(\last ▭ (〈b2,h1〉::r1)) →
   \snd(\last ▭ (〈b2,h2〉::ys)) = \snd(\last ▭ (〈b2,h2〉::r2)) →
   b2 < b1 →
   rebase_cases (〈b1,h1〉::xs) (〈b2,h2〉::ys) 〈〈b2,〈OQ,OQ〉〉::r1,〈b2,h2〉::r2〉     
| rb_all_empty : rebase_cases [] [] 〈[],[]〉.

alias symbol "pi2" = "pair pi2".
alias symbol "pi1" = "pair pi1".
alias symbol "leq" = "natural 'less or equal to'".
inductive rebase_spec_aux_p (l1, l2:list bar) (p:(list bar) × (list bar)) : Prop ≝
| prove_rebase_spec_aux:
   rebase_cases l1 l2 p →
   (sorted q2_lt (\fst p)) →
   (sorted q2_lt (\snd p)) → 
   (same_bases (\fst p) (\snd p)) →
   (same_values_simpl l1 (\fst p)) → 
   (same_values_simpl l2 (\snd p)) →  
   rebase_spec_aux_p l1 l2 p.   

lemma aux_preserves_sorting:
 ∀b,b3,l2,l3,w. rebase_cases l2 l3 w → 
  sorted q2_lt (b::l2) → sorted q2_lt (b3::l3) → \fst b3 = \fst b →
  sorted q2_lt (\fst w) → sorted q2_lt (\snd w) → 
  same_bases (\fst w) (\snd w) → 
    sorted q2_lt (b :: \fst w).
intros 6; cases H; simplify; intros; clear H;
[ apply (sorted_cons q2_lt); [2:assumption] apply (inversion_sorted2 ??? H1);
| apply (sorted_cons q2_lt); [2:assumption]
  whd; rewrite < H3; apply (inversion_sorted2 ??? H2);
| apply (sorted_cons q2_lt); [2:assumption] apply (inversion_sorted2 ??? H3);
| apply (sorted_cons q2_lt); [2:assumption] apply (inversion_sorted2 ??? H4);
| apply (sorted_cons q2_lt); [2:assumption] 
  whd; rewrite < H6; apply (inversion_sorted2 ??? H5);
| apply (sorted_one q2_lt);]
qed.   

lemma aux_preserves_sorting2:
 ∀b,b3,l2,l3,w. rebase_cases l2 l3 w → 
  sorted q2_lt (b::l2) → sorted q2_lt (b3::l3) → \fst b3 = \fst b →
  sorted q2_lt (\fst w) → sorted q2_lt (\snd w) → same_bases (\fst w) (\snd w) → 
  sorted q2_lt (b :: \snd w).
intros 6; cases H; simplify; intros; clear H;
[ apply (sorted_cons q2_lt); [2:assumption] apply (inversion_sorted2 ??? H1);   
| apply (sorted_cons q2_lt); [2:assumption] 
  whd; rewrite < H3; apply (inversion_sorted2 ??? H2);
| apply (sorted_cons q2_lt); [2: assumption] apply (inversion_sorted2 ??? H3);
| apply (sorted_cons q2_lt); [2: assumption] apply (inversion_sorted2 ??? H4);
| apply (sorted_cons q2_lt); [2: assumption] 
  whd; rewrite < H6; apply (inversion_sorted2 ??? H5);
| apply (sorted_one q2_lt);]
qed.
*)



definition rebase_spec_aux ≝ 
 λl1,l2
 :list bar.λp:(list bar) × (list bar).
 sorted q2_lt l1 → (\snd (\last ▭ l1) = 〈OQ,OQ〉) →
 sorted q2_lt l2 → (\snd (\last ▭ l2) = 〈OQ,OQ〉) → 
   rebase_spec_aux_p l1 l2 p.

alias symbol "lt" = "Q less than".
alias symbol "Q" = "Rationals".
axiom q_unlimited: ∀x:ℚ.∃y:ratio.x<Qpos y.                
axiom q_halving: ∀x,y:ℚ.∃z:ℚ.x<z ∧ z<y.
alias symbol "not" = "logical not".
axiom q_not_OQ_lt_Qneg: ∀r. ¬ (OQ < Qneg r).
lemma same_values_unit_OQ: 
  ∀b1,b2,h1,l. OQ < b2 → b2 < b1 → sorted q2_lt (〈b1,h1〉::l) →
    sorted q2_lt  [〈b2,〈OQ,OQ〉〉] → 
    same_values_simpl (〈b1,h1〉::l) [〈b2,〈OQ,OQ〉〉]  → h1 = 〈OQ,OQ〉.
intros 5 (b1 b2 h1 l POS); cases l;
[1: intros; cases (q_unlimited b1); cut (b2 < Qpos w); [2:apply (q_lt_trans ??? H H4);] 
    lapply (H3 H1 ? H2 ? w H4 Hcut) as K; simplify; [1,2: autobatch]
    rewrite > (value_unit 〈b1,h1〉) in K;
    rewrite > (value_unit 〈b2,〈OQ,OQ〉〉) in K; assumption;
|2: intros; unfold in H3; lapply depth=0 (H3 H1 ? H2 ?) as K; [1,2:simplify; autobatch]
    clear H3; cases (q_halving b1 (b1 + \fst p)) (w Pw); cases w in Pw; intros;
    [cases (q_lt_le_incompat ?? POS); apply q_lt_to_le; cases H3;
     apply (q_lt_trans ???? H4); assumption;
    |3: elim H3; lapply (q_lt_trans ??? H H4); lapply (q_lt_trans ??? POS Hletin);
        cases (q_not_OQ_lt_Qneg ? Hletin1);
    | cases H3; lapply (K r);
      [2: simplify; assumption
      |3: simplify; apply (q_lt_trans ???? H4); assumption;
      |rewrite > (value_head b1,h1 .. q) in Hletin;
        


 (* MANCA che le basi sono positive, 
               poi con halving prendi tra b1 e \fst p e hai h1=OQ,OQ*)


definition eject ≝
  λP.λp:∃x:(list bar) × (list bar).P x.match p with [ex_introT p _ ⇒ p].
coercion eject.
definition inject ≝ λP.λp:(list bar) × (list bar).λh:P p. ex_introT ? P p h.
coercion inject with 0 1 nocomposites.

definition rebase: ∀l1,l2:q_f.∃p:q_f × q_f.rebase_spec l1 l2 p.
intros 2 (f1 f2); cases f1 (b1 Hs1 Hb1 He1); cases f2 (b2 Hs2 Hb2 He2); clear f1 f2;
alias symbol "leq" = "natural 'less or equal to'".
alias symbol "minus" = "Q minus".
letin aux ≝ ( 
let rec aux (l1,l2:list bar) (n : nat) on n : (list bar) × (list bar) ≝
match n with
[ O ⇒ 〈[], []〉
| S m ⇒
  match l1 with
  [ nil ⇒ 〈copy l2, l2〉
  | cons he1 tl1 ⇒
     match l2 with
     [ nil ⇒ 〈l1, copy l1〉
     | cons he2 tl2 ⇒  
         let base1 ≝ \fst he1 in
         let base2 ≝ \fst he2 in
         let height1 ≝ \snd he1 in
         let height2 ≝ \snd he2 in
         match q_cmp base1 base2 with
         [ q_leq Hp1 ⇒ 
             match q_cmp base2 base1 with
             [ q_leq Hp2 ⇒
                 let rc ≝ aux tl1 tl2 m in 
                 〈he1 :: \fst rc,he2 :: \snd rc〉
             | q_gt Hp ⇒ 
                 let rest ≝ base2 - base1 in
                 let rc ≝ aux tl1 (〈rest,height2〉 :: tl2) m in
                 〈〈base1,height1〉 :: \fst rc,〈base1,height2〉 :: \snd rc〉] 
         | q_gt Hp ⇒ 
             let rest ≝ base1 - base2 in
             let rc ≝ aux (〈rest,height1〉 :: tl1) tl2 m in
             〈〈base2,height1〉 :: \fst rc,〈base2,height2〉 :: \snd rc〉]]]]
in aux : ∀l1,l2,m.∃z.\len l1 + \len l2 ≤ m → rebase_spec_aux l1 l2 z);
[7: clearbody aux; cases (aux b1 b2 (\len b1 + \len b2)) (res Hres);
    exists; [split; constructor 1; [apply (\fst res)|5:apply (\snd res)]]
    [1,4: apply hide; cases (Hres (le_n ?) Hs1 He1 Hs2 He2); assumption;
    |2,5: apply hide; cases (Hres (le_n ?) Hs1 He1 Hs2 He2); clear Hres aux;
          lapply (H3 O) as K; clear H1 H2 H3 H4 H5; unfold nth_base; 
          cases H in K He1 He2 Hb1 Hb2; simplify; intros; assumption;
    |3,6: apply hide; cases (Hres (le_n ?) Hs1 He1 Hs2 He2); clear Hres aux;
          cases H in He1 He2; simplify; intros;
          [1,6,8,12: assumption;
          |2,7: rewrite > len_copy; generalize in match (\len ?); intro X;
                cases X; [1,3: reflexivity] simplify;
                [apply (copy_OQ ys n);|apply (copy_OQ xs n);]
          |3,4: rewrite < H6; assumption;
          |5: cases r1 in H6; simplify; intros; [reflexivity] rewrite < H6; assumption;
          |9,11: rewrite < H7; assumption;
          |10: cases r2 in H7; simplify; intros; [reflexivity] rewrite < H7; assumption]]
    split; cases (Hres (le_n ?) Hs1 He1 Hs2 He2); clear Hres; unfold same_values; intros; 
    [1: assumption
    |2,3: simplify in match (\snd 〈?,?〉); simplify in match (\fst 〈?,?〉);
        apply same_values_simpl_to_same_values; assumption]
|3: cut (\fst b3 = \fst b) as E; [2: apply q_le_to_le_to_eq; assumption]
    clear H6 H5 H4 H3 He2 Hb2 Hs2 b2 He1 Hb1 Hs1 b1; cases (aux l2 l3 n1) (rc Hrc); 
    clear aux; intro K; simplify in K; rewrite <plus_n_Sm in K; 
    lapply le_S_S_to_le to K as W; lapply lt_to_le to W as R; 
    simplify in match (? ≪rc,Hrc≫); intros (Hsbl2 Hendbl2 Hsb3l3 Hendb3l3);
    change in Hendbl2 with (\snd (\last ▭ (b::l2)) = 〈OQ,OQ〉);
    change in Hendb3l3 with (\snd (\last ▭ (b3::l3)) = 〈OQ,OQ〉);
    cases (Hrc R) (RC S1 S2 SB SV1 SV2); clear Hrc R W K; 
      [2,4: apply (sorted_tail q2_lt);[apply b|3:apply b3]assumption;
      |3: cases l2 in Hendbl2; simplify; intros; [reflexivity] assumption; 
      |5: cases l3 in Hendb3l3; simplify; intros; [reflexivity] assumption;]
    constructor 1; simplify in match (\fst 〈?,?〉); simplify in match (\snd 〈?,?〉);
    [1: cases b in E Hsbl2 Hendbl2; cases b3 in Hsb3l3 Hendb3l3; intros (Hsbl3 Hendbl2 E Hsb3l2 Hendb3l3); 
        simplify in E; destruct E; constructor 3;
        [1: clear Hendbl2 Hsbl3 SV2 SB S2;
            cases RC in S1 SV1 Hsb3l2 Hendb3l3; intros; 
            [1,6: reflexivity;
            |3,4: assumption;
            |5: simplify in H6:(??%) ⊢ %; rewrite > H3; cases r1 in H6; intros [2:reflexivity]
                use same_values_unit_OQ; 

            |2: simplify in H3:(??%) ⊢ %; rewrite > H3; rewrite > len_copy; elim (\len ys); [reflexivity]
          symmetry; apply (copy_OQ ys n2);
        | cases H8 in H5 H7; simplify; intros; [2,6:reflexivity|3,4,5: assumption] 
          simplify; rewrite > H5; rewrite > len_copy; elim (\len xs); [reflexivity]
          symmetry; apply (copy_OQ xs n2);]
    |2: apply (aux_preserves_sorting ? b3 ??? H8); assumption;
    |3: apply (aux_preserves_sorting2 ? b3 ??? H8); try assumption;
        try reflexivity; cases (inversion_sorted ?? H4);[2:rewrite >H3; apply (sorted_one q2_lt);]
        cases l2 in H3 H4; intros; [apply (sorted_one q2_lt)]
        apply (sorted_cons q2_lt);[2:apply (sorted_tail q2_lt ?? H3);] whd;
        rewrite > E; assumption;
    |4: apply I 
    |5: apply I
    |6: intro; elim i; intros; simplify; solve [symmetry;assumption|apply H13]
    |7: unfold; intros; clear H9 H10 H11 H12 H13; simplify in Hi1 Hi2 H16 H18;
       cases H8 in H14 H15 H17 H3 H16 H18 H5 H6; 
       simplify in match (\fst 〈?,?〉); simplify in match (\snd 〈?,?〉); intros;
       [1: reflexivity;
       |2: simplify in H3; rewrite > (value_unit b); rewrite > H3; symmetry;
           cases b in H3 H12 Hi2; intros 2; simplify in H12; rewrite > H12;
           intros; change in ⊢ (? ? (? % ? ? ? ?) ?) with (copy (〈q,〈OQ,OQ〉〉::〈b1,〈OQ,OQ〉〉::ys));
           apply (value_copy (〈q,〈OQ,OQ〉〉::〈b1,〈OQ,OQ〉〉::ys));
       |3: apply (same_value_tail b b1 h1 h3 xs r1 input); assumption;
       |4: apply (same_value_tail b b1 h1 h1 xs r1 input); assumption;
       |5: simplify in H9; STOP
             
       |6: reflexivity;]
                          
            ]
    |8: 
    

include "Q/q/qtimes.ma".

let rec area (l:list bar) on l ≝
  match l with 
  [ nil ⇒ OQ
  | cons he tl ⇒ area tl + Qpos (\fst he) * ⅆ[OQ,\snd he]].

alias symbol "pi1" = "exT \fst".
alias symbol "minus" = "Q minus".
alias symbol "exists" = "CProp exists".
definition minus_spec_bar ≝
 λf,g,h:list bar.
   same_bases f g → len f = len g →
     ∀s,i:ℚ. \snd (\fst (value (mk_q_f s h) i)) = 
       \snd (\fst (value (mk_q_f s f) i)) - \snd (\fst (value (mk_q_f s g) i)). 

definition minus_spec ≝
 λf,g:q_f.
   ∃h:q_f. 
     ∀i:ℚ. \snd (\fst (value h i)) = 
       \snd (\fst (value f i)) - \snd (\fst (value g i)). 

definition eject_bar : ∀P:list bar → CProp.(∃l:list bar.P l) → list bar ≝
 λP.λp.match p with [ex_introT x _ ⇒ x].
definition inject_bar ≝ ex_introT (list bar).

coercion inject_bar with 0 1 nocomposites.
coercion eject_bar with 0 0 nocomposites.

lemma minus_q_f : ∀f,g. minus_spec f g.
intros;
letin aux ≝ (
  let rec aux (l1, l2 : list bar) on l1 ≝
    match l1 with
    [ nil ⇒ []
    | cons he1 tl1 ⇒
        match l2 with
        [ nil ⇒ []
        | cons he2 tl2 ⇒ 〈\fst he1, \snd he1 - \snd he2〉 :: aux tl1 tl2]]
  in aux : ∀l1,l2 : list bar.∃h.minus_spec_bar l1 l2 h);
[2: intros 4; simplify in H3; destruct H3;
|3: intros 4; simplify in H3; cases l1 in H2; [2: intro X; simplify in X; destruct X]    
    intros; rewrite > (value_OQ_e (mk_q_f s []) i); [2: reflexivity]
    rewrite > q_elim_minus; rewrite > q_plus_OQ; reflexivity;
|1: cases (aux l2 l3); unfold in H2; intros 4;
    simplify in ⊢ (? ? (? ? ? (? ? ? (? % ?))) ?);
    cases (q_cmp i (s + Qpos (\fst b)));
    


definition excess ≝ 
  λf,g.∃i.\snd (\fst (value f i)) < \snd (\fst (value g i)).
  
