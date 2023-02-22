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

include "excess.ma".

record semi_lattice_base : Type ≝ {
  sl_carr:> apartness;
  sl_op: sl_carr → sl_carr → sl_carr;
  sl_op_refl: ∀x.sl_op x x ≈ x;  
  sl_op_comm: ∀x,y:sl_carr. sl_op x y ≈ sl_op y x;
  sl_op_assoc: ∀x,y,z:sl_carr. sl_op x (sl_op y z) ≈ sl_op (sl_op x y) z;
  sl_strong_extop: ∀x.strong_ext ? (sl_op x)  
}.

notation "a \cross b" left associative with precedence 55 for @{ 'op $a $b }.
interpretation "semi lattice base operation" 'op a b = (sl_op ? a b).

lemma excess_of_semi_lattice_base: semi_lattice_base → excess.
intro l;
apply mk_excess;
[1: apply mk_excess_;
    [1: apply mk_excess_dual_smart;
         
  apply (mk_excess_base (sl_carr l));
    [1: apply (λa,b:sl_carr l.a # (a ✗ b));
    |2: unfold; intros 2 (x H); simplify in H;
        lapply (Ap≪ ? (sl_op_refl ??) H) as H1; clear H;
        apply (ap_coreflexive ?? H1);
    |3: unfold; simplify; intros (x y z H1);
        cases (ap_cotransitive ??? ((x ✗ z) ✗ y) H1) (H2 H2);[2:
          lapply (Ap≪ ? (sl_op_comm ???) H2) as H21;
          lapply (Ap≫ ? (sl_op_comm ???) H21) as H22; clear H21 H2;
          lapply (sl_strong_extop ???? H22); clear H22; 
          left; apply ap_symmetric; assumption;]
        cases (ap_cotransitive ??? (x ✗ z) H2) (H3 H3);[left;assumption]
        right; lapply (Ap≫ ? (sl_op_assoc ????) H3) as H31;
        apply (sl_strong_extop ???? H31);]

    |2:
    apply apartness_of_excess_base; 
    
  apply (mk_excess_base (sl_carr l));
    [1: apply (λa,b:sl_carr l.a # (a ✗ b));
    |2: unfold; intros 2 (x H); simplify in H;
        lapply (Ap≪ ? (sl_op_refl ??) H) as H1; clear H;
        apply (ap_coreflexive ?? H1);
    |3: unfold; simplify; intros (x y z H1);
        cases (ap_cotransitive ??? ((x ✗ z) ✗ y) H1) (H2 H2);[2:
          lapply (Ap≪ ? (sl_op_comm ???) H2) as H21;
          lapply (Ap≫ ? (sl_op_comm ???) H21) as H22; clear H21 H2;
          lapply (sl_strong_extop ???? H22); clear H22; 
          left; apply ap_symmetric; assumption;]
        cases (ap_cotransitive ??? (x ✗ z) H2) (H3 H3);[left;assumption]
        right; lapply (Ap≫ ? (sl_op_assoc ????) H3) as H31;
        apply (sl_strong_extop ???? H31);]
    
    |3: apply refl_eq;]
|2,3: intros (x y H); assumption;]         
qed.    

record semi_lattice : Type ≝ {
  sl_exc:> excess;
  sl_meet: sl_exc → sl_exc → sl_exc;
  sl_meet_refl: ∀x.sl_meet x x ≈ x;  
  sl_meet_comm: ∀x,y. sl_meet x y ≈ sl_meet y x;
  sl_meet_assoc: ∀x,y,z. sl_meet x (sl_meet y z) ≈ sl_meet (sl_meet x y) z;
  sl_strong_extm: ∀x.strong_ext ? (sl_meet x);
  sl_le_to_eqm: ∀x,y.x ≤ y → x ≈ sl_meet x y;
  sl_lem: ∀x,y.(sl_meet x y) ≤ y 
}.
 
interpretation "semi lattice meet" 'and a b = (sl_meet ? a b).

lemma sl_feq_ml: ∀ml:semi_lattice.∀a,b,c:ml. a ≈ b → (c ∧ a) ≈ (c ∧ b).
intros (l a b c H); unfold eq in H ⊢ %; unfold Not in H ⊢ %;
intro H1; apply H; clear H; apply (sl_strong_extm ???? H1);
qed.

lemma sl_feq_mr: ∀ml:semi_lattice.∀a,b,c:ml. a ≈ b → (a ∧ c) ≈ (b ∧ c).
intros (l a b c H); 
apply (Eq≈ ? (sl_meet_comm ???)); apply (Eq≈ ?? (sl_meet_comm ???));
apply sl_feq_ml; assumption;
qed.
 
 
(*
lemma semi_lattice_of_semi_lattice_base: semi_lattice_base → semi_lattice.
intro slb; apply (mk_semi_lattice (excess_of_semi_lattice_base slb));
[1: apply (sl_op slb);
|2: intro x; apply (eq_trans (excess_of_semi_lattice_base slb)); [2: 
      apply (sl_op_refl slb);|1:skip] (sl_op slb x x)); ? (sl_op_refl slb x));

 unfold excess_of_semi_lattice_base; simplify;
    intro H; elim H;
    [ 
    
    
    lapply (ap_rewl (excess_of_semi_lattice_base slb) x ? (sl_op slb x x) 
      (eq_sym (excess_of_semi_lattice_base slb) ?? (sl_op_refl slb x)) t);
    change in x with (sl_carr slb);
    apply (Ap≪ (x ✗ x)); (sl_op_refl slb x)); 

whd in H; elim H; clear H;
    [ apply (ap_coreflexive (excess_of_semi_lattice_base slb) (x ✗ x) t);

prelattice (excess_of_directed l_)); [apply (sl_op l_);]
unfold excess_of_directed; try unfold apart_of_excess; simplify;
unfold excl; simplify;
[intro x; intro H; elim H; clear H; 
 [apply (sl_op_refl l_ x); 
  lapply (Ap≫ ? (sl_op_comm ???) t) as H; clear t; 
  lapply (sl_strong_extop l_ ??? H); apply ap_symmetric; assumption
 | lapply (Ap≪ ? (sl_op_refl ?x) t) as H; clear t;
   lapply (sl_strong_extop l_ ??? H); apply (sl_op_refl l_ x);
   apply ap_symmetric; assumption]
|intros 3 (x y H); cases H (H1 H2); clear H;
 [lapply (Ap≪ ? (sl_op_refl ? (sl_op l_ x y)) H1) as H; clear H1;
  lapply (sl_strong_extop l_ ??? H) as H1; clear H;
  lapply (Ap≪ ? (sl_op_comm ???) H1); apply (ap_coreflexive ?? Hletin);
 |lapply (Ap≪ ? (sl_op_refl ? (sl_op l_ y x)) H2) as H; clear H2;
  lapply (sl_strong_extop l_ ??? H) as H1; clear H;
  lapply (Ap≪ ? (sl_op_comm ???) H1);apply (ap_coreflexive ?? Hletin);]
|intros 4 (x y z H); cases H (H1 H2); clear H;
 [lapply (Ap≪ ? (sl_op_refl ? (sl_op l_ x (sl_op l_ y z))) H1) as H; clear H1;
  lapply (sl_strong_extop l_ ??? H) as H1; clear H;
  lapply (Ap≪ ? (eq_sym ??? (sl_op_assoc ?x y z)) H1) as H; clear H1;
  apply (ap_coreflexive ?? H);
 |lapply (Ap≪ ? (sl_op_refl ? (sl_op l_ (sl_op l_ x y) z)) H2) as H; clear H2;
  lapply (sl_strong_extop l_ ??? H) as H1; clear H;
  lapply (Ap≪ ? (sl_op_assoc ?x y z) H1) as H; clear H1;
  apply (ap_coreflexive ?? H);]
|intros (x y z H); elim H (H1 H1); clear H;
 lapply (Ap≪ ? (sl_op_refl ??) H1) as H; clear H1;
 lapply (sl_strong_extop l_ ??? H) as H1; clear H;
 lapply (sl_strong_extop l_ ??? H1) as H; clear H1;
 cases (ap_cotransitive ??? (sl_op l_ y z) H);[left|right|right|left] try assumption;
 [apply ap_symmetric;apply (Ap≪ ? (sl_op_comm ???));
 |apply (Ap≫ ? (sl_op_comm ???));
 |apply ap_symmetric;] assumption;
|intros 4 (x y H H1); apply H; clear H; elim H1 (H H);
 lapply (Ap≪ ? (sl_op_refl ??) H) as H1; clear H;
 lapply (sl_strong_extop l_ ??? H1) as H; clear H1;[2: apply ap_symmetric]
 assumption
|intros 3 (x y H); 
 cut (sl_op l_ x y ≈ sl_op l_ x (sl_op l_ y y)) as H1;[2:
   intro; lapply (sl_strong_extop ???? a); apply (sl_op_refl l_ y);
   apply ap_symmetric; assumption;]
 lapply (Ap≪ ? (eq_sym ??? H1) H); apply (sl_op_assoc l_ x y y);
 assumption; ]
qed.
*)

(* ED(≰,≱) → EB(≰') → ED(≰',≱') *)
lemma subst_excess_base: excess_dual → excess_base → excess_dual.
intros; apply (mk_excess_dual_smart e1);
qed.

(* E_(ED(≰,≱),AP(#),c ED = c AP) → ED' → c DE' = c E_ → E_(ED',#,p) *)
lemma subst_dual_excess: ∀e:excess_.∀e1:excess_dual.exc_carr e = exc_carr e1 → excess_.
intros (e e1 p); apply (mk_excess_ e1 e); cases p; reflexivity;
qed. 

(* E(E_,H1,H2) → E_' → H1' → H2' → E(E_',H1',H2') *)
alias symbol "nleq" = "Excess excess_".
lemma subst_excess_: ∀e:excess. ∀e1:excess_. 
  (∀y,x:e1. y # x → y ≰ x ∨ x ≰ y) →
  (∀y,x:e1.y ≰ x ∨ x ≰ y →  y # x) →
  excess.
intros (e e1 H1 H2); apply (mk_excess e1 H1 H2); 
qed. 

definition hole ≝ λT:Type.λx:T.x.

notation < "\ldots" non associative with precedence 55 for @{'hole}.
interpretation "hole" 'hole = (hole ? ?).

(* SL(E,M,H2-5(#),H67(≰)) → E' → c E = c E' → H67'(≰') → SL(E,M,p2-5,H67') *)
lemma subst_excess: 
  ∀l:semi_lattice.
  ∀e:excess. 
  ∀p:exc_ap l = exc_ap e.
  (∀x,y:e.(le (exc_dual_base e)) x y → x ≈ (?(sl_meet l)) x y) →
  (∀x,y:e.(le (exc_dual_base e)) ((?(sl_meet l)) x y) y) → 
  semi_lattice.
[1,2:intro M;
 change with ((λx.ap_carr x) e -> (λx.ap_carr x) e -> (λx.ap_carr x) e);
 cases p; apply M;
|intros (l e p H1 H2);
 apply (mk_semi_lattice e);
   [ change with ((λx.ap_carr x) e -> (λx.ap_carr x) e -> (λx.ap_carr x) e);
     cases p; simplify; apply (sl_meet l);
   |2: change in ⊢ (% → ?) with ((λx.ap_carr x) e); cases p; simplify; apply sl_meet_refl;
   |3: change in ⊢ (% → % → ?) with ((λx.ap_carr x) e); cases p; simplify; apply sl_meet_comm;
   |4: change in ⊢ (% → % → % → ?) with ((λx.ap_carr x) e); cases p; simplify; apply sl_meet_assoc;  
   |5: change in ⊢ (% → ?) with ((λx.ap_carr x) e); cases p; simplify; apply sl_strong_extm;
   |6: clear H2; apply hole; apply H1;
   |7: clear H1; apply hole; apply H2;]]
qed.

lemma excess_of_excess_base: excess_base → excess.
intro eb;
apply mk_excess;
  [apply (mk_excess_ (mk_excess_dual_smart eb));
    [apply (apartness_of_excess_base eb);
    |reflexivity]
  |2,3: intros; assumption]
qed. 

lemma subst_excess_preserves_aprtness:
  ∀l:semi_lattice.
  ∀e:excess.
  ∀p,H1,H2. 
  exc_ap l = exc_ap (subst_excess l e p H1 H2).
intros; 
unfold subst_excess;
simplify; assumption;
qed.


lemma subst_excess__preserves_aprtness:
  ∀l:excess.
  ∀e:excess_base.
  ∀p,H1,H2. 
  exc_ap l = apartness_OF_excess (subst_excess_ l (subst_dual_excess l (subst_excess_base l e) p) H1 H2).
intros 3; (unfold subst_excess_; unfold subst_dual_excess; unfold subst_excess_base; unfold exc_ap; unfold mk_excess_dual_smart; simplify);
(unfold subst_excess_base in p; unfold mk_excess_dual_smart in p; simplify in p);
intros; cases p;
reflexivity;
qed.

lemma subst_excess_base_in_excess_:
  ∀d:excess_.
  ∀eb:excess_base.
  ∀p:exc_carr d = exc_carr eb.
  excess_.
intros (e_ eb);
apply (subst_dual_excess e_);
  [apply (subst_excess_base e_ eb);
  |assumption]
qed.

lemma subst_excess_base_in_excess:
  ∀d:excess.
  ∀eb:excess_base.
  ∀p:exc_carr d = exc_carr eb.
  (∀y1,x1:eb. (?(ap_apart d)) y1  x1 → y1 ≰ x1 ∨ x1 ≰ y1) →
  (∀y2,x2:eb.y2 ≰ x2 ∨ x2 ≰ y2 →  (?(ap_apart d)) y2 x2) →
  excess.
[1,3,4:apply Type|2,5:intro f; cases p; apply f]
intros (d eb p H1 H2);
apply (subst_excess_ d);
  [apply (subst_excess_base_in_excess_ d eb p);
  |apply hole; clear H2; 
   change in ⊢ (%→%→?) with (exc_carr eb);      
   change in ⊢ (?→?→?→? (? % ? ?) (? % ? ?)) with eb; intros (y x H3);
   apply H1; generalize in match H3;
   unfold ap_apart; unfold subst_excess_base_in_excess_;
   unfold subst_dual_excess; simplify; 
   generalize in match x;
   generalize in match y;
   cases p; simplify; intros; assumption;
  |apply hole; clear H1; 
   change in ⊢ (%→%→?) with (exc_carr eb);      
   change in ⊢ (?→?→? (? % ? ?) (? % ? ?)→?) with eb; intros (y x H3);
   unfold ap_apart; unfold subst_excess_base_in_excess_;
   unfold subst_dual_excess; simplify; generalize in match (H2 ?? H3);
   generalize in match x; generalize in match y; cases p;
   intros; assumption;]
qed.    

lemma tech1: ∀e:excess.
 ∀eb:excess_base.
 ∀p,H1,H2.
 exc_ap e = exc_ap_  (subst_excess_base_in_excess e eb p H1 H2).
intros (e eb p H1 H2);
unfold subst_excess_base_in_excess;
unfold subst_excess_; simplify;
unfold subst_excess_base_in_excess_;
unfold subst_dual_excess; simplify; reflexivity;
qed.

lemma tech2: 
 ∀e:excess_.∀eb.∀p.
  exc_ap e = exc_ap (mk_excess_ (subst_excess_base e eb) (exc_ap e) p).
intros (e eb p);unfold exc_ap; simplify; cases p; simplify; reflexivity;
qed.
  
(*
lemma eq_fap:
 ∀a1,b1,a2,b2,a3,b3,a4,b4,a5,b5.
 a1=b1 → a2=b2 → a3=b3 → a4=b4 → a5=b5 → mk_apartness a1 a2 a3 a4 a5 = mk_apartness b1 b2 b3 b4 b5.
intros; cases H; cases H1; cases H2; cases H3; cases H4; reflexivity;
qed.
*)

lemma subst_excess_base_in_excess_preserves_apartness:
 ∀e:excess.
 ∀eb:excess_base.
 ∀H,H1,H2.
 apartness_OF_excess e =
 apartness_OF_excess (subst_excess_base_in_excess e eb H H1 H2).
intros (e eb p H1 H2);
unfold subst_excess_base_in_excess;
unfold subst_excess_; unfold subst_excess_base_in_excess_;
unfold subst_dual_excess; unfold apartness_OF_excess;
simplify in ⊢ (? ? ? (? %));
rewrite < (tech2 e eb );
reflexivity;
qed.
 
 
 
alias symbol "nleq" = "Excess base excess".
lemma subst_excess_base_in_semi_lattice: 
  ∀sl:semi_lattice.
  ∀eb:excess_base.
  ∀p:exc_carr sl = exc_carr eb.
  (∀y1,x1:eb. (?(ap_apart sl)) y1  x1 → y1 ≰ x1 ∨ x1 ≰ y1) →
  (∀y2,x2:eb.y2 ≰ x2 ∨ x2 ≰ y2 →  (?(ap_apart sl)) y2 x2) →
  (∀x3,y3:eb.(le eb) x3 y3 → (?(eq sl)) x3 ((?(sl_meet sl)) x3 y3)) →
  (∀x4,y4:eb.(le eb) ((?(sl_meet sl)) x4 y4) y4) → 
  semi_lattice.
[2:apply Prop|3,7,9,10:apply Type|4:apply (exc_carr eb)|1,5,6,8,11:intro f; cases p; apply f;]
intros (sl eb H H1 H2 H3 H4); 
apply (subst_excess sl);
  [apply (subst_excess_base_in_excess sl eb H H1 H2);
  |apply subst_excess_base_in_excess_preserves_apartness;
  |change in ⊢ (%→%→?) with ((λx.ap_carr x) (subst_excess_base_in_excess (sl_exc sl) eb H H1 H2)); simplify;
   intros 3 (x y LE); clear H3 LE;
   generalize in match x as x; generalize in match y as y;
   generalize in match H1 as H1;generalize in match H2 as H2;
   clear x y H1 H2 H4; STOP
 
   apply (match H return λr:Type.λm:Type_OF_semi_lattice sl=r.
   ∀H2:(Πy2:exc_carr eb
               .Πx2:exc_carr eb
                .Or (exc_excess eb y2 x2) (exc_excess eb x2 y2)
                 →match H
                     in eq
                     return 
                    λright_1:Type
                    .(λmatched:eq Type (Type_OF_semi_lattice sl) right_1
                      .right_1→right_1→Type)
                     with 
                    [refl_eq⇒ap_apart (apartness_OF_semi_lattice sl)] y2 x2)
.∀H1:Πy1:exc_carr eb
               .Πx1:exc_carr eb
                .match H
                  in eq
                  return 
                 λright_1:Type
                 .(λmatched:eq Type (Type_OF_semi_lattice sl) right_1
                   .right_1→right_1→Type)
                  with 
                 [refl_eq⇒ap_apart (apartness_OF_semi_lattice sl)] y1 x1
                 →Or (exc_excess eb y1 x1) (exc_excess eb x1 y1)
 .∀y:ap_carr
              (apartness_OF_excess (subst_excess_base_in_excess (sl_exc sl) eb H H1 H2))
  .∀x:ap_carr
               (apartness_OF_excess
                (subst_excess_base_in_excess (sl_exc sl) eb H H1 H2))
   .eq
    (apartness_OF_excess (subst_excess_base_in_excess (sl_exc sl) eb H H1 H2)) x
    (match 
     subst_excess_base_in_excess_preserves_apartness (sl_exc sl) eb H H1 H2
      in eq
      return 
     λright_1:apartness
     .(λmatched:eq apartness (apartness_OF_semi_lattice sl) right_1
       .ap_carr right_1→ap_carr right_1→ap_carr right_1)
      with 
     [refl_eq⇒sl_meet sl] x y)
   
   with [ refl_eq ⇒ ?]);
   
   
   cases (subst_excess_base_in_excess_preserves_apartness sl eb H H1 H2);
   cases H;
   cases (subst_excess_base_in_excess_preserves_apartness (sl_exc sl) eb H H1 H2); simplify;
   change in x:(%) with (exc_carr eb);
   change in y:(%) with (exc_carr eb);
   generalize in match OK; generalize in match x as x; generalize in match y as y;
   cases H; simplify; (* funge, ma devo fare 2 rewrite in un colpo solo *)
   *) 
  |cases FALSE;
  ] 
qed.

record lattice_ : Type ≝ {
  latt_mcarr:> semi_lattice;
  latt_jcarr_: semi_lattice;
  W1:?; W2:?; W3:?; W4:?; W5:?;
  latt_with1: latt_jcarr_ = subst_excess_base_in_semi_lattice latt_jcarr_
    (excess_base_OF_semi_lattice latt_mcarr) W1 W2 W3 W4 W5   
}.

lemma latt_jcarr : lattice_ → semi_lattice.
intro l; apply (subst_excess_base_in_semi_lattice (latt_jcarr_ l) (excess_base_OF_semi_lattice (latt_mcarr l)) (W1 l) (W2 l) (W3 l) (W4 l) (W5 l));
qed.
    
coercion cic:/matita/lattice/latt_jcarr.con.

interpretation "Lattice meet" 'and a b =
 (sl_meet (latt_mcarr _) a b).  

interpretation "Lattice join" 'or a b =
 (sl_meet (latt_jcarr _) a b).  

record lattice : Type ≝ {
  latt_carr:> lattice_;
  absorbjm: ∀f,g:latt_carr. (f ∨ (f ∧ g)) ≈ f;
  absorbmj: ∀f,g:latt_carr. (f ∧ (f ∨ g)) ≈ f
}.

notation "'meet'"        non associative with precedence 55 for @{'meet}.
notation "'meet_refl'"   non associative with precedence 55 for @{'meet_refl}.
notation "'meet_comm'"   non associative with precedence 55 for @{'meet_comm}.
notation "'meet_assoc'"  non associative with precedence 55 for @{'meet_assoc}.
notation "'strong_extm'" non associative with precedence 55 for @{'strong_extm}.
notation "'le_to_eqm'"   non associative with precedence 55 for @{'le_to_eqm}.
notation "'lem'"         non associative with precedence 55 for @{'lem}.
notation "'join'"        non associative with precedence 55 for @{'join}.
notation "'join_refl'"   non associative with precedence 55 for @{'join_refl}.
notation "'join_comm'"   non associative with precedence 55 for @{'join_comm}.
notation "'join_assoc'"  non associative with precedence 55 for @{'join_assoc}.
notation "'strong_extj'" non associative with precedence 55 for @{'strong_extj}.
notation "'le_to_eqj'"   non associative with precedence 55 for @{'le_to_eqj}.
notation "'lej'"         non associative with precedence 55 for @{'lej}.

interpretation "Lattice meet"        'meet        = (sl_meet (latt_mcarr ?)).
interpretation "Lattice meet_refl"   'meet_refl   = (sl_meet_refl (latt_mcarr ?)).
interpretation "Lattice meet_comm"   'meet_comm   = (sl_meet_comm (latt_mcarr ?)).
interpretation "Lattice meet_assoc"  'meet_assoc  = (sl_meet_assoc (latt_mcarr ?)).
interpretation "Lattice strong_extm" 'strong_extm = (sl_strong_extm (latt_mcarr ?)).
interpretation "Lattice le_to_eqm"   'le_to_eqm   = (sl_le_to_eqm (latt_mcarr ?)).
interpretation "Lattice lem"         'lem         = (sl_lem (latt_mcarr ?)).
interpretation "Lattice join"        'join        = (sl_meet (latt_jcarr ?)).
interpretation "Lattice join_refl"   'join_refl   = (sl_meet_refl (latt_jcarr ?)).
interpretation "Lattice join_comm"   'join_comm   = (sl_meet_comm (latt_jcarr ?)).
interpretation "Lattice join_assoc"  'join_assoc  = (sl_meet_assoc (latt_jcarr ?)).
interpretation "Lattice strong_extm" 'strong_extj = (sl_strong_extm (latt_jcarr ?)).
interpretation "Lattice le_to_eqj"   'le_to_eqj   = (sl_le_to_eqm (latt_jcarr ?)).
interpretation "Lattice lej"         'lej         = (sl_lem (latt_jcarr ?)).

notation "'feq_jl'" non associative with precedence 55 for @{'feq_jl}.
notation "'feq_jr'" non associative with precedence 55 for @{'feq_jr}.
notation "'feq_ml'" non associative with precedence 55 for @{'feq_ml}.
notation "'feq_mr'" non associative with precedence 55 for @{'feq_mr}.
interpretation "Lattice feq_jl" 'feq_jl = (sl_feq_ml (latt_jcarr ?)).
interpretation "Lattice feq_jr" 'feq_jr = (sl_feq_mr (latt_jcarr ?)).
interpretation "Lattice feq_ml" 'feq_ml = (sl_feq_ml (latt_mcarr ?)).
interpretation "Lattice feq_mr" 'feq_mr = (sl_feq_mr (latt_mcarr ?)).


interpretation "Lattive meet le" 'leq a b = (le (excess_OF_lattice1 ?) a b).

interpretation "Lattive join le (aka ge)" 'geq a b =
 (le (excess_OF_lattice _) a b).

(* these coercions help unification, handmaking a bit of conversion 
   over an open term 
*)
lemma le_to_ge: ∀l:lattice.∀a,b:l.a ≤ b → b ≥ a.
intros(l a b H); apply H;
qed.

lemma ge_to_le: ∀l:lattice.∀a,b:l.b ≥ a → a ≤ b.
intros(l a b H); apply H;
qed.

coercion cic:/matita/lattice/le_to_ge.con nocomposites.
coercion cic:/matita/lattice/ge_to_le.con nocomposites.
