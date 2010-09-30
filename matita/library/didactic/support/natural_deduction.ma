(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

(* Logic system *)

inductive Imply (A,B:CProp) : CProp ≝
| Imply_intro: (A → B) → Imply A B.
 
definition Imply_elim ≝ λA,B.λf:Imply A B. λa:A.
  match f with [ Imply_intro g ⇒ g a].

inductive And (A,B:CProp) : CProp ≝
| And_intro: A → B → And A B.

definition And_elim_l ≝ λA,B.λc:And A B.
  match c with [ And_intro a b ⇒ a ].

definition And_elim_r ≝ λA,B.λc:And A B.
  match c with [ And_intro a b ⇒ b ].

inductive Or (A,B:CProp) : CProp ≝
| Or_intro_l: A → Or A B
| Or_intro_r: B → Or A B. 
 
definition Or_elim ≝ λA,B,C:CProp.λc:Or A B.λfa: A → C.λfb: B → C.
  match c with 
  [ Or_intro_l a ⇒ fa a 
  | Or_intro_r b ⇒ fb b].

inductive Top : CProp := 
| Top_intro : Top.

inductive Bot : CProp := .

definition Bot_elim ≝ λP:CProp.λx:Bot.
  match x in Bot return λx.P with []. 

definition Not := λA:CProp.Imply A Bot.

definition Not_intro : ∀A.(A → Bot) → Not A ≝  λA. 
  Imply_intro A Bot.

definition Not_elim : ∀A.Not A → A → Bot ≝ λA. 
  Imply_elim ? Bot.  

definition Discharge := λA:CProp.λa:A.
  a.

axiom Raa : ∀A.(Not A → Bot) → A.

axiom sort : Type.

inductive Exists (A:Type) (P:A→CProp) : CProp ≝
  Exists_intro: ∀w:A. P w → Exists A P.

definition Exists_elim ≝
  λA:Type.λP:A→CProp.λC:CProp.λc:Exists A P.λH:(Πx.P x → C).
   match c with [ Exists_intro w p ⇒ H w p ].

inductive Forall (A:Type) (P:A→CProp) : CProp ≝
 Forall_intro: (∀n:A. P n) → Forall A P.

definition Forall_elim ≝
 λA:Type.λP:A→CProp.λn:A.λf:Forall A P.match f with [ Forall_intro g ⇒ g n ].

(* Dummy proposition *)
axiom unit : CProp.

(* Notations *)
notation "hbox(a break ⇒ b)" right associative with precedence 20 
for @{ 'Imply $a $b }.
interpretation "Imply" 'Imply a b = (Imply a b).
interpretation "constructive or" 'or x y = (Or x y).
interpretation "constructive and" 'and x y = (And x y).
notation "⊤" non associative with precedence 90 for @{'Top}.
interpretation "Top" 'Top = Top.
notation "⊥" non associative with precedence 90 for @{'Bot}.
interpretation "Bot" 'Bot = Bot.
interpretation "Not" 'not a = (Not a).
notation "✶" non associative with precedence 90 for @{'unit}.
interpretation "dummy prop" 'unit = unit.
notation > "\exists list1 ident x sep , . term 19 Px" with precedence 20
for ${ fold right @{$Px} rec acc @{'myexists (λ${ident x}.$acc)} }.
notation < "hvbox(\exists ident i break . p)" with precedence 20
for @{ 'myexists (\lambda ${ident i} : $ty. $p) }.
interpretation "constructive ex" 'myexists \eta.x = (Exists sort x).
notation > "\forall ident x.break term 19 Px" with precedence 20
for @{ 'Forall (λ${ident x}.$Px) }.
notation < "\forall ident x.break term 19 Px" with precedence 20
for @{ 'Forall (λ${ident x}:$tx.$Px) }.
interpretation "Forall" 'Forall \eta.Px = (Forall ? Px).
 
(* Variables *)
axiom A : CProp.
axiom B : CProp.
axiom C : CProp.
axiom D : CProp.
axiom E : CProp.
axiom F : CProp.
axiom G : CProp.
axiom H : CProp.
axiom I : CProp.
axiom J : CProp.
axiom K : CProp.
axiom L : CProp.
axiom M : CProp.
axiom N : CProp.
axiom O : CProp.
axiom  x: sort.
axiom  y: sort.
axiom  z: sort.
axiom  w: sort.

(* Every formula user provided annotates its proof:
   `A` becomes `(show A ?)` *)
definition show : ΠA.A→A ≝ λA:CProp.λa:A.a.

(* When something does not fit, this daemon is used *)
axiom cast: ΠA,B:CProp.B → A.

(* begin a proof: draws the root *)
notation > "'prove' p" non associative with precedence 19 
for @{ 'prove $p }.
interpretation "prove KO" 'prove p = (cast ? ? (show p ?)).
interpretation "prove OK" 'prove p = (show p ?).

(* Leaves *)
notation < "\infrule (t\atop ⋮) a ?" with precedence 19
for @{ 'leaf_ok $a $t }.
interpretation "leaf OK" 'leaf_ok a t = (show a t).
notation < "\infrule (t\atop ⋮) mstyle color #ff0000 (a) ?" with precedence 19 
for @{ 'leaf_ko $a $t }.
interpretation "leaf KO" 'leaf_ko a t = (cast ? ? (show a t)).

(* discharging *)
notation < "[ a ] \sup mstyle color #ff0000 (H)" with precedence 19 
for @{ 'discharge_ko_1 $a $H }.
interpretation "discharge_ko_1" 'discharge_ko_1 a H = 
  (show a (cast ? ? (Discharge ? H))).
notation < "[ mstyle color #ff0000 (a) ] \sup mstyle color #ff0000 (H)" with precedence 19 
for @{ 'discharge_ko_2 $a $H }.
interpretation "discharge_ko_2" 'discharge_ko_2 a H = 
  (cast ? ? (show a (cast ? ? (Discharge ? H)))).

notation < "[ a ] \sup H" with precedence 19 
for @{ 'discharge_ok_1 $a $H }.
interpretation "discharge_ok_1" 'discharge_ok_1 a H = 
  (show a (Discharge ? H)).
notation < "[ mstyle color #ff0000 (a) ] \sup H" with precedence 19 
for @{ 'discharge_ok_2 $a $H }.
interpretation "discharge_ok_2" 'discharge_ok_2 a H = 
  (cast ? ? (show a (Discharge ? H))).

notation > "'discharge' [H]" with precedence 19 
for @{ 'discharge $H }.
interpretation "discharge KO" 'discharge H = (cast ? ? (Discharge ? H)).
interpretation "discharge OK" 'discharge H = (Discharge ? H).

(* ⇒ introduction *)
notation < "\infrule hbox(\emsp b \emsp) ab (mstyle color #ff0000 (⇒\sub\i \emsp) ident H) " with precedence 19
for @{ 'Imply_intro_ko_1 $ab (λ${ident H}:$p.$b) }.
interpretation "Imply_intro_ko_1" 'Imply_intro_ko_1 ab \eta.b = 
  (show ab (cast ? ? (Imply_intro ? ? b))).

notation < "\infrule hbox(\emsp b \emsp) mstyle color #ff0000 (ab) (mstyle color #ff0000 (⇒\sub\i \emsp) ident H) " with precedence 19
for @{ 'Imply_intro_ko_2 $ab (λ${ident H}:$p.$b) }.
interpretation "Imply_intro_ko_2" 'Imply_intro_ko_2 ab \eta.b = 
  (cast ? ? (show ab (cast ? ? (Imply_intro ? ? b)))).

notation < "maction (\infrule hbox(\emsp b \emsp) ab (⇒\sub\i \emsp ident H) ) (\vdots)" with precedence 19
for @{ 'Imply_intro_ok_1 $ab (λ${ident H}:$p.$b) }.
interpretation "Imply_intro_ok_1" 'Imply_intro_ok_1 ab \eta.b = 
  (show ab (Imply_intro ? ? b)).

notation < "\infrule hbox(\emsp b \emsp) mstyle color #ff0000 (ab) (⇒\sub\i \emsp ident H) " with precedence 19
for @{ 'Imply_intro_ok_2 $ab (λ${ident H}:$p.$b) }.
interpretation "Imply_intro_ok_2" 'Imply_intro_ok_2 ab \eta.b = 
  (cast ? ? (show ab (Imply_intro ? ? b))).

notation > "⇒#'i' [ident H] term 90 b" with precedence 19
for @{ 'Imply_intro $b (λ${ident H}.show $b ?) }.

interpretation "Imply_intro KO" 'Imply_intro b pb = 
  (cast ? (Imply unit b) (Imply_intro ? b pb)).
interpretation "Imply_intro OK" 'Imply_intro b pb = 
  (Imply_intro ? b pb).

(* ⇒ elimination *)
notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) b mstyle color #ff0000 (⇒\sub\e) " with precedence 19
for @{ 'Imply_elim_ko_1 $ab $a $b }.
interpretation "Imply_elim_ko_1" 'Imply_elim_ko_1 ab a b = 
  (show b (cast ? ? (Imply_elim ? ? (cast ? ? ab) (cast ? ? a)))).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) mstyle color #ff0000 (b) mstyle color #ff0000 (⇒\sub\e) " with precedence 19 
for @{ 'Imply_elim_ko_2 $ab $a $b }.
interpretation "Imply_elim_ko_2" 'Imply_elim_ko_2 ab a b = 
  (cast ? ? (show b (cast ? ? (Imply_elim ? ? (cast ? ? ab) (cast ? ? a))))).

notation < "maction (\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) b (⇒\sub\e) ) (\vdots)" with precedence 19 
for @{ 'Imply_elim_ok_1 $ab $a $b }.
interpretation "Imply_elim_ok_1" 'Imply_elim_ok_1 ab a b = 
  (show b (Imply_elim ? ? ab a)).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) mstyle color #ff0000 (b) (⇒\sub\e) " with precedence 19 
for @{ 'Imply_elim_ok_2 $ab $a $b }.
interpretation "Imply_elim_ok_2" 'Imply_elim_ok_2 ab a b = 
  (cast ? ? (show b (Imply_elim ? ? ab a))).

notation > "⇒#'e' term 90 ab term 90 a" with precedence 19 
for @{ 'Imply_elim (show $ab ?) (show $a ?) }.
interpretation "Imply_elim KO" 'Imply_elim ab a = 
  (cast ? ? (Imply_elim ? ? (cast (Imply unit unit) ? ab) (cast unit ? a))).
interpretation "Imply_elim OK" 'Imply_elim ab a = 
  (Imply_elim ? ? ab a). 

(* ∧ introduction *)
notation < "\infrule hbox(\emsp a \emsp\emsp\emsp b \emsp) ab mstyle color #ff0000 (∧\sub\i)" with precedence 19 
for @{ 'And_intro_ko_1 $a $b $ab }.
interpretation "And_intro_ko_1" 'And_intro_ko_1 a b ab = 
  (show ab (cast ? ? (And_intro ? ? a b))).

notation < "\infrule hbox(\emsp a \emsp\emsp\emsp b \emsp) mstyle color #ff0000 (ab) mstyle color #ff0000 (∧\sub\i)" with precedence 19 
for @{ 'And_intro_ko_2 $a $b $ab }.
interpretation "And_intro_ko_2" 'And_intro_ko_2 a b ab = 
  (cast ? ? (show ab (cast ? ? (And_intro ? ? a b)))).

notation < "maction (\infrule hbox(\emsp a \emsp\emsp\emsp b \emsp) ab (∧\sub\i)) (\vdots)" with precedence 19 
for @{ 'And_intro_ok_1 $a $b $ab }.
interpretation "And_intro_ok_1" 'And_intro_ok_1 a b ab = 
  (show ab (And_intro ? ? a b)).

notation < "\infrule hbox(\emsp a \emsp\emsp\emsp b \emsp) mstyle color #ff0000 (ab) (∧\sub\i)" with precedence 19 
for @{ 'And_intro_ok_2 $a $b $ab }.
interpretation "And_intro_ok_2" 'And_intro_ok_2 a b ab = 
  (cast ? ? (show ab (And_intro ? ? a b))).

notation > "∧#'i' term 90 a term 90 b" with precedence 19 
for @{ 'And_intro (show $a ?) (show $b ?) }.
interpretation "And_intro KO" 'And_intro a b = (cast ? ? (And_intro ? ? a b)).
interpretation "And_intro OK" 'And_intro a b = (And_intro ? ? a b).

(* ∧ elimination *)
notation < "\infrule hbox(\emsp ab \emsp) a mstyle color #ff0000 (∧\sub(\e_\l))" with precedence 19 
for @{ 'And_elim_l_ko_1 $ab $a }.
interpretation "And_elim_l_ko_1" 'And_elim_l_ko_1 ab a = 
  (show a (cast ? ? (And_elim_l ? ? (cast ? ? ab)))).

notation < "\infrule hbox(\emsp ab \emsp) mstyle color #ff0000 (a) mstyle color #ff0000 (∧\sub(\e_\l))" with precedence 19 
for @{ 'And_elim_l_ko_2 $ab $a }.
interpretation "And_elim_l_ko_2" 'And_elim_l_ko_2 ab a = 
  (cast ? ? (show a (cast ? ? (And_elim_l ? ? (cast ? ? ab))))).

notation < "maction (\infrule hbox(\emsp ab \emsp) a (∧\sub(\e_\l))) (\vdots)" with precedence 19 
for @{ 'And_elim_l_ok_1 $ab $a }.
interpretation "And_elim_l_ok_1" 'And_elim_l_ok_1 ab a = 
  (show a (And_elim_l ? ? ab)).

notation < "\infrule hbox(\emsp ab \emsp) mstyle color #ff0000 (a) (∧\sub(\e_\l))" with precedence 19 
for @{ 'And_elim_l_ok_2 $ab $a }.
interpretation "And_elim_l_ok_2" 'And_elim_l_ok_2 ab a = 
  (cast ? ? (show a (And_elim_l ? ? ab))).

notation > "∧#'e_l' term 90 ab" with precedence 19
for @{ 'And_elim_l (show $ab ?) }.
interpretation "And_elim_l KO" 'And_elim_l a = (cast ? ? (And_elim_l ? ? (cast (And unit unit) ? a))).
interpretation "And_elim_l OK" 'And_elim_l a = (And_elim_l ? ? a).

notation < "\infrule hbox(\emsp ab \emsp) a mstyle color #ff0000 (∧\sub(\e_\r))" with precedence 19 
for @{ 'And_elim_r_ko_1 $ab $a }.
interpretation "And_elim_r_ko_1" 'And_elim_r_ko_1 ab a = 
  (show a (cast ? ? (And_elim_r ? ? (cast ? ? ab)))).

notation < "\infrule hbox(\emsp ab \emsp) mstyle color #ff0000 (a) mstyle color #ff0000 (∧\sub(\e_\r))" with precedence 19 
for @{ 'And_elim_r_ko_2 $ab $a }.
interpretation "And_elim_r_ko_2" 'And_elim_r_ko_2 ab a = 
  (cast ? ? (show a (cast ? ? (And_elim_r ? ? (cast ? ? ab))))).

notation < "maction (\infrule hbox(\emsp ab \emsp) a (∧\sub(\e_\r))) (\vdots)" with precedence 19 
for @{ 'And_elim_r_ok_1 $ab $a }.
interpretation "And_elim_r_ok_1" 'And_elim_r_ok_1 ab a = 
  (show a (And_elim_r ? ? ab)).

notation < "\infrule hbox(\emsp ab \emsp) mstyle color #ff0000 (a) (∧\sub(\e_\r))" with precedence 19 
for @{ 'And_elim_r_ok_2 $ab $a }.
interpretation "And_elim_r_ok_2" 'And_elim_r_ok_2 ab a = 
  (cast ? ? (show a (And_elim_r ? ? ab))).

notation > "∧#'e_r' term 90 ab" with precedence 19
for @{ 'And_elim_r (show $ab ?) }.
interpretation "And_elim_r KO" 'And_elim_r a = (cast ? ? (And_elim_r ? ? (cast (And unit unit) ? a))).
interpretation "And_elim_r OK" 'And_elim_r a = (And_elim_r ? ? a).

(* ∨ introduction *)
notation < "\infrule hbox(\emsp a \emsp) ab mstyle color #ff0000 (∨\sub(\i_\l))" with precedence 19 
for @{ 'Or_intro_l_ko_1 $a $ab }.
interpretation "Or_intro_l_ko_1" 'Or_intro_l_ko_1 a ab = 
  (show ab (cast ? ? (Or_intro_l ? ? a))).

notation < "\infrule hbox(\emsp a \emsp) mstyle color #ff0000 (ab) mstyle color #ff0000 (∨\sub(\i_\l))" with precedence 19 
for @{ 'Or_intro_l_ko_2 $a $ab }.
interpretation "Or_intro_l_ko_2" 'Or_intro_l_ko_2 a ab = 
  (cast ? ? (show ab (cast ? ? (Or_intro_l ? ? a)))).

notation < "maction (\infrule hbox(\emsp a \emsp) ab (∨\sub(\i_\l))) (\vdots)" with precedence 19 
for @{ 'Or_intro_l_ok_1 $a $ab }.
interpretation "Or_intro_l_ok_1" 'Or_intro_l_ok_1 a ab = 
  (show ab (Or_intro_l ? ? a)).

notation < "\infrule hbox(\emsp a \emsp) mstyle color #ff0000 (ab) (∨\sub(\i_\l))" with precedence 19 
for @{ 'Or_intro_l_ok_2 $a $ab }.
interpretation "Or_intro_l_ok_2" 'Or_intro_l_ok_2 a ab = 
  (cast ? ? (show ab (Or_intro_l ? ? a))).

notation > "∨#'i_l' term 90 a" with precedence 19
for @{ 'Or_intro_l (show $a ?) }.
interpretation "Or_intro_l KO" 'Or_intro_l a = (cast ? (Or ? unit) (Or_intro_l ? ? a)).
interpretation "Or_intro_l OK" 'Or_intro_l a = (Or_intro_l ? ? a). 
  
notation < "\infrule hbox(\emsp a \emsp) ab mstyle color #ff0000 (∨\sub(\i_\r))" with precedence 19 
for @{ 'Or_intro_r_ko_1 $a $ab }.
interpretation "Or_intro_r_ko_1" 'Or_intro_r_ko_1 a ab = 
  (show ab (cast ? ? (Or_intro_r ? ? a))).

notation < "\infrule hbox(\emsp a \emsp) mstyle color #ff0000 (ab) mstyle color #ff0000 (∨\sub(\i_\r))" with precedence 19 
for @{ 'Or_intro_r_ko_2 $a $ab }.
interpretation "Or_intro_r_ko_2" 'Or_intro_r_ko_2 a ab = 
  (cast ? ? (show ab (cast ? ? (Or_intro_r ? ? a)))).

notation < "maction (\infrule hbox(\emsp a \emsp) ab (∨\sub(\i_\r))) (\vdots)" with precedence 19 
for @{ 'Or_intro_r_ok_1 $a $ab }.
interpretation "Or_intro_r_ok_1" 'Or_intro_r_ok_1 a ab = 
  (show ab (Or_intro_r ? ? a)).

notation < "\infrule hbox(\emsp a \emsp) mstyle color #ff0000 (ab) (∨\sub(\i_\r))" with precedence 19 
for @{ 'Or_intro_r_ok_2 $a $ab }.
interpretation "Or_intro_r_ok_2" 'Or_intro_r_ok_2 a ab = 
  (cast ? ? (show ab (Or_intro_r ? ? a))).

notation > "∨#'i_r' term 90 a" with precedence 19
for @{ 'Or_intro_r (show $a ?) }.
interpretation "Or_intro_r KO" 'Or_intro_r a = (cast ? (Or unit ?) (Or_intro_r ? ? a)).
interpretation "Or_intro_r OK" 'Or_intro_r a = (Or_intro_r ? ? a). 

(* ∨ elimination *)
notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp ac \emsp\emsp\emsp bc \emsp) c (mstyle color #ff0000 (∨\sub\e \emsp) ident Ha \emsp ident Hb)" with precedence 19
for @{ 'Or_elim_ko_1 $ab $c (λ${ident Ha}:$ta.$ac) (λ${ident Hb}:$tb.$bc) }.
interpretation "Or_elim_ko_1" 'Or_elim_ko_1 ab c \eta.ac \eta.bc = 
  (show c (cast ? ? (Or_elim ? ? ? (cast ? ? ab) (cast ? ? ac) (cast ? ? bc)))).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp ac \emsp\emsp\emsp bc \emsp) mstyle color #ff0000 (c) (mstyle color #ff0000 (∨\sub\e) \emsp ident Ha \emsp ident Hb)" with precedence 19
for @{ 'Or_elim_ko_2 $ab (λ${ident Ha}:$ta.$ac) (λ${ident Hb}:$tb.$bc) $c }.
interpretation "Or_elim_ko_2" 'Or_elim_ko_2 ab \eta.ac \eta.bc c = 
  (cast ? ? (show c (cast ? ? (Or_elim ? ? ? (cast ? ? ab) (cast ? ? ac) (cast ? ? bc))))).

notation < "maction (\infrule hbox(\emsp ab \emsp\emsp\emsp ac \emsp\emsp\emsp bc \emsp) c (∨\sub\e \emsp ident Ha \emsp ident Hb)) (\vdots)" with precedence 19
for @{ 'Or_elim_ok_1 $ab (λ${ident Ha}:$ta.$ac) (λ${ident Hb}:$tb.$bc) $c }.
interpretation "Or_elim_ok_1" 'Or_elim_ok_1 ab \eta.ac \eta.bc c = 
  (show c (Or_elim ? ? ? ab ac bc)).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp ac \emsp\emsp\emsp bc \emsp) mstyle color #ff0000 (c) (∨\sub\e \emsp ident Ha \emsp ident Hb)" with precedence 19
for @{ 'Or_elim_ok_2 $ab (λ${ident Ha}:$ta.$ac) (λ${ident Hb}:$tb.$bc) $c }.
interpretation "Or_elim_ok_2" 'Or_elim_ok_2 ab \eta.ac \eta.bc c = 
  (cast ? ? (show c (Or_elim ? ? ? ab ac bc))).

definition unit_to ≝ λx:CProp.unit → x.

notation > "∨#'e' term 90 ab [ident Ha] term 90 cl [ident Hb] term 90 cr" with precedence 19
for @{ 'Or_elim (show $ab ?) (λ${ident Ha}.show $cl ?) (λ${ident Hb}.show $cr ?) }.
interpretation "Or_elim KO" 'Or_elim ab ac bc = 
  (cast ? ? (Or_elim ? ? ? 
    (cast (Or unit unit) ? ab) 
    (cast (unit_to unit) (unit_to ?) ac) 
    (cast (unit_to unit) (unit_to ?) bc))).
interpretation "Or_elim OK" 'Or_elim ab ac bc = (Or_elim ? ? ? ab ac bc).

(* ⊤ introduction *)
notation < "\infrule \nbsp ⊤ mstyle color #ff0000 (⊤\sub\i)" with precedence 19 
for @{'Top_intro_ko_1}.
interpretation "Top_intro_ko_1" 'Top_intro_ko_1 = 
  (show ? (cast ? ? Top_intro)).

notation < "\infrule \nbsp mstyle color #ff0000 (⊤) mstyle color #ff0000 (⊤\sub\i)" with precedence 19 
for @{'Top_intro_ko_2}.
interpretation "Top_intro_ko_2" 'Top_intro_ko_2 = 
  (cast ? ? (show ? (cast ? ? Top_intro))).

notation < "maction (\infrule \nbsp ⊤ (⊤\sub\i)) (\vdots)" with precedence 19 
for @{'Top_intro_ok_1}.
interpretation "Top_intro_ok_1" 'Top_intro_ok_1 = (show ? Top_intro).

notation < "maction (\infrule \nbsp ⊤ (⊤\sub\i)) (\vdots)" with precedence 19 
for @{'Top_intro_ok_2 }.
interpretation "Top_intro_ok_2" 'Top_intro_ok_2 = (cast ? ? (show ? Top_intro)).

notation > "⊤#'i'" with precedence 19 for @{ 'Top_intro }.
interpretation "Top_intro KO" 'Top_intro = (cast ? ? Top_intro).
interpretation "Top_intro OK" 'Top_intro = Top_intro.

(* ⊥ introduction *)
notation < "\infrule b a mstyle color #ff0000 (⊥\sub\e)" with precedence 19 
for @{'Bot_elim_ko_1 $a $b}.
interpretation "Bot_elim_ko_1" 'Bot_elim_ko_1 a b = 
  (show a (Bot_elim ? (cast ? ? b))).

notation < "\infrule b mstyle color #ff0000 (a) mstyle color #ff0000 (⊥\sub\e)" with precedence 19 
for @{'Bot_elim_ko_2 $a $b}.
interpretation "Bot_elim_ko_2" 'Bot_elim_ko_2 a b = 
  (cast ? ? (show a (Bot_elim ? (cast ? ? b)))).

notation < "maction (\infrule b a (⊥\sub\e)) (\vdots)" with precedence 19 
for @{'Bot_elim_ok_1 $a $b}.
interpretation "Bot_elim_ok_1" 'Bot_elim_ok_1 a b = 
  (show a (Bot_elim ? b)).

notation < "\infrule b mstyle color #ff0000 (a) (⊥\sub\e)" with precedence 19 
for @{'Bot_elim_ok_2 $a $b}.
interpretation "Bot_elim_ok_2" 'Bot_elim_ok_2 a b = 
  (cast ? ? (show a (Bot_elim ? b))).

notation > "⊥#'e' term 90 b" with precedence 19 
for @{ 'Bot_elim (show $b ?) }.
interpretation "Bot_elim KO" 'Bot_elim a = (Bot_elim ? (cast ? ? a)).  
interpretation "Bot_elim OK" 'Bot_elim a = (Bot_elim ? a).

(* ¬ introduction *)
notation < "\infrule hbox(\emsp b \emsp) ab (mstyle color #ff0000 (\lnot\sub(\emsp\i)) \emsp ident H)" with precedence 19
for @{ 'Not_intro_ko_1 $ab (λ${ident H}:$p.$b) }.
interpretation "Not_intro_ko_1" 'Not_intro_ko_1 ab \eta.b = 
  (show ab (cast ? ? (Not_intro ? (cast ? ? b)))).

notation < "\infrule hbox(\emsp b \emsp) mstyle color #ff0000 (ab) (mstyle color #ff0000 (\lnot\sub(\emsp\i)) \emsp ident H)" with precedence 19
for @{ 'Not_intro_ko_2 $ab (λ${ident H}:$p.$b) }.
interpretation "Not_intro_ko_2" 'Not_intro_ko_2 ab \eta.b = 
  (cast ? ? (show ab (cast ? ? (Not_intro ? (cast ? ? b))))).

notation < "maction (\infrule hbox(\emsp b \emsp) ab (\lnot\sub(\emsp\i) \emsp ident H) ) (\vdots)" with precedence 19
for @{ 'Not_intro_ok_1 $ab (λ${ident H}:$p.$b) }.
interpretation "Not_intro_ok_1" 'Not_intro_ok_1 ab \eta.b = 
  (show ab (Not_intro ? b)).

notation < "\infrule hbox(\emsp b \emsp) mstyle color #ff0000 (ab) (\lnot\sub(\emsp\i) \emsp ident H) " with precedence 19
for @{ 'Not_intro_ok_2 $ab (λ${ident H}:$p.$b) }.
interpretation "Not_intro_ok_2" 'Not_intro_ok_2 ab \eta.b = 
  (cast ? ? (show ab (Not_intro ? b))).

notation > "¬#'i' [ident H] term 90 b" with precedence 19
for @{ 'Not_intro (λ${ident H}.show $b ?) }.
interpretation "Not_intro KO" 'Not_intro a = (cast ? ? (Not_intro ? (cast ? ? a))).
interpretation "Not_intro OK" 'Not_intro a = (Not_intro ? a).

(* ¬ elimination *)
notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) b mstyle color #ff0000 (\lnot\sub(\emsp\e)) " with precedence 19 
for @{ 'Not_elim_ko_1 $ab $a $b }.
interpretation "Not_elim_ko_1" 'Not_elim_ko_1 ab a b = 
  (show b (cast ? ? (Not_elim ? (cast ? ? ab) (cast ? ? a)))).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) mstyle color #ff0000 (b) mstyle color #ff0000 (\lnot\sub(\emsp\e)) " with precedence 19 
for @{ 'Not_elim_ko_2 $ab $a $b }.
interpretation "Not_elim_ko_2" 'Not_elim_ko_2 ab a b = 
  (cast ? ? (show b (cast ? ? (Not_elim ? (cast ? ? ab) (cast ? ? a))))).

notation < "maction (\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) b (\lnot\sub(\emsp\e)) ) (\vdots)" with precedence 19 
for @{ 'Not_elim_ok_1 $ab $a $b }.
interpretation "Not_elim_ok_1" 'Not_elim_ok_1 ab a b = 
  (show b (Not_elim ? ab a)).

notation < "\infrule hbox(\emsp ab \emsp\emsp\emsp a\emsp) mstyle color #ff0000 (b) (\lnot\sub(\emsp\e)) " with precedence 19 
for @{ 'Not_elim_ok_2 $ab $a $b }.
interpretation "Not_elim_ok_2" 'Not_elim_ok_2 ab a b = 
  (cast ? ? (show b (Not_elim ? ab a))).

notation > "¬#'e' term 90 ab term 90 a" with precedence 19
for @{ 'Not_elim (show $ab ?) (show $a ?) }.
interpretation "Not_elim KO" 'Not_elim ab a = 
  (cast ? ? (Not_elim unit (cast ? ? ab) (cast ? ? a))).
interpretation "Not_elim OK" 'Not_elim ab a = 
  (Not_elim ? ab a).

(* RAA *)
notation < "\infrule hbox(\emsp Px \emsp) Pn (mstyle color #ff0000 (\RAA) \emsp ident x)" with precedence 19
for @{ 'RAA_ko_1 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "RAA_ko_1" 'RAA_ko_1 Px Pn = 
  (show Pn (cast ? ? (Raa ? (cast ? ? Px)))).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000 (Pn) (mstyle color #ff0000 (\RAA) \emsp ident x)" with precedence 19
for @{ 'RAA_ko_2 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "RAA_ko_2" 'RAA_ko_2 Px Pn = 
  (cast ? ? (show Pn (cast ? ? (Raa ? (cast ? ? Px))))).

notation < "maction (\infrule hbox(\emsp Px \emsp) Pn (\RAA \emsp ident x)) (\vdots)" with precedence 19
for @{ 'RAA_ok_1 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "RAA_ok_1" 'RAA_ok_1 Px Pn = 
  (show Pn (Raa ? Px)).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000 (Pn) (\RAA \emsp ident x)" with precedence 19
for @{ 'RAA_ok_2 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "RAA_ok_2" 'RAA_ok_2 Px Pn = 
  (cast ? ? (show Pn (Raa ? Px))).

notation > "'RAA' [ident H] term 90 b" with precedence 19 
for @{ 'Raa (λ${ident H}.show $b ?) }. 
interpretation "RAA KO" 'Raa p = (cast ? unit (Raa ? (cast ? (unit_to ?) p))).
interpretation "RAA OK" 'Raa p = (Raa ? p).

(* ∃ introduction *)
notation < "\infrule hbox(\emsp Pn \emsp) Px mstyle color #ff0000 (∃\sub\i)" with precedence 19
for @{ 'Exists_intro_ko_1 $Pn $Px }.
interpretation "Exists_intro_ko_1" 'Exists_intro_ko_1 Pn Px = 
  (show Px (cast ? ? (Exists_intro ? ? ? (cast ? ? Pn)))).

notation < "\infrule hbox(\emsp Pn \emsp) mstyle color #ff0000 (Px) mstyle color #ff0000 (∃\sub\i)" with precedence 19
for @{ 'Exists_intro_ko_2 $Pn $Px }.
interpretation "Exists_intro_ko_2" 'Exists_intro_ko_2 Pn Px = 
  (cast ? ? (show Px (cast ? ? (Exists_intro ? ? ? (cast ? ? Pn))))).

notation < "maction (\infrule hbox(\emsp Pn \emsp) Px (∃\sub\i)) (\vdots)" with precedence 19
for @{ 'Exists_intro_ok_1 $Pn $Px }.
interpretation "Exists_intro_ok_1" 'Exists_intro_ok_1 Pn Px = 
  (show Px (Exists_intro ? ? ? Pn)).

notation < "\infrule hbox(\emsp Pn \emsp) mstyle color #ff0000 (Px) (∃\sub\i)" with precedence 19
for @{ 'Exists_intro_ok_2 $Pn $Px }.
interpretation "Exists_intro_ok_2" 'Exists_intro_ok_2 Pn Px = 
  (cast ? ? (show Px (Exists_intro ? ? ? Pn))).

notation >"∃#'i' {term 90 t} term 90 Pt" non associative with precedence 19
for @{'Exists_intro $t (λw.? w) (show $Pt ?)}. 
interpretation "Exists_intro KO" 'Exists_intro t P Pt =
 (cast ? ? (Exists_intro sort P t (cast ? ? Pt))).
interpretation "Exists_intro OK" 'Exists_intro t P Pt =
 (Exists_intro sort P t Pt).
 
(* ∃ elimination *)
notation < "\infrule hbox(\emsp ExPx \emsp\emsp\emsp Pc \emsp) c (mstyle color #ff0000 (∃\sub\e) \emsp ident n \emsp ident HPn)" with precedence 19
for @{ 'Exists_elim_ko_1 $ExPx (λ${ident n}:$tn.λ${ident HPn}:$Pn.$Pc) $c }.
interpretation "Exists_elim_ko_1" 'Exists_elim_ko_1 ExPx Pc c =
    (show c (cast ? ? (Exists_elim ? ? ? (cast ? ? ExPx) (cast ? ? Pc)))).

notation < "\infrule hbox(\emsp ExPx \emsp\emsp\emsp Pc \emsp) mstyle color #ff0000 (c) (mstyle color #ff0000 (∃\sub\e) \emsp ident n \emsp ident HPn)" with precedence 19
for @{ 'Exists_elim_ko_2 $ExPx (λ${ident n}:$tn.λ${ident HPn}:$Pn.$Pc) $c }.
interpretation "Exists_elim_ko_2" 'Exists_elim_ko_2 ExPx Pc c =
    (cast ? ? (show c (cast ? ? (Exists_elim ? ? ? (cast ? ? ExPx) (cast ? ? Pc))))).

notation < "maction (\infrule hbox(\emsp ExPx \emsp\emsp\emsp Pc \emsp) c (∃\sub\e \emsp ident n \emsp ident HPn)) (\vdots)" with precedence 19
for @{ 'Exists_elim_ok_1 $ExPx (λ${ident n}:$tn.λ${ident HPn}:$Pn.$Pc) $c }.
interpretation "Exists_elim_ok_1" 'Exists_elim_ok_1 ExPx Pc c =
    (show c (Exists_elim ? ? ? ExPx Pc)).

notation < "\infrule hbox(\emsp ExPx \emsp\emsp\emsp Pc \emsp) mstyle color #ff0000 (c) (∃\sub\e \emsp ident n \emsp ident HPn)" with precedence 19
for @{ 'Exists_elim_ok_2 $ExPx (λ${ident n}:$tn.λ${ident HPn}:$Pn.$Pc) $c }.
interpretation "Exists_elim_ok_2" 'Exists_elim_ok_2 ExPx Pc c =
    (cast ? ? (show c (Exists_elim ? ? ? ExPx Pc))).

definition ex_concl := λx:sort → CProp.∀y:sort.unit → x y.
definition ex_concl_dummy := ∀y:sort.unit → unit.
definition fake_pred := λx:sort.unit.

notation >"∃#'e' term 90 ExPt {ident t} [ident H] term 90 c" non associative with precedence 19
for @{'Exists_elim (λx.? x) (show $ExPt ?) (λ${ident t}:sort.λ${ident H}.show $c ?)}. 
interpretation "Exists_elim KO" 'Exists_elim P ExPt c =
 (cast ? ? (Exists_elim sort P ? 
   (cast (Exists ? P)  ? ExPt) 
   (cast ex_concl_dummy (ex_concl ?) c))).
interpretation "Exists_elim OK" 'Exists_elim P ExPt c =
 (Exists_elim sort P ? ExPt c).

(* ∀ introduction *)

notation < "\infrule hbox(\emsp Px \emsp) Pn (mstyle color #ff0000 (∀\sub\i) \emsp ident x)" with precedence 19
for @{ 'Forall_intro_ko_1 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "Forall_intro_ko_1" 'Forall_intro_ko_1 Px Pn = 
  (show Pn (cast ? ? (Forall_intro ? ? (cast ? ? Px)))).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000(Pn) (mstyle color #ff0000 (∀\sub\i) \emsp ident x)" with precedence 19
for @{ 'Forall_intro_ko_2 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "Forall_intro_ko_2" 'Forall_intro_ko_2 Px Pn = 
  (cast ? ? (show Pn (cast ? ? (Forall_intro ? ? (cast ? ? Px))))).

notation < "maction (\infrule hbox(\emsp Px \emsp) Pn (∀\sub\i \emsp ident x)) (\vdots)" with precedence 19
for @{ 'Forall_intro_ok_1 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "Forall_intro_ok_1" 'Forall_intro_ok_1 Px Pn = 
  (show Pn (Forall_intro ? ? Px)).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000 (Pn) (∀\sub\i \emsp ident x)" with precedence 19
for @{ 'Forall_intro_ok_2 (λ${ident x}:$tx.$Px) $Pn }.
interpretation "Forall_intro_ok_2" 'Forall_intro_ok_2 Px Pn = 
  (cast ? ? (show Pn (Forall_intro ? ? Px))).

notation > "∀#'i' {ident y} term 90 Px" non associative with precedence 19
for @{ 'Forall_intro (λ_.?) (λ${ident y}.show $Px ?) }. 
interpretation "Forall_intro KO" 'Forall_intro P Px =
  (cast ? ? (Forall_intro sort P (cast ? ? Px))). 
interpretation "Forall_intro OK" 'Forall_intro P Px =
  (Forall_intro sort P Px). 

(* ∀ elimination *)
notation < "\infrule hbox(\emsp Px \emsp) Pn (mstyle color #ff0000 (∀\sub\e))" with precedence 19
for @{ 'Forall_elim_ko_1 $Px $Pn }.
interpretation "Forall_elim_ko_1" 'Forall_elim_ko_1 Px Pn = 
  (show Pn (cast ? ? (Forall_elim ? ? ? (cast ? ? Px)))).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000(Pn) (mstyle color #ff0000 (∀\sub\e))" with precedence 19
for @{ 'Forall_elim_ko_2 $Px $Pn }.
interpretation "Forall_elim_ko_2" 'Forall_elim_ko_2 Px Pn = 
  (cast ? ? (show Pn (cast ? ? (Forall_elim ? ? ? (cast ? ? Px))))).

notation < "maction (\infrule hbox(\emsp Px \emsp) Pn (∀\sub\e)) (\vdots)" with precedence 19
for @{ 'Forall_elim_ok_1 $Px $Pn }.
interpretation "Forall_elim_ok_1" 'Forall_elim_ok_1 Px Pn = 
  (show Pn (Forall_elim ? ? ? Px)).

notation < "\infrule hbox(\emsp Px \emsp) mstyle color #ff0000 (Pn) (∀\sub\e)" with precedence 19
for @{ 'Forall_elim_ok_2 $Px $Pn }.
interpretation "Forall_elim_ok_2" 'Forall_elim_ok_2 Px Pn = 
  (cast ? ? (show Pn (Forall_elim ? ? ? Px))).

notation > "∀#'e' {term 90 t} term 90 Pn" non associative with precedence 19
for @{ 'Forall_elim (λ_.?) $t (show $Pn ?) }. 
interpretation "Forall_elim KO" 'Forall_elim P t Px =
  (cast ? unit (Forall_elim sort P t (cast ? ? Px))). 
interpretation "Forall_elim OK" 'Forall_elim P t Px =
  (Forall_elim sort P t Px). 

(* already proved lemma *)
definition hide_args : ∀A:Type.A→A := λA:Type.λa:A.a.
notation < "t" non associative with precedence 90 for @{'hide_args $t}.
interpretation "hide 0 args"  'hide_args t = (hide_args ? t).
interpretation "hide 1 args"  'hide_args t = (hide_args ? t ?).
interpretation "hide 2 args"  'hide_args t = (hide_args ? t ? ?).
interpretation "hide 3 args"  'hide_args t = (hide_args ? t ? ? ?).
interpretation "hide 4 args"  'hide_args t = (hide_args ? t ? ? ? ?). 
interpretation "hide 5 args"  'hide_args t = (hide_args ? t ? ? ? ? ?).
interpretation "hide 6 args"  'hide_args t = (hide_args ? t ? ? ? ? ? ?).
interpretation "hide 7 args"  'hide_args t = (hide_args ? t ? ? ? ? ? ? ?).

(* more args crashes the pattern matcher *)

(* already proved lemma, 0 assumptions *)
definition Lemma : ΠA.A→A ≝ λA:CProp.λa:A.a.

notation < "\infrule 
         (\infrule 
             (\emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma_ko_1 $p ($H : $_) }.
interpretation "lemma_ko_1" 'lemma_ko_1 p H = 
  (show p (cast ? ? (Lemma ? (cast ? ? H)))). 

notation < "\infrule 
         (\infrule 
             (\emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma_ko_2 $p ($H : $_) }.
interpretation "lemma_ko_2" 'lemma_ko_2 p H = 
  (cast ? ? (show p (cast ? ? 
    (Lemma ? (cast ? ? H))))). 


notation < "\infrule 
         (\infrule 
             (\emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma_ok_1 $p ($H : $_) }.
interpretation "lemma_ok_1" 'lemma_ok_1 p H = 
  (show p (Lemma ? H)). 

notation < "\infrule 
         (\infrule 
             (\emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma_ok_2 $p ($H : $_) }.
interpretation "lemma_ok_2" 'lemma_ok_2 p H = 
  (cast ? ? (show p (Lemma ? H))). 

notation > "'lem' 0 term 90 l" non associative with precedence 19
for @{ 'Lemma (hide_args ? $l : ?) }.
interpretation "lemma KO" 'Lemma l = 
  (cast ? ? (Lemma unit (cast unit ? l))). 
interpretation "lemma OK" 'Lemma l = (Lemma ? l).


(* already proved lemma, 1 assumption *)
definition Lemma1 : ΠA,B. (A ⇒ B) → A → B ≝ 
 λA,B:CProp.λf:A⇒B.λa:A.
  Imply_elim A B f a.

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma1_ko_1 $a $p ($H : $_) }.
interpretation "lemma1_ko_1" 'lemma1_ko_1 a p H = 
  (show p (cast ? ? (Lemma1 ? ? (cast ? ? H) (cast ? ? a)))). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma1_ko_2 $a $p ($H : $_) }.
interpretation "lemma1_ko_2" 'lemma1_ko_2 a p H = 
  (cast ? ? (show p (cast ? ? 
    (Lemma1 ? ? (cast ? ? H) (cast ? ? a))))). 


notation < "\infrule 
         (\infrule 
             (\emsp a \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma1_ok_1 $a $p ($H : $_) }.
interpretation "lemma1_ok_1" 'lemma1_ok_1 a p H = 
  (show p (Lemma1 ? ? H a)). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma1_ok_2 $a $p ($H : $_) }.
interpretation "lemma1_ok_2" 'lemma1_ok_2 a p H = 
  (cast ? ? (show p (Lemma1 ? ? H a))). 


notation > "'lem' 1 term 90 l term 90 p" non associative with precedence 19
for @{ 'Lemma1 (hide_args ? $l : ?) (show $p ?) }.
interpretation "lemma 1 KO" 'Lemma1 l p = 
  (cast ? ? (Lemma1 unit unit (cast (Imply unit unit) ? l) (cast unit ? p))). 
interpretation "lemma 1 OK" 'Lemma1 l p = (Lemma1 ? ? l p).

(* already proved lemma, 2 assumptions *)
definition Lemma2 : ΠA,B,C. (A ⇒ B ⇒ C) → A → B → C ≝ 
 λA,B,C:CProp.λf:A⇒B⇒C.λa:A.λb:B.
  Imply_elim B C (Imply_elim A (B⇒C) f a) b.

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma2_ko_1 $a $b $p ($H : $_) }.
interpretation "lemma2_ko_1" 'lemma2_ko_1 a b p H = 
  (show p (cast ? ? (Lemma2 ? ? ? (cast ? ? H) (cast ? ? a) (cast ? ? b)))). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma2_ko_2 $a $b $p ($H : $_) }.
interpretation "lemma2_ko_2" 'lemma2_ko_2 a b p H = 
  (cast ? ? (show p (cast ? ? 
    (Lemma2 ? ? ? (cast ? ? H) (cast ? ? a) (cast ? ? b))))). 


notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma2_ok_1 $a $b $p ($H : $_) }.
interpretation "lemma2_ok_1" 'lemma2_ok_1 a b p H = 
  (show p (Lemma2 ? ? ? H a b)). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma2_ok_2 $a $b $p ($H : $_) }.
interpretation "lemma2_ok_2" 'lemma2_ok_2 a b p H = 
  (cast ? ? (show p (Lemma2 ? ? ? H a b))). 

notation > "'lem' 2 term 90 l term 90 p term 90 q" non associative with precedence 19
for @{ 'Lemma2 (hide_args ? $l : ?) (show $p ?) (show $q ?) }.
interpretation "lemma 2 KO" 'Lemma2 l p q = 
  (cast ? ? (Lemma2 unit unit unit (cast (Imply unit (Imply unit unit)) ? l) (cast unit ? p) (cast unit ? q))). 
interpretation "lemma 2 OK" 'Lemma2 l p q = (Lemma2 ? ? ? l p q).

(* already proved lemma, 3 assumptions *)
definition Lemma3 : ΠA,B,C,D. (A ⇒ B ⇒ C ⇒ D) → A → B → C → D ≝ 
 λA,B,C,D:CProp.λf:A⇒B⇒C⇒D.λa:A.λb:B.λc:C.
  Imply_elim C D (Imply_elim B (C⇒D) (Imply_elim A (B⇒C⇒D) f a) b) c.

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp\emsp\emsp c \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma3_ko_1 $a $b $c $p ($H : $_) }.
interpretation "lemma3_ko_1" 'lemma3_ko_1 a b c p H = 
  (show p (cast ? ? 
   (Lemma3 ? ? ? ? (cast ? ? H) (cast ? ? a) (cast ? ? b) (cast ? ? c)))). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp\emsp\emsp c \emsp) 
             (╲ mstyle mathsize normal (mstyle color #ff0000 (H)) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma3_ko_2 $a $b $c $p ($H : $_) }.
interpretation "lemma3_ko_2" 'lemma3_ko_2 a b c p H = 
  (cast ? ? (show p (cast ? ? 
    (Lemma3 ? ? ? ? (cast ? ? H) (cast ? ? a) (cast ? ? b) (cast ? ? c))))). 


notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp\emsp\emsp c \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         p \nbsp" 
non associative with precedence 19
for @{ 'lemma3_ok_1 $a $b $c $p ($H : $_) }.
interpretation "lemma3_ok_1" 'lemma3_ok_1 a b c p H = 
  (show p (Lemma3 ? ? ? ? H a b c)). 

notation < "\infrule 
         (\infrule 
             (\emsp a \emsp\emsp\emsp b \emsp\emsp\emsp c \emsp) 
             (╲ mstyle mathsize normal (H) ╱) \nbsp) 
         mstyle color #ff0000 (p) \nbsp" 
non associative with precedence 19
for @{ 'lemma3_ok_2 $a $b $c $p ($H : $_) }.
interpretation "lemma3_ok_2" 'lemma3_ok_2 a b c p H = 
  (cast ? ? (show p (Lemma3 ? ? ? ? H a b c))). 

notation > "'lem' 3 term 90 l term 90 p term 90 q term 90 r" non associative with precedence 19
for @{ 'Lemma3 (hide_args ? $l : ?) (show $p ?) (show $q ?) (show $r ?) }.
interpretation "lemma 3 KO" 'Lemma3 l p q r = 
  (cast ? ? (Lemma3 unit unit unit unit (cast (Imply unit (Imply unit (Imply unit unit))) ? l) (cast unit ? p) (cast unit ? q) (cast unit ? r))). 
interpretation "lemma 3 OK" 'Lemma3 l p q r = (Lemma3 ? ? ? ? l p q r).
