(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "turing/universal/alphabet.ma".
include "turing/mono.ma".

(************************* turning DeqMove into a DeqSet **********************)
definition move_eq ≝ λm1,m2:move.
  match m1 with
  [R ⇒ match m2 with [R ⇒ true | _ ⇒ false]
  |L ⇒ match m2 with [L ⇒ true | _ ⇒ false]
  |N ⇒ match m2 with [N ⇒ true | _ ⇒ false]].

lemma move_eq_true:∀m1,m2.
  move_eq m1 m2 = true ↔ m1 = m2.
*
  [* normalize [% #_ % |2,3: % #H destruct ]
  |* normalize [1,3: % #H destruct |% #_ % ]
  |* normalize [1,2: % #H destruct |% #_ % ]
qed.

definition DeqMove ≝ mk_DeqSet move move_eq move_eq_true.

unification hint 0 ≔ ;
    X ≟ DeqMove
(* ---------------------------------------- *) ⊢ 
    move ≡ carr X.

unification hint  0 ≔ m1,m2; 
    X ≟ DeqMove
(* ---------------------------------------- *) ⊢ 
    move_eq m1 m2 ≡ eqb X m1 m2.


(************************ turning DeqMove into a FinSet ***********************)
definition move_enum ≝ [L;R;N].

lemma move_enum_unique: uniqueb ? [L;R;N] = true.
// qed.

lemma move_enum_complete: ∀x:move. memb ? x [L;R;N] = true.
* // qed.

definition FinMove ≝ 
  mk_FinSet DeqMove [L;R;N] move_enum_unique move_enum_complete.

unification hint  0 ≔ ; 
    X ≟ FinMove
(* ---------------------------------------- *) ⊢ 
    move ≡ FinSetcarr X.

(*************************** normal Turing Machines ***************************)

(* A normal turing machine is just an ordinary machine where:
  1. the tape alphabet is bool
  2. the finite state are supposed to be an initial segment of the natural 
     numbers. 
  Formally, it is specified by a record with the number n of states, a proof
  that n is positive, the transition function and the halting function.
*)

definition trans_source ≝ λn.FinProd (initN n) (FinOption FinBool).
definition trans_target ≝ λn.FinProd (initN n) (FinOption (FinProd FinBool FinMove)).

record normalTM : Type[0] ≝ 
{ no_states : nat;
  pos_no_states : (0 < no_states); 
  ntrans : trans_source no_states → trans_target no_states;
  nhalt : initN no_states → bool
}.

(* A normal machine is just a special case of Turing Machine. *)

definition normalTM_to_TM ≝ λM:normalTM.
  mk_TM FinBool (initN (no_states M)) 
   (ntrans M) (mk_Sig ?? 0 (pos_no_states M)) (nhalt M).

coercion normalTM_to_TM.

definition nconfig ≝ λn. config FinBool (initN n).

(******************************** tuples **************************************)

(* By general results on FinSets we know that every function f between two 
finite sets A and B can be described by means of a finite graph of pairs
〈a,f a〉. Hence, the transition function of a normal turing machine can be
described by a finite set of tuples 〈i,c〉,〈j,action〉〉 of the following type:
  (Nat_to n × (option FinBool)) × (Nat_to n × (option (FinBool × move))).  
Unfortunately this description is not suitable for a Universal Machine, since
such a machine must work with a fixed alphabet, while the size on n is unknown.
Hence, we must pass from natural numbers to a representation for them on a 
finitary, e.g. binary, alphabet. In general, we shall associate
to a pair 〈〈i,c〉,〈j,action〉〉 a tuple with the following syntactical structure
           |w_ix,w_jy,z
where 
1. "|" and "," are special characters used as delimiters;
2. w_i and w_j are list of booleans representing the states $i$ and $j$; 
3. x is special symbol null if c=None and is a if c=Some a
4. y and z are both null if action = None, and are equal to b,m' if 
   action = Some b,m; 
5. finally, m' = 0 if m = L, m' = 1 if m=R and m' = null if m = N

As a minor, additional complication, we shall suppose that every characters is
decorated by an additonal bit, normally set to false, to be used as a marker.
*)

definition mk_tuple ≝ λqin,cin,qout,cout,mv.
  〈bar,false〉::qin@cin::〈comma,false〉::qout@cout::〈comma,false〉::[mv].

(* by definition, a tuple is not marked *)
definition tuple_TM : nat → list STape → Prop ≝ 
 λn,t.∃qin,cin,qout,cout,mv.
 no_marks qin ∧ no_marks qout ∧
 only_bits qin ∧ only_bits qout ∧ 
 bit_or_null cin = true ∧ bit_or_null cout = true ∧ bit_or_null mv = true ∧
 (cout = null → mv = null) ∧
 |qin| = n ∧ |qout| = n ∧
 t = mk_tuple qin 〈cin,false〉 qout 〈cout,false〉 〈mv,false〉.

(***************************** state encoding *********************************)
(* p < n is represented with a list of bits of lenght n with the p-th bit from 
left set to 1. An additional intial bit is set to 1 if the state is final and
to 0 otherwise. *)
 
let rec to_bitlist n p: list bool ≝
  match n with [ O ⇒ [ ] | S q ⇒ (eqb p q)::to_bitlist q p].
  
let rec from_bitlist l ≝
  match l with 
  [ nil ⇒ 0 (* assert false *)
  | cons b tl ⇒ if b then |tl| else from_bitlist tl].

lemma bitlist_length: ∀n,p.|to_bitlist n p| = n.
#n elim n normalize // 
qed.
  
lemma bitlist_inv1: ∀n,p.p<n → from_bitlist (to_bitlist n p) = p.
#n elim n normalize -n
  [#p #abs @False_ind /2/
  |#n #Hind #p #lepn 
   cases (le_to_or_lt_eq … (le_S_S_to_le … lepn))
    [#ltpn lapply (lt_to_not_eq … ltpn) #Hpn
     >(not_eq_to_eqb_false … Hpn) normalize @Hind @ltpn
    |#Heq >(eq_to_eqb_true … Heq) normalize <Heq //
    ]
  ]
qed.

lemma bitlist_lt: ∀l. 0 < |l| → from_bitlist l < |l|.
#l elim l normalize // #b #tl #Hind cases b normalize //
#Htl cases (le_to_or_lt_eq … (le_S_S_to_le … Htl)) -Htl #Htl
  [@le_S_S @lt_to_le @Hind //  
  |cut (tl=[ ]) [/2 by append_l2_injective/] #eqtl >eqtl @le_n
  ]
qed.

definition nat_of: ∀n. Nat_to n → nat.
#n normalize * #p #_ @p
qed. 

definition bits_of_state ≝ λn.λh:Nat_to n → bool.λs:Nat_to n.
  h s::(to_bitlist n (nat_of n s)).

definition m_bits_of_state ≝ λn.λh.λp.
  map ? (unialpha×bool) (λx.〈bit x,false〉) (bits_of_state n h p).
  
lemma no_marks_bits_of_state : ∀n,h,p. no_marks (m_bits_of_state n h p).
#n #h #p #x whd in match (m_bits_of_state n h p);
#H cases (orb_true_l … H) -H 
  [#H >(\P H) %
  |elim (to_bitlist n (nat_of n p))
    [whd in ⊢ ((??%?)→?); #H destruct 
    |#b #l #Hind #H cases (orb_true_l … H) -H #H
      [>(\P H) % |@Hind @H]
    ]
  ]
qed.

lemma only_bits_bits_of_state : ∀n,h,p. only_bits (m_bits_of_state n h p).
#n #h #p #x whd in match (m_bits_of_state n h p);
#H cases (orb_true_l … H) -H 
  [#H >(\P H) %
  |elim (to_bitlist n (nat_of n p))
    [whd in ⊢ ((??%?)→?); #H destruct 
    |#b #l #Hind #H cases (orb_true_l … H) -H #H
      [>(\P H) % |@Hind @H ]
    ]
  ]
qed.

(******************************** action encoding *****************************)
definition low_action ≝ λaction. 
  match action with 
    [ None ⇒ 〈null,null〉
    | Some act ⇒ let 〈na,m〉 ≝ act in 
      match m with 
      [ R ⇒ 〈bit na,bit true〉
      | L ⇒ 〈bit na,bit false〉
      | N ⇒ 〈bit na,null〉]
    ].

(******************************** tuple encoding ******************************)
definition tuple_type ≝ λn.
 (Nat_to n × (option FinBool)) × (Nat_to n × (option (FinBool × move))).  

definition tuple_encoding ≝ λn.λh:Nat_to n→bool. 
  λp:tuple_type n.
  let 〈inp,outp〉 ≝ p in
  let 〈q,a〉 ≝ inp in
  let cin ≝ match a with [ None ⇒ null | Some b ⇒ bit b ] in
  let 〈qn,action〉 ≝ outp in
  let 〈cout,mv〉 ≝ low_action action in
  let qin ≝ m_bits_of_state n h q in
  let qout ≝ m_bits_of_state n h qn in
  mk_tuple qin 〈cin,false〉 qout 〈cout,false〉 〈mv,false〉.

(*
definition WFTuple_conditions ≝ 
 λn,qin,cin,qout,cout,mv.
 no_marks qin ∧ no_marks qout ∧ (* queste fuori ? *)
 only_bits qin ∧ only_bits qout ∧ 
 bit_or_null cin = true ∧ bit_or_null cout = true ∧ bit_or_null mv = true ∧
 (cout = null → mv = null) ∧
 |qin| = n ∧ |qout| = n. *)

lemma is_tuple: ∀n,h,p. tuple_TM (S n) (tuple_encoding n h p).
#n #h * * #q #a * #qn #action
@(ex_intro … (m_bits_of_state n h q))
letin cin ≝ match a with [ None ⇒ null | Some b ⇒ bit b ]
@(ex_intro … cin)
@(ex_intro … (m_bits_of_state n h qn))
letin cout ≝ 
  match action with 
  [ None ⇒ null | Some act ⇒ bit (\fst act)]
@(ex_intro … cout)
letin mv ≝ match action with 
  [ None ⇒ null
  | Some act ⇒ 
      match \snd act with 
      [ R ⇒ bit true | L ⇒ bit false | N ⇒ null]
  ]
@(ex_intro … mv)
%[%[%[%[%[%[%[% /3/ 
             |whd in match cin ; cases a //]
           |whd in match cout; cases action //]
         |whd in match mv; cases action // * #b #m cases m //]
       |whd in match cout; whd in match mv; cases action
         [// | #act whd in ⊢ ((??%?)→?); #Hfalse destruct ]]
     |>length_map normalize @eq_f //]
   |>length_map normalize @eq_f //]
 |normalize cases a cases action normalize //
   [* #c #m cases m % |* #c #m #c1 cases m %]
 ]
qed. 

definition tuple_length ≝ λn.2*n+6.

lemma length_of_tuple: ∀n,t. tuple_TM n t → 
  |t| = tuple_length n.
#n #t * #qin * #cin * #qout * #cout * #mv *** #_ #Hqin #Hqout #eqt >eqt 
whd in match (mk_tuple ?????); normalize >length_append >Hqin -Hqin normalize 
>length_append normalize >Hqout -Hqout //
qed.

definition tuples_list ≝ λn.λh.map … (λp.tuple_encoding n h p).

(******************* general properties of encoding of tuples *****************)

lemma no_grids_in_tuple : ∀n,l.tuple_TM n l → no_grids l.
#n #l * #qin * #cin * #qout * #cout * #mv * * * * * * * * * *
#_ #_ #Hqin #Hqout #Hcin #Hcout #Hmv #_ #_ #_ #Hl >Hl
#c #Hc cases (orb_true_l … Hc) -Hc #Hc
[ >(\P Hc) %
| cases (memb_append … Hc) -Hc #Hc
[ @bit_not_grid @(Hqin … Hc)
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈cin,false〉 = true) in Hc; >(\P Hc) @bit_or_null_not_grid //
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈comma,false〉 = true) in Hc; >(\P Hc) %
| cases (memb_append …Hc) -Hc #Hc
[ @bit_not_grid @(Hqout … Hc)
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈cout,false〉 = true) in Hc; >(\P Hc) @bit_or_null_not_grid //
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈comma,false〉 = true) in Hc; >(\P Hc) %
| >(memb_single … Hc) @bit_or_null_not_grid @Hmv
]]]]]]
qed.

lemma no_marks_in_tuple : ∀n,l.tuple_TM n l → no_marks l.
#n #l * #qin * #cin * #qout * #cout * #mv * * * * * * * * * *
#Hqin #Hqout #_ #_ #_ #_ #_ #_ #_ #_ #Hl >Hl
#c #Hc cases (orb_true_l … Hc) -Hc #Hc
[ >(\P Hc) %
| cases (memb_append … Hc) -Hc #Hc
[ @(Hqin … Hc)
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈cin,false〉 = true) in Hc; >(\P Hc) %
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈comma,false〉 = true) in Hc; >(\P Hc) %
| cases (memb_append … Hc) -Hc #Hc
[ @(Hqout … Hc)
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈cout,false〉 = true) in Hc; >(\P Hc) %
| cases (orb_true_l … Hc) -Hc #Hc 
[ change with (c == 〈comma,false〉 = true) in Hc; >(\P Hc) %
| >(memb_single … Hc) %
]]]]]]
qed.


