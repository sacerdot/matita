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



include "turing/universal/tuples.ma".
include "basics/fun_graph.ma".

(* p < n is represented with a list of bits of lenght n with the
 p-th bit from left set to 1 *)
 
let rec to_bitlist n p: list bool ≝
  match n with
  [ O ⇒ [ ]
  | S q ⇒ (eqb p q)::to_bitlist q p].
  
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
      [>(\P H) %
      |@Hind @H
      ]
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
      [>(\P H) %
      |@Hind @H
      ]
    ]
  ]
qed.

definition tuple_type ≝ λn.
 (Nat_to n × (option FinBool)) × (Nat_to n × (option (FinBool × move))).  

definition tuple_of_pair ≝ λn.λh:Nat_to n→bool. 
  λp:tuple_type n.
  let 〈inp,outp〉 ≝ p in
  let 〈q,a〉 ≝ inp in
  let cin ≝ match a with [ None ⇒ null | Some b ⇒ bit b ] in
  let 〈qn,action〉 ≝ outp in
  let 〈cout,mv〉 ≝ 
    match action with 
    [ None ⇒ 〈null,null〉
    | Some act ⇒ let 〈na,m〉 ≝ act in 
      match m with 
      [ R ⇒ 〈bit na,bit true〉
      | L ⇒ 〈bit na,bit false〉
      | N ⇒ 〈bit na,null〉]
    ] in
  let qin ≝ m_bits_of_state n h q in
  let qout ≝ m_bits_of_state n h qn in
  mk_tuple qin 〈cin,false〉 qout 〈cout,false〉 〈mv,false〉.

definition WFTuple_conditions ≝ 
 λn,qin,cin,qout,cout,mv.
 no_marks qin ∧ no_marks qout ∧ (* queste fuori ? *)
 only_bits qin ∧ only_bits qout ∧ 
 bit_or_null cin = true ∧ bit_or_null cout = true ∧ bit_or_null mv = true ∧
 (cout = null → mv = null) ∧
 |qin| = n ∧ |qout| = n.

lemma is_tuple: ∀n,h,p. tuple_TM (S n) (tuple_of_pair n h p).
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
             |whd in match cin ; cases a //
             ]
           |whd in match cout; cases action //
           ]
         |whd in match mv; cases action //
          * #b #m cases m //
         ]
       |whd in match cout; whd in match mv; cases action
         [// | #act whd in ⊢ ((??%?)→?); #Hfalse destruct ]
       ]
     |>length_map normalize @eq_f //
     ]
   |>length_map normalize @eq_f //
   ]
 |normalize cases a cases action normalize //
   [* #c #m cases m %
   |* #c #m #c1 cases m %
   ]
 ]
qed. 

definition tuple_length ≝ λn.2*n+3.

axiom length_of_tuple: ∀n,t. tuple_TM n t → 
  |t| = tuple_length n.

definition move_eq ≝ λm1,m2:move.
  match m1 with
  [R ⇒ match m2 with [R ⇒ true | _ ⇒ false]
  |L ⇒ match m2 with [L ⇒ true | _ ⇒ false]
  |N ⇒ match m2 with [N ⇒ true | _ ⇒ false]].
  
definition tuples_of_pairs ≝ λn.λh.map … (λp.(tuple_of_pair n h p)@[〈bar,false〉]).

definition flatten ≝ λA.foldr (list A) (list A) (append A) [].

lemma wftable: ∀n,h,l.table_TM (S n) (flatten ? (tuples_of_pairs n h l)).
#n #h #l elim l // -l #a #tl #Hind 
whd in match (flatten … (tuples_of_pairs …));
>associative_append @ttm_cons //
qed.

lemma flatten_to_mem: ∀A,n,l,l1,l2.∀a:list A. 0 < n →
  (∀x. mem ? x l → |x| = n) → |a| = n → flatten ? l = l1@a@l2  →
    (∃q.|l1| = n*q)  → mem ? a l.
#A #n #l elim l
  [normalize #l1 #l2 #a #posn #Hlen #Ha #Hnil @False_ind
   cut (|a|=0) [@daemon] /2/
  |#hd #tl #Hind #l1 #l2 #a #posn #Hlen #Ha 
   whd in match (flatten ??); #Hflat * #q cases q
    [<times_n_O #Hl1 
     cut (a = hd) [@daemon] /2/
    |#q1 #Hl1 lapply (split_exists … n l1 ?) //
     * #l11 * #l12 * #Heql1 #Hlenl11 %2
     @(Hind l12 l2 … posn ? Ha) 
      [#x #memx @Hlen %2 //
      |@(append_l2_injective ? hd l11) 
        [>Hlenl11 @Hlen %1 %
        |>Hflat >Heql1 >associative_append %
        ]
      |@(ex_intro …q1) @(injective_plus_r n) 
       <Hlenl11 in ⊢ (??%?); <length_append <Heql1 >Hl1 //
      ]
    ]
  ]
qed.

axiom match_decomp: ∀n,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv l →
  ∃l1,l2. l = l1@((mk_tuple qin cin qout cout mv)@[〈bar,false〉])@l2 ∧
    (∃q.|l1| = (S (tuple_length (S n)))*q) ∧ tuple_TM (S n) (mk_tuple qin cin qout cout mv).
(*
lemma match_tech: ∀n,l,qin,cin,qout,cout,mv.
  (∀t. mem ? t l → |t| = |mk_tuple qin cin qout cout mv|) →
  match_in_table (S n) qin cin qout cout mv (flatten ? l) → 
    ∃p. p = mk_tuple qin cin qout cout mv ∧ mem ? p l.
#n #l #qin #cin #qout #cout #mv #Hlen #Hmatch 
@(ex_intro … (mk_tuple qin cin qout cout mv)) % //
@flatten_to_mem *)

lemma match_to_tuple: ∀n,h,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_of_pairs n h l)) → 
    ∃p. p = mk_tuple qin cin qout cout mv ∧ mem ? (p@[〈bar,false〉]) (tuples_of_pairs n h l).
#n #h #l #qin #cin #qout #cout #mv #Hmatch 
@(ex_intro … (mk_tuple qin cin qout cout mv)) % //
cases (match_decomp … Hmatch) #l1 * #l2 * * #Hflat #Hlen #Htuple
@(flatten_to_mem … Hflat … Hlen)  
  [// 
  |@daemon
  |>length_append >(length_of_tuple … Htuple) normalize //
  ]
qed.

lemma mem_map: ∀A,B.∀f:A→B.∀l,b. 
  mem ? b (map … f l) → ∃a. mem ? a l ∧ f a = b.
#A #B #f #l elim l 
  [#b normalize @False_ind
  |#a #tl #Hind #b normalize *
    [#eqb @(ex_intro … a) /3/
    |#memb cases (Hind … memb) #a * #mema #eqb
     @(ex_intro … a) /3/
    ]
  ]
qed.

lemma match_to_pair: ∀n,h,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_of_pairs n h l)) → 
    ∃p. tuple_of_pair n h p = mk_tuple qin cin qout cout mv ∧ mem ? p l.
#n #h #l #qin #cin #qout #cout #mv #Hmatch 
cases (match_to_tuple … Hmatch)
#p * #eqp #memb 
cases(mem_map … (λp.(tuple_of_pair n h p)@[〈bar,false〉]) … memb)
#p1 * #Hmem #H @(ex_intro … p1) % /2/
qed.

(* turning DeqMove into a DeqSet *)
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

(* turning DeqMove into a FinSet *)
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

definition trans_source ≝ λn.FinProd (initN n) (FinOption FinBool).
definition trans_target ≝ λn.FinProd (initN n) (FinOption (FinProd FinBool FinMove)).

lemma match_to_trans: 
  ∀n.∀trans: trans_source n → trans_target n.
  ∀h,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_of_pairs n h (graph_enum ?? trans))) → 
  ∃s,t. tuple_of_pair n h 〈s,t〉 = mk_tuple qin cin qout cout mv 
    ∧ trans s = t.
#n #trans #h #qin #cin #qout #cout #mv #Hmatch
cases (match_to_pair … Hmatch) -Hmatch * #s #t * #Heq #Hmem
@(ex_intro … s) @(ex_intro … t) % // @graph_enum_correct 
@mem_to_memb @Hmem 
qed.

