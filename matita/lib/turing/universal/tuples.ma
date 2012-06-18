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


(****************************** table of tuples *******************************)
include "turing/universal/normalTM.ma".

(* a well formed table is a list of tuples *) 
 
inductive table_TM (n:nat) : list STape → Prop ≝ 
| ttm_nil  : table_TM n [] 
| ttm_cons : ∀t1,T.tuple_TM n t1 → table_TM n T → table_TM n (t1@T).

lemma wftable: ∀n,h,l.table_TM (S n) (flatten ? (tuples_list n h l)).
#n #h #l elim l // -l #a #tl #Hind 
whd in match (flatten … (tuples_list …));
@ttm_cons //
qed.

(*********************** general properties of tables *************************)
lemma no_grids_in_table: ∀n.∀l.table_TM n l → no_grids l.
#n #l #t elim t   
  [normalize #c #H destruct
  |#t1 #t2 #Ht1 #Ht2 #IH lapply (no_grids_in_tuple … Ht1) -Ht1 #Ht1 #x #Hx
   cases (memb_append … Hx) -Hx #Hx
   [ @(Ht1 … Hx)
   | @(IH … Hx) ] ]
qed.

lemma no_marks_in_table: ∀n.∀l.table_TM n l → no_marks l.
#n #l #t elim t   
  [normalize #c #H destruct
  |#t1 #t2 #Ht1 #Ht2 #IH lapply (no_marks_in_tuple … Ht1) -Ht1 #Ht1 #x #Hx
   cases (memb_append … Hx) -Hx #Hx
   [ @(Ht1 … Hx)
   | @(IH … Hx) ] ] 
qed.      

axiom last_of_table: ∀n,l,b.¬ table_TM n (l@[〈bar,b〉]).

(************************** matching in a table *******************************)
inductive match_in_table (n:nat) (qin:list STape) (cin: STape) 
                         (qout:list STape) (cout:STape) (mv:STape) 
: list STape → Prop ≝ 
| mit_hd : 
   ∀tb.
   tuple_TM n (mk_tuple qin cin qout cout mv) → 
   match_in_table n qin cin qout cout mv 
     (mk_tuple qin cin qout cout mv @tb)
| mit_tl :
   ∀qin0,cin0,qout0,cout0,mv0,tb.
   tuple_TM n (mk_tuple qin0 cin0 qout0 cout0 mv0) → 
   match_in_table n qin cin qout cout mv tb → 
   match_in_table n qin cin qout cout mv  
     (mk_tuple qin0 cin0 qout0 cout0 mv0@tb).

lemma tuple_to_match:  ∀n,h,l,qin,cin,qout,cout,mv,p.
  p = mk_tuple qin cin qout cout mv 
  → mem ? p (tuples_list n h l) →
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_list n h l)).
#n #h #l #qin #cin #qout #cout #mv #p
#Hp elim l 
  [whd in ⊢ (%→?); @False_ind
  |#p1 #tl #Hind *
    [#H whd in match (tuples_list ???);
     <H >Hp @mit_hd //
    |#H whd in match (tuples_list ???); 
     cases (is_tuple n h p1) #qin1 * #cin1 * #qout1 * #cout1 * #mv1
     * #_ #Htuplep1 >Htuplep1 @mit_tl // @Hind //
    ]
  ]
qed.

axiom match_decomp: ∀n,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv l →
  ∃l1,l2. l = l1@(mk_tuple qin cin qout cout mv)@l2 ∧
    (∃q.|l1| = (tuple_length (S n))*q) ∧ 
      tuple_TM (S n) (mk_tuple qin cin qout cout mv).

lemma match_to_tuples_list: ∀n,h,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_list n h l)) → 
    ∃p. p = mk_tuple qin cin qout cout mv ∧ mem ? p (tuples_list n h l).
#n #h #l #qin #cin #qout #cout #mv #Hmatch 
@(ex_intro … (mk_tuple qin cin qout cout mv)) % //
cases (match_decomp … Hmatch) #l1 * #l2 * * #Hflat #Hlen #Htuple
@(flatten_to_mem … Hflat … Hlen)  
  [// 
  |#x #memx @length_of_tuple 
   cases (mem_map ????? memx) #t * #memt #Ht <Ht // 
  |@(length_of_tuple … Htuple) 
  ]
qed.

lemma match_to_tuple: ∀n,h,l,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_list n h l)) → 
    ∃p. tuple_encoding n h p = mk_tuple qin cin qout cout mv ∧ mem ? p l.
#n #h #l #qin #cin #qout #cout #mv #Hmatch 
cases (match_to_tuples_list … Hmatch)
#p * #eqp #memb 
cases(mem_map … (λp.tuple_encoding n h p) … memb)
#p1 * #Hmem #H @(ex_intro … p1) % /2/
qed.

lemma match_to_trans: 
  ∀n.∀trans: trans_source n → trans_target n.
  ∀h,qin,cin,qout,cout,mv.
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_list n h (graph_enum ?? trans))) → 
  ∃s,t. tuple_encoding n h 〈s,t〉 = mk_tuple qin cin qout cout mv 
    ∧ trans s = t.
#n #trans #h #qin #cin #qout #cout #mv #Hmatch
cases (match_to_tuple … Hmatch) -Hmatch * #s #t * #Heq #Hmem
@(ex_intro … s) @(ex_intro … t) % // @graph_enum_correct 
@mem_to_memb @Hmem 
qed.

lemma trans_to_match:
  ∀n.∀h.∀trans: trans_source n → trans_target n.
  ∀s,t,qin,cin,qout,cout,mv. trans s = t →
  tuple_encoding n h 〈s,t〉 = mk_tuple qin cin qout cout mv →
  match_in_table (S n) qin cin qout cout mv (flatten ? (tuples_list n h (graph_enum ?? trans))).
#n #h #trans #inp #outp #qin #cin #qout #cout #mv #Htrans #Htuple 
@(tuple_to_match … (refl…)) <Htuple @mem_map_forward 
@(memb_to_mem (FinProd (trans_source n) (trans_target n)))
@graph_enum_complete //
qed.

(*
axiom append_eq_tech1 :
  ∀A,l1,l2,l3,l4.l1@l2 = l3@l4 → |l1| < |l3| → ∃la:list A.l1@la = l3.
axiom append_eq_tech2 :
  ∀A,l1,l2,l3,l4,a.l1@a::l2 = l3@l4 → memb A a l4 = false → ∃la:list A.l3 = l1@a::la.
axiom list_decompose_cases : 
  ∀A,l1,l2,l3,l4,a.l1@a::l2 = l3@l4 → ∃la,lb:list A.l3 = la@a::lb ∨ l4 = la@a::lb.
axiom list_decompose_l :
  ∀A,l1,l2,l3,l4,a.l1@a::l2 = l3@l4 → memb A a l4 = false → 
  ∃la,lb.l2 = la@lb ∧ l3 = l1@a::la.*)
  
lemma list_decompose_r :
  ∀A,l1,l2,l3,l4,a.l1@a::l2 = l3@l4 → memb A a l3 = false → 
  ∃la,lb.l1 = la@lb ∧ l4 = lb@a::l2.
#A #l1 #l2 #l3 generalize in match l1; generalize in match l2; elim l3
  [normalize #l1 #l2 #l4 #a #H #_ @(ex_intro … []) @(ex_intro … l2) /2/
  |#b #tl #Hind #l1 #l2 #l4 #a cases l2 
    [normalize #Heq destruct >(\b (refl … b)) normalize #Hfalse destruct
    |#c #tl2 whd in ⊢ ((??%%)→?); #Heq destruct #Hmema 
     cases (Hind l1 tl2 l4 a ??)
      [#l5 * #l6 * #eql #eql4 
       @(ex_intro … (b::l5)) @(ex_intro … l6) % /2/
      |@e0
      |cases (true_or_false (memb ? a tl)) [2://]
       #H @False_ind @(absurd ?? not_eq_true_false)
       <Hmema @sym_eq @memb_cons //
      ]
    ]
  ]
qed. 
         
(*axiom list_decompose_memb :
  ∀A,l1,l2,l3,l4,a.l1@a::l2 = l3@l4 → |l1| < |l3| → memb A a l3 = true.*)

lemma table_invert_r : ∀n,t,T.
  tuple_TM n t → table_TM n (t@T) → table_TM n T.
#n #t #T #Htuple #Htable inversion Htable
[ cases Htuple #qin * #cin * #qout * #cout * #mv * #_ #Ht >Ht
  normalize #Hfalse destruct (Hfalse)
| #t0 #T0 #Htuple0 #Htable0 #_ #Heq 
  lapply (append_l2_injective ?????? Heq)
  [ >(length_of_tuple … Htuple) >(length_of_tuple … Htuple0) % ]
  -Heq #Heq destruct (Heq) // ]
qed.

lemma match_in_table_to_tuple :
  ∀n,T,qin,cin,qout,cout,mv.
  match_in_table n qin cin qout cout mv T → table_TM n T → 
  tuple_TM n (mk_tuple qin cin qout cout mv).
#n #T #qin #cin #qout #cout #mv #Hmatch elim Hmatch
[ //
| #qin0 #cin0 #qout0 #cout0 #mv0 #tb #Htuple #Hmatch #IH #Htable
  @IH @(table_invert_r ???? Htable) @Htuple
]
qed.

lemma match_in_table_append :
  ∀n,T,qin,cin,qout,cout,mv,t.
  tuple_TM n t → 
  match_in_table n qin cin qout cout mv (t@T) → 
  t = mk_tuple qin cin qout cout mv ∨ match_in_table n qin cin qout cout mv T.
#n #T #qin #cin #qout #cout #mv #t #Ht #Hmatch inversion Hmatch
[ #T0 #H #H1 % >(append_l1_injective … H1) //
  >(length_of_tuple … Ht) >(length_of_tuple … H) %
| #qin0 #cin0 #qout0 #cout0 #mv0 #T0 #H #H1 #_ #H2 %2
  >(append_l2_injective … H2) // >(length_of_tuple … Ht) >(length_of_tuple … H) %
]
qed.

lemma generic_match_to_match_in_table_tech : 
  ∀n,t,T0,T1,T2.tuple_TM n t → table_TM n (T1@〈bar,false〉::T2) → 
   t@T0 = T1@〈bar,false〉::T2 → T1 = [] ∨ ∃T3.T1 = t@T3.
#n #t #T0 #T1 #T2 #Ht cases T1
[ #_ #_ % %
| normalize #c #T1c #Htable #Heq %2
  cases Ht in Heq; #qin * #cin * #qout * #cout * #mv **********
  #Hqin1 #Hqout1 #Hqin2 #Hqout2 #Hcin #Hcout #Hmv #Hcoutmv #Hqinlen #Hqoutlen
  #Heqt >Heqt whd in ⊢ (??%%→?); #Ht lapply (cons_injective_r ????? Ht)
  #Ht' cases (list_decompose_r STape … (sym_eq … Ht') ?)
  [ #la * #lb * #HT1c #HT0 %{lb} >HT1c @(eq_f2 ??? (append ?) (c::la)) //
    >HT0 in Ht'; >HT1c >associative_append in ⊢ (???%→?); #Ht'
    <(append_l1_injective_r … Ht') // <(cons_injective_l ????? Ht) %
  |@(noteq_to_eqnot ? true) @(not_to_not … not_eq_true_false) #Hbar @sym_eq 
   cases (memb_append … Hbar) -Hbar #Hbar
    [@(Hqin2 … Hbar) 
    |cases (orb_true_l … Hbar) -Hbar
      [#Hbar lapply (\P Hbar) -Hbar #Hbar destruct (Hbar) @Hcin
      |whd in ⊢ ((??%?)→?); #Hbar cases (memb_append … Hbar) -Hbar #Hbar
        [@(Hqout2 … Hbar)
        |cases (orb_true_l … Hbar) -Hbar
          [#Hbar lapply (\P Hbar) -Hbar #Hbar destruct (Hbar) @Hcout
          |#Hbar cases (orb_true_l … Hbar) -Hbar 
            [whd in ⊢ ((??%?)→?); #Hbar @Hbar
            |#Hbar lapply (memb_single … Hbar) -Hbar #Hbar destruct (Hbar) @Hmv
            ]
          ]
        ]
      ]
    ]
  ]
qed.
    
lemma generic_match_to_match_in_table :
  ∀n,T.table_TM n T → 
  ∀qin,cin,qout,cout,mv.|qin| = n → |qout| = n → 
  only_bits qin → only_bits qout → 
  bit_or_null (\fst cin) = true → bit_or_null (\fst cout) = true → 
  bit_or_null (\fst mv) = true →  
  ∀t1,t2.
  T = (t1@〈bar,false〉::qin@cin::〈comma,false〉::qout@cout::〈comma,false〉::[mv])@t2 → 
  match_in_table n qin cin qout cout mv T.
#n #T #Htable #qin #cin #qout #cout #mv #Hlenqin #Hlenqout
#Hqinbits #Hqoutbits #Hcin #Hcout #Hmv
elim Htable
[ * [ #t2 normalize in ⊢ (%→?); #Hfalse destruct (Hfalse)
    | #c0 #t1 #t2 normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
| #tuple #T0 #H1 #Htable0#IH #t1 #t2 #HT cases H1 #qin0 * #cin0 * #qout0 * #cout0 * #mv0
  * * * * * * * * * *
  #Hqin0marks #Hqout0marks #Hqin0bits #Hqout0bits #Hcin0 #Hcout0 #Hmv0 #Hcout0mv0
  #Hlenqin0 #Hlenqout0 #Htuple 
  lapply (generic_match_to_match_in_table_tech n ? T0 t1 
           (qin@cin::〈comma,false〉::qout@[cout;〈comma,false〉;mv]@t2) H1) #Htmp
  >Htuple in H1; #H1 
  lapply (ttm_cons … T0 H1 Htable0) <Htuple in ⊢ (%→?); >HT
  >associative_append normalize >associative_append normalize
  >associative_append #Htable cases (Htmp Htable ?)
  [ #Ht1 >Htuple in HT; >Ht1 normalize in ⊢ (??%%→?);
    >associative_append >associative_append #HT
    cut (qin0 = qin ∧ (〈cin0,false〉 = cin ∧ (qout0 = qout ∧ 
         (〈cout0,false〉 = cout ∧ (〈mv0,false〉 = mv ∧ T0 = t2)))))
    [ lapply (cons_injective_r ????? HT) -HT #HT 
      lapply (append_l1_injective … HT) [ >Hlenqin @Hlenqin0 ]
      #Hqin % [ @Hqin ] -Hqin
      lapply (append_l2_injective … HT) [ >Hlenqin @Hlenqin0 ] -HT #HT
      lapply (cons_injective_l ????? HT) #Hcin % [ @Hcin ] -Hcin
      lapply (cons_injective_r ????? HT) -HT #HT 
      lapply (cons_injective_r ????? HT) -HT
      >associative_append >associative_append #HT
      lapply (append_l1_injective … HT) [ >Hlenqout @Hlenqout0 ]
      #Hqout % [ @Hqout ] -Hqout
      lapply (append_l2_injective … HT) [ >Hlenqout @Hlenqout0 ] -HT normalize #HT
      lapply (cons_injective_l ????? HT) #Hcout % [ @Hcout ] -Hcout
      lapply (cons_injective_r ????? HT) -HT #HT 
      lapply (cons_injective_r ????? HT) -HT #HT
      lapply (cons_injective_l ????? HT) #Hmv % [ @Hmv ] -Hmv
      @(cons_injective_r ????? HT) ]
    -HT * #Hqin * #Hcin * #Hqout * #Hcout * #Hmv #HT0
    >(?:〈bar,false〉::qin0@(〈cin0,false〉::〈comma,false〉::qout0@
        [〈cout0,false〉;〈comma,false〉;〈mv0,false〉])@T0 = tuple@T0)
    [ >Htuple >Hqin >Hqout >Hcin >Hcout >Hmv % //
    | >Htuple normalize >associative_append normalize >associative_append
      normalize >associative_append % ]
  | * #T3 #HT3 >HT3 in HT; >associative_append; >associative_append #HT
    lapply (append_l2_injective … HT) // -HT #HT %2 //
    @(IH T3 t2) >HT >associative_append %
  |>HT >associative_append normalize >associative_append normalize
   >associative_append % ]
]
qed.
