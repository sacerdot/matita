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

definition write_states ≝ initN 2.

definition wr0 : write_states ≝ mk_Sig ?? 0 (leb_true_to_le 1 2 (refl …)).
definition wr1 : write_states ≝ mk_Sig ?? 1 (leb_true_to_le 2 2 (refl …)).

definition write ≝ λalpha,c.
  mk_TM alpha write_states
  (λp.let 〈q,a〉 ≝ p in
    match pi1 … q with 
    [ O ⇒ 〈wr1,Some ? 〈c,N〉〉
    | S _ ⇒ 〈wr1,None ?〉 ])
  wr0 (λx.x == wr1).
  
definition R_write ≝ λalpha,c,t1,t2.
  ∀ls,x,rs.t1 = midtape alpha ls x rs → t2 = midtape alpha ls c rs.
  
axiom sem_write : ∀alpha,c.Realize ? (write alpha c) (R_write alpha c).

definition copy_step_subcase ≝
  λalpha,c,elseM.ifTM ? (test_char ? (λx.x == 〈c,true〉))
    (seq (FinProd alpha FinBool) (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked alpha))
          (seq ? (write ? 〈c,false〉)
            (seq ? (move_r …)
              (seq ? (mark …)
                (seq ? (move_r …) (adv_to_mark_r … (is_marked alpha)))))))))
    elseM tc_true.

definition R_copy_step_subcase ≝ 
  λalpha,c,RelseM,t1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape (FinProd … alpha FinBool) (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = c ∧ t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ c ∧ RelseM t1 t2).
    
lemma sem_copy_step_subcase : 
  ∀alpha,c,elseM,RelseM. Realize ? elseM RelseM → 
  Realize ? (copy_step_subcase alpha c elseM) (R_copy_step_subcase alpha c RelseM).
#alpha #c #elseM #RelseM #HelseM #intape
cases (sem_if ? (test_char ? (λx. x == 〈c,true〉)) ?????? tc_true (sem_test_char ? (λx.x == 〈c,true〉))
        (sem_seq ????? (sem_adv_mark_r alpha)
          (sem_seq ????? (sem_move_l …)
            (sem_seq ????? (sem_adv_to_mark_l … (is_marked alpha))
              (sem_seq ????? (sem_write ? 〈c,false〉)
                (sem_seq ????? (sem_move_r …)
                  (sem_seq ????? (sem_mark …)
                    (sem_seq ????? (sem_move_r …) (sem_adv_to_mark_r … (is_marked alpha)))))))))
        HelseM intape)
#k * #outc * #Hloop #HR %{k} %{outc} % [@Hloop] -Hloop
#a #l1 #x0 #a0 #l2 #x #l3 #Hintape #Hl1marks cases HR -HR
[ * #ta * whd in ⊢ (%→?); >Hintape #Hta cases (Hta … (refl ??)) -Hta #Hx #Hta
  * #tb * whd in ⊢ (%→?); #Htb lapply (Htb … Hta) -Hta -Htb #Htb
  * #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htb -Htc #Htc
  * #td * whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd
  [ >Htc * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  * #_ #Htd lapply (Htd (l1@[〈a0,false〉]) 〈x0,true〉 l2 ? (refl ??) ?) -Htd
  [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1 [@(Hl1marks ? Hx1)|>(memb_single … Hx1) %]
  | normalize >associative_append % ] #Htd
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Hte -Htd -Htc #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Hte -Htf >reverse_append #Htf
  * #tg * whd in ⊢ (%→?); #Htg lapply (Htg … Htf) -Htf -Htg >reverse_single #Htg
  * #th * whd in ⊢ (%→?); #Hth lapply (Hth … Htg) -Htg -Hth
  generalize in match Hl1marks; -Hl1marks @(list_elim_left … l1)
  [ #Hl1marks #Hth whd in ⊢ (%→?); #Houtc cases (Houtc … Hth) -Houtc
    [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
    * #_ #Houtc lapply (Houtc [] ?? (refl ??) (refl ??) Hl1marks) -Houtc
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) % % [%] @Houtc
  | -l1 #c1 #l1 #_ #Hl1marks >reverse_append >reverse_single
    #Hth whd in ⊢ (%→?); #Houtc cases (Houtc … Hth) -Houtc
    [ * >Hl1marks [ #Hfalse destruct (Hfalse) ] @memb_append_l2 @memb_hd ]
    * #_ #Houtc lapply (Houtc (reverse ? l1@[〈x,false〉]) 〈a,true〉 l3 ? (refl ??) ?) -Houtc
    [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1 [ @Hl1marks @memb_append_l1 @daemon | >(memb_single … Hx1) % ]
    | normalize >associative_append % ] 
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) % % [%] >Houtc
    >reverse_append >reverse_reverse >associative_append >associative_append % ]
| * #ta * whd in ⊢ (%→?); >Hintape #Hta cases (Hta ? (refl ??)) -Hta 
  #Hxc #Hta >Hta #Houtc %2 % // lapply (\Pf Hxc) @not_to_not #Heq >Heq % ]
qed.
    
(*
if current = 0,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(0,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = 1,tt
   then advance_mark_r;
        move_l;
        advance_to_mark_l;
        write(1,ff)
        move_r;
        mark;
        move_r;
        advance_to_mark_r;
else if current = null 
   then advance_mark_r;
        move_l;
        advance_to_mark_l
        adv_mark_r;
        move_r;
        advance_to_mark_r
*)

definition nocopy_subcase ≝
  ifTM STape (test_char ? (λx:STape.x == 〈null,true〉))
    (seq ? (adv_mark_r …)
      (seq ? (move_l …)
        (seq ? (adv_to_mark_l … (is_marked ?))
          (seq ? (adv_mark_r …)
            (seq ? (move_r …) (adv_to_mark_r … (is_marked ?)))))))
    (nop ?) tc_true.

definition R_nocopy_subcase ≝ 
  λt1,t2.
    ∀a,l1,x0,a0,l2,x,l3.
    t1 = midtape STape (l1@〈a0,false〉::〈x0,true〉::l2) 
         〈x,true〉 (〈a,false〉::l3) → 
    (∀c.memb ? c l1 = true → is_marked ? c = false) →          
    (x = null ∧
     t2 = midtape ? (〈x,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3) ∨
    (x ≠ null ∧ t2 = t1).
    
lemma sem_nocopy_subcase : Realize ? nocopy_subcase R_nocopy_subcase.
#intape
cases (sem_if ? (test_char ? (λx:STape.x == 〈null,true〉)) ?????? tc_true
        (sem_test_char ? (λx:STape.x == 〈null,true〉))
          (sem_seq … (sem_adv_mark_r …)
            (sem_seq … (sem_move_l …)
              (sem_seq … (sem_adv_to_mark_l … (is_marked ?))
                (sem_seq … (sem_adv_mark_r …)
                  (sem_seq … (sem_move_r …) 
                    (sem_adv_to_mark_r … (is_marked ?))))))) (sem_nop ?) intape)
#k * #outc * #Hloop #HR @(ex_intro ?? k) @(ex_intro ?? outc)  % [@Hloop] -Hloop
#a #l1 #x0 #a0 #l2 #x #l3 #Hintape #Hl1marks cases HR -HR
[ * #ta * whd in ⊢ (%→?); >Hintape #Hta cases (Hta … (refl ??)) -Hta #Hx #Hta
  * #tb * whd in ⊢ (%→?); #Htb lapply (Htb … Hta) -Hta -Htb #Htb
  * #tc * whd in ⊢ (%→?); #Htc lapply (Htc … Htb) -Htb -Htc #Htc
  * #td * whd in ⊢ (%→?); #Htd cases (Htd … Htc) -Htd
  [ >Htc * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
  * #_ #Htd lapply (Htd (l1@[〈a0,false〉]) 〈x0,true〉 l2 ? (refl ??) ?) -Htd
  [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1 [@(Hl1marks ? Hx1)|>(memb_single … Hx1) %]
  | normalize >associative_append % ] >reverse_append #Htd
  * #te * whd in ⊢ (%→?); #Hte lapply (Hte … Htd) -Hte -Htd -Htc #Hte
  * #tf * whd in ⊢ (%→?); #Htf lapply (Htf … Hte) -Hte -Htf
  generalize in match Hl1marks; -Hl1marks @(list_elim_left … l1)
  [ #Hl1marks #Hth whd in ⊢ (%→?); #Houtc cases (Houtc … Hth) -Houtc
    [ * normalize in ⊢ (%→?); #Hfalse destruct (Hfalse) ]
    * #_ #Houtc lapply (Houtc [] ?? (refl ??) (refl ??) Hl1marks) -Houtc
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) % % [%] @Houtc
  | -l1 #c1 #l1 #_ #Hl1marks >reverse_append >reverse_single
    #Hth whd in ⊢ (%→?); #Houtc cases (Houtc … Hth) -Houtc
    [ * >Hl1marks [ #Hfalse destruct (Hfalse) ] @memb_append_l2 @memb_hd ]
    * #_ #Houtc lapply (Houtc (reverse ? l1@[〈x,false〉]) 〈a,true〉 l3 ? (refl ??) ?) -Houtc
    [ #x1 #Hx1 cases (memb_append … Hx1) -Hx1 #Hx1 [ @Hl1marks @memb_append_l1 @daemon | >(memb_single … Hx1) % ]
    | normalize >associative_append % ] 
    #Houtc lapply (\P Hx) -Hx #Hx destruct (Hx) % % [%] >Houtc
    >reverse_append >reverse_reverse >associative_append >associative_append % ]
| * #ta * whd in ⊢ (%→?); >Hintape #Hta cases (Hta ? (refl ??)) -Hta 
  #Hxc #Hta >Hta whd in ⊢ (%→?); #Houtc %2 %
  [ lapply (\Pf Hxc) @not_to_not #Heq >Heq %
  | @Houtc ]
qed.

definition copy_step ≝
  ifTM ? (test_char STape (λc.bit_or_null (\fst c)))
  (single_finalTM ? (copy_step_subcase FSUnialpha (bit false)
    (copy_step_subcase FSUnialpha (bit true) nocopy_subcase)))
  (nop ?)
  tc_true.
  
definition R_copy_step_true ≝ 
  λt1,t2.
    ∀ls,c,rs. t1 = midtape STape ls 〈c,true〉 rs → 
    bit_or_null c = true ∧
    (∀a,l1,x0,a0,l2,l3.
     ls = (l1@〈a0,false〉::〈x0,true〉::l2) → 
     rs = (〈a,false〉::l3) → 
     no_marks l1 →          
     ((∃x. c = bit x ∧
      t2 = midtape STape (〈bit x,false〉::l1@〈a0,true〉::〈bit x,false〉::l2) 〈a,true〉 l3) ∨
      (c = null ∧
      t2 = midtape ? (〈null,false〉::l1@〈a0,true〉::〈x0,false〉::l2) 〈a,true〉 l3))).
     
definition R_copy_step_false ≝ 
  λt1,t2.
   ∀ls,c,rs.t1 = midtape (FinProd … FSUnialpha FinBool) ls c rs → 
   bit_or_null (\fst c) = false ∧ t2 = t1.
   
lemma sem_copy_step : 
  accRealize ? copy_step (inr … (inl … (inr … start_nop))) R_copy_step_true R_copy_step_false.
#intape
@(acc_sem_if_app … (sem_test_char ? (λc:STape.bit_or_null (\fst c)))  …
    (sem_copy_step_subcase FSUnialpha (bit false) …
       (sem_copy_step_subcase FSUnialpha (bit true) … (sem_nocopy_subcase …)))
          (sem_nop …))
[ #t1 #t2 #t3 whd in ⊢ (%→%→?); #H1 #H2 #ls #c #rs #Ht1 >Ht1 in H1; #H1
  cases (H1 … (refl ??)) #Hc #Ht3 % [ @Hc ]
  #a #l1 #x0 #a0 #l2 #l3 #Hls #Hrs #Hl1marks >Hls in Ht3; >Hrs #Ht3
  cases (H2 … Ht3 ?)
  [ * #Hc' #Ht2 % %{false} % // <Hc' @Ht2
  | * #Hnotfalse whd in ⊢ (%→?); #Ht2 cases (Ht2 … Ht3 ?) -Ht2
    [ * #Hc' #Ht2 % %{true} % // <Hc' @Ht2
    |  * #Hnottrue whd in ⊢ (%→?); #Ht2 cases (Ht2 … Ht3 ?) -Ht2
      [ * #Hc' #Ht2 %2 <Hc' % // @Ht2
      | * #Hnotnull @False_ind
        generalize in match Hnotnull;generalize in match Hnottrue;generalize in match Hnotfalse;
        cases c in Hc; normalize
        [ * [ #_ #_ * #Hfalse #_ | #_ * #Hfalse #_ #_ ]
        | #_ #_ #_ * #Hfalse
        |*: #Hfalse destruct (Hfalse) ] @Hfalse %
      | @Hl1marks ]
    | @Hl1marks ]
  | @Hl1marks ]
| #t1 #t2 #t3 whd in ⊢ (%→%→?); #H1 #H2 #ls #c #rs #Ht1
  >Ht1 in H1; #H1 cases (H1 … (refl ??)) #_ #Ht3 cases (H1 ? (refl ??)) -H1
  #Hc #Ht3 % //
]
qed.

(*
1) il primo carattere è marcato
2) l'ultimo carattere è l'unico che può essere null, gli altri sono bit
3) il terminatore non è né bit, né null
*)
   
definition copy0 ≝ whileTM ? copy_step (inr … (inl … (inr … start_nop))).

let rec merge_config (l1,l2:list STape) ≝ 
  match l1 with
  [ nil ⇒ nil ?
  | cons p1 l1' ⇒ match l2 with
    [ nil ⇒ nil ? 
    | cons p2 l2' ⇒ 
           let 〈c1,b1〉 ≝ p1 in let 〈c2,b2〉 ≝ p2 in
           match c2 with
           [ null ⇒ p1
           | _ ⇒ p2 ] :: merge_config l1' l2' ] ].
           
lemma merge_config_append :
 ∀l1,l2,l3,l4.|l1| = |l2| → 
 merge_config (l1@l3) (l2@l4) = merge_config l1 l2@merge_config l3 l4.
#l1 #l2 #l3 #l4 #Hlen @(list_ind2 … Hlen)
[normalize //
| #t1 #t2 * #c1 #b1 * #c2 #b2 #IH whd in ⊢ (??%%); >IH % ]
qed.

definition R_copy0 ≝ λt1,t2.
  ∀ls,c,c0,rs,l1,l3,l4.
  t1 = midtape STape (l3@l4@〈c0,true〉::ls) 〈c,true〉 (l1@rs) → 
  no_marks l1 → no_marks (l3@l4) → |l1| = |l4| → 
  ∀l1',bv.〈c,false〉::l1 = l1'@[〈comma,bv〉] → only_bits_or_nulls l1' → 
  ∀l4',bg.l4@[〈c0,false〉] = 〈grid,bg〉::l4' → only_bits_or_nulls l4' → 
  (c = comma ∧ t2 = t1) ∨
  (c ≠ comma ∧ 
    t2 = midtape ? (reverse ? l1'@l3@〈grid,true〉::
                  merge_config l4' (reverse ? l1')@ls) 
     〈comma,true〉 rs).
     
lemma inj_append_singleton_l1 :
  ∀A.∀l1,l2:list A.∀a1,a2.l1@[a1] = l2@[a2] → l1 = l2.
#A #l1 #l2 #a1 #a2 #H lapply (eq_f … (reverse ?) … H)
>reverse_append >reverse_append normalize #H1 destruct
lapply (eq_f … (reverse ?) … e0) >reverse_reverse >reverse_reverse //
qed.

lemma inj_append_singleton_l2 :
  ∀A.∀l1,l2:list A.∀a1,a2.l1@[a1] = l2@[a2] → a1 = a2.
#A #l1 #l2 #a1 #a2 #H lapply (eq_f … (reverse ?) … H)
>reverse_append >reverse_append normalize #H1 destruct %
qed.

lemma wsem_copy0 : WRealize ? copy0 R_copy0.
#intape #k #outc #Hloop 
lapply (sem_while … sem_copy_step intape k outc Hloop) [%] -Hloop
* #ta * #Hstar @(star_ind_l ??????? Hstar)
[ #tb whd in ⊢ (%→?); #Hleft
  #ls #c #c0 #rs #l1 #l3 #l4 #Htb #Hl1nomarks #Hl3l4nomarks #Hlen #l1' #bv
  #Hl1 #Hl1bits #l4' #bg #Hl4 #Hl4bits
  cases (Hleft … Htb) -Hleft #Hc #Houtc % %
  [ generalize in match Hl1bits; -Hl1bits cases l1' in Hl1;
    [ normalize #Hl1 #c1 destruct (Hl1) %
    | * #c' #b' #l0 #Heq normalize in Heq; destruct (Heq)
      #Hl1bits lapply (Hl1bits 〈c',false〉 ?) [ @memb_hd ] 
      >Hc #Hfalse destruct ]
  | @Houtc ]
| #tb #tc #td whd in ⊢ (%→?→(?→%)→%→?); #Htc #Hstar1 #Hind #Htd
  lapply (Hind Htd) -Hind #Hind
  #ls #c #c0 #rs #l1 #l3 #l4 #Htb #Hl1nomarks #Hl3l4nomarks #Hlen #l1' #bv
  #Hl1 #Hl1bits #l4' #bg #Hl4 #Hl4bits %2
  cases (Htc … Htb) -Htc #Hcbitnull #Htc
  % [ % #Hc' >Hc' in Hcbitnull; normalize #Hfalse destruct (Hfalse) ]
  cut (|l1| = |reverse ? l4|) [@daemon] #Hlen1
  @(list_cases2 … Hlen1)
  [ (* case l1 = [] is discriminated because l1 contains at least comma *)
    #Hl1nil @False_ind >Hl1nil in Hl1; cases l1' normalize
    [ #Hl1 destruct normalize in Hcbitnull; destruct (Hcbitnull)
    | #p0 #l0 normalize #Hfalse destruct (Hfalse) cases l0 in e0;
      [ normalize #Hfalse1 destruct (Hfalse1)
      | #p0' #l0' normalize #Hfalse1 destruct (Hfalse1) ] ]
  | (* case c::l1 = c::a::l1'' *)
    * #a #ba * #a0 #ba0 #l1'' #l4'' #Hl1cons #Hl4cons
    lapply (eq_f ?? (reverse ?) ?? Hl4cons) >reverse_reverse >reverse_cons -Hl4cons #Hl4cons
    cut (ba = false) 
    [ >Hl1cons in Hl1nomarks; #Hl1nomarks lapply (Hl1nomarks 〈a,ba〉 ?)
      [ @memb_hd | normalize // ] ] #Hba
    cut (ba0 = false) 
    [ >Hl4cons in Hl3l4nomarks; #Hl3l4nomarks lapply (Hl3l4nomarks 〈a0,ba0〉 ?)
      [ @memb_append_l2 @memb_append_l2 @memb_hd | normalize // ] ] #Hba0
    >Hba0 in Hl4cons; >Hba in Hl1cons; -Hba0 -Hba #Hl1cons #Hl4cons
    >Hl4cons in Htc; >Hl1cons #Htc
    lapply (Htc a (l3@reverse ? l4'') c0 a0 ls (l1''@rs) ? (refl ??) ?)
    [ #x #Hx @Hl3l4nomarks >Hl4cons <associative_append
      @memb_append_l1 @Hx
    | >associative_append >associative_append %
    | -Htc
      cut (∃la.l1' = 〈c,false〉::la)
      [ >Hl1cons in Hl1; cases l1'
        [normalize #Hfalse destruct (Hfalse)
        | #p #la normalize #Hla destruct (Hla) @(ex_intro ?? la) % ] ]
      * #la #Hla
      cut (∃lb.l4' = lb@[〈c0,false〉])
      [ >Hl4cons in Hl4;
        @(list_elim_left … l4')
        [ #Heq lapply (eq_f … (length ?) … Heq)
          >length_append >length_append 
          >commutative_plus normalize >commutative_plus normalize
          #Hfalse destruct
        | #a1 #tl #_ #Heq 
          >(inj_append_singleton_l2 ? (reverse ? l4''@[〈a0,false〉]) (〈grid,bg〉::tl) 〈c0,false〉 a1 Heq)
          @ex_intro //
      ] ] * #lb #Hlb
      cut (|lb| = |reverse ? la|) 
      [ >Hla in Hl1; >Hlb in Hl4; #Hl4 #Hl1
        >(?:l1 = la@[〈comma,bv〉]) in Hlen;
        [|normalize in Hl1; destruct (Hl1) %]
        >(?:l4 = 〈grid,bg〉::lb)
        [|@(inj_append_singleton_l1 ?? (〈grid,bg〉::lb) ?? Hl4) ]
        >length_append >commutative_plus >length_reverse
        normalize #Hlalb destruct (Hlalb) //
      ] #Hlen2
      *
      (* by hyp on the first iteration step, 
         we consider whether c = bit x or c = null *)
      (* c = bit x *)
      [ * #x * #Hx #Htc 
        lapply (Hind (〈bit x,false〉::ls) a a0 rs l1'' 
                (〈bit x,false〉::l3) (reverse ? l4'') ????) 
        [ >Hl1cons in Hlen; >Hl4cons >length_append >commutative_plus 
          normalize #Hlen destruct (Hlen) //
        | #x0 #Hx0 cases (orb_true_l … Hx0)
          [ #Hx0eq >(\P Hx0eq) %
          | -Hx0 #Hx0 @Hl3l4nomarks >Hl4cons
            <associative_append @memb_append_l1 // ]
        | #x0 #Hx0 @Hl1nomarks >Hl1cons @memb_cons //
        | >Htc >associative_append % 
        | -Hind 
          <Hl1cons <Hl4cons #Hind lapply (Hind la bv ?? lb bg ??)
          [ #x0 #Hx0 @Hl4bits >Hlb @memb_append_l1 //
          | >Hlb in Hl4; normalize in ⊢ (%→?); #Hl4
            @(inj_append_singleton_l1 ? l4 (〈grid,bg〉::lb) … Hl4)
          | #x0 #Hx0 @Hl1bits >Hla @memb_cons //
          | >Hla in Hl1; normalize in ⊢ (%→?); #Hl1
            destruct (Hl1) // ] -Hind
          (* by IH, we proceed by cases, whether a = comma 
             (consequently several lists = []) or not *)          
          *
          [ * #Ha #Houtc1
(*           cut (l1 = [〈a,false〉])
           [ cases l1'' in Hl1cons; // #y #ly #Hly
             >Hly in Hl1; cases l1' in Hl1bits;
             [ #_ normalize #Hfalse destruct (Hfalse)
             | #p #lp #Hl1bits normalize #Heq destruct (Heq)
               @False_ind lapply (Hl1bits 〈a,false〉 ?)
               [ cases lp in e0;
                 [ normalize #Hfalse destruct (Hfalse)
                 | #p0 #lp0 normalize in ⊢ (%→?); #Heq destruct (Heq)
                   @memb_cons @memb_hd ]
               | >Ha normalize #Hfalse destruct (Hfalse) ]
             ]
           ] #Hl1a
           cut (l4 = [〈a0,false〉])
           [ generalize in match Hl4bits; cases l4' in Hl4;
             [ >Hl4cons #Hfalse #_ 
               lapply (inj_append_singleton_l1 ?? [] ?? Hfalse)
               cases (reverse ? l4'') normalize
               [ #Hfalse1 | #p0 #lp0 #Hfalse1 ] destruct (Hfalse1)
             | #p #lp 
           
             cases l4'' in Hl4cons; // #y #ly #Hly
             >Hly in Hl4; cases l4' in Hl4bits;
             [ #_ >reverse_cons #Hfalse
               lapply (inj_append_singleton_l1 ?? [] ?? Hfalse)
               -Hfalse cases ly normalize
               [ #Hfalse | #p #Hp #Hfalse ] destruct (Hfalse)
                
             | #p #lp #Hl1bits normalize #Heq destruct (Heq)
               @False_ind lapply (Hl1bits 〈a,false〉 ?)
               [ cases lp in e0;
                 [ normalize #Hfalse destruct (Hfalse)
                 | #p0 #lp0 normalize in ⊢ (%→?); #Heq destruct (Heq)
                   @memb_cons @memb_hd ]
               | >Ha normalize #Hfalse destruct (Hfalse) ]
             ]
           ] #Hl1a
             
              >Hla normalize #Hl1 destruct (Hl1) lapply (inj_append_ @False_ind
             
           cut (l1'' = [] ∧ l4'' = [])
           [ % [ >Hla in Hl1; normalize #Hl1 destruct (Hl1)
           
            cases l1'' in Hl1bits;
                
                 [ #_ normalize #H *)
           cut (la = [] ∧ lb = [] ∧ l1'' = [] ∧ l4'' = [])
           [ @daemon ] * * * #Hla1 #Hlb1 #Hl1nil #Hl4nil
           >Hl1cons in Hl1; >Hla
           >Houtc1 >Htc #Hl1
           >Hl4cons in Hl4; >Hlb #Hl4
           >Hla1 >Hlb1 >Hl1nil >Hl4nil >Hx
           cut (a0 = grid) [ @daemon ] #Ha0 <Ha <Ha0
           normalize in ⊢ (??(??%?%)(??%?%)); >associative_append %
          | * #Ha #Houtc1 >Houtc1 @eq_f3 //
            >Hla >reverse_cons >associative_append @eq_f
            >Hx whd in ⊢ (??%?); @eq_f whd in ⊢ (???%); @eq_f @eq_f
            >Hlb >append_cons @eq_f2 // >(merge_config_append … Hlen2) %            
          ]
       ]
    | (* c = null *)
      * #Hc #Htc 
      lapply (Hind (〈c0,false〉::ls) a a0 rs l1'' (〈null,false〉::l3) (reverse ? l4'') ????)
      [  >Hl1cons in Hlen; >Hl4cons >length_append >commutative_plus normalize
         #Hlen destruct (Hlen) @e0
      | #x0 #Hx0 cases (memb_append STape ? [〈null,false〉] (l3@reverse ? l4'') … Hx0) -Hx0 #Hx0
        [ >(memb_single … Hx0) %
        | @Hl3l4nomarks cases (memb_append … Hx0) -Hx0 #Hx0
          [ @memb_append_l1 //
          | @memb_append_l2 >Hl4cons @memb_append_l1 // ]
        ]
      | >Hl1cons #x' #Hx0 @Hl1nomarks >Hl1cons @memb_cons //
      | >Htc @eq_f3 // >associative_append % ] -Hind <Hl1cons <Hl4cons #Hind
        lapply (Hind la bv ?? lb bg ??)
          [ #x0 #Hx0 @Hl4bits >Hlb @memb_append_l1 //
          | >Hlb in Hl4; normalize in ⊢ (%→?); #Hl4
            @(inj_append_singleton_l1 ? l4 (〈grid,bg〉::lb) … Hl4)
          | #x0 #Hx0 @Hl1bits >Hla @memb_cons //
          | >Hla in Hl1; normalize in ⊢ (%→?); #Hl1
            destruct (Hl1) // ] -Hind *
          (* by IH, we proceed by cases, whether a = comma 
             (consequently several lists = []) or not *)          
          [ * #Ha #Houtc1 >Hl1cons in Hl1; >Hla
           >Houtc1 >Htc #Hl1
           >Hl4cons in Hl4; >Hlb #Hl4
           cut (la = [] ∧ lb = [] ∧ l1'' = [] ∧ l4'' = []) 
           [@daemon] * * * #Hla1 #Hlb1 #Hl1nil #Hl4nil
           >Hla1 >Hlb1 >Hl1nil >Hl4nil >Hc
           cut (a0 = grid) [ @daemon ] #Ha0 <Ha <Ha0
           normalize in ⊢ (??(??%?%)(??%?%)); >associative_append %
          | * #Ha #Houtc1 >Houtc1 @eq_f3 //
            >Hla >reverse_cons >associative_append @eq_f
            >Hc whd in ⊢ (??%?); @eq_f whd in ⊢ (???%); @eq_f @eq_f
            >Hlb >append_cons @eq_f2 // >(merge_config_append … Hlen2) %
          ]
       ]
]]]
qed.

definition merge_char ≝ λc1,c2.
  match c2 with
  [ null ⇒ c1
  | _ ⇒ c2 ].
  
lemma merge_cons : 
  ∀c1,c2,conf1,conf2.
  merge_config (〈c1,false〉::conf1) (〈c2,false〉::conf2) = 
    〈merge_char c1 c2,false〉::merge_config conf1 conf2.
#c1 #c2 #conf1 #conf2 normalize @eq_f2 //
cases c2 /2/
qed.

lemma merge_bits : ∀l1,l2.|l1| = |l2| → only_bits l2 → merge_config l1 l2 = l2.
#l1 #l2 #Hlen @(list_ind2 … Hlen) //
#tl1 #tl2 #hd1 #hd2 #IH
>(eq_pair_fst_snd … hd1) >(eq_pair_fst_snd … hd2) #Hbits
change with (cons ???) in ⊢ (??%?); @eq_f2
[ cases (\fst hd2) in Hbits; 
  [ #b #_ %
  |*: #Hfalse lapply (Hfalse … (memb_hd …)) normalize #Hfalse1 destruct (Hfalse1) ]
| @IH #x #Hx @Hbits @memb_cons // ]
qed.

lemma merge_config_c_nil : 
  ∀c.merge_config c [] = [].
#c cases c normalize //
qed.

lemma reverse_merge_config :
  ∀c1,c2.|c1| = |c2| → reverse ? (merge_config c1 c2) = 
    merge_config (reverse ? c1) (reverse ? c2).        
#c1 #c2 <(length_reverse ? c1) <(length_reverse ? c2) #Hlen
<(reverse_reverse ? c1) in ⊢ (??%?); <(reverse_reverse ? c2) in ⊢ (??%?);
generalize in match Hlen; @(list_ind2 … Hlen) -Hlen //
#tl1 #tl2 #hd1 #hd2 #IH whd in ⊢ (??%%→?); #Hlen destruct (Hlen) -Hlen
<(length_reverse ? tl1) in e0; <(length_reverse ? tl2) #Hlen
>reverse_cons >reverse_cons >(merge_config_append ???? Hlen)
>reverse_append >(eq_pair_fst_snd ?? hd1) >(eq_pair_fst_snd ?? hd2)
whd in ⊢ (??%%); @eq_f2 // @IH //
qed.

definition copy
≝ 
  seq STape copy0 (seq ? (move_l …) (seq ? (adv_to_mark_l … (is_marked ?))
   (seq ? (clear_mark …) (seq ? (adv_to_mark_r … (is_marked ?)) (clear_mark …))))).

(*
   s0, s1 = caratteri di testa dello stato
   c0 = carattere corrente del nastro oggetto
   c1 = carattere in scrittura sul nastro oggetto
   
   questa dimostrazione sfrutta il fatto che 
   merge_config (l0@[c0]) (l1@[c1]) = l1@[merge_char c0 c1] 
   se l0 e l1 non contengono null
*)

definition R_copy ≝ λt1,t2.
  ∀ls,s0,s1,c0,c1,rs,l1,l3,l4.
  t1 = midtape STape (l3@〈grid,false〉::〈c0,false〉::l4@〈s0,true〉::ls) 〈s1,true〉 (l1@〈c1,false〉::〈comma,false〉::rs) → 
  no_marks l1 → no_marks l3 → no_marks l4 → |l1| = |l4| → 
  only_bits (l4@[〈s0,false〉]) → only_bits (〈s1,false〉::l1) → 
  bit_or_null c0 = true → bit_or_null c1 = true → 
  t2 = midtape STape (〈c1,false〉::reverse ? l1@〈s1,false〉::l3@〈grid,false〉::
                      〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)
       〈comma,false〉 rs.
       
axiom sem_copy0 : Realize ? copy0 R_copy0.

definition option_cons ≝ λA.λa:option A.λl.
  match a with
  [ None ⇒ l
  | Some a' ⇒ a'::l ].

lemma sem_copy : Realize ? copy R_copy.
#intape 
cases (sem_seq … (sem_copy0 …)
        (sem_seq … (sem_move_l …)
          (sem_seq … (sem_adv_to_mark_l … (is_marked ?))
            (sem_seq … (sem_clear_mark …)
              (sem_seq … (sem_adv_to_mark_r … (is_marked ?)) (sem_clear_mark …))))) intape)
#k * #outc * #Hloop #HR %{k} %{outc} % [@Hloop] -Hloop
#ls #s0 #s1 #c0 #c1 #rs #l1 #l2 #l3 #Hintape #Hl1marks #Hl2marks #Hl3marks #Hlen
#Hbits1 #Hbits2 #Hc0bits #Hc1bits
cases HR -HR #ta * whd in ⊢ (%→?); #Hta 
cut (ta = midtape STape (〈c1,false〉::reverse ? l1@〈s1,false〉::l2@〈grid,true〉::
                      〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)
       〈comma,true〉 rs)
[lapply (Hta ls s1 s0 rs (l1@[〈c1,false〉;〈comma,false〉]) l2 (〈grid,false〉::〈c0,false〉::l3) ?)
  [>associative_append in ⊢ (???(????%)); normalize in ⊢ (???(??%%%)); @Hintape ]
 -Hta #Hta cases (Hta ??? (〈s1,false〉::l1@[〈c1,false〉]) false ? ? ?? (refl ??) ?)
  [3: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ @Hl1marks //
    | cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) % | >(memb_single … Hx) % ]] 
  |4: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ @Hl2marks //
    | cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) % | cases (orb_true_l … Hx) [-Hx #Hx >(\P Hx) % | @Hl3marks ] ] ]
  |5: >length_append normalize >Hlen >commutative_plus %
  |6: normalize >associative_append %
  |7: #x #Hx cases (memb_append ?? (〈s1,false〉::l1) … Hx) -Hx #Hx
    [ whd in ⊢ (??%?); >(Hbits2 … Hx) %
    | >(memb_single … Hx) // ]
  |8: #x #Hx cases (memb_append … Hx) -Hx #Hx
    [ cases (orb_true_l … Hx) -Hx #Hx [ >(\P Hx) // | whd in ⊢ (??%?); >Hbits1 // @memb_append_l1 // ]
    | >(memb_single … Hx) whd in ⊢ (??%?); >(Hbits1 〈s0,false〉) // @memb_append_l2 @memb_hd ]
  | * #Hs1 @False_ind >Hs1 in Hbits2; #Hbits2 lapply (Hbits2 〈comma,false〉 ?) //
    normalize #Hfalse destruct (Hfalse)
  | * #Hs1 #Ht2 >Ht2 >reverse_cons >reverse_append >reverse_single @eq_f3 //
    >merge_cons >merge_bits
    [2: #x #Hx @Hbits2 cases (memb_append STape ? (reverse ? l1) ? Hx) -Hx #Hx
      [@daemon | >(memb_single … Hx) @memb_hd ]
    |3: >length_append >length_append >length_reverse >Hlen % ]
    normalize >associative_append normalize >associative_append %
  ]
] -Hta #Hta * #tb * whd in ⊢ (%→?); #Htb
lapply (Htb … Hta) -Htb #Htb change with (midtape ????) in Htb:(???%);
* #tc * whd in ⊢ (%→?); #Htc 
cases (Htc … Htb)
[ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
* #_ #Htc 
lapply (Htc (reverse ? l1@〈s1,false〉::l2) 〈grid,true〉 
          (〈merge_char c0 c1,false〉::reverse ? l1@〈s1,false〉::ls)???)
[ #x #Hx cases (memb_append … Hx) -Hx #Hx
  [ @Hl1marks @daemon
  | cases (orb_true_l … Hx) -Hx #Hx
    [ >(\P Hx) % | @(Hl2marks … Hx) ] ]
| %
| whd in ⊢ (??%?); >associative_append % ] -Htc #Htc
* #td * whd in ⊢ (%→?); #Htd lapply (Htd … Htc) -Htd #Htd
* #te * whd in ⊢ (%→?); #Hte cases (Hte … Htd) -Hte -Htd
[ * #Hfalse normalize in Hfalse; destruct (Hfalse) ]
* #_ #Hte 
lapply (Hte (reverse ? (reverse ? l1@〈s1,false〉::l2)@[〈c1,false〉])
         〈comma,true〉 rs ? (refl ??) ?) -Hte
[ >reverse_append >reverse_cons >reverse_reverse #x #Hx
  cases (memb_append … Hx) -Hx #Hx
  [ cases (memb_append … Hx) -Hx #Hx
    [ cases (memb_append … Hx) -Hx #Hx
      [ @daemon 
      | lapply (memb_single … Hx) -Hx #Hx >Hx % ]
    | @(Hl1marks … Hx) ]
  | lapply (memb_single … Hx) -Hx #Hx >Hx % ]
| >reverse_append >reverse_reverse >reverse_cons
  >associative_append >associative_append >associative_append
  >associative_append >associative_append % ]
#Hte whd in ⊢ (%→?); #Houtc lapply (Houtc … Hte) -Houtc #Houtc >Houtc
@eq_f3 //
>reverse_append >reverse_append >reverse_single >reverse_cons
>reverse_append >reverse_append >reverse_reverse >reverse_reverse
>reverse_single >associative_append >associative_append %
qed.