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

include "projdat/basic_type.ma".


theorem base_iff: ∀b,y:bool. if b then y else y = y.
* normalize // qed.

theorem base_iff2: ∀b. if b then true else false = b.
* normalize // qed.

theorem hp_tesi: ∀D:DeqSet. ∀x,y:D. ∀b:bool. if (x==y) then b else false=true→b=true.
#D #x #y #b elim b #Hp // normalize in Hp; > base_iff in Hp; // qed.

theorem hp_tesi2: ∀D:DeqSet. ∀x,y:D. ∀b:bool. if (x==y) then b else false=true→(x==y)=true.
#D #x #y #b #Hp lapply (hp_tesi … Hp) #Hp2
destruct >base_iff2 in Hp; // qed.

(******************************************************************************)
(*                       Coercizione per i dati lista                         *)
(******************************************************************************)

let rec eqb_lD (T:DeqSet) (x,y:list T) on x : bool ≝
  match x with
  [ nil ⇒ 
    match y with
    [ nil ⇒ true
    | _ ⇒ false]
  | cons a b ⇒ 
    match y with
    [ nil ⇒ false
    | cons c d ⇒ (eqb T a c)∧(eqb_lD T b d)]].
    
lemma eqb_same_D: ∀D:DeqSet. ∀x:D. (eqb D x x)=true.
#D #same @(proj2 … (eqb_true D ? ? ) …) // qed.

theorem listD_elim2 :
∀D:DeqSet.
 ∀R:list D→ list D → Prop.
  (∀n:list D. R [] n) 
  → (∀n,r. R (r::n) [])
  → (∀n,m,r,u. R n m → R (r::n) (u::m))
  → ∀n,m. R n m.
#D
#R #ROn #RSO #RSS #n (elim n) // #n0 #lN0 #Rn0m #m (cases m) /2/ qed.

lemma list_destr_l: ∀D:DeqSet. ∀a,b:D.∀r,s:list D. (a=b)∧(r=s)→(a::r)=(b::s).
#D #x #y #r #s #Hp
lapply (proj1 (x=y) (r=s) Hp) 
     lapply (proj2 (x=y) (r=s) Hp)
#H #H2 >H >H2 // qed.

lemma list_destr_r: ∀D:DeqSet. ∀a,b:D.∀r,s:list D. (a::r)=(b::s)→(a=b)∧(r=s).
#D #x #y *
  [ * 
    [ #Hp % 
    
      [destruct @refl
      |//
      ]
    | #d #lD #hp destruct
    ]
  | #d #lD #s #hp destruct % @refl] qed.
  
lemma obv_eqb: ∀D:DeqSet.∀x:D. (x==x)=true.
#D #l @(proj2 … (eqb_true ???) ) // qed.
  
lemma obv_eb_l: ∀D. ∀e,l. (eqb_lD D (e::l) (e::l)=true).
#D #x#y normalize elim y normalize >obv_eqb // 
#X #lX normalize #Hp >obv_eqb normalize @Hp qed.

lemma liD_right: ∀D:DeqSet. ∀x,y:list D. (x=y)→(eqb_lD D x y)=true.
#D
@listD_elim2
[ #n #asmpt <asmpt //
| #L #r #Hp>Hp //
| #l1 #l2 #e1 #e2 #Hp #eI lapply(list_destr_r D e1 e2 l1 l2 eI)
  #HpE lapply (proj1 ? ? HpE) lapply (proj2 ? ? HpE) -HpE
  #ls lapply (Hp ls) -Hp
  #eqv #hp destruct
   destruct
  normalize >obv_eqb normalize @eqv] qed.

lemma lid_left_1: ∀D:DeqSet. ∀x,y:D. ∀l1,l2:list D. ((x==y)=true)∧(l1=l2)→(x::l1=y::l2).
#D #x #y #L #M * #Hp lapply (proj1 … (eqb_true D ? ? ) Hp) -Hp #Hp #LH destruct // qed.

lemma tesi3: ∀D:DeqSet. ∀x,y:D. ∀M. (x=y)→(x::M=y::M).
#T#a #b #L #hp destruct // qed. 

lemma liD_left: ∀D:DeqSet. ∀x,y:list D. (eqb_lD D x y)=true→(x=y).
#D @listD_elim2 
  [ * normalize // #hp #HHp #abs destruct
  | #L #el normalize #abs destruct
  | #L #M #x #y #Hp normalize #N lapply (hp_tesi2… N) #Hp2 
    lapply(hp_tesi D … N) -N #N lapply(Hp N) 
    -Hp -N #HP destruct @tesi3 @(proj1 … (eqb_true D ? ? )) //] qed.

lemma biimplication_lD: ∀D:DeqSet. ∀x,y:list D. iff ((eqb_lD D x y)=true) (x=y).
#D #x #y %
  [ @liD_left | @liD_right ]
qed.


definition DeqList ≝ λT:DeqSet. mk_DeqSet (list T) (eqb_lD T) (biimplication_lD T).

unification hint  0 ≔ C1:DeqSet; 
    X ≟ DeqList C1
(* ---------------------------------------- *) ⊢ 
    DeqList C1 ≡ carr X.
    
unification hint  0 ≔ C1:DeqSet,b1:list C1,b2: list C1; 
    X ≟ DeqList C1
(* ---------------------------------------- *) ⊢ 
    eqb_lD C1 b1 b2 ≡ eqb X b1 b2.


(******************************************************************************)
(*                           Coercizione per i dati Σ                         *)
(******************************************************************************)

definition Sig_fst  ≝ λA:Type[0].λP:A→Prop.λx:Sig A P. 
  match x with [mk_Sig a h ⇒ a].

definition Sig_snd : ∀A,P.∀x:Sig A P.P (Sig_fst A P x) ≝ λA,P,x.
  match x return λx.P (Sig_fst A P x) with [mk_Sig a h ⇒ h].
  
definition Sig_eq  ≝ λA:DeqSet.λP:A→Prop. λx,y:Sig A P. 
  ((Sig_fst A P x)==(Sig_fst A P y)).

lemma biimplication_Sig: ∀A:DeqSet.∀P:A→Prop. ∀x,y:Sig A P.
  (Sig_eq A P x y)=true↔(x=y).
#A #P * #a1 #p1 
      * #a2 #p2
      %
      [ normalize #Hp
        lapply (proj1 … (eqb_true A ? ?) Hp)
        -Hp
        #Hp destruct //
      | #Hp destruct normalize //] qed.
      
definition DeqSig ≝ λT:DeqSet.λP:T→Prop. mk_DeqSet (Sig T P) (Sig_eq T P) (biimplication_Sig T P).

unification hint  0 ≔ C1:DeqSet,C2:C1→Prop; 
    X ≟ DeqSig C1 C2
(* ---------------------------------------- *) ⊢ 
    DeqSig C1 C2 ≡ carr X.
    
unification hint  0 ≔ C1:DeqSet,C2:C1→Prop,b1:Sig C1 C2,b2:Sig C1 C2; 
    X ≟ DeqSig C1 C2
(* ---------------------------------------- *) ⊢ 
    Sig_eq C1 C2 b1 b2 ≡ eqb X b1 b2.

definition mk_DeqSig : ∀T:DeqSet.∀P:T→Prop.∀x:T. (P x)→(DeqSig T P) ≝
λT,P,x,p. mk_Sig T P x p.


(******************************************************************************)
(*                        Coercizione per i dati Cast                         *)
(******************************************************************************)

lemma eqc_b: ∀n1,hs. (eq_c (CBool n1) (CBool hs))=(beqb n1 hs).
#n1 #hs normalize // qed.

lemma eqc_n: ∀n1,hs. (eq_c (CNat n1) (CNat hs))=(eqb n1 hs).
#n1 #hs normalize // qed.
 

theorem dimplication_cast: ∀a,b. eq_c a b=true → a = b.
* #n1   
  [* normalize #n2 [#Hp @eq_f @eqb_true_to_eq //
                   |#Hp @False_ind /2/]
  |*  [normalize #n2 #abs @False_ind /2/
                   | #b >eqc_b #hp @eq_f @(\P hp)]
  ] qed.
  
theorem eimplication_cast: ∀a,b. a = b →eq_c a b=true. 
*
  [ #n * #m #Hp  
    [ normalize @eq_to_eqb_true destruct //
    | <Hp normalize //]
  | #b * #c #Hp
    [ >Hp normalize //
    | destruct @(proj2 … (beqb_true …) ) //
  ]
qed. 


theorem biimplication_cast: ∀a,b. iff (eq_c a b=true) (a = b).
#A #B % [ @dimplication_cast | @eimplication_cast ] qed.

definition DeqCoer ≝ mk_DeqSet coerc eq_c biimplication_cast.

unification hint  0 ≔ ; 
    X ≟ DeqCoer
(* ---------------------------------------- *) ⊢ 
    coerc ≡ carr X.
    
unification hint  0 ≔ b1,b2:coerc; 
    X ≟ DeqCoer
(* ---------------------------------------- *) ⊢ 
    eq_c b1 b2 ≡ eqb X b1 b2.
    
(******************************************************************************)
(*                        Coercizione per i dati Type                         *)
(******************************************************************************)

theorem biimplication_type: ∀a,b. iff (eqb_type a b=true) (a=b).
*  *  % // 
  [ normalize #abs  @False_ind /2/
  | #Hp >Hp //
  | normalize #abs  @False_ind /2/
  | #Hp >Hp //] qed.

definition DeqType ≝ mk_DeqSet type eqb_type biimplication_type.

unification hint  0 ≔ ; 
    X ≟ DeqType
(* ---------------------------------------- *) ⊢ 
    type ≡ carr X.
    
unification hint  0 ≔ b1,b2:type; 
    X ≟ DeqType
(* ---------------------------------------- *) ⊢ 
    eqb_type b1 b2 ≡ eqb X b1 b2.

(******************************************************************************)
(*                    Coercizione per i dati naturali                         *)
(******************************************************************************)

definition eqb_nat ≝λx,y:nat. eqb x y.
theorem biimplication_nat: ∀a,b. iff (eqb_nat a b=true) (a = b).
#A #B % [ @eqb_true_to_eq | @eq_to_eqb_true ] qed.

definition DeqNat ≝ mk_DeqSet ℕ eqb_nat biimplication_nat.

unification hint  0 ≔ ; 
    X ≟ DeqNat
(* ---------------------------------------- *) ⊢ 
    nat ≡ carr X.
    
unification hint  0 ≔ b1,b2:nat; 
    X ≟ DeqNat
(* ---------------------------------------- *) ⊢ 
    eqb_nat b1 b2 ≡ eqb X b1 b2.
