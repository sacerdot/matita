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

include "basics/vectors.ma".
(* include "basics/relations.ma". *)

record tape (sig:FinSet): Type[0] ≝ 
{ left : list sig;
  right: list sig
}.

inductive move : Type[0] ≝
| L : move 
| R : move
.

(* We do not distinuish an input tape *)

record TM (sig:FinSet): Type[1] ≝ 
{ states : FinSet;
  trans : states × (option sig) → states × (option (sig × move));
  start: states;
  halt : states → bool
}.

record config (sig:FinSet) (M:TM sig): Type[0] ≝ 
{ cstate : states sig M;
  ctape: tape sig
}.

definition option_hd ≝ λA.λl:list A.
  match l with
  [nil ⇒ None ?
  |cons a _ ⇒ Some ? a
  ].

definition tape_move ≝ λsig.λt: tape sig.λm:option (sig × move).
  match m with 
  [ None ⇒ t
  | Some m1 ⇒ 
    match \snd m1 with
    [ R ⇒ mk_tape sig ((\fst m1)::(left ? t)) (tail ? (right ? t))
    | L ⇒ mk_tape sig (tail ? (left ? t)) ((\fst m1)::(right ? t))
    ]
  ].

definition step ≝ λsig.λM:TM sig.λc:config sig M.
  let current_char ≝ option_hd ? (right ? (ctape ?? c)) in
  let 〈news,mv〉 ≝ trans sig M 〈cstate ?? c,current_char〉 in
  mk_config ?? news (tape_move sig (ctape ?? c) mv).
  
let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].

definition initc ≝ λsig.λM:TM sig.λt.
  mk_config sig M (start sig M) t.

definition Realize ≝ λsig.λM:TM sig.λR:relation (tape sig).
∀t.∃i.∃outc.
  loop ? i (step sig M) (λc.halt sig M (cstate ?? c)) (initc sig M t) = Some ? outc ∧
  R t (ctape ?? outc).

(* Compositions *)

definition seq_trans ≝ λsig. λM1,M2 : TM sig. 
λp. let 〈s,a〉 ≝ p in
  match s with 
  [ inl s1 ⇒ 
      if halt sig M1 s1 then 〈inr … (start sig M2), None ?〉
      else 
      let 〈news1,m〉 ≝ trans sig M1 〈s1,a〉 in
      〈inl … news1,m〉
  | inr s2 ⇒ 
      let 〈news2,m〉 ≝ trans sig M2 〈s2,a〉 in
      〈inr … news2,m〉
  ].
 
definition seq ≝ λsig. λM1,M2 : TM sig. 
  mk_TM sig 
    (FinSum (states sig M1) (states sig M2))
    (seq_trans sig M1 M2) 
    (inl … (start sig M1))
    (λs.match s with
      [ inl _ ⇒ false | inr s2 ⇒ halt sig M2 s2]). 

definition Rcomp ≝ λA.λR1,R2:relation A.λa1,a2.
  ∃am.R1 a1 am ∧ R2 am a2.

(*
definition injectRl ≝ λsig.λM1.λM2.λR.
   λc1,c2. ∃c11,c12. 
     inl … (cstate sig M1 c11) = cstate sig (seq sig M1 M2) c1 ∧ 
     inl … (cstate sig M1 c12) = cstate sig (seq sig M1 M2) c2 ∧
     ctape sig M1 c11 = ctape sig (seq sig M1 M2) c1 ∧ 
     ctape sig M1 c12 = ctape sig (seq sig M1 M2) c2 ∧ 
     R c11 c12.

definition injectRr ≝ λsig.λM1.λM2.λR.
   λc1,c2. ∃c21,c22. 
     inr … (cstate sig M2 c21) = cstate sig (seq sig M1 M2) c1 ∧ 
     inr … (cstate sig M2 c22) = cstate sig (seq sig M1 M2) c2 ∧
     ctape sig M2 c21 = ctape sig (seq sig M1 M2) c1 ∧ 
     ctape sig M2 c22 = ctape sig (seq sig M1 M2) c2 ∧ 
     R c21 c22.
     
definition Rlink ≝ λsig.λM1,M2.λc1,c2.
  ctape sig (seq sig M1 M2) c1 = ctape sig (seq sig M1 M2) c2 ∧
  cstate sig (seq sig M1 M2) c1 = inl … (halt sig M1) ∧
  cstate sig (seq sig M1 M2) c2 = inr … (start sig M2). *)
  
interpretation "relation composition" 'compose R1 R2 = (Rcomp ? R1 R2).

theorem sem_seq: ∀sig,M1,M2,R1,R2.
  Realize sig M1 R1 → Realize sig M2 R2 → 
    Realize sig (seq sig M1 M2) (R1 ∘ R2).
#sig #M1 #M2 #R1 #R2 #HR1 #HR2 #t 
cases (HR1 t) #k1 * #outc1 * #Hloop1 #HM1
cases (HR2 (ctape sig M1 outc1)) #k2 * #outc2 * #Hloop2 #HM2
@(ex_intro … (S(k1+k2))) @




definition empty_tapes ≝ λsig.λn.
mk_Vector ? n (make_list (tape sig) (mk_tape sig [] []) n) ?.
elim n // normalize //
qed.

definition init ≝ λsig.λM:TM sig.λi:(list sig).
  mk_config ??
    (start sig M)
    (vec_cons ? (mk_tape sig [] i) ? (empty_tapes sig (tapes_no sig M)))
    [ ].

definition stop ≝ λsig.λM:TM sig.λc:config sig M.
  halt sig M (state sig M c).

let rec loop (A:Type[0]) n (f:A→A) p a on n ≝
  match n with 
  [ O ⇒ None ?
  | S m ⇒ if p a then (Some ? a) else loop A m f p (f a)
  ].

(* Compute ? M f states that f is computed by M *)
definition Compute ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  out ?? c = f l.

(* for decision problems, we accept a string if on termination
output is not empty *)

definition ComputeB ≝ λsig.λM:TM sig.λf:(list sig) → bool.
∀l.∃i.∃c.
  loop ? i (step sig M) (stop sig M) (init sig M l) = Some ? c ∧
  (isnilb ? (out ?? c) = false).

(* alternative approach.
We define the notion of computation. The notion must be constructive,
since we want to define functions over it, like lenght and size 

Perche' serve Type[2] se sposto a e b a destra? *)

inductive cmove (A:Type[0]) (f:A→A) (p:A →bool) (a,b:A): Type[0] ≝
  mk_move: p a = false → b = f a → cmove A f p a b.
  
inductive cstar (A:Type[0]) (M:A→A→Type[0]) : A →A → Type[0] ≝
| empty : ∀a. cstar A M a a
| more : ∀a,b,c. M a b → cstar A M b c → cstar A M a c.

definition computation ≝ λsig.λM:TM sig.
  cstar ? (cmove ? (step sig M) (stop sig M)).

definition Compute_expl ≝ λsig.λM:TM sig.λf:(list sig) → (list sig).
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ out ?? c = f l.

definition ComputeB_expl ≝ λsig.λM:TM sig.λf:(list sig) → bool.
  ∀l.∃c.computation sig M (init sig M l) c → 
   (stop sig M c = true) ∧ (isnilb ? (out ?? c) = false).
