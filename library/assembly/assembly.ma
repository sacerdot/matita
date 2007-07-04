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

set "baseuri" "cic:/matita/assembly/".

include "nat/times.ma".
include "nat/compare.ma".
include "list/list.ma".

(*alias id "OO" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "SS" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".

let rec matita_nat_of_coq_nat n ≝
 match n with
  [ OO ⇒ O
  | SS y ⇒ S (matita_nat_of_coq_nat y)
  ].
coercion cic:/matita/assembly/matita_nat_of_coq_nat.con.
alias num (instance 0) = "natural number".
*)
definition byte ≝ nat.
definition addr ≝ nat.

inductive opcode: Type ≝
   ADDd: opcode  (* 3 clock, 171 *)
 | BEQ: opcode   (* 3, 55 *)
 | BRA: opcode   (* 3, 48 *)
 | DECd: opcode  (* 5, 58 *)
 | LDAi: opcode  (* 2, 166 *)
 | LDAd: opcode  (* 3, 182 *)
 | STAd: opcode. (* 3, 183 *)

alias num (instance 0) = "natural number".
let rec cycles_of_opcode op : nat ≝
 match op with
  [ ADDd ⇒ 3
  | BEQ ⇒ 3
  | BRA ⇒ 3
  | DECd ⇒ 5
  | LDAi ⇒ 2
  | LDAd ⇒ 3
  | STAd ⇒ 3
  ].

inductive cartesian_product (A,B: Type) : Type ≝
 couple: ∀a:A.∀b:B. cartesian_product A B.

definition opcodemap ≝
 [ couple ? ? ADDd 171;
   couple ? ? BEQ 55;
   couple ? ? BRA 48;
   couple ? ? DECd 58;
   couple ? ? LDAi 166;
   couple ? ? LDAd 182;
   couple ? ? STAd 183 ].

definition opcode_of_byte ≝
 λb.
  let rec aux l ≝
   match l with
    [ nil ⇒ ADDd
    | cons c tl ⇒
       match c with
        [ couple op n ⇒
           match eqb n b with
            [ true ⇒ op
            | false ⇒ aux tl
            ]]]
  in
   aux opcodemap.

definition magic_of_opcode ≝
 λop1.
  match op1 with
   [ ADDd ⇒ 0
   | BEQ ⇒  1 
   | BRA ⇒  2
   | DECd ⇒ 3
   | LDAi ⇒ 4
   | LDAd ⇒ 5
   | STAd ⇒ 6 ].
   
definition opcodeeqb ≝
 λop1,op2. eqb (magic_of_opcode op1) (magic_of_opcode op2).

definition byte_of_opcode : opcode → byte ≝
 λop.
  let rec aux l ≝
   match l with
    [ nil ⇒ 0
    | cons c tl ⇒
       match c with
        [ couple op' n ⇒
           match opcodeeqb op op' with
            [ true ⇒ n
            | false ⇒ aux tl
            ]]]
  in
   aux opcodemap.

notation "hvbox(# break a)"
  non associative with precedence 80
for @{ 'byte_of_opcode $a }.
interpretation "byte_of_opcode" 'byte_of_opcode a =
 (cic:/matita/assembly/byte_of_opcode.con a).

definition mult_source : list byte ≝
  [#LDAi; 0;
   #STAd; 32; (* 18 = locazione $12 *)
   #LDAd; 31; (* 17 = locazione $11 *)
   #BEQ;  12;
   #LDAd; 18;
   #DECd; 31;
   #ADDd; 30; (* 16 = locazione $10 *)
   #STAd; 32;
   #LDAd; 31;
   #BRA;  246; (* 242 = -14 *)
   #LDAd; 32].
   
definition mult_source' : list byte.

record status : Type ≝ {
  acc : byte;
  pc  : addr;
  spc : addr;
  zf  : bool;
  cf  : bool;
  mem : addr → byte;
  clk : nat
}.

definition mult_status : status ≝
 mk_status 0 0 0 false false (λa:addr. nth ? mult_source 0 a) 0.
 
definition update ≝
 λf: addr → byte.λa.λv.λx.
  match eqb x a with
   [ true ⇒ v
   | false ⇒ f x ].

definition tick ≝
 λs:status.
  (* fetch *)
  let opc ≝ opcode_of_byte (mem s (pc s)) in
  let op1 ≝ mem s (S (pc s)) in
  let op2 ≝ mem s (S (S (pc s))) in
  let clk' ≝ cycles_of_opcode opc in
  match eqb (S (clk s)) clk' with
   [ false ⇒
       mk_status
        (acc s) (pc s) (spc s) (zf s) (cf s) (mem s) (S (clk s))
   | true ⇒
      match opc with
       [ ADDd ⇒
          let x ≝ mem s op1 in
          let acc' ≝ x + acc s in (* signed!!! *)
           mk_status acc' (2 + pc s) (spc s)
            (eqb O acc') (cf s) (mem s) 0
       | BEQ ⇒
          mk_status
           (acc s)
           (match zf s with
             [ true ⇒ 2 + op1 + pc s   (* signed!!! *)
             | false ⇒ 2 + pc s
             ])
           (spc s)
           (zf s)
           (cf s)
           (mem s)
           0
       | BRA ⇒
          mk_status
           (acc s) (2 + op1 + pc s) (* signed!!! *)
           (spc s)
           (zf s)
           (cf s)
           (mem s)
           0
       | DECd ⇒
          let x ≝ pred (mem s op1) in (* signed!!! *)
          let mem' ≝ update (mem s) op1 x in
           mk_status (acc s) (2 + pc s) (spc s)
            (eqb O x) (cf s) mem' 0 (* check zb!!! *)
       | LDAi ⇒
          mk_status op1 (2 + pc s) (spc s) (eqb O op1) (cf s) (mem s) 0
       | LDAd ⇒
          let x ≝ pred (mem s op1) in
           mk_status x (2 + pc s) (spc s) (eqb O x) (cf s) (mem s) 0
       | STAd ⇒
          mk_status (acc s) (2 + pc s) (spc s) (zf s) (cf s)
           (update (mem s) op1 (acc s)) 0
       ]
   ].

let rec execute s n on n ≝
 match n with
  [ O ⇒ s
  | S n' ⇒ execute (tick s) n'
  ].
  
lemma foo: ∀s,n. execute s (S n) = execute (tick s) n.
 intros; reflexivity.
qed.
(*
lemma goo: pc (execute mult_status 4) = O.
 reduce;
 CSC.


 simplify;
 whd in ⊢ (? ? (? (? (? %))) ?);
 do 2 (simplify in match (matita_nat_of_coq_nat ?));
 simplify in match (matita_nat_of_coq_nat ?);
 whd in ⊢ (? ? (? (? (? (? ? ? ? ? ? ? %)))) ?);
 whd in ⊢ (? ? (? (? (? %))) ?);












 change with (tick (tick (tick mult_status)) = mult_status);
 change with (tick (tick mult_status) = mult_status);
 change with (tick mult_status = mult_status);
 change with (mult_status = mult_status);
 reflexivity.
qed.

(*
 unfold mult_status; 
 simplify;
 whd in ⊢ (? ?
(?
 (?
  (?
   match match ? % in nat return ? with [O\rArr ?|S\rArr ?] in bool return ?
    with 
   [true\rArr ?|false\rArr ?]))) ?);
 simplify;
 whd in ⊢ (? ?
(?
 (?
  (?
   match % in opcode return ? with 
   [ADDd\rArr ?
   |BEQ\rArr ?
   |BRA\rArr ?
   |DECd\rArr ?
   |LDAi\rArr ?
   |LDAd\rArr ?
   |STAd\rArr ?]))) ?);
 simplify;
 whd in \vdash (? ?
(?
 (?
  match match % in nat return ? with [O\rArr ?|S\rArr ?] in bool return ? with 
  [true\rArr ?|false\rArr ?])) ?);
 simplify;
 whd in \vdash (? ?
(?
 (?
  match % in opcode return ? with 
  [ADDd\rArr ?
  |BEQ\rArr ?
  |BRA\rArr ?
  |DECd\rArr ?
  |LDAi\rArr ?
  |LDAd\rArr ?
  |STAd\rArr ?])) ?);
 simplify;
 whd in \vdash (? ? (? match % in bool return ? with [true\rArr ?|false\rArr ?]) ?);
 simplify;
 whd in \vdash (? ?
(?
 match % in opcode return ? with 
 [ADDd\rArr ?
 |BEQ\rArr ?
 |BRA\rArr ?
 |DECd\rArr ?
 |LDAi\rArr ?
 |LDAd\rArr ?
 |STAd\rArr ?]) ?);
 simplify;
 whd in \vdash (? ? match % in bool return ? with [true\rArr ?|false\rArr ?] ?);
 simplify;
 whd in \vdash (? ?
match % in opcode return ? with 
[ADDd\rArr ?
|BEQ\rArr ?
|BRA\rArr ?
|DECd\rArr ?
|LDAi\rArr ?
|LDAd\rArr ?
|STAd\rArr ?] ?);
 simplify;
 reflexivity.
*)
*)