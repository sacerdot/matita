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



include "assembly/byte.ma".

definition addr ≝ nat.

definition addr_of_byte : byte → addr ≝ λb. nat_of_byte b.

coercion cic:/matita/assembly/vm/addr_of_byte.con.

inductive opcode: Type ≝
   ADDd: opcode  (* 3 clock, 171 *)
 | BEQ: opcode   (* 3, 55 *)
 | BRA: opcode   (* 3, 48 *)
 | DECd: opcode  (* 5, 58 *)
 | LDAi: opcode  (* 2, 166 *)
 | LDAd: opcode  (* 3, 182 *)
 | STAd: opcode. (* 3, 183 *)

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

definition opcodemap ≝
 [ couple ? ? ADDd (mk_byte xA xB);
   couple ? ? BEQ (mk_byte x3 x7);
   couple ? ? BRA (mk_byte x3 x0);
   couple ? ? DECd (mk_byte x3 xA);
   couple ? ? LDAi (mk_byte xA x6);
   couple ? ? LDAd (mk_byte xB x6);
   couple ? ? STAd (mk_byte xB x7) ].

definition opcode_of_byte ≝
 λb.
  let rec aux l ≝
   match l with
    [ nil ⇒ ADDd
    | cons c tl ⇒
       match c with
        [ couple op n ⇒
           match eqbyte n b with
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
    [ nil ⇒ mk_byte x0 x0
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
 (cic:/matita/assembly/vm/byte_of_opcode.con a).

record status : Type ≝ {
  acc : byte;
  pc  : addr;
  spc : addr;
  zf  : bool;
  cf  : bool;
  mem : addr → byte;
  clk : nat
}.

notation "{hvbox('Acc' ≝ acc ; break 'Pc' ≝ pc ; break 'Spc' ≝ spc ; break 'Fz' ≝ fz ; break 'Fc' ≝ fc ; break  'M' ≝ m ; break 'Clk' ≝ clk)}"
non associative with precedence 80 for
 @{ 'mkstatus $acc $pc $spc $fz $fc $m $clk }.
 
interpretation "mk_status" 'mkstatus acc pc spc fz fc m clk =
 (cic:/matita/assembly/vm/status.ind#xpointer(1/1/1) acc pc spc fz fc m clk).

definition update ≝
 λf: addr → byte.λa.λv.λx.
  match eqb x a with
   [ true ⇒ v
   | false ⇒ f x ].

notation "hvbox(m break {a ↦ break v})" non associative with precedence 80 for 
 @{ 'update $m $a $v }.
 
notation "hvbox(m break {a ↦ break v} \nbsp x)" non associative with precedence 80 for 
 @{ 'update4 $m $a $v $x }.
 
interpretation "update" 'update m a v =
  (cic:/matita/assembly/vm/update.con m a v).

interpretation "update4" 'update4 m a v x =
  (cic:/matita/assembly/vm/update.con m a v x).

lemma update_update_a_a:
 ∀s,a,v1,v2,b.
  update (update s a v1) a v2 b = update s a v2 b.
 intros;
 unfold update;
 unfold update;
 elim (eqb b a);
 reflexivity.
qed. 

lemma update_update_a_b:
 ∀s,a1,v1,a2,v2,b.
  a1 ≠ a2 →
   update (update s a1 v1) a2 v2 b = update (update s a2 v2) a1 v1 b.
 intros;
 unfold update;
 unfold update;
 apply (bool_elim ? (eqb b a1)); intros;
 apply (bool_elim ? (eqb b a2)); intros;
 simplify;
 [ elim H;
   rewrite < (eqb_true_to_eq ? ? H1);
   apply eqb_true_to_eq;
   assumption
 |*: reflexivity
 ].
qed.

lemma eq_update_s_a_sa: ∀s,a,b. update s a (s a) b = s b.
 intros;
 unfold update;
 apply (bool_elim ? (eqb b a) ? ?); simplify; intros;
  [ rewrite > (eqb_true_to_eq ? ? H);
    reflexivity
  | reflexivity
  ]
qed.

lemma inj_update:
 ∀s,s',a,v,b. (a ≠ b → s b = s' b) → update s a v b = update s' a v b.
 intros;
 unfold update;
 apply (bool_elim ? (eqb b a) ? ?); simplify; intros;
  [ reflexivity
  | apply H;
    intro;
    autobatch
  ]
qed.

lemma not_eq_a_b_to_eq_update_a_b: ∀s,a,b,v. a ≠ b → update s a v b = s b.
 intros;
 unfold update;
 rewrite > not_eq_to_eqb_false; simplify;
  [ reflexivity
  | intro;
    autobatch
  ]
qed.

definition mmod16 ≝ λn. nat_of_byte (byte_of_nat n).

definition tick ≝
 λs:status. match s with [ mk_status acc pc spc zf cf mem clk ⇒
  let opc ≝ opcode_of_byte (mem pc) in
  let op1 ≝ mem (S pc) in
  let clk' ≝ cycles_of_opcode opc in
  match eqb (S clk) clk' with
   [ true ⇒
      match opc with
       [ ADDd ⇒
          let res ≝ plusbyte acc (mem op1) false in (* verify carrier! *)
          let acc' ≝ match res with [ couple acc' _ ⇒ acc' ] in
          let c' ≝ match res with [ couple _ c' ⇒ c'] in
           mk_status acc' (2 + pc) spc
            (eqbyte (mk_byte x0 x0) acc') c' mem 0 (* verify carrier! *)
       | BEQ ⇒
          mk_status
           acc
           (match zf with
             [ true ⇒ mmod16 (2 + op1 + pc) (*\mod 256*)   (* signed!!! *)
                      (* FIXME: can't work - address truncated to 8 bits *)
             | false ⇒ 2 + pc
             ])
           spc
           zf
           cf
           mem
           0
       | BRA ⇒
          mk_status
           acc (mmod16 (2 + op1 + pc) (*\mod 256*)) (* signed!!! *)
                                      (* FIXME: same as above *)
           spc
           zf
           cf
           mem
           0
       | DECd ⇒
          let x ≝ bpred (mem op1) in (* signed!!! *)
          let mem' ≝ update mem op1 x in
           mk_status acc (2 + pc) spc
            (eqbyte (mk_byte x0 x0) x) cf mem' 0 (* check zb!!! *)
       | LDAi ⇒
          mk_status op1 (2 + pc) spc (eqbyte (mk_byte x0 x0) op1) cf mem 0
       | LDAd ⇒
          let x ≝ mem op1 in
           mk_status x (2 + pc) spc (eqbyte (mk_byte x0 x0) x) cf mem 0
       | STAd ⇒
          mk_status acc (2 + pc) spc zf cf
           (update mem op1 acc) 0
       ]
   | false ⇒
       mk_status
        acc pc spc zf cf mem (S clk)
   ]].

let rec execute s n on n ≝
 match n with
  [ O ⇒ s
  | S n' ⇒ execute (tick s) n'
  ].
  
lemma breakpoint:
 ∀s,n1,n2. execute s (n1 + n2) = execute (execute s n1) n2.
 intros;
 generalize in match s; clear s;
 elim n1;
  [ reflexivity
  | simplify;
    apply H;
  ]
qed.

axiom status_eq:
 ∀s,s'.
  acc s = acc s' →
  pc s = pc s' →
  spc s = spc s' →
  zf s = zf s' →
  cf s = cf s' →
  (∀a. mem s a = mem s' a) →
  clk s = clk s' →
   s=s'.
