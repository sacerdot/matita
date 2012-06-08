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


(* ALphabet of the universal machine *)

include "basics/finset.ma".

(*
include "turing/if_machine.ma".
include "turing/universal/tests.ma". *)

inductive unialpha : Type[0] ≝ 
| bit : bool → unialpha
| null : unialpha
| comma : unialpha
| bar : unialpha
| grid : unialpha.

definition unialpha_eq ≝ 
  λa1,a2.match a1 with
  [ bit x ⇒ match a2 with [ bit y ⇒ ¬ xorb x y | _ ⇒ false ]
  | null ⇒ match a2 with [ null ⇒ true | _ ⇒ false ]
  | comma ⇒ match a2 with [ comma ⇒ true | _ ⇒ false ]
  | bar ⇒ match a2 with [ bar ⇒ true | _ ⇒ false ]
  | grid ⇒ match a2 with [ grid ⇒ true | _ ⇒ false ] ].
  
definition DeqUnialpha ≝ mk_DeqSet unialpha unialpha_eq ?.
* [ #x * [ #y cases x cases y normalize % // #Hfalse destruct
         | *: normalize % #Hfalse destruct ]
  |*: * [1,6,11,16: #y ] normalize % #H1 destruct % ]
qed.

lemma unialpha_unique : 
  uniqueb DeqUnialpha [bit true;bit false;null;comma;bar;grid] = true.
// qed.

lemma unialpha_complete :∀x:DeqUnialpha. 
  memb ? x [bit true;bit false;null;comma;bar;grid] = true.
* // * //
qed.

definition FSUnialpha ≝ 
  mk_FinSet DeqUnialpha [bit true;bit false;null;comma;bar;grid] 
  unialpha_unique unialpha_complete.

(*************************** testing characters *******************************)
definition is_bit ≝ λc.match c with [ bit _ ⇒ true | _ ⇒ false ].

definition is_null ≝ λc.match c with [ null ⇒ true | _ ⇒ false ].

definition is_grid ≝ λc.match c with [ grid ⇒ true | _ ⇒ false ].

definition is_bar ≝ λc.match c with [ bar ⇒ true | _ ⇒ false ].

definition is_comma ≝ λc.match c with [ comma ⇒ true | _ ⇒ false ].

definition bit_or_null ≝ λc.is_bit c ∨ is_null c.

lemma bit_not_grid: ∀d. is_bit d = true → is_grid d = false.
* // normalize #H destruct
qed.

lemma bit_or_null_not_grid: ∀d. bit_or_null d = true → is_grid d = false.
* // normalize #H destruct
qed.

lemma bit_not_bar: ∀d. is_bit d = true → is_bar d = false.
* // normalize #H destruct
qed.

lemma bit_or_null_not_bar: ∀d. bit_or_null d = true → is_bar d = false.
* // normalize #H destruct
qed.
(**************************** testing strings *********************************)
definition is_marked ≝ λalpha.λp:FinProd … alpha FinBool.
  let 〈x,b〉 ≝ p in b.

definition STape ≝ FinProd … FSUnialpha FinBool.

definition only_bits ≝ λl.
  ∀c.memb STape c l = true → is_bit (\fst c) = true.

definition only_bits_or_nulls ≝ λl.
  ∀c.memb STape c l = true → bit_or_null (\fst c) = true.
  
definition no_grids ≝ λl.
  ∀c.memb STape c l = true → is_grid (\fst c) = false.

definition no_bars ≝ λl.
  ∀c.memb STape c l = true → is_bar (\fst c) = false.

definition no_marks ≝ λl.
  ∀c.memb STape c l = true → is_marked ? c = false.

definition bar_or_grid ≝ λc:STape.is_bar (\fst c) ∨ is_grid (\fst c).

