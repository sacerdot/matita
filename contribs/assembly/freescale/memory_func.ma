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

(* ********************************************************************** *)
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/memory_struct.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* (mf_check_update_ranged chk inf sup mode) = setta tipo memoria *)
definition mf_check_update_ranged ≝
λf:word16 → memory_type.λi.λs.λv.
 λx.match in_range x i s with
  [ true ⇒ v
  | false ⇒ f x ].

(* tutta la memoria non installata *)
definition mf_out_of_bound_memory ≝ λ_:word16.MEM_OUT_OF_BOUND.

definition mf_chk_get ≝
λc:word16 → memory_type.λa:word16.
 match c a with
  [ MEM_READ_ONLY ⇒ array_8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
  | MEM_READ_WRITE ⇒ array_8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
  | MEM_OUT_OF_BOUND ⇒ array_8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
  ].

(* (mf_mem_update mem checked addr val) = scrivi controllando il tipo di memoria *)
definition mf_mem_update ≝
λf:word16 → byte8.λc:Prod8T memory_type.λa:word16.λv:byte8.
 match getn_array8T o0 ? c with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? f
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (λx.match eq_w16 x a with [ true ⇒ v | false ⇒ f x ])
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* tutta la memoria a 0 *)
definition mf_zero_memory ≝ λ_:word16.〈x0,x0〉.

(* (mf_mem_read mem check addr) = leggi controllando il tipo di memoria *)
definition mf_mem_read ≝
λf:word16 → byte8.λc:word16 → memory_type.λa.
 match c a with
  [ MEM_READ_ONLY ⇒ Some ? (f a)
  | MEM_READ_WRITE ⇒ Some ? (f a)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, scartando source (pescando da old_mem) se si supera 0xFFFF... *)
let rec mf_load_from_source_at (old_mem:word16 → byte8) (source:list byte8) (addr:word16) on source ≝
match source with
 (* fine di source: carica da old_mem *)
 [ nil ⇒ old_mem
 | cons hd tl ⇒ λx:word16.match lt_w16 x addr with
  (* e' prima di source: carica da old_mem *)
  [ true ⇒ old_mem x
  | false ⇒ match eq_w16 x addr with
   (* la locazione corrisponde al punto corrente di source *)
   [ true ⇒ hd
   (* la locazione e' piu' avanti: ricorsione *)
   | false ⇒ (mf_load_from_source_at old_mem tl (plus_w16nc addr 〈〈x0,x0〉:〈x0,x1〉〉)) x
   ]
  ]
 ].

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

(*
lemma mem_update_mem_update_a_a:
 ∀s,a,v1,v2,b.
  mem_update (mem_update s a v1) a v2 b = mem_update s a v2 b.
 intros;
 unfold mem_update;
 unfold mem_update;
 elim (eqb b a);
 reflexivity.
qed.

lemma mem_update_mem_update_a_b:
 ∀s,a1,v1,a2,v2,b.
  a1 ≠ a2 →
   mem_update (mem_update s a1 v1) a2 v2 b = mem_update (mem_update s a2 v2) a1 v1 b.
 intros;
 unfold mem_update;
 unfold mem_update;
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
*)
