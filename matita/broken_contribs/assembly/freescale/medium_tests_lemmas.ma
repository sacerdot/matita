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

include "freescale/medium_tests_tools.ma".

(* ***************** *)
(* assiomi e teoremi *)
(* ***************** *)

axiom get_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.
  get_clk_desc m t (set_clk_desc m t s clk) = clk.

axiom set_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk1,clk2.
  set_clk_desc m t (set_clk_desc m t s clk1) clk2 =
  set_clk_desc m t s clk2. 

axiom memory_filter_read_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀addr.∀clk.
  memory_filter_read m t (set_clk_desc m t s clk) addr =
  memory_filter_read m t s addr.

axiom filtered_inc_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀w.
  filtered_inc_w16 m t (set_clk_desc m t s clk) w =
  filtered_inc_w16 m t s w.

axiom filtered_plus_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀w.∀n.
  filtered_plus_w16 m t (set_clk_desc m t s clk) w n =
  filtered_plus_w16 m t s w n.

axiom filtered_plus_set_mem_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀mem.∀w.∀n.
  filtered_plus_w16 m t (set_mem_desc m t s mem) w n =
  filtered_plus_w16 m t s w n.

axiom filtered_plus_and_inc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀w.∀n.
  filtered_plus_w16 m t s (filtered_inc_w16 m t s w) n =
  filtered_plus_w16 m t s w (S n).

axiom get_alu_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.
  alu m t (set_clk_desc m t s clk) =
  alu m t s.

axiom get_chk_desc_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.
  get_chk_desc m t (set_clk_desc m t s clk) =
  get_chk_desc m t s.

axiom get_chk_desc_set_mem_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀mem.
  get_chk_desc m t (set_mem_desc m t s mem) =
  get_chk_desc m t s.

axiom get_mem_desc_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.
  get_mem_desc m t (set_clk_desc m t s clk) =
  get_mem_desc m t s.

axiom set_clk_desc_set_mem_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀mem.
  set_mem_desc m t (set_clk_desc m t s clk) mem =
  set_clk_desc m t (set_mem_desc m t s mem) clk.

axiom set_clk_desc_set_alu :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀alu.
  set_alu m t (set_clk_desc m t s clk) alu =
  set_clk_desc m t (set_alu m t s alu) clk.

axiom set_clk_desc_set_z_flag :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀z.
  set_z_flag m t (set_clk_desc m t s clk) z =
  set_clk_desc m t (set_z_flag m t s z) clk.

axiom set_clk_desc_setweak_n_flag :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀n.
  setweak_n_flag m t (set_clk_desc m t s clk) n =
  set_clk_desc m t (setweak_n_flag m t s n) clk.

axiom set_clk_desc_setweak_v_flag :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀v.
  setweak_v_flag m t (set_clk_desc m t s clk) v =
  set_clk_desc m t (setweak_v_flag m t s v) clk.

axiom set_clk_desc_set_pc_reg :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀clk.∀pc.
  set_pc_reg m t (set_clk_desc m t s clk) pc =
  set_clk_desc m t (set_pc_reg m t s pc) clk.

axiom set_clk_f_set_clk_desc :
 ∀m:mcu_type.∀t:memory_impl.∀s:any_status m t.∀f.
  (get_clk_desc m t s = None ?) →
  (set_clk_desc m t (f s) (None ?) = (f s)).

axiom w16h_of_make_word16 :
 ∀bh,bl:byte8.
  w16h (mk_word16 bh bl) = bh.

axiom MSB16_of_make_word16 :
 ∀bh,bl:byte8.
  MSB_w16 (mk_word16 bh bl) = MSB_b8 bh.

lemma execute_HCS08_LDHX_maIMM2 :
 ∀t:memory_impl.∀s:any_status HCS08 t.∀bhigh,blow:byte8.
  (get_clk_desc HCS08 t s = None ?) →
  (memory_filter_read HCS08 t s (get_pc_reg HCS08 t s) = Some ? 〈x4,x5〉) →
  (memory_filter_read HCS08 t s (filtered_inc_w16 HCS08 t s
                                 (get_pc_reg HCS08 t s)) = Some ? bhigh) →
  (memory_filter_read HCS08 t s (filtered_inc_w16 HCS08 t s
                                 (filtered_inc_w16 HCS08 t s
                                  (get_pc_reg HCS08 t s))) = Some ? blow)
  → (execute HCS08 t (TickOK ? s) 3 =
    TickOK ? (set_pc_reg HCS08 t
              (setweak_v_flag HCS08 t
               (setweak_n_flag HCS08 t 
                (set_z_flag HCS08 t
                 (set_alu HCS08 t s
                  (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉))
                (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉))
               (MSB_w16 〈bhigh:blow〉))
              false)
             (filtered_plus_w16 HCS08 t s (get_pc_reg HCS08 t s) 3))).
elim daemon.
(* intros;
 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H;

 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match % in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H1;

 whd in ⊢ (? ? match match % in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 change in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (match (quadrupleT (any_opcode HCS08) ??? LDHX MODE_IMM2 〈x4,x5〉 〈x0,x3〉) with 
   [quadrupleT pseudo mode _ tot_clk ⇒ match eq_b8 〈x0,x1〉 tot_clk with 
    [ true ⇒ tick_execute HCS08 t s pseudo mode (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s))
    | false ⇒ TickOK (any_status HCS08 t) (set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x1〉 pseudo mode tot_clk (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))]]);
 change in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (match eq_b8 〈x0,x1〉 〈x0,x3〉 with 
   [ true ⇒ tick_execute HCS08 t s (anyOP HCS08 LDHX) MODE_IMM2 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s))
   | false ⇒ TickOK (any_status HCS08 t) (set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x1〉     (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))]);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 letin status1 ≝ (set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))));
 change in ⊢ (? ? % ?) with
  (match 2 with 
   [ O ⇒ TickOK ? status1
   | S (n':nat) ⇒ execute HCS08 t (tick HCS08 t status1) n']);
 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? % ?] ?);
 unfold status1 in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_. ? ? ? match ? ? ? % in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > (get_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))));
 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? % ?] ?);
 normalize in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? (? ? (? ? ? ? (? ? (? ? ? ? ? ? % ? ? ? ?)))) ?] ?);
 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.%] ?);

 unfold status1 in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? (? ? (? ? ? % ?)) ?] ?);
 rewrite > (set_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))
  in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? (? ? %) ?] ?);
 letin status2 ≝ (set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))));

 change in ⊢ (? ? % ?) with
  (match 1 with 
   [ O ⇒ TickOK ? status2
   | S (n':nat) ⇒ execute HCS08 t (tick HCS08 t status2) n']);
 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? % ?] ?);
 unfold status2 in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_.  ? ? ? match ? ? ? % in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > (get_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))));
 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? % ?] ?);
 change in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_.? ? ? match % in option return ? with [_⇒?|_⇒?] ?] ?) with
  (execute_LDHX HCS08 t status2 MODE_IMM2
 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)));
 whd in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_.? ? ? match % in option return ? with [_⇒?|_⇒?] ?] ?);
 whd in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_.? ? ? match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);

 unfold status2 in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match ? ? ? % ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > (memory_filter_read_set_clk_desc HCS08 t s (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))
  in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > H2 in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 whd in ⊢ (? ? match ? in nat return ? with [_⇒? |_⇒λ_. ? ? ? match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);

 unfold status2 in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > (filtered_inc_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))
  in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match ? ? ? ? % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > (memory_filter_read_set_clk_desc HCS08 t s (filtered_inc_w16 HCS08 t s (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s))) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))
  in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);
 rewrite > H3 in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_. ? ? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ?] ?);

 whd in ⊢ (? ? match ? in nat return ? with [_⇒?|_⇒λ_.? ? ? % ?] ?);
 change in ⊢ (? ? % ?) with
  (TickOK ?
  (set_clk_desc HCS08 t
   (set_pc_reg HCS08 t
    (setweak_v_flag HCS08 t
     (setweak_n_flag HCS08 t
      (set_z_flag HCS08 t
       (set_alu HCS08 t status2
        (set_indX_16_reg_HC08 (alu HCS08 t status2) 〈bhigh:blow〉))
       (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉))
      (MSB_w16 〈bhigh:blow〉)) false)
    (filtered_plus_w16 HCS08 t status2
     (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)) 2))
   (None ?)));

 unfold status2 in ⊢ (? ? (? ? (? ? ? (? ? ? ? (? ? ? % ? ?)) ?)) ?);
 rewrite > (filtered_plus_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)) 2);
 rewrite > (filtered_plus_and_inc HCS08 t s (get_pc_reg HCS08 t s) 2);
 unfold status2 in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? (? ? ? %) ?)) ?) ?) ?) ?) ?)) ?);
 rewrite > (get_alu_set_clk_desc HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? % ?)) ?) ?) ?) ?) ?)) ?);
 unfold status2 in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? % ?) ?) ?) ?) ?) ?)) ?);
 rewrite > (set_clk_desc_set_alu HCS08 t s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? % ?) ?) ?) ?) ?)) ?);
 rewrite > (set_clk_desc_set_z_flag HCS08 t (set_alu HCS08 t s (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉)) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉));
 rewrite > (set_clk_desc_setweak_n_flag HCS08 t (set_z_flag HCS08 t (set_alu HCS08 t s (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉)) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉)) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (MSB_w16 〈bhigh:blow〉));
 rewrite > (set_clk_desc_setweak_v_flag HCS08 t (setweak_n_flag HCS08 t (set_z_flag HCS08 t (set_alu HCS08 t s (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉)) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_w16 〈bhigh:blow〉)) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) false);
 rewrite > (set_clk_desc_set_pc_reg HCS08 t (setweak_v_flag HCS08 t (setweak_n_flag HCS08 t (set_z_flag HCS08 t (set_alu HCS08 t s (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉)) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_w16 〈bhigh:blow〉)) false) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (filtered_plus_w16 HCS08 t s (get_pc_reg HCS08 t s) 3));
 rewrite > (set_set_clk_desc HCS08 t (set_pc_reg HCS08 t (setweak_v_flag HCS08 t (setweak_n_flag HCS08 t (set_z_flag HCS08 t (set_alu HCS08 t s (set_indX_16_reg_HC08 (alu HCS08 t s) 〈bhigh:blow〉)) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_w16 〈bhigh:blow〉)) false) (filtered_plus_w16 HCS08 t s (get_pc_reg HCS08 t s) 3)) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 LDHX) MODE_IMM2 〈x0,x3〉 (filtered_inc_w16 HCS08 t s (get_pc_reg HCS08 t s)))) (None ?));
 rewrite > (set_clk_f_set_clk_desc HCS08 t s (λtmps.set_pc_reg HCS08 t (setweak_v_flag HCS08 t (setweak_n_flag HCS08 t (set_z_flag HCS08 t (set_alu HCS08 t tmps (set_indX_16_reg_HC08 (alu HCS08 t tmps) 〈bhigh:blow〉)) (eq_w16 〈bhigh:blow〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_w16 〈bhigh:blow〉)) false) (filtered_plus_w16 HCS08 t tmps (get_pc_reg HCS08 t tmps) 3))) in ⊢ (? ? (? ? %) ?);
 [2: elim H; reflexivity ]
 reflexivity.*)
qed.

definition execute_HCS08_STHX_maSP1_aux ≝
 λs:any_status HCS08 MEM_TREE.λblow:byte8.
  TickOK ? (set_pc_reg HCS08 MEM_TREE
            (setweak_v_flag HCS08 MEM_TREE
             (setweak_n_flag HCS08 MEM_TREE
              (set_z_flag HCS08 MEM_TREE
               (set_mem_desc HCS08 MEM_TREE s
                (mt_update byte8
                 (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s)
                  (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)
                  (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))
                 (succ_w16
                  (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉))
                 (indX_low_reg_HC08 (alu HCS08 MEM_TREE s))))
               (eq_w16 〈(indX_high_reg_HC08 (alu HCS08 MEM_TREE s)):(indX_low_reg_HC08 (alu HCS08 MEM_TREE s))〉 〈〈x0,x0〉:〈x0,x0〉〉))
              (MSB_b8 (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))))
             false)
            (filtered_plus_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s) 3)).

lemma execute_HCS08_STHX_maSP1 :
 ∀s:any_status HCS08 MEM_TREE.∀blow:byte8.
  (get_clk_desc HCS08 MEM_TREE s = None ?) →
  (memory_filter_read HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s) = Some ? 〈x9,xE〉) →
  (memory_filter_read HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s
                                 (get_pc_reg HCS08 MEM_TREE s)) = Some ? 〈xF,xF〉) →
  (memory_filter_read HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s
                                 (filtered_inc_w16 HCS08 MEM_TREE s
                                  (get_pc_reg HCS08 MEM_TREE s))) = Some ? blow) →
  (chk_get MEM_TREE (get_chk_desc HCS08 MEM_TREE s)
             (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) =
   array_8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE) →
  (chk_get MEM_TREE (get_chk_desc HCS08 MEM_TREE s)
             (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) =
   array_8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE) → 
   (execute HCS08 MEM_TREE (TickOK ? s) 5 = execute_HCS08_STHX_maSP1_aux s blow).
elim daemon.
(* intros;
 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H;

 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match % in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H1;

 whd in ⊢ (? ? match match % in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H2 in ⊢ (? ? match match match % in option return ? with [_⇒?|_⇒?] in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match % in fetch_result return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 change in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (match quadrupleT ???? (anyOP HCS08 STHX) MODE_SP1 〈〈x9,xE〉:〈xF,xF〉〉 〈x0,x5〉 with [ quadrupleT pseudo mode _ tot_clk ⇒ match eq_b8 〈x0,x1〉 tot_clk with [true⇒tick_execute HCS08 MEM_TREE s pseudo mode (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) |false⇒ TickOK (any_status HCS08 MEM_TREE) (set_clk_desc HCS08 MEM_TREE s (Some (Prod5T byte8 (any_opcode HCS08) instr_mode byte8 word16) (quintupleT byte8 (any_opcode HCS08) instr_mode byte8 word16 〈x0,x1〉 pseudo mode tot_clk (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))]]);
 change in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (match eq_b8 〈x0,x1〉 〈x0,x5〉 with [true⇒ tick_execute HCS08 MEM_TREE s (anyOP HCS08 STHX) MODE_SP1 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) |false⇒ TickOK (any_status HCS08 MEM_TREE) (set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))]);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 letin status1 ≝ (set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE  s (get_pc_reg HCS08 MEM_TREE s))))));
 change in ⊢ (? ? match ? ? % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with (status1);
 change in ⊢ (? ? % ?) with (execute HCS08 MEM_TREE (TickOK ? status1) 4);

 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status1 in ⊢ (? ? match match ? ? ? % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) ) in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status1 in ⊢ (? ? match ? ? (? ? ? % ?) in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (set_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x1〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match ? ? % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 letin status2 ≝ (set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))));
 change in ⊢ (? ? % ?) with (execute HCS08 MEM_TREE (TickOK ? status2) 3);

 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status2 in ⊢ (? ? match match ? ? ? % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status2 in ⊢ (? ? match ? ? (? ? ? % ?) in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (set_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x2〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) (Some ? (quintupleT ????? 〈x0,x3〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match ? ? % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 letin status3 ≝ (set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x3〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))));
 change in ⊢ (? ? % ?) with (execute HCS08 MEM_TREE (TickOK ? status3) 2);

 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status3 in ⊢ (? ? match match ? ? ? % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x3〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status3 in ⊢ (? ? match ? ? (? ? ? % ?) in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (set_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x3〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match ? ? % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 letin status4 ≝ (set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))));
 change in ⊢ (? ? % ?) with (execute HCS08 MEM_TREE (TickOK ? status4) 1);

 whd in ⊢ (? ? % ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status4 in ⊢ (? ? match match ? ? ? % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match % in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 change in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with (execute_STHX HCS08 MEM_TREE status4 MODE_SP1 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))));
 whd in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 unfold status4 in ⊢ (? ? match match match match ? ? ? % ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (memory_filter_read_set_clk_desc HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H3 in ⊢ (? ? match match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 whd in ⊢ (? ? match match match match ? in option return ? with [_⇒?|_⇒λ_.(λoffs:?.%) ?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match match match ? in option return ? with [_⇒?|_⇒λ_.(λoffs:?.match % in option return ? with [_⇒?|_⇒?]) ?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match match match ? in option return ? with [_⇒?|_⇒λ_.(λoffs:?.match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?]) ?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? in option return ? with [_⇒? |_⇒λ_. (λoffs:?.match match match ? ? ? (? ? ? (? (? %) ?)) in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?]) ?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_chk_desc_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? in option return ? with [_⇒?|_⇒λ_.(λoffs:? .match match match ? ? ? (? ? % ?) in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?]) ?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 change in ⊢ (? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (match match match getn_array8T o0 memory_type (chk_get MEM_TREE (get_chk_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) in memory_type return λm.(option (Prod16T (Prod16T (Prod16T (Prod16T byte8))))) with [MEM_READ_ONLY⇒ Some (Prod16T (Prod16T (Prod16T (Prod16T byte8)))) (get_mem_desc HCS08 MEM_TREE status4) |MEM_READ_WRITE⇒ Some (Prod16T (Prod16T (Prod16T (Prod16T byte8)))) (mt_update byte8 (get_mem_desc HCS08 MEM_TREE status4) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE status4)) 〈〈x0,x0〉:blow〉) (w16h 〈(indX_high_reg_HC08 (alu HCS08 MEM_TREE status4)):(indX_low_reg_HC08 (alu HCS08 MEM_TREE status4))〉)) |MEM_OUT_OF_BOUND⇒None (Prod16T (Prod16T (Prod16T (Prod16T byte8))))] in option return λo.(option (any_status HCS08 MEM_TREE)) with [None⇒None (any_status HCS08 MEM_TREE) |Some x⇒ (λmem.Some (any_status HCS08 MEM_TREE) (set_mem_desc HCS08 MEM_TREE status4 mem)) x] in option return λo.(option (Prod (any_status HCS08 MEM_TREE) word16)) with [None⇒None (Prod (any_status HCS08 MEM_TREE) word16) |Some x⇒ (λtmps1.opt_map (any_status HCS08 MEM_TREE) (Prod (any_status HCS08 MEM_TREE) word16) (memory_filter_write HCS08 MEM_TREE tmps1 (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE status4)) 〈〈x0,x0〉:blow〉)) (w16l 〈(indX_high_reg_HC08 (alu HCS08 MEM_TREE status4)):(indX_low_reg_HC08 (alu HCS08 MEM_TREE status4))〉)) (λtmps2.Some (Prod (any_status HCS08 MEM_TREE) word16) (pair (any_status HCS08 MEM_TREE) word16 tmps2 (filtered_plus_w16 HCS08 MEM_TREE tmps2 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) 1)))) x]);
 rewrite > H4 in ⊢ (? ? match match match match match match ? ? ? % in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?); 

 whd in ⊢ (? ? match match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_mem_desc_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? ? (? ? ? ? (? ? % ? ?)) in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? ? (? ? ? ? (? ? ? ? (? (? (? %) ?)))) in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? ? (? ? ? ? (? ? ? (? (? %) ?) ?)) in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match match ? ? (? ? ? ? (? ? ? ? (? (? ? (? %))))) in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 rewrite > (set_clk_desc_set_mem_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (w16h 〈(indX_high_reg_HC08 (alu HCS08 MEM_TREE s)):(indX_low_reg_HC08 (alu HCS08 MEM_TREE s))〉)) )
  in ⊢ (? ? match match match match ? ? % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (w16h_of_make_word16 (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s)))
  in ⊢ (? ? match match match match ? ? (? ? ? (? ? ? ? (? ? ? ? %)) ?) in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?); 
 letin status5 ≝ (set_clk_desc HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) (Some (Prod5T byte8 (any_opcode HCS08) instr_mode byte8 word16) (quintupleT byte8 (any_opcode HCS08) instr_mode byte8 word16 〈x0,x4〉 STHX MODE_SP1 〈x0,x5〉  (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))));
 change in ⊢ (? ? match match match match ? ? % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with (status5);
 change in ⊢ (? ? match match match % in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?) with
  (opt_map ?? (memory_filter_write HCS08 MEM_TREE status5 (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE status4)) 〈〈x0,x0〉:blow〉)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE status4))) (λtmps2:any_status HCS08 MEM_TREE .Some ? (pair ?? tmps2 (filtered_plus_w16 HCS08 MEM_TREE tmps2 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) 1))));
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match ? ? ? (? ? ? ? ? (? %)) ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match ? ? ? (? ? ? ? (? (? (? %) ?)) ?) ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 whd in ⊢ (? ? match match match ? ? ? % ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? match match match ? ? ? match % in option return ? with [_⇒?|_⇒?] ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_chk_desc_set_clk_desc HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? match match match ? ? ? match match ? ? ? (? ? % ?) in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > (get_chk_desc_set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))))
  in ⊢ (? ? match match match ? ? ? match match ? ? ? (? ? % ?) in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 rewrite > H5 in ⊢ (? ? match match match ? ? ? match match ? ? ? % in memory_type return ? with [_⇒?|_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] ? in option return ? with [_⇒?|_⇒?] in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);

 whd in ⊢ (? ? match match % in option return ? with [_⇒?|_⇒?] in tick_result return ? with [_⇒?|_⇒?|_⇒?] ?);
 whd in ⊢ (? ? % ?);
 rewrite > (filtered_plus_set_mem_desc HCS08 MEM_TREE status5 (mt_update byte8 (get_mem_desc HCS08 MEM_TREE status5) (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s))) (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) 1)
  in ⊢ (? ? (? ? (? ? ? (? ? ? ? %) ?)) ?);
 rewrite > (filtered_plus_set_clk_desc HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) (Some (Prod5T byte8 (any_opcode HCS08) instr_mode byte8 word16) (quintupleT byte8 (any_opcode HCS08) instr_mode byte8 word16 〈x0,x4〉 STHX MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))) (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) 1)
  in ⊢ (? ? (? ? (? ? ? (? ? ? ? %) ?)) ?); 
 rewrite > (filtered_plus_set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))) (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))) 1)
  in ⊢ (? ? (? ? (? ? ? (? ? ? ? %) ?)) ?);
 rewrite > (filtered_plus_and_inc HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)) 1)
   in ⊢ (? ? (? ? (? ? ? (? ? ? ? %) ?)) ?);
 rewrite > (filtered_plus_and_inc HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s) 2)
  in ⊢ (? ? (? ? (? ? ? (? ? ? ? %) ?)) ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? (? (? %) ?))) ?) ?) ?)) ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? (? ? (? %)))) ?) ?) ?)) ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? (? ? (? %)) ?)) ?) ?) ?) ?)) ?);
 rewrite > (get_alu_set_clk_desc HCS08 MEM_TREE s (Some ? (quintupleT ????? 〈x0,x4〉 (anyOP HCS08 STHX) MODE_SP1 〈x0,x5〉 (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s))))))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? (? (? %) ?) ?)) ?) ?) ?) ?)) ?);
 rewrite > (MSB16_of_make_word16 (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s)))
  in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? ? %) ?) ?) ?)) ?);  clearbody status;
 clearbody status;
 clearbody status1;
 clearbody status2;
 clearbody status3;
 clearbody status4;

 cut (get_mem_desc HCS08 MEM_TREE (set_clk_desc HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) (mk_word16 (mk_byte8 x0 x0) blow)) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) (Some (Prod5T byte8 (any_opcode HCS08) instr_mode byte8 word16) (quintupleT byte8 (any_opcode HCS08) instr_mode byte8 word16 (mk_byte8 x0 x4) STHX MODE_SP1 (mk_byte8 x0 x5) (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) = mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) (mk_word16 (mk_byte8 x0 x0) blow)) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)));

 (* basta... *)
 [2: elim daemon ]
 rewrite > Hcut in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? ? (? ? % ? ?)) ?) ?) ?) ?) ?)) ?);

 cut (set_mem_desc HCS08 MEM_TREE (set_clk_desc HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) (Some (Prod5T byte8 (any_opcode HCS08) instr_mode byte8 word16) (quintupleT byte8 (any_opcode HCS08) instr_mode byte8 word16 〈x0,x4〉 STHX MODE_SP1 〈x0,x5〉  (filtered_inc_w16 HCS08 MEM_TREE s (filtered_inc_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s)))))) (mt_update byte8 (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))) (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s))) = set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))) (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s))));
 [2: elim daemon ]
 rewrite > Hcut1 in ⊢ (? ? (? ? (? ? ? (? ? ? (? ? ? (? ? ? (? ? ? % ?) ?) ?) ?) ?)) ?);

 rewrite > (set_clk_f_set_clk_desc HCS08 MEM_TREE s (λs.set_pc_reg HCS08 MEM_TREE (setweak_v_flag HCS08 MEM_TREE (setweak_n_flag HCS08 MEM_TREE (set_z_flag HCS08 MEM_TREE (set_mem_desc HCS08 MEM_TREE s (mt_update byte8 (mt_update byte8 (get_mem_desc HCS08 MEM_TREE s) (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉) (indX_high_reg_HC08 (alu HCS08 MEM_TREE s))) (succ_w16 (plus_w16nc (sp_reg_HC08 (alu HCS08 MEM_TREE s)) 〈〈x0,x0〉:blow〉)) (indX_low_reg_HC08 (alu HCS08 MEM_TREE s)))) (eq_w16 〈(indX_high_reg_HC08 (alu HCS08 MEM_TREE s)):(indX_low_reg_HC08 (alu HCS08 MEM_TREE s))〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_b8 (indX_high_reg_HC08 (alu HCS08 MEM_TREE s)))) false) (filtered_plus_w16 HCS08 MEM_TREE s (get_pc_reg HCS08 MEM_TREE s) 3)))
  in ⊢ (? ? (? ? %) ?);
 [2: elim H; reflexivity ]
 reflexivity.*)
qed.
