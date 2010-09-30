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
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "emulator/status/status_setter.ma".
include "emulator/read_write/read_write_base.ma".

ndefinition IP2022_ADDRSEL_loc ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x2〉〉〉.
ndefinition IP2022_ADDRX_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x3〉〉〉.
ndefinition IP2022_IPH_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x4〉〉〉.
ndefinition IP2022_IPL_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x5〉〉〉.
ndefinition IP2022_SPH_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x6〉〉〉.
ndefinition IP2022_SPL_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x7〉〉〉.
ndefinition IP2022_PCH_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x8〉〉〉.
ndefinition IP2022_PCL_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,x9〉〉〉.
ndefinition IP2022_W_loc       ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xA〉〉〉.
ndefinition IP2022_STATUS_loc  ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xB〉〉〉.
ndefinition IP2022_DPH_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xC〉〉〉.
ndefinition IP2022_DPL_loc     ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xD〉〉〉.
ndefinition IP2022_SPEED_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xE〉〉〉.
ndefinition IP2022_MULH_loc    ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,xF〉〉〉.
ndefinition IP2022_ADDRH_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x0〉〉〉.
ndefinition IP2022_ADDRL_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x1〉〉〉.
ndefinition IP2022_DATAH_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x2〉〉〉.
ndefinition IP2022_DATAL_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x3〉〉〉.
ndefinition IP2022_CALLH_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x4〉〉〉.
ndefinition IP2022_CALLL_loc   ≝ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x1,x5〉〉〉.

(* **** *)
(* READ *)
(* **** *)

(* NB: non ci sono strane indirezioni,
       solo registri memory mapped da intercettare *)
ndefinition IP2022_memory_filter_read_aux ≝
λt:memory_impl.λs:any_status IP2022 t.λaddr:word32.
λT:Type.λfREG:byte8 → option T.λfMEM:aux_mem_type t → aux_chk_type t → word32 → option T.
(* intercettare le locazioni memory mapped *)
 match eq_w32 addr IP2022_ADDRSEL_loc with
  [ true ⇒ fREG (addrsel_reg_IP2022 (alu … s))
  | false ⇒
 match eq_w32 addr IP2022_ADDRX_loc with
  [ true ⇒ fREG (w24x (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                     (addr_array_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_IPH_loc with
  [ true ⇒ fREG (cnH ? (ip_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_IPL_loc with
  [ true ⇒ fREG (cnL ? (ip_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_SPH_loc with
  [ true ⇒ fREG (cnH ? (sp_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_SPL_loc with
  [ true ⇒ fREG (cnL ? (sp_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_PCH_loc with
  [ true ⇒ fREG (cnH ? (pc_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_PCL_loc with
  [ true ⇒ fREG (cnL ? (pc_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_W_loc with
  [ true ⇒ fREG (acc_low_reg_IP2022 (alu … s))
  | false ⇒
 (* PAGE[7:5] Z[2] H[1] C [0] *)
 match eq_w32 addr IP2022_STATUS_loc with
  [ true ⇒ fREG 〈(rol_ex (ex_of_oct (page_reg_IP2022 (alu … s)))),
                 (or_ex (or_ex (match z_flag_IP2022 (alu … s) with
                                 [ true ⇒ x4 | false ⇒ x0 ])
                               (match h_flag_IP2022 (alu … s) with
                                 [ true ⇒ x2 | false ⇒ x0 ]))
                        (match c_flag_IP2022 (alu … s) with
                          [ true ⇒ x1 | false ⇒ x0 ]))〉
  | false ⇒
 match eq_w32 addr IP2022_DPH_loc with
  [ true ⇒ fREG (cnH ? (dp_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_DPL_loc with
  [ true ⇒ fREG (cnL ? (dp_reg_IP2022 (alu … s)))
  | false ⇒
 (* SPEED[3:0] *)
 match eq_w32 addr IP2022_SPEED_loc with
  [ true ⇒ fREG 〈x0,(speed_reg_IP2022 (alu … s))〉
  | false ⇒
 match eq_w32 addr IP2022_MULH_loc with
  [ true ⇒ fREG (mulh_reg_IP2022 (alu … s))
  | false ⇒
 match eq_w32 addr IP2022_ADDRH_loc with
  [ true ⇒ fREG (w24h (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                     (addr_array_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_ADDRL_loc with
  [ true ⇒ fREG (w24l (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                     (addr_array_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_DATAH_loc with
  [ true ⇒ fREG (cnH ? (data_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_DATAL_loc with
  [ true ⇒ fREG (cnL ? (data_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_CALLH_loc with
  [ true ⇒ fREG (cnH ? (getn_array16T x0 ? (call_stack_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_CALLL_loc with
  [ true ⇒ fREG (cnL ? (getn_array16T x0 ? (call_stack_IP2022 (alu … s))))
(* accesso normale *)
  | false ⇒ fMEM (mem_desc … s) (chk_desc … s) addr
  ]]]]]]]]]]]]]]]]]]]].

(* lettura IP2022 di un byte *)
ndefinition IP2022_memory_filter_read ≝
λt:memory_impl.λs:any_status IP2022 t.λaddr:word32.
 IP2022_memory_filter_read_aux t s addr byte8
  (λb.Some byte8 b)
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word32.mem_read t m c a).

(* lettura IP2022 di un bit *)
ndefinition IP2022_memory_filter_read_bit ≝
λt:memory_impl.λs:any_status IP2022 t.λaddr:word32.λsub:oct.
 IP2022_memory_filter_read_aux t s addr bool
  (λb.Some bool (getn_array8T sub bool (bits_of_byte8 b)))
  (λm:aux_mem_type t.λc:aux_chk_type t.λa:word32.mem_read_bit t m c a sub).

(* ***** *)
(* WRITE *)
(* ***** *)

ndefinition high_write_aux_w16 ≝
λf:byte8 → byte8.λw:word16.〈(f (cnH ? w)):(cnL ? w)〉.

ndefinition lowc_write_aux_w16 ≝
λf:byte8 → byte8.λw:word16.λflag:aux_mod_type.
 〈((match flag with
    [ auxMode_ok ⇒ λx.x
    | auxMode_inc ⇒ succ_b8
    | auxMode_dec ⇒ pred_b8 ]) (cnH ? w)):
  (f (cnL ? w))〉.

ndefinition lownc_write_aux_w16 ≝
λf:byte8 → byte8.λw:word16.〈(cnH ? w):(f (cnL ? w))〉.

ndefinition ext_write_aux_w24 ≝
λf:byte8 → byte8.λw:word24.〈(f (w24x w));(w24h w);(w24l w)〉.

ndefinition high_write_aux_w24 ≝
λf:byte8 → byte8.λw:word24.〈(w24x w);(f (w24h w));(w24l w)〉.

ndefinition low_write_aux_w24 ≝
λf:byte8 → byte8.λw:word24.λflag:aux_mod_type.
 match (match flag with
         [ auxMode_ok ⇒ λx.x
         | auxMode_inc ⇒ succ_w16
         | auxMode_dec ⇒ pred_w16 ]) 〈(w24x w):(w24h w)〉 with
  [ mk_comp_num wx' wh' ⇒ 〈wx';wh';(w24l w)〉 ].

(* flag di carry: riportare il carry al byte logicamente superiore *)
(* modifica di pc: non inserita nella stato ma postposta *)
ndefinition IP2022_memory_filter_write_aux ≝
λt:memory_impl.λs:any_status IP2022 t.λaddr:word32.λflag:aux_mod_type.
λfREG:byte8 → byte8.λfMEM:aux_mem_type t → aux_chk_type t → word32 → option (aux_mem_type t).
(* intercettare le locazioni memory mapped *)
 match eq_w32 addr IP2022_ADDRSEL_loc with
  [ true ⇒ set_addrsel_reg … s (fREG (addrsel_reg_IP2022 (alu … s)))
  | false ⇒ 
 match eq_w32 addr IP2022_ADDRX_loc with
  [ true ⇒ set_addr_reg … s (ext_write_aux_w24 fREG (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                                                   (addr_array_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_IPH_loc with
  [ true ⇒ set_ip_reg … s (high_write_aux_w16 fREG (ip_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_IPL_loc with
  [ true ⇒ set_ip_reg … s (lowc_write_aux_w16 fREG (ip_reg_IP2022 (alu … s)) flag)
  | false ⇒
 match eq_w32 addr IP2022_SPH_loc with
  [ true ⇒ set_sp_reg … s (high_write_aux_w16 fREG (sp_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_SPL_loc with
  [ true ⇒ set_sp_reg … s (lowc_write_aux_w16 fREG (sp_reg_IP2022 (alu … s)) flag)
  | false ⇒
 match eq_w32 addr IP2022_PCL_loc with
  [ true ⇒ Some ? (set_pc_reg … s (lowc_write_aux_w16 fREG (pc_reg_IP2022 (alu … s)) flag))
  | false ⇒
 match eq_w32 addr IP2022_W_loc with
  [ true ⇒ Some ? (set_acc_8_low_reg … s (fREG (acc_low_reg_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_DPH_loc with
  [ true ⇒ set_dp_reg … s (high_write_aux_w16 fREG (dp_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_DPL_loc with
  [ true ⇒ set_dp_reg … s (lowc_write_aux_w16 fREG (dp_reg_IP2022 (alu … s)) flag)
  | false ⇒
 match eq_w32 addr IP2022_MULH_loc with
  [ true ⇒ set_mulh_reg … s (fREG (mulh_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_ADDRH_loc with
  [ true ⇒ set_addr_reg … s (high_write_aux_w24 fREG (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                                                    (addr_array_IP2022 (alu … s))))
  | false ⇒
 match eq_w32 addr IP2022_ADDRL_loc with
  [ true ⇒ set_addr_reg … s (low_write_aux_w24 fREG (get_addrarray (addrsel_reg_IP2022 (alu … s))
                                                                   (addr_array_IP2022 (alu … s))) flag)
  | false ⇒
 match eq_w32 addr IP2022_DATAH_loc with
  [ true ⇒ set_data_reg … s (high_write_aux_w16 fREG (data_reg_IP2022 (alu … s)))
  | false ⇒
(* nessun riporto automatico *)
 match eq_w32 addr IP2022_DATAL_loc with
  [ true ⇒ set_data_reg … s (lownc_write_aux_w16 fREG (data_reg_IP2022 (alu … s)))
  | false ⇒
 match eq_w32 addr IP2022_CALLH_loc with
  [ true ⇒ set_call_reg … s (high_write_aux_w16 fREG (getn_array16T x0 ? (call_stack_IP2022 (alu … s))))
  | false ⇒
(* nessun riporto automatico *)
 match eq_w32 addr IP2022_CALLL_loc with
  [ true ⇒ set_call_reg … s (lownc_write_aux_w16 fREG (getn_array16T x0 ? (call_stack_IP2022 (alu … s))))
(* accesso normale *)
  | false ⇒ opt_map … (fMEM (mem_desc … s) (chk_desc … s) addr)
             (λmem'.Some ? (set_mem_desc … s mem'))
  ]]]]]]]]]]]]]]]]].

(* scrittura IP2022 di un byte *)
ndefinition IP2022_memory_filter_write ≝
λt:memory_impl.λs:any_status IP2022 t.
λaddr:word32.λflag:aux_mod_type.λval:byte8.
 (* PAGE[7:5] Z[2] H[1] C [0] *)
 match eq_w32 addr IP2022_STATUS_loc with
  [ true ⇒ Some ? 
            (set_alu … s
             (set_page_reg_IP2022
              (set_z_flag_IP2022
               (set_h_flag_IP2022
                (set_c_flag_IP2022 (alu … s)
                 (getn_array8T o7 ? (bits_of_byte8 val)))
                (getn_array8T o6 ? (bits_of_byte8 val)))
               (getn_array8T o5 ? (bits_of_byte8 val)))
              (oct_of_exH (cnH ? val))))
 (* accesso a registro_non_spezzato/normale *)
  | false ⇒ IP2022_memory_filter_write_aux t s addr flag
             (λb.val)
             (λm:aux_mem_type t.λc:aux_chk_type t.λa:word32.mem_update t m c a val) ].

(* scrittura IP2022 di un bit *)
ndefinition IP2022_memory_filter_write_bit ≝
λt:memory_impl.λs:any_status IP2022 t.
λaddr:word32.λsub:oct.λval:bool.
 (* PAGE[7:5] Z[2] H[1] C [0] *)
 match eq_w32 addr IP2022_STATUS_loc with
  [ true ⇒ Some ? (set_alu … s
   (match sub with
     [ o0 ⇒ set_page_reg_IP2022 (alu … s)
                                ((match val with [ true ⇒ or_oct o4 | false ⇒ and_oct o3 ])
                                  (page_reg_IP2022 (alu … s)))
     | o1 ⇒ set_page_reg_IP2022 (alu … s)
                                ((match val with [ true ⇒ or_oct o2 | false ⇒ and_oct o5 ])
                                  (page_reg_IP2022 (alu … s)))
     | o2 ⇒ set_page_reg_IP2022 (alu … s) 
                                ((match val with [ true ⇒ or_oct o1 | false ⇒ and_oct o6 ])
                                  (page_reg_IP2022 (alu … s)))
     | o5 ⇒ set_z_flag_IP2022 (alu … s) val
     | o6 ⇒ set_h_flag_IP2022 (alu … s) val
     | o7 ⇒ set_c_flag_IP2022 (alu … s) val
     | _ ⇒ alu … s ]))
 (* accesso a registro_non_spezzato/normale *)
  | false ⇒ IP2022_memory_filter_write_aux t s addr auxMode_ok
             (λb.byte8_of_bits (setn_array8T sub bool (bits_of_byte8 b) val))
             (λm:aux_mem_type t.λc:aux_chk_type t.λa:word32.mem_update_bit t m c a sub val) ].
