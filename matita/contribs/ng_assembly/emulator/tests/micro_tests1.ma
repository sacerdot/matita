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

include "emulator/tests/micro_tests_tools.ma".
include "emulator/multivm/multivm.ma".
include "emulator/status/status_lemmas.ma".
include "emulator/model/model.ma".

(* ****************************************** *)
(* MICRO TEST DI CORRETTEZZA DELLE ISTRUZIONI *)
(* ****************************************** *)

(* ********* *)
(* HCS08 ADC *)
(* ********* *)

ndefinition mTest_HCS08_ADC_source ≝ source_to_byte8 HCS08 (
(* testa la logica di ADC e le modalita' IMM1,DIR1/2,IX0/1/2,SP1/2 *)
(* BEFORE: A=0x00 H:X=0xFF50 PC=0x1860 SP=0x0110 C=true *)
(* [0x1860] 2clk *) (compile HCS08 ? ADC (maIMM1 〈xA,xA〉) ?) @         (* AFTER1: imm1=0xAA quindi 0x00+imm1+true=A:0xAB C:false *)
(* [0x1862] 3clk *) (compile HCS08 ? ADC (maDIR1 〈xF,xF〉) ?) @         (* AFTER2: dir1=[0x00FF]=0x8F quindi 0xAB+dir1+false=A:0x3A C:true *)
(* [0x1864] 4clk *) (compile HCS08 ? ADC (maDIR2 〈〈xF,xF〉:〈x1,x1〉〉) ?) @ (* AFTER3: dir2=[0xFF11]=0x11 quindi 0x3A+dir2+true=A:0x4C C:false *)
(* [0x1867] 4clk *) (compile HCS08 ? ADC (maIX2 〈〈xF,xF〉:〈xF,x0〉〉) ?) @  (* AFTER4: ix2=[X+0xFFF0]=[0xFF40]=0x40 quindi 0x4C+ix2+false=A:0x8C C:false *)
(* [0x186A] 3clk *) (compile HCS08 ? ADC (maIX1 〈x2,x4〉) ?) @          (* AFTER5: ix1=[X+0x0024]=[0xFF74]=0x74 quindi 0x8C+ix1+false=A:0x00 C:true *)
(* [0x186C] 3clk *) (compile HCS08 ? ADC maIX0 ?) @                   (* AFTER6: ix0=[X]=[0xFF50]=0x50 quindi 0x00+ix0+true=A:0x51 C:false *)
(* [0x186D] 5clk *) (compile HCS08 ? ADC (maSP2 〈〈xF,xF〉:〈x6,x1〉〉) ?) @  (* AFTER7: sp2=[SP+0xFF61]=[0x0071]=0x01 quindi 0x51+sp2+false=A:0x52 C:false *)
(* [0x1871] 4clk *) (compile HCS08 ? ADC (maSP1 〈x2,x4〉) ?)            (* AFTER8: sp1=[SP+0x0024]=[0x0134]=0xC4 quindi 0x52+sp1+false=A:0x16 C:true *)
(* [0x1874] si puo' quindi enunciare che dopo 2+3+4+4+3+3+5+4=28 clk *)
(*          A<-0x16 PC<-0x1874 *)
). napply I. nqed.

(* creazione del processore+caricamento+impostazione registri *)
ndefinition mTest_HCS08_ADC_status ≝
λt:memory_impl.
 set_c_flag HCS08 t (* C<-true *)
  (setweak_sp_reg HCS08 t (* SP<-0x0110 *)
   (setweak_indX_16_reg HCS08 t (* H:X<-0xFF50 *)
    (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
     (start_of_model HCS08 MC9S08AW60 t
      (load_from_source_at t (* carica mTest_bytes in ROM:mTest_HCS08_data *)
       (load_from_source_at t (* carica mTest_bytes in RAM:mTest_HCS08_RAM *)
        (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
          mTest_HCS08_ADC_source (extu_w32 mTest_HCS08_prog))
         mTest_bytes (extu_w32 mTest_HCS08_RAM))
        mTest_bytes (extu_w32 mTest_HCS08_data))
      (build_memory_type_of_model HCS08 MC9S08AW60 t)
      (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
      false false false false false false) (* non deterministici tutti a 0 *)
     mTest_HCS08_prog)
    (mk_word16 〈xF,xF〉 〈x5,x0〉))
   (mk_word16 〈x0,x1〉 〈x1,x0〉))
  true.

(* dimostrazione senza svolgimento degli stati, immediata *)
nlemma ok_mTest_HCS08_ADC_full :
 let t ≝ MEM_TREE in
 execute HCS08 t (TickOK ? (mTest_HCS08_ADC_status t)) nat28 =
 (* NB: V,N,Z sono tornati false C e' tornato true *)
 TickOK ? (set_pc_reg HCS08 t (* nuovo PC *)
           (set_acc_8_low_reg HCS08 t (mTest_HCS08_ADC_status t) 〈x1,x6〉) (* nuovo A *)
            (mk_word16 〈x1,x8〉 〈x7,x4〉)).
 (* esempio per svoglimento degli stati manualmente*)
  nletin BEFORE ≝ (alu HCS08 t (mTest_HCS08_ADC_status t));
  nnormalize in BEFORE:(%);

 nletin AFTER_ALU1 ≝ (match execute HCS08 t (TickOK ? (mTest_HCS08_ADC_status t)) nat2 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU1:(%);

 nletin AFTER_ALU2 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU1)) nat3 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU2:(%);

 nletin AFTER_ALU3 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU2)) nat4 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU3:(%);  

 nletin AFTER_ALU4 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU3)) nat4 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU4:(%); 

 nletin AFTER_ALU5 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU4)) nat3 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU5:(%); 

 nletin AFTER_ALU6 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU5)) nat3 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU6:(%); 

 nletin AFTER_ALU7 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU6)) nat5 with
  [ TickERR _ _ ⇒ BEFORE 
  | TickSUSP _ _ ⇒ BEFORE 
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU7:(%); 

 nletin AFTER_ALU8 ≝ (match execute HCS08 t (TickOK ? 
                     (set_alu HCS08 t (mTest_HCS08_ADC_status t) AFTER_ALU7)) nat4 with
  [ TickERR _ _ ⇒ BEFORE
  | TickSUSP _ _ ⇒ BEFORE
  | TickOK s ⇒ alu HCS08 t s ]);
 nnormalize in AFTER_ALU8:(%); *) 

 napply refl_eq.
nqed.
