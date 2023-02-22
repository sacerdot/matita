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

include "freescale/multivm.ma".

(* ****************************************** *)
(* MICRO TEST DI CORRETTEZZA DELLE ISTRUZIONI *)
(* ****************************************** *)

(* tabella 0x00 - 0xFF utile da caricare in RAM/ROM *)
definition mTest_bytes : list byte8 ≝
 [   〈x0,x0〉 ; 〈x0,x1〉 ; 〈x0,x2〉 ; 〈x0,x3〉 ; 〈x0,x4〉 ; 〈x0,x5〉 ; 〈x0,x6〉 ; 〈x0,x7〉
 ; 〈x0,x8〉 ; 〈x0,x9〉 ; 〈x0,xA〉 ; 〈x0,xB〉 ; 〈x0,xC〉 ; 〈x0,xD〉 ; 〈x0,xE〉 ; 〈x0,xF〉 ]
@[   〈x1,x0〉 ; 〈x1,x1〉 ; 〈x1,x2〉 ; 〈x1,x3〉 ; 〈x1,x4〉 ; 〈x1,x5〉 ; 〈x1,x6〉 ; 〈x1,x7〉
 ; 〈x1,x8〉 ; 〈x1,x9〉 ; 〈x1,xA〉 ; 〈x1,xB〉 ; 〈x1,xC〉 ; 〈x1,xD〉 ; 〈x1,xE〉 ; 〈x1,xF〉 ]
@[   〈x2,x0〉 ; 〈x2,x1〉 ; 〈x2,x2〉 ; 〈x2,x3〉 ; 〈x2,x4〉 ; 〈x2,x5〉 ; 〈x2,x6〉 ; 〈x2,x7〉
 ; 〈x2,x8〉 ; 〈x2,x9〉 ; 〈x2,xA〉 ; 〈x2,xB〉 ; 〈x2,xC〉 ; 〈x2,xD〉 ; 〈x2,xE〉 ; 〈x2,xF〉 ]
@[   〈x3,x0〉 ; 〈x3,x1〉 ; 〈x3,x2〉 ; 〈x3,x3〉 ; 〈x3,x4〉 ; 〈x3,x5〉 ; 〈x3,x6〉 ; 〈x3,x7〉
 ; 〈x3,x8〉 ; 〈x3,x9〉 ; 〈x3,xA〉 ; 〈x3,xB〉 ; 〈x3,xC〉 ; 〈x3,xD〉 ; 〈x3,xE〉 ; 〈x3,xF〉 ]
@[   〈x4,x0〉 ; 〈x4,x1〉 ; 〈x4,x2〉 ; 〈x4,x3〉 ; 〈x4,x4〉 ; 〈x4,x5〉 ; 〈x4,x6〉 ; 〈x4,x7〉
 ; 〈x4,x8〉 ; 〈x4,x9〉 ; 〈x4,xA〉 ; 〈x4,xB〉 ; 〈x4,xC〉 ; 〈x4,xD〉 ; 〈x4,xE〉 ; 〈x4,xF〉 ]
@[   〈x5,x0〉 ; 〈x5,x1〉 ; 〈x5,x2〉 ; 〈x5,x3〉 ; 〈x5,x4〉 ; 〈x5,x5〉 ; 〈x5,x6〉 ; 〈x5,x7〉
 ; 〈x5,x8〉 ; 〈x5,x9〉 ; 〈x5,xA〉 ; 〈x5,xB〉 ; 〈x5,xC〉 ; 〈x5,xD〉 ; 〈x5,xE〉 ; 〈x5,xF〉 ]
@[   〈x6,x0〉 ; 〈x6,x1〉 ; 〈x6,x2〉 ; 〈x6,x3〉 ; 〈x6,x4〉 ; 〈x6,x5〉 ; 〈x6,x6〉 ; 〈x6,x7〉
 ; 〈x6,x8〉 ; 〈x6,x9〉 ; 〈x6,xA〉 ; 〈x6,xB〉 ; 〈x6,xC〉 ; 〈x6,xD〉 ; 〈x6,xE〉 ; 〈x6,xF〉 ]
@[   〈x7,x0〉 ; 〈x7,x1〉 ; 〈x7,x2〉 ; 〈x7,x3〉 ; 〈x7,x4〉 ; 〈x7,x5〉 ; 〈x7,x6〉 ; 〈x7,x7〉
 ; 〈x7,x8〉 ; 〈x7,x9〉 ; 〈x7,xA〉 ; 〈x7,xB〉 ; 〈x7,xC〉 ; 〈x7,xD〉 ; 〈x7,xE〉 ; 〈x7,xF〉 ]
@[  〈x8,x0〉 ; 〈x8,x1〉 ; 〈x8,x2〉 ; 〈x8,x3〉 ; 〈x8,x4〉 ; 〈x8,x5〉 ; 〈x8,x6〉 ; 〈x8,x7〉
 ; 〈x8,x8〉 ; 〈x8,x9〉 ; 〈x8,xA〉 ; 〈x8,xB〉 ; 〈x8,xC〉 ; 〈x8,xD〉 ; 〈x8,xE〉 ; 〈x8,xF〉 ]
@[   〈x9,x0〉 ; 〈x9,x1〉 ; 〈x9,x2〉 ; 〈x9,x3〉 ; 〈x9,x4〉 ; 〈x9,x5〉 ; 〈x9,x6〉 ; 〈x9,x7〉
 ; 〈x9,x8〉 ; 〈x9,x9〉 ; 〈x9,xA〉 ; 〈x9,xB〉 ; 〈x9,xC〉 ; 〈x9,xD〉 ; 〈x9,xE〉 ; 〈x9,xF〉 ]
@[   〈xA,x0〉 ; 〈xA,x1〉 ; 〈xA,x2〉 ; 〈xA,x3〉 ; 〈xA,x4〉 ; 〈xA,x5〉 ; 〈xA,x6〉 ; 〈xA,x7〉
 ; 〈xA,x8〉 ; 〈xA,x9〉 ; 〈xA,xA〉 ; 〈xA,xB〉 ; 〈xA,xC〉 ; 〈xA,xD〉 ; 〈xA,xE〉 ; 〈xA,xF〉 ]
@[   〈xB,x0〉 ; 〈xB,x1〉 ; 〈xB,x2〉 ; 〈xB,x3〉 ; 〈xB,x4〉 ; 〈xB,x5〉 ; 〈xB,x6〉 ; 〈xB,x7〉
 ; 〈xB,x8〉 ; 〈xB,x9〉 ; 〈xB,xA〉 ; 〈xB,xB〉 ; 〈xB,xC〉 ; 〈xB,xD〉 ; 〈xB,xE〉 ; 〈xB,xF〉 ]
@[   〈xC,x0〉 ; 〈xC,x1〉 ; 〈xC,x2〉 ; 〈xC,x3〉 ; 〈xC,x4〉 ; 〈xC,x5〉 ; 〈xC,x6〉 ; 〈xC,x7〉
 ; 〈xC,x8〉 ; 〈xC,x9〉 ; 〈xC,xA〉 ; 〈xC,xB〉 ; 〈xC,xC〉 ; 〈xC,xD〉 ; 〈xC,xE〉 ; 〈xC,xF〉 ]
@[   〈xD,x0〉 ; 〈xD,x1〉 ; 〈xD,x2〉 ; 〈xD,x3〉 ; 〈xD,x4〉 ; 〈xD,x5〉 ; 〈xD,x6〉 ; 〈xD,x7〉
 ; 〈xD,x8〉 ; 〈xD,x9〉 ; 〈xD,xA〉 ; 〈xD,xB〉 ; 〈xD,xC〉 ; 〈xD,xD〉 ; 〈xD,xE〉 ; 〈xD,xF〉 ]
@[   〈xE,x0〉 ; 〈xE,x1〉 ; 〈xE,x2〉 ; 〈xE,x3〉 ; 〈xE,x4〉 ; 〈xE,x5〉 ; 〈xE,x6〉 ; 〈xE,x7〉
 ; 〈xE,x8〉 ; 〈xE,x9〉 ; 〈xE,xA〉 ; 〈xE,xB〉 ; 〈xE,xC〉 ; 〈xE,xD〉 ; 〈xE,xE〉 ; 〈xE,xF〉 ]
@[   〈xF,x0〉 ; 〈xF,x1〉 ; 〈xF,x2〉 ; 〈xF,x3〉 ; 〈xF,x4〉 ; 〈xF,x5〉 ; 〈xF,x6〉 ; 〈xF,x7〉
 ; 〈xF,x8〉 ; 〈xF,x9〉 ; 〈xF,xA〉 ; 〈xF,xB〉 ; 〈xF,xC〉 ; 〈xF,xD〉 ; 〈xF,xE〉 ; 〈xF,xF〉
 ].

(* RIASSUNTO MCU/MODELLO/MEMORIA DA USARE

   HC05 (MC68HC05J5A)   [0x0080-0x00FF] RAM [0x0300-0x0CFF] ROM
   HC08 (MC68HC08AB16A) [0x0050-0x024F] RAM [0xBE00-0xFDFF] ROM
   HCS08 (MC9S08AW60)   [0x0070-0x086F] RAM [0x1860-0xFFFF] FLASH
   RS08 (MC9RS08KA2)    [0x0020-0x004F] RAM [0x3800-0x3FFF] FLASH *)

(*
   1) mTest_x_RAM : inizio della RAM
       (start point per caricamento mTest_bytes in RAM) 
   2) mTest_x_prog: inizio della ROM
       (start point per caricamento programma in ROM)
   3) mTest_x_data: ultimi 256b della ROM
       (start point per caricamento mTest_bytes in ROM)
*)
definition mTest_HC05_RAM ≝ 〈〈x0,x0〉:〈x8,x0〉〉.
definition mTest_HC05_prog ≝ 〈〈x0,x3〉:〈x0,x0〉〉.
definition mTest_HC05_data ≝ 〈〈x0,xC〉:〈x0,x0〉〉.

definition mTest_HC08_RAM ≝ 〈〈x0,x0〉:〈x5,x0〉〉.
definition mTest_HC08_prog ≝ 〈〈xB,xE〉:〈x0,x0〉〉.
definition mTest_HC08_data ≝ 〈〈xF,xD〉:〈x0,x0〉〉.

definition mTest_HCS08_RAM ≝ 〈〈x0,x0〉:〈x7,x0〉〉.
definition mTest_HCS08_prog ≝ 〈〈x1,x8〉:〈x6,x0〉〉.
definition mTest_HCS08_data ≝ 〈〈xF,xF〉:〈x0,x0〉〉.

definition mTest_RS08_RAM ≝ 〈〈x0,x0〉:〈x2,x0〉〉.
definition mTest_RS08_prog ≝ 〈〈x3,x8〉:〈x0,x0〉〉.
definition mTest_RS08_data ≝ 〈〈x3,xF〉:〈x0,x0〉〉.

(* ********* *)
(* HCS08 ADC *)
(* ********* *)

(* testa la logica di ADC e le modalita' IMM1,DIR1/2,IX0/1/2,SP1/2 *)
definition mTest_HCS08_ADC_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: A=0x00 H:X=0xFF50 PC=0x1860 SP=0x0110 C=true *)
(* [0x1860] 2clk *) (compile m ? ADC (maIMM1 〈xA,xA〉) I) @
(* AFTER1: imm1=0xAA quindi 0x00+imm1+true=A:0xAB C:false *)
(* [0x1862] 3clk *) (compile m ? ADC (maDIR1 〈xF,xF〉) I) @
(* AFTER2: dir1=[0x00FF]=0x8F quindi 0xAB+dir1+false=A:0x3A C:true *)
(* [0x1864] 4clk *) (compile m ? ADC (maDIR2 〈〈xF,xF〉:〈x1,x1〉〉) I) @
(* AFTER3: dir2=[0xFF11]=0x11 quindi 0x3A+dir2+true=A:0x4C C:false *)
(* [0x1867] 4clk *) (compile m ? ADC (maIX2 〈〈xF,xF〉:〈xF,x0〉〉) I) @
(* AFTER4: ix2=[X+0xFFF0]=[0xFF40]=0x40 quindi 0x4C+ix2+false=A:0x8C C:false *)
(* [0x186A] 3clk *) (compile m ? ADC (maIX1 〈x2,x4〉) I) @
(* AFTER5: ix1=[X+0x0024]=[0xFF74]=0x74 quindi 0x8C+ix1+false=A:0x00 C:true *)
(* [0x186C] 3clk *) (compile m ? ADC maIX0 I) @
(* AFTER6: ix0=[X]=[0xFF50]=0x50 quindi 0x00+ix0+true=A:0x51 C:false *)
(* [0x186D] 5clk *) (compile m ? ADC (maSP2 〈〈xF,xF〉:〈x6,x1〉〉) I) @
(* AFTER7: sp2=[SP+0xFF61]=[0x0071]=0x01 quindi 0x51+sp2+false=A:0x52 C:false *)
(* [0x1871] 4clk *) (compile m ? ADC (maSP1 〈x2,x4〉) I)
(* AFTER8: sp1=[SP+0x0024]=[0x0134]=0xC4 quindi 0x52+sp1+false=A:0x16 C:true *)
(* [0x1874] si puo' quindi enunciare che dopo 2+3+4+4+3+3+5+4=28 clk *)
(*          A<-0x16 PC<-0x1874 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_ADC_status ≝
λt:memory_impl.
 set_c_flag HCS08 t (* C<-true *)
  (setweak_sp_reg HCS08 t (* SP<-0x0110 *)
   (setweak_indX_16_reg HCS08 t (* H:X<-0xFF50 *)
    (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
     (start_of_mcu_version
      MC9S08AW60 t
      (load_from_source_at t (* carica mTest_bytes in ROM:mTest_HCS08_data *)
       (load_from_source_at t (* carica mTest_bytes in RAM:mTest_HCS08_RAM *)
        (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
          mTest_HCS08_ADC_source mTest_HCS08_prog)
         mTest_bytes mTest_HCS08_RAM)
        mTest_bytes mTest_HCS08_data)
      (build_memory_type_of_mcu_version MC9S08AW60 t)
      (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
      false false false false false false) (* non deterministici tutti a 0 *)
     mTest_HCS08_prog)
    (mk_word16 (mk_byte8 xF xF) (mk_byte8 x5 x0)))
   (mk_word16 (mk_byte8 x0 x1) (mk_byte8 x1 x0)))
  true.

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_HCS08_ADC_full :
 ∀t:memory_impl.
 execute HCS08 t (TickOK ? (mTest_HCS08_ADC_status t)) 28 =
 (* NB: V,N,Z sono tornati false C e' tornato true *)
 TickOK ? (set_pc_reg HCS08 t (* nuovo PC *)
           (set_acc_8_low_reg HCS08 t (mTest_HCS08_ADC_status t) 〈x1,x6〉) (* nuovo A *)
            (mk_word16 〈x1,x8〉 〈x7,x4〉)).
 intro;
 elim t;
 reflexivity.
qed.

(* ********* *)
(* HCS08 MOV *)
(* ********* *)

(* testa la logica di MOV e le modalita' xxx_to_xxx *)
definition mTest_HCS08_MOV_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: H:X=0x0071 PC=0x1860 *)

(* [0x1860] 4clk *) (compile m ? MOV (maIMM1_to_DIR1 〈x3,xA〉 〈x7,x0〉) I) @
(* 0x3A in [0x0070] *)
(* [0x1863] 5clk *) (compile m ? MOV (maDIR1_to_DIR1 〈x7,x0〉 〈x7,x1〉) I) @
(* [0x0070] in [0x0071] *)
(* [0x1866] 5clk *) (compile m ? MOV (maIX0p_to_DIR1 〈x7,x2〉) I) @
(* [X++=0x0071] in [0x0072] *)
(* [0x1868] 5clk *) (compile m ? MOV (maDIR1_to_IX0p 〈x7,x2〉) I)
(* [0x0072] in [X++=0x0072] *)
(* [0x186A] si puo' quindi enunciare che dopo 4+5+5+5=19 clk *)
(*          PC<-0x186A X<-0x0073 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_MOV_status ≝
λt:memory_impl.
λb1,b2,b3:byte8.
 setweak_indX_16_reg HCS08 t (* H:X<-0x0071 *)
  (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
   (start_of_mcu_version
    MC9S08AW60 t
    (load_from_source_at t (* carica b1-3 in RAM:mTest_HCS08_RAM *)
     (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
       mTest_HCS08_MOV_source mTest_HCS08_prog)
     [ b1 ; b2 ; b3 ] mTest_HCS08_RAM)
    (build_memory_type_of_mcu_version MC9S08AW60 t)
    (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
    false false false false false false) (* non deterministici tutti a 0 *)
   mTest_HCS08_prog)
  (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x7 x1)).

(* dimostrazione senza svolgimento degli stati, immediata *)
(* NB: la memoria e' cambiata e bisogna applicare eq_status_axiom *)
lemma ok_mTest_HCS08_MOV_full :
 ∀t:memory_impl.
 match execute HCS08 t (TickOK ? (mTest_HCS08_MOV_status t 〈x0,x0〉 〈x0,x0〉 〈x0,x0〉)) 19 with 
  [ TickERR s _ ⇒ s | TickSUSP s _ ⇒ s | TickOK s ⇒ s ] =
 setweak_indX_16_reg HCS08 t (* H:X *) 
  (set_pc_reg HCS08 t (mTest_HCS08_MOV_status t 〈x3,xA〉 〈x3,xA〉 〈x3,xA〉) (* PC *)
   (mk_word16 〈x1,x8〉 〈x6,xA〉))
    (mk_word16 〈x0,x0〉 〈x7,x3〉).
 intro;
 elim t;
 [ apply (eq_status_axiom mTest_HCS08_RAM 2 HCS08 MEM_FUNC); reflexivity; ] 
 reflexivity.
qed.

(* ************* *)
(* HCS08 ROL/ROR *)
(* ************* *)

(* testa la logica di ROL/ROR e le modalita' IMM2,INHx *)
definition mTest_HCS08_ROL_ROR_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: A=0x00 H:X=0x0000 PC=0x1860 Z=true *)
(* [0x1860] 3clk *) (compile m ? LDHX (maIMM2 〈〈x1,x2〉:〈x3,x4〉〉) I) @
(* [0x1863] 2clk *) (compile m ? LDA (maIMM1 〈x5,x6〉) I) @
(* [0x1865] 1clk *) (compile m ? ROL maINHA I) @
(* [0x1866] 1clk *) (compile m ? ROL maINHX I) @
(* [0x1867] 1clk *) (compile m ? ROR maINHA I) @
(* [0x1868] 1clk *) (compile m ? ROR maINHX I) @
(* [0x1869] 1clk *) (compile m ? CLR maINHA I) @
(* [0x186A] 1clk *) (compile m ? CLR maINHX I) @
(* [0x186B] 1clk *) (compile m ? CLR maINHH I)
(* [0x186C] si puo' quindi enunciare che dopo 3+2+1+1+1+1+1+1+1=12 clk *)
(*          PC<-0x186C *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_ROL_ROR_status ≝
λt:memory_impl.
 set_z_flag HCS08 t (* Z<-true *)
  (setweak_indX_16_reg HCS08 t (* H:X<-0x0000 *)
   (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
    (start_of_mcu_version
     MC9S08AW60 t
     (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
      mTest_HCS08_ROL_ROR_source mTest_HCS08_prog)
     (build_memory_type_of_mcu_version MC9S08AW60 t)
     (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
     false false false false false false) (* non deterministici tutti a 0 *)
    mTest_HCS08_prog)
   (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x0 x0)))
  true.

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_HCS08_ROL_ROR_full :
 ∀t:memory_impl.
 execute HCS08 t (TickOK ? (mTest_HCS08_ROL_ROR_status t)) 12 =
 TickOK ? (set_pc_reg HCS08 t (* nuovo PC *)
           (mTest_HCS08_ROL_ROR_status t) (mk_word16 〈x1,x8〉 〈x6,xC〉)).
 intro;
 elim t;
 reflexivity.
qed.

(* **************** *)
(* HCS08 CBEQx/DBNZ *)
(* **************** *)

(* testa la logica di CBEQx/DBNZ e le modalita' xxx_and_IMM1 *)
definition mTest_HCS08_CBEQ_DBNZ_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: H:X=0x006F SP=0x006F PC=0x1860 *)
(* [0x1860] 5clk *) (compile m ? CBEQA (maDIR1_and_IMM1 〈x7,x1〉 〈x0,x1〉) I) @
(* [0x1863] 1clk *) (compile m ? NOP maINH I) @ (* eseguito: A≠[0x0071]=0x01 *)
(* [0x1864] 4clk *) (compile m ? CBEQA (maIMM1_and_IMM1 〈x0,x0〉 〈x0,x1〉) I) @
(* [0x1867] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: A=0x00 *)
(* [0x1868] 4clk *) (compile m ? CBEQX (maIMM1_and_IMM1 〈x6,xF〉 〈x0,x1〉) I) @
(* [0x186B] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: X=0x6F *)
(* [0x186C] 5clk *) (compile m ? CBEQA (maIX1p_and_IMM1 〈x0,x1〉 〈x0,x1〉) I) @ (* H:X++ *)
(* [0x186F] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: A=[X+0x01]=[0x0070]=0x00 *)
(* [0x1870] 5clk *) (compile m ? CBEQA (maIX0p_and_IMM1 〈x0,x1〉) I) @ (* H:X++ *)
(* [0x1872] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: A=[X]=[0x0070]=0x00 *)
(* [0x1873] 6clk *) (compile m ? CBEQA (maSP1_and_IMM1 〈x0,x2〉 〈x0,x1〉) I) @
(* [0x1877] 1clk *) (compile m ? NOP maINH I) @ (* eseguito: A≠[SP+0x02]=[0x0071]=0x01 *)

(* [0x1878] 7clk *) (compile m ? DBNZ (maDIR1_and_IMM1 〈x7,x2〉 〈x0,x1〉) I) @
(* [0x187B] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: --[0x0072]=0x01≠0 *)
(* [0x187C] 4clk *) (compile m ? DBNZ (maINHA_and_IMM1 〈x0,x1〉) I) @
(* [0x187E] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: --A=0xFF≠0 *)
(* [0x187F] 4clk *) (compile m ? DBNZ (maINHX_and_IMM1 〈x0,x1〉) I) @
(* [0x1881] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: --X=0x70≠0 *)
(* [0x1882] 7clk *) (compile m ? DBNZ (maIX1_and_IMM1 〈x0,x2〉 〈x0,x1〉) I) @
(* [0x1885] 1clk *) (compile m ? NOP maINH I) @ (* eseguito: --[X+0x02]=[0x0072]=0x00=0 *)
(* [0x1886] 6clk *) (compile m ? DBNZ (maIX0_and_IMM1 〈x0,x1〉) I) @
(* [0x1888] 1clk *) (compile m ? NOP maINH I) @ (* non eseguito: --[X]=[0x0070]=0xFF≠0 *)
(* [0x1889] 8clk *) (compile m ? DBNZ (maSP1_and_IMM1 〈x0,x1〉 〈x0,x1〉) I) @ 
(* [0x188D] 1clk *) (compile m ? NOP maINH I) (* non eseguito: --[SP+0x01]=[0x0070]=0xFE≠0 *)
(* [0x188E] si puo' quindi enunciare che dopo 5+1+4+4+5+5+6+1 (31)
                                              7+4+4+7+1+6+8   (37) =68 clk *)
(*          A<-0xFF PC<-0x188E H:X<-0070 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_CBEQ_DBNZ_status ≝
λt:memory_impl.
λb1,b2,b3:byte8.
 setweak_sp_reg HCS08 t (* SP<-0x006F *)
  (setweak_indX_16_reg HCS08 t (* H:X<-0x006F *)
   (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
    (start_of_mcu_version
     MC9S08AW60 t
     (load_from_source_at t (* carica b1-3 in RAM:mTest_HCS08_RAM *)
      (load_from_source_at t (* carica mTest_bytes in RAM:mTest_HCS08_RAM *)
       (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
         mTest_HCS08_CBEQ_DBNZ_source mTest_HCS08_prog)
        mTest_bytes mTest_HCS08_RAM)
       [ b1 ; b2 ; b3 ] mTest_HCS08_RAM)
     (build_memory_type_of_mcu_version MC9S08AW60 t)
     (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
     false false false false false false) (* non deterministici tutti a 0 *)
    mTest_HCS08_prog)
   (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x6 xF)))
  (mk_word16 (mk_byte8 x0 x0) (mk_byte8 x6 xF)).

(* dimostrazione senza svolgimento degli stati, immediata *)
(* NB: la memoria e' cambiata e bisogna applicare eq_status_axiom *)
lemma ok_mTest_HCS08_CBEQ_DBNZ_full :
 ∀t:memory_impl.
 match execute HCS08 t (TickOK ? (mTest_HCS08_CBEQ_DBNZ_status t 〈x0,x0〉 〈x0,x1〉 〈x0,x2〉)) 68 with
  [ TickERR s _ ⇒ s | TickSUSP s _ ⇒ s | TickOK s ⇒ s ] =
 set_acc_8_low_reg HCS08 t (* nuovo A *)
  (set_pc_reg HCS08 t (* nuovo PC *)
   (setweak_indX_16_reg HCS08 t (mTest_HCS08_CBEQ_DBNZ_status t 〈xF,xE〉 〈x0,x1〉 〈x0,x0〉) (* nuovo H:X *)
    (mk_word16 〈x0,x0〉 〈x7,x0〉))
   (mk_word16 〈x1,x8〉 〈x8,xE〉))
  (mk_byte8 xF xF).
 intro;
 elim t;
 [ apply (eq_status_axiom mTest_HCS08_RAM 2 HCS08 MEM_FUNC); reflexivity; ]
 reflexivity.
qed.

(* ***************** *)
(* HCS08 BSETn/BCLRn *)
(* ***************** *)

(* testa la logica di BSETn/BCLRn e le modalita' DIRn *)
definition mTest_HCS08_BSETn_BCLRn_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: PC=0x1860 *)
(* [0x1860] 5clk *) (compile m ? BSETn (maDIRn o0 〈x7,x0〉) I) @ (* [0x0070]=0x01 *)
(* [0x1862] 5clk *) (compile m ? BSETn (maDIRn o1 〈x7,x0〉) I) @ (* [0x0070]=0x03 *)
(* [0x1864] 5clk *) (compile m ? BSETn (maDIRn o2 〈x7,x0〉) I) @ (* [0x0070]=0x07 *)
(* [0x1866] 5clk *) (compile m ? BSETn (maDIRn o3 〈x7,x0〉) I) @ (* [0x0070]=0x0F *)
(* [0x1868] 5clk *) (compile m ? BSETn (maDIRn o4 〈x7,x0〉) I) @ (* [0x0070]=0x1F *)
(* [0x186A] 5clk *) (compile m ? BSETn (maDIRn o5 〈x7,x0〉) I) @ (* [0x0070]=0x3F *)
(* [0x186C] 5clk *) (compile m ? BSETn (maDIRn o6 〈x7,x0〉) I) @ (* [0x0070]=0x7F *)
(* [0x186E] 5clk *) (compile m ? BSETn (maDIRn o7 〈x7,x0〉) I) @ (* [0x0070]=0xFF *)
(* [0x1870] 5clk *) (compile m ? BCLRn (maDIRn o0 〈x7,x0〉) I) @ (* [0x0070]=0xFE *)
(* [0x1872] 5clk *) (compile m ? BCLRn (maDIRn o1 〈x7,x0〉) I) @ (* [0x0070]=0xFC *)
(* [0x1874] 5clk *) (compile m ? BCLRn (maDIRn o2 〈x7,x0〉) I) @ (* [0x0070]=0xF8 *)
(* [0x1876] 5clk *) (compile m ? BCLRn (maDIRn o3 〈x7,x0〉) I) @ (* [0x0070]=0xF0 *)
(* [0x1878] 5clk *) (compile m ? BCLRn (maDIRn o4 〈x7,x0〉) I) @ (* [0x0070]=0xE0 *)
(* [0x187A] 5clk *) (compile m ? BCLRn (maDIRn o5 〈x7,x0〉) I) @ (* [0x0070]=0xC0 *)
(* [0x187C] 5clk *) (compile m ? BCLRn (maDIRn o6 〈x7,x0〉) I) @ (* [0x0070]=0x80 *)
(* [0x187E] 5clk *) (compile m ? BCLRn (maDIRn o7 〈x7,x0〉) I)   (* [0x0070]=0x00 *)
(* [0x1880] si puo' quindi enunciare che dopo 5+5+5+5+5+5+5+5
                                              5+5+5+5+5+5+5+5 =80 clk *)
(*          PC<-0x1880 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_BSETn_BCLRn_status ≝
λt:memory_impl.
λb1:byte8.
 set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
  (start_of_mcu_version
   MC9S08AW60 t
   (load_from_source_at t (* carica b1 in RAM:mTest_HCS08_RAM *)
    (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_HCS08_prog *)
      mTest_HCS08_BSETn_BCLRn_source mTest_HCS08_prog)
     [ b1 ] mTest_HCS08_RAM)
   (build_memory_type_of_mcu_version MC9S08AW60 t)
   (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
   false false false false false false) (* non deterministici tutti a 0 *)
  mTest_HCS08_prog.

(* dimostrazione senza svolgimento degli stati, immediata *)
(* NB: la memoria e' cambiata e bisogna applicare eq_status_axiom *)
lemma ok_mTest_HCS08_BSETn_BCLRn_full :
 ∀t:memory_impl.
 match execute HCS08 t (TickOK ? (mTest_HCS08_BSETn_BCLRn_status t 〈x0,x0〉)) 80 with
  [ TickERR s _ ⇒ s | TickSUSP s _ ⇒ s | TickOK s ⇒ s ] =
 set_pc_reg HCS08 t (mTest_HCS08_BSETn_BCLRn_status t 〈x0,x0〉) 〈〈x1,x8〉:〈x8,x0〉〉. (* nuovo PC *)
 intro;
 elim t;
 [ apply (eq_status_axiom mTest_HCS08_RAM 0 HCS08 MEM_FUNC); reflexivity ]
 reflexivity.
qed.

(* ******************* *)
(* HCS08 BRSETn/BRCLRn *)
(* ******************* *)

(* testa la logica di BRSETn/BRCLRn e le modalita' DIRn_and_IMM1 *)
definition mTest_HCS08_BRSETn_BRCLRn_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: va a testare [0x00C5]=0x55 PC=0x1860 *)
(* [0x1860] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o0 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1863] 1clk *) (compile m ? NOP maINH I) @
(* [0x1864] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o1 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1867] 1clk *) (compile m ? NOP maINH I) @
(* [0x1868] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o2 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x186B] 1clk *) (compile m ? NOP maINH I) @
(* [0x186C] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o3 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x186F] 1clk *) (compile m ? NOP maINH I) @
(* [0x1870] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o4 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1873] 1clk *) (compile m ? NOP maINH I) @
(* [0x1874] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o5 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1877] 1clk *) (compile m ? NOP maINH I) @
(* [0x1878] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o6 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x187B] 1clk *) (compile m ? NOP maINH I) @
(* [0x187C] 5clk *) (compile m ? BRSETn (maDIRn_and_IMM1 o7 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x187F] 1clk *) (compile m ? NOP maINH I) @

(* [0x1880] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o0 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1883] 1clk *) (compile m ? NOP maINH I) @
(* [0x1884] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o1 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1887] 1clk *) (compile m ? NOP maINH I) @
(* [0x1888] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o2 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x188B] 1clk *) (compile m ? NOP maINH I) @
(* [0x188C] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o3 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x188F] 1clk *) (compile m ? NOP maINH I) @
(* [0x1890] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o4 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1893] 1clk *) (compile m ? NOP maINH I) @
(* [0x1894] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o5 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x1897] 1clk *) (compile m ? NOP maINH I) @
(* [0x1898] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o6 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x189B] 1clk *) (compile m ? NOP maINH I) @
(* [0x189C] 5clk *) (compile m ? BRCLRn (maDIRn_and_IMM1 o7 〈xC,x5〉 〈x0,x1〉) I) @
(* [0x189F] 1clk *) (compile m ? NOP maINH I)

(* [0x18A0] si puo' quindi enunciare che dopo 80+8=88 clk
            (vengono eseguiti 16*5 test, meta' BRSETn/BRCLRn saltano *) 
(*          PC<-0x18A0 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_HCS08_BRSETn_BRCLRn_status ≝
λt:memory_impl.
 set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
  (start_of_mcu_version
   MC9S08AW60 t
   (load_from_source_at t
    (load_from_source_at t (zero_memory t) (* carica mTest_bytes in RAM:mTest_HCS08_RAM *)
      mTest_HCS08_BRSETn_BRCLRn_source mTest_HCS08_prog) (* carica source in ROM:mTest_HCS08_prog *)
     mTest_bytes mTest_HCS08_RAM)
   (build_memory_type_of_mcu_version MC9S08AW60 t)
   (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
   false false false false false false) (* non deterministici tutti a 0 *)
  mTest_HCS08_prog.

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_HCS08_BRSETn_BRCLRn_full :
 ∀t:memory_impl.
 execute HCS08 t (TickOK ? (mTest_HCS08_BRSETn_BRCLRn_status t)) 88 =
 TickOK ? (set_pc_reg HCS08 t (mTest_HCS08_BRSETn_BRCLRn_status t) (* nuovo PC *)
           (mk_word16 〈x1,x8〉 〈xA,x0〉)).
 intro;
 elim t;
 reflexivity.
qed.

(* *************** *)
(* RS08 X,D[X],TNY *)
(* *************** *)

(* testa la logica RS08 X,D[X] le modalita' TNY *)
(* NB: il meccanismo utilizzato e' quello complesso dell'RS08
       fare riferimento alle spiegazioni in STATUS/LOAD_WRITE *)
definition mTest_RS08_TNY_source: list byte8 ≝
let m ≝ RS08 in source_to_byte8 m (
(* X=20 PS=0 *)
(* [0x3800] 3clk *) (compile m ? ADD (maTNY xD) I) @ (* ... +[0x000D]=0x0C *)
(* [0x3801] 3clk *) (compile m ? ADD (maTNY xE) I) @ (* ... +D[X]=[0x0020]=0x1F *)
(* [0x3802] 3clk *) (compile m ? ADD (maTNY xF) I) @ (* ... +X=0x20 *)
(* [0x3803] 3clk *) (compile m ? ADD (maDIR1 〈xC,xF〉) I) @ (* ... +X=0x20 *)
(* [0x3805] 3clk *) (compile m ? ADD (maDIR1 〈xC,xE〉) I) (* ... +[0x000E]=0x0D *)
(* [0x3807] si puo' quindi enunciare che dopo 15 clk
            A<-0x78 PC<-0x3807 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_RS08_TNY_status ≝
λt:memory_impl.
 setweak_x_map RS08 t (* X<-0x20 *)
 (setweak_ps_map RS08 t (* PS<-0x00 *)
 (set_pc_reg RS08 t (* PC<-mTest_RS08_prog *)
  (start_of_mcu_version 
   MC9RS08KA2 t
   (load_from_source_at t (* carica mTest_bytes in RAM:mTest_RS08_RAM *)
    (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_RS08_prog *)
     mTest_RS08_TNY_source mTest_RS08_prog)
    mTest_bytes 〈〈x0,x0〉:〈x0,x1〉〉)
   (build_memory_type_of_mcu_version MC9RS08KA2 t)
   (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
   false false false false false false (* non deterministici tutti a 0 *)
   ) mTest_RS08_prog)
  (mk_byte8 x0 x0))
  (mk_byte8 x2 x0).

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_RS08_TNY_full :
 ∀t:memory_impl.
 execute RS08 t (TickOK ? (mTest_RS08_TNY_status t)) 15 =
 TickOK ? (set_acc_8_low_reg RS08 t (* nuovo A *)
           (set_pc_reg RS08 t (mTest_RS08_TNY_status t) (* nuovo PC *)
            (mk_word16 〈x3,x8〉 〈x0,x7〉))
             (mk_byte8 x7 x8)).
 intro;
 elim t;
 reflexivity.
qed.

(* *********** *)
(* RS08 PS,SRT *)
(* *********** *)

(* testa la logica RS08 PS le modalita' SRT *)
(* NB: il meccanismo utilizzato e' quello complesso dell'RS08
       fare riferimento alle spiegazioni in STATUS/LOAD_WRITE *)
definition mTest_RS08_SRT_source: list byte8 ≝
let m ≝ RS08 in source_to_byte8 m (
(* X=0x1F PS=0xFE Z=1 *)
(* [0x3800] 3clk *) (compile m ? LDA (maSRT t1F) I) @ (* A<-PS *)
(* [0x3801] 2clk *) (compile m ? SUB (maIMM1 〈xF,xE〉) I) @ (* risulta 0 *)
(* [0x3803] 3clk *) (compile m ? BEQ (maIMM1 〈x0,x1〉) I) @ (* salta *)
(* [0x3805] 1clk *) (compile m ? NOP maINH I) @

(* [0x3806] 3clk *) (compile m ? LDA (maSRT t0E) I) @ (* A<-PS *)
(* [0x3807] 2clk *) (compile m ? SUB (maIMM1 〈xF,xE〉) I) @ (* risulta 0 *)
(* [0x3809] 3clk *) (compile m ? BEQ (maIMM1 〈x0,x1〉) I) @ (* salta *)
(* [0x380B] 1clk *) (compile m ? NOP maINH I) @

(* [0x380C] 3clk *) (compile m ? LDA (maDIR1 〈xC,x3〉) I) @ (* A<-[0x00C3]=[0x3F83]=0x83 *)
(* [0x380E] 2clk *) (compile m ? SUB (maIMM1 〈x8,x3〉) I) @ (* risulta 0 *)
(* [0x3810] 3clk *) (compile m ? BEQ (maIMM1 〈x0,x1〉) I) @ (* salta *)
(* [0x3812] 1clk *) (compile m ? NOP maINH I)
(* [0x3813] si puo' quindi enunciare che dopo 24 clk
            PC<-0x3813 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_RS08_SRT_status ≝
λt:memory_impl.
 setweak_x_map RS08 t (* X<-0x1F *)
  (setweak_ps_map RS08 t (* PS<-0xFE *)
   (set_z_flag RS08 t (* Z<-true *)
    (set_pc_reg RS08 t (* PC<-mTest_RS08_prog *)
     (start_of_mcu_version 
      MC9RS08KA2 t
       (load_from_source_at t (* carica mTest_bytes in ROM:mTest_RS08_data *)
        (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_RS08_prog *)
         mTest_RS08_SRT_source mTest_RS08_prog)
        mTest_bytes mTest_RS08_data)
       (build_memory_type_of_mcu_version MC9RS08KA2 t)
      (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
      false false false false false false (* non deterministici tutti a 0 *)
      ) mTest_RS08_prog)
     true)
    (mk_byte8 xF xE))
   (mk_byte8 x1 xF).

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_RS08_SRT_full :
 ∀t:memory_impl.
 execute RS08 t (TickOK ? (mTest_RS08_SRT_status t)) 24 =
 TickOK ? (set_pc_reg RS08 t (mTest_RS08_SRT_status t) (* nuovo PC *)
           (mk_word16 〈x3,x8〉 〈x1,x3〉)).
 intro;
 elim t;
 reflexivity.
qed.

(* ********************* *)
(* TEOREMA MULT PER RS08 *)
(* ********************* *)

(* 
   ZH:ZL=X*Y con [0x0020-0x004F] X ≝ [0x0020] Y ≝ [0x0021] ZH ≝ [0x0022] ZL ≝ [0x0023]
*)
definition mTest_RS08_mult_source: list byte8 ≝
let m ≝ RS08 in source_to_byte8 m (
(* [0x3800] ZH <- 0      3clk *) (compile m ? CLR (maDIR1 〈x2,x2〉) I) @
(* [0x3802] ZL <- 0      3clk *) (compile m ? CLR (maDIR1 〈x2,x3〉) I) @
(* [0x3804] (l1) A <- Y  3clk *) (compile m ? LDA (maDIR1 〈x2,x1〉) I) @
(* [0x3806] A=0 goto l2  3clk *) (compile m ? BEQ (maIMM1 〈x0,xE〉) I) @
(* [0x3808] A <- ZL      3clk *) (compile m ? LDA (maDIR1 〈x2,x3〉) I) @
(* [0x380A] Y --         5clk *) (compile m ? DEC (maDIR1 〈x2,x1〉) I) @
(* [0x380C] A += X       3clk *) (compile m ? ADD (maDIR1 〈x2,x0〉) I) @
(* [0x380E] C=0 goto l3  3clk *) (compile m ? BCC (maIMM1 〈x0,x2〉) I) @
(* [0x3810] ZH ++        5clk *) (compile m ? INC (maDIR1 〈x2,x2〉) I) @
(* [0x3812] (l3) ZL <- A 3clk *) (compile m ? STA (maDIR1 〈x2,x3〉) I) @
(* [0x3814] goto l1      3clk *) (compile m ? BRA (maIMM1 〈xE,xE〉) I)
(* [0x3816] (l2) si puo' quindi enunciare che
                 - il caso base X * 0 richiede 12 cicli
                 - bisogna aggiungere Y * 26 cicli, Y>0
                 - bisogna aggiungere ZH * 5 cicli, X * Y > 0xFF *)
).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_RS08_mult_status ≝
λt:memory_impl.
λb1,b2,b3,b4:byte8.
 set_z_flag RS08 t (* Z<-true *)
 (set_pc_reg RS08 t (* PC<-mTest_RS08_prog *)
  (start_of_mcu_version 
   MC9RS08KA2 t
   (load_from_source_at t (* carica X,Y,ZH,ZL:mTest_RS08_RAM *)
    (load_from_source_at t (zero_memory t) (* carica source in ROM:mTest_RS08_prog *)
     mTest_RS08_mult_source mTest_RS08_prog)
    [ b1 ; b2 ; b3 ; b4 ] mTest_RS08_RAM)
   (build_memory_type_of_mcu_version MC9RS08KA2 t)
   (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
   false false false false false false (* non deterministici tutti a 0 *)
   ) mTest_RS08_prog)
  true.

(* parametrizzazione dell'enunciato del teorema mult *)
lemma ok_mTest_RS08_mult_full_aux ≝
 λt:memory_impl.
 λX,Y:byte8.
 match execute RS08 t
       (TickOK ? (mTest_RS08_mult_status t X Y 〈x0,x0〉 〈x0,x0〉))
       (12 +
        (26 * (nat_of_byte8 Y)) +
        (5 * (nat_of_byte8 (w16h (mul_b8 X Y))))) with
  (* controllo che coincidano ALU,ZH,ZL *)
  [ TickERR s _ ⇒ s
  | TickSUSP s _ ⇒ s
  (* FIXME: alla ALU azzero C perche' la funzione che ne
            descrive il valore finale e' MOLTO complessa *)
  | TickOK s ⇒ set_c_flag RS08 t s false ] =
 (* alla fine per come e' scritto il programma: A=0 Z=true *)
 set_pc_reg RS08 t (mTest_RS08_mult_status t X 〈x0,x0〉 (w16h (mul_b8 X Y)) (w16l (mul_b8 X Y)))
  (mk_word16 〈x3,x8〉 〈x1,x6〉).

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_RS08_mult_full : 
 ∀t:memory_impl.
  ok_mTest_RS08_mult_full_aux t 〈xF,xF〉 〈x1,xE〉.
 unfold ok_mTest_RS08_mult_full_aux;
 intro;
 elim t;
 [ apply (eq_status_axiom mTest_RS08_RAM 3 RS08 MEM_FUNC); reflexivity ]
 reflexivity.
qed.

(* ************************ *)
(* TEST SU GRANULARITA' BIT *)
(* ************************ *)

definition mTest_bits_source : list byte8 ≝
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: va a testare [0x0070]=0x00 *)
(* [0x1860] 4clk *) (compile m ? MOV (maIMM1_to_DIR1 〈xF,xF〉 〈x7,x0〉) I)
(* [0x1863] *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition mTest_bits_status ≝
λt:memory_impl.
λsub:oct.
λb:byte8.
 setweak_n_flag HCS08 t (* N<-1 *)
  (set_pc_reg HCS08 t (* PC<-mTest_HCS08_prog *)
   (start_of_mcu_version
    MC9S08AW60 t
    (load_from_source_at t
     (load_from_source_at t (zero_memory t) (* carica b in RAM:mTest_HCS08_RAM *)
       mTest_bits_source mTest_HCS08_prog) (* carica source in ROM:mTest_HCS08_prog *)
      [ b ] mTest_HCS08_RAM)
    (check_update_bit t (* setta mTest_HCS08_RAM,o come ROM *)
     (build_memory_type_of_mcu_version MC9S08AW60 t)
     mTest_HCS08_RAM sub MEM_READ_ONLY)
    (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
    false false false false false false) (* non deterministici tutti a 0 *)
   mTest_HCS08_prog)
  true.

(* dimostrazione senza svolgimento degli stati, immediata *)
lemma ok_mTest_bits_MEM_BITS_full :
 ∀sub:oct.
 execute HCS08 MEM_BITS (TickOK ? (mTest_bits_status MEM_BITS sub 〈x0,x0〉)) 4 =
 TickOK ? (set_pc_reg HCS08 MEM_BITS (mTest_bits_status MEM_BITS sub (byte8_of_bits (setn_array8T sub ? (bits_of_byte8 〈xF,xF〉) false))) (* nuovo PC *)
           (mk_word16 〈x1,x8〉 〈x6,x3〉)).
 intro;
 elim sub;
 reflexivity.
qed.

lemma ok_mTest_bits_NO_MEM_BITS_full :
 ∀sub:oct.
 (match execute HCS08 MEM_FUNC (TickOK ? (mTest_bits_status MEM_FUNC sub 〈x0,x0〉)) 4 with
  [ TickERR s _ ⇒ s | TickSUSP s _ ⇒ s | TickOK s ⇒ s ] =
 set_pc_reg HCS08 MEM_FUNC (mTest_bits_status MEM_FUNC sub 〈xF,xF〉) (* nuovo PC *)
           (mk_word16 〈x1,x8〉 〈x6,x3〉)) ∧
 (match execute HCS08 MEM_TREE (TickOK ? (mTest_bits_status MEM_TREE sub 〈x0,x0〉)) 4 with
  [ TickERR s _ ⇒ s | TickSUSP s _ ⇒ s | TickOK s ⇒ s ] =
 set_pc_reg HCS08 MEM_TREE (mTest_bits_status MEM_TREE sub 〈xF,xF〉) (* nuovo PC *)
           (mk_word16 〈x1,x8〉 〈x6,x3〉)).
 intro;
 elim sub;
 split;
 [ 1,3,5,7,9,11,13,15:
   apply (eq_status_axiom mTest_HCS08_RAM 0 HCS08 MEM_FUNC); reflexivity; ]
   apply (eq_status_axiom mTest_HCS08_RAM 0 HCS08 MEM_TREE); reflexivity;
qed.

(* svolgimento degli stati passo passo: esempio 

 letin BEFORE ≝ ...

 letin AFTER_ALU1 ≝ (match execute RS08 (TickOK ? BEFORE) 3 with
  [ TickERR _ _ ⇒ get_alu RS08 BEFORE 
  | TickSUSP _ _ ⇒ get_alu RS08 BEFORE 
  | TickOK s ⇒ get_alu RS08 s ]);
 normalize in AFTER_ALU1:(%);

 letin AFTER_ALU2 ≝ (match execute RS08 (TickOK ? 
                     (set_alu RS08 BEFORE AFTER_ALU1)) 3 with
  [ TickERR _ _ ⇒ get_alu RS08 BEFORE 
  | TickSUSP _ _ ⇒ get_alu RS08 BEFORE 
  | TickOK s ⇒ get_alu RS08 s ]);
 normalize in AFTER_ALU2:(%); 
 clearbody AFTER_ALU1;

 ...

 letin AFTER_ALU6 ≝ (match execute RS08 (TickOK ? 
                     (set_alu RS08 BEFORE AFTER_ALU5)) 5 with
  [ TickERR _ _ ⇒ get_alu RS08 BEFORE 
  | TickSUSP _ _ ⇒ get_alu RS08 BEFORE 
  | TickOK s ⇒ get_alu RS08 s ]);
 letin Y6 ≝ (match execute RS08 (TickOK ? 
             (set_alu RS08 BEFORE AFTER_ALU5)) 5
  return λ_.byte8 with
  [ TickERR _ _ ⇒ (get_mem_desc RS08 BEFORE) 〈〈x0,x0〉:〈x2,x1〉〉
  | TickSUSP _ _ ⇒ (get_mem_desc RS08 BEFORE) 〈〈x0,x0〉:〈x2,x1〉〉
  | TickOK s ⇒ (get_mem_desc RS08 s) 〈〈x0,x0〉:〈x2,x1〉〉 ]);
 normalize in AFTER_ALU6:(%); 
 normalize in Y6:(%); 
 clearbody AFTER_ALU5;

 letin AFTER_ALU7 ≝ (match execute RS08 (TickOK ? 
                     (set_mem_desc RS08 
                      (set_alu RS08 BEFORE AFTER_ALU6)
                       (load_from_source_at (get_mem_desc RS08 BEFORE)
                        (mTest_RS08_mult_load 〈xF,xF〉 Y6 〈x0,x0〉 〈x0,x0〉) mTest_RS08_RAM) 
                     )) 3 with
  [ TickERR _ _ ⇒ get_alu RS08 BEFORE 
  | TickSUSP _ _ ⇒ get_alu RS08 BEFORE 
  | TickOK s ⇒ get_alu RS08 s ]);
 normalize in AFTER_ALU7:(%); 
 clearbody AFTER_ALU6;

 ...
*)
