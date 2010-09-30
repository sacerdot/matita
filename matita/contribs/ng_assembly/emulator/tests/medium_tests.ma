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

include "emulator/tests/medium_tests_tools.ma".
include "common/list_utility.ma".
include "common/nat_to_num.ma".
include "emulator/model/model.ma".

(* ************************ *)
(* HCS08GB60 String Reverse *)
(* ************************ *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
ndefinition dTest_HCS08_sReverse_source : word16 → (list byte8) ≝
λelems:word16.source_to_byte8 HCS08 (
(* BEFORE: A=0x00 H:X=0x0D4B SP=0x0D4A PC=0x18E0 Z=true *)

(* static unsigned char dati[3072]={...};

   void swap(unsigned char *a, unsigned char *b)
    { unsigned char tmp=*a; *a=*b; *b=tmp; return; } *)

(* [0x18C8]    allineamento *) (compile HCS08 ? NOP maINH ?) @

(* argomenti: HX e [0x0D49-A], passaggio ibrido reg, stack *)
(* [0x18C9] PSHX      *) (compile HCS08 ? PSHX maINH ?) @
(* [0x18CA] PSHH      *) (compile HCS08 ? PSHH maINH ?) @
(* [0x18CB] LDHX 5,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,x5〉) ?) @
(* [0x18CE] LDA ,X    *) (compile HCS08 ? LDA maIX0 ?) @
(* [0x18CF] LDHX 1,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x18D2] PSHA      *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18D3] LDA ,X    *) (compile HCS08 ? LDA maIX0 ?) @
(* [0x18D4] LDHX 6,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,x6〉) ?) @
(* [0x18D7] STA ,X    *) (compile HCS08 ? STA maIX0 ?) @
(* [0x18D8] LDHX 2,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,x2〉) ?) @
(* [0x18DB] PULA      *) (compile HCS08 ? PULA maINH ?) @
(* [0x18DC] STA ,X    *) (compile HCS08 ? STA maIX0 ?) @
(* [0x18DD] AIS #2    *) (compile HCS08 ? AIS (maIMM1 〈x0,x2〉) ?) @
(* [0x18DF] RTS       *) (compile HCS08 ? RTS maINH ?) @

(* void main(void)
   {
   unsigned int pos=0,limit=0;
 
   for(limit=3072;pos<(limit/2);pos++)
    { swap(&dati[pos],&dati[limit-pos-1]); } *)

(* [0x18E0] LDHX #elems     *) (compile HCS08 ? LDHX (maIMM2 elems) ?) @
(* [0x18E3] STHX 4,SP       *) (compile HCS08 ? STHX (maSP1 〈x0,x4〉) ?) @
(* [0x18E6] BRA *+52 ; 191A *) (compile HCS08 ? BRA (maIMM1 〈x3,x2〉) ?) @
(* [0x18E8] TSX             *) (compile HCS08 ? TSX maINH ?) @
(* [0x18E9] LDA 2,X         *) (compile HCS08 ? LDA (maIX1 〈x0,x2〉) ?) @
(* [0x18EB] ADD #0x00       *) (compile HCS08 ? ADD (maIMM1 〈x0,x0〉) ?) @
(* [0x18ED] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18EE] LDA 1,X         *) (compile HCS08 ? LDA (maIX1 〈x0,x1〉) ?) @
(* [0x18F0] ADC #0x01       *) (compile HCS08 ? ADC (maIMM1 〈x0,x1〉) ?) @
(* [0x18F2] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18F3] LDA 4,X         *) (compile HCS08 ? LDA (maIX1 〈x0,x4〉) ?) @
(* [0x18F5] SUB 2,X         *) (compile HCS08 ? SUB (maIX1 〈x0,x2〉) ?) @
(* [0x18F7] STA ,X          *) (compile HCS08 ? STA maIX0 ?) @
(* [0x18F8] LDA 3,X         *) (compile HCS08 ? LDA (maIX1 〈x0,x3〉) ?) @
(* [0x18FA] SBC 1,X         *) (compile HCS08 ? SBC (maIX1 〈x0,x1〉) ?) @
(* [0x18FC] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18FD] LDX ,X          *) (compile HCS08 ? LDX maIX0 ?) @
(* [0x18FE] PULH            *) (compile HCS08 ? PULH maINH ?) @
(* [0x18FF] AIX #-1         *) (compile HCS08 ? AIX (maIMM1 〈xF,xF〉) ?) @
(* [0x1901] TXA             *) (compile HCS08 ? TXA maINH ?) @
(* [0x1902] ADD #0x00       *) (compile HCS08 ? ADD (maIMM1 〈x0,x0〉) ?) @
(* [0x1904] PSHH            *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1905] TSX             *) (compile HCS08 ? TSX maINH ?) @
(* [0x1906] STA 3,X         *) (compile HCS08 ? STA (maIX1 〈x0,x3〉) ?) @
(* [0x1908] PULA            *) (compile HCS08 ? PULA maINH ?) @
(* [0x1909] ADC #0x01       *) (compile HCS08 ? ADC (maIMM1 〈x0,x1〉) ?) @
(* [0x190B] LDX 3,X         *) (compile HCS08 ? LDX (maIX1 〈x0,x3〉) ?) @
(* [0x190D] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x190E] PULH            *) (compile HCS08 ? PULH maINH ?) @
(* [0x190F] BSR *-70 ; 18C9 *) (compile HCS08 ? BSR (maIMM1 〈xB,x8〉) ?) @
(* [0x1911] AIS #2          *) (compile HCS08 ? AIS (maIMM1 〈x0,x2〉) ?) @
(* [0x1913] TSX             *) (compile HCS08 ? TSX maINH ?) @
(* [0x1914] INC 2,X         *) (compile HCS08 ? INC (maIX1 〈x0,x2〉) ?) @
(* [0x1916] BNE *+4 ; 191A  *) (compile HCS08 ? BNE (maIMM1 〈x0,x2〉) ?) @
(* [0x1918] INC 1,X         *) (compile HCS08 ? INC (maIX1 〈x0,x1〉) ?) @
(* [0x191A] TSX             *) (compile HCS08 ? TSX maINH ?) @
(* [0x191B] LDA 3,X         *) (compile HCS08 ? LDA (maIX1 〈x0,x3〉) ?) @
(* [0x191D] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x191E] PULH            *) (compile HCS08 ? PULH maINH ?) @
(* [0x191F] LSRA            *) (compile HCS08 ? LSR maINHA ?) @
(* [0x1920] TSX             *) (compile HCS08 ? TSX maINH ?) @
(* [0x1921] LDX 4,X         *) (compile HCS08 ? LDX (maIX1 〈x0,x4〉) ?) @
(* [0x1923] RORX            *) (compile HCS08 ? ROR maINHX ?) @
(* [0x1924] PSHA            *) (compile HCS08 ? PSHA maINH ?) @
(* [0x1925] PULH            *) (compile HCS08 ? PULH maINH ?) @
(* [0x1926] CPHX 2,SP       *) (compile HCS08 ? CPHX (maSP1 〈x0,x2〉) ?) @
(* [0x1929] BHI *-65 ; 18E8 *) (compile HCS08 ? BHI (maIMM1 〈xB,xD〉) ?)

(* [0x192B] !FINE!
            attraverso simulazione in CodeWarrior si puo' enunciare che dopo
            42+79*n+5*(n>>9) ci sara' il reverse di n byte (PARI) e
            H:X=n/2 *)
 ). napply I. nqed.

(* creazione del processore+caricamento+impostazione registri *)
ndefinition dTest_HCS08_sReverse_status ≝
λt:memory_impl.
λA_op:byte8.
λHX_op:word16.
λelems:word16.
λdata:list byte8.
 set_acc_8_low_reg HCS08 t (* A<-A_op *)
 (set_z_flag HCS08 t (* Z<-true *)
  (setweak_sp_reg HCS08 t (* SP<-0x0D4A *)
   (setweak_indX_16_reg HCS08 t (* H:X<-HX_op *)
    (set_pc_reg HCS08 t (* PC<-0x18E0 *)
     (start_of_model HCS08 MC9S08GB60 t
      (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
       (load_from_source_at t (zero_memory t) (* carica source in ROM:dTest_HCS08_prog *)
         (dTest_HCS08_sReverse_source elems) (extu_w32 dTest_HCS08_prog))
        data (extu_w32 dTest_HCS08_RAM))
      (build_memory_type_of_model HCS08 MC9S08GB60 t)
      (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
      false false false false false false) (* non deterministici tutti a 0 *)
     (mk_word16 (mk_byte8 x1 x8) (mk_byte8 xE x0)))
    HX_op)
   (mk_word16 (mk_byte8 x0 xD) (mk_byte8 x4 xA)))
  true)
 A_op.

(* parametrizzazione dell'enunciato del teorema *)
(* primo sbozzo: confronto esecuzione con hexdump... *)
nlemma dTest_HCS08_sReverse_dump_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) la stringa deve avere lunghezza pari *)
 ((and_b8 (cnL ? (byte8_strlen string)) 〈x0,x1〉) = 〈x0,x0〉) ∧
 (* 3) match di esecuzione su tempo in forma di tempo esatto *)
 (match execute HCS08 t
  (* parametri IN: t,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_sReverse_status t 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 42+79*n+5*(n>>9) *)
  (nat42 + (nat79 * (len_list ? string))+(nat5 * ((len_list ? string) / nat512))) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (byte8_hexdump t (mem_desc HCS08 t s) (extu_w32 dTest_HCS08_RAM) (len_list ? string))
   ] =
  Some ? (reverse_list ? string)).

(* confronto esecuzione con hexdump... *)
(*
lemma dTest_HCS08_sReverse_dump :
 dTest_HCS08_sReverse_dump_aux MEM_TREE dTest_random_32.
 unfold dTest_HCS08_sReverse_dump_aux;
 split;
 [ split; [ normalize in ⊢ (%); autobatch ] reflexivity ]
 reflexivity.
qed.
*)

(* parametrizzazione dell'enunciato del teorema *)
(* dimostrazione senza svolgimento degli stati *)
nlemma dTest_HCS08_sReverse_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) la stringa deve avere lunghezza pari *)
 ((and_b8 (cnL ? (byte8_strlen string)) 〈x0,x1〉) = 〈x0,x0〉) ∧
 (* 3) match di esecuzione su tempo in forma di tempo esatto *)
 (match execute HCS08 t
  (* parametri IN: t,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_sReverse_status t 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 42+79*n+5*(n>>9) *)
  (nat42 + (nat79 * (len_list ? string))+(nat5 * ((len_list ? string) / nat512))) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (mem_desc HCS08 t s) dTest_zeros (extu_w32 〈〈x0,xD〉:〈x0,x0〉〉)))
   ] =
  Some ? (set_pc_reg HCS08 t
   (dTest_HCS08_sReverse_status t (snd … (shr_b8 (cnH ? (byte8_strlen string)))) (snd … (shr_w16 (byte8_strlen string))) (byte8_strlen string) (reverse_list ? string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x2 xB)))).

(*
lemma dTest_HCS08_sReverse :
 dTest_HCS08_sReverse_aux MEM_TREE dTest_random_32.
 unfold dTest_HCS08_sReverse_aux;
 split;
 [ split; [ normalize in ⊢ (%); autobatch ] reflexivity ]

 rewrite > (breakpoint HCS08 MEM_TREE (TickOK ? (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉   (byte8_strlen dTest_random_32) dTest_random_32)) 3 (39+79*byte8_strlen dTest_random_32+5*(byte8_strlen dTest_random_32/512))) in ⊢ (? ? match % in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?);
 letin status0 ≝ (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen dTest_random_32) dTest_random_32);
 change in ⊢ (? ? match ? ? ? (? ? ? % ?) ? in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?) with
  (TickOK ? status0); 
 rewrite > (execute_HCS08_LDHX_maIMM2 MEM_TREE status0 〈x0,x0〉 〈x2,x0〉) in ⊢ (? ? match ? ? ? % ? in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?);
 [ 2,3,4,5: reflexivity; ]

 letin status1 ≝ (set_pc_reg HCS08 MEM_TREE (setweak_v_flag HCS08 MEM_TREE (setweak_n_flag HCS08 MEM_TREE (set_z_flag HCS08 MEM_TREE (set_alu HCS08 MEM_TREE (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen dTest_random_32) dTest_random_32) (set_indX_16_reg_HC08 (alu HCS08 MEM_TREE (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen dTest_random_32) dTest_random_32)) 〈〈x0,x0〉:〈x2,x0〉〉)) (eq_w16 〈〈x0,x0〉:〈x2,x0〉〉 〈〈x0,x0〉:〈x0,x0〉〉)) (MSB_w16 〈〈x0,x0〉:〈x2,x0〉〉)) false) (filtered_plus_w16 HCS08 MEM_TREE (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen dTest_random_32) dTest_random_32) (get_pc_reg HCS08 MEM_TREE (dTest_HCS08_sReverse_status MEM_TREE 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen dTest_random_32) dTest_random_32)) 3));
 change in ⊢ (? ? match ? ? ? % ? in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?) with (TickOK ? status1);

 rewrite > (breakpoint HCS08 MEM_TREE (TickOK ? status1) 5 (34+79*byte8_strlen dTest_random_32+5*(byte8_strlen dTest_random_32/512))) in ⊢ (? ? match % in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?);
 change in ⊢ (? ? match ? ? ? (? ? ? % ?) ? in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?) with (TickOK ? status1);
 rewrite > (execute_HCS08_STHX_maSP1 status1 〈x0,x4〉)
  in ⊢ (? ? match ? ? ? % ? in tick_result return ? with [TickERR⇒?|TickSUSP⇒?|TickOK⇒?] ?);
 [ 2,3,4,5,6,7: reflexivity; ]

 elim daemon.

qed.
*)

ndefinition sReverseCalc ≝
λstring:list byte8.
 match execute HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_sReverse_status MEM_TREE 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (nat42 + (nat79 * (len_list ? string))+(nat5 * ((len_list ? string) / nat512))) with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (mem_desc HCS08 MEM_TREE s) dTest_zeros (extu_w32 〈〈x0,xD〉:〈x0,x0〉〉)))
   ]. 

ndefinition sReverseNoCalc ≝
λstring:list byte8.
 Some ? (set_pc_reg HCS08 MEM_TREE
   (dTest_HCS08_sReverse_status MEM_TREE (snd … (shr_b8 (cnH ? (byte8_strlen string))))
                                         (snd … (shr_w16 (byte8_strlen string)))
                                         (byte8_strlen string) (reverse_list ? string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x2 xB))).

ndefinition sReverseCalc32   ≝ sReverseCalc dTest_random_32.
ndefinition sReverseCalc64   ≝ sReverseCalc dTest_random_64.
ndefinition sReverseCalc128  ≝ sReverseCalc dTest_random_128.
ndefinition sReverseCalc256  ≝ sReverseCalc dTest_random_256.
ndefinition sReverseCalc512  ≝ sReverseCalc dTest_random_512.
ndefinition sReverseCalc1024 ≝ sReverseCalc dTest_random_1024.
ndefinition sReverseCalc2048 ≝ sReverseCalc dTest_random_2048.
ndefinition sReverseCalc3072 ≝ sReverseCalc dTest_random_3072.

ndefinition sReverseNoCalc32   ≝ sReverseNoCalc dTest_random_32.
ndefinition sReverseNoCalc64   ≝ sReverseNoCalc dTest_random_64.
ndefinition sReverseNoCalc128  ≝ sReverseNoCalc dTest_random_128.
ndefinition sReverseNoCalc256  ≝ sReverseNoCalc dTest_random_256.
ndefinition sReverseNoCalc512  ≝ sReverseNoCalc dTest_random_512.
ndefinition sReverseNoCalc1024 ≝ sReverseNoCalc dTest_random_1024.
ndefinition sReverseNoCalc2048 ≝ sReverseNoCalc dTest_random_2048.
ndefinition sReverseNoCalc3072 ≝ sReverseNoCalc dTest_random_3072.

(* *********************** *)
(* HCS08GB60 Counting Sort *)
(* *********************** *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
ndefinition dTest_HCS08_cSort_source : word16 → (list byte8) ≝
λelems:word16.source_to_byte8 HCS08 (
(* BEFORE: A=0x00 H:X=0x0F4C SP=0x0F4B PC=0x18C8 Z=true *)

(* /* IPOTESI: INIT VARIABILI+ARRAY GIA' ESEGUITO */
   static unsigned int counters[256]={ campitura di 0 };
   static unsigned char dati[3072]={ dati random };

   void CountingSort(void)
    {
    unsigned int index=0,position=0; *)

(* /* TESI: CODICE DA ESEGUIRE

    /* calcolo del # ripetizioni degli elementi byte */
    for(;index<3072;index++)
     { counters[dati[index]]++; } *)

(* [0x18C8] BRA *+31;18E7 *) (compile HCS08 ? BRA (maIMM1 〈x1,xD〉) ?) @
(* [0x18CA] LDHX 1,SP     *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x18CD] LDA 256,X     *) (compile HCS08 ? LDA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) ?) @
(* [0x18D0] LSLA          *) (compile HCS08 ? ASL maINHA ?) @
(* [0x18D1] CLRX          *) (compile HCS08 ? CLR maINHX ?) @
(* [0x18D2] ROLX          *) (compile HCS08 ? ROL maINHX ?) @
(* [0x18D3] ADD #0x00     *) (compile HCS08 ? ADD (maIMM1 〈x0,x0〉) ?) @
(* [0x18D5] PSHA          *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18D6] TXA           *) (compile HCS08 ? TXA maINH ?) @
(* [0x18D7] ADC #0x0D     *) (compile HCS08 ? ADC (maIMM1 〈x0,xD〉) ?) @
(* [0x18D9] PSHA          *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18DA] PULH          *) (compile HCS08 ? PULH maINH ?) @
(* [0x18DB] PULX          *) (compile HCS08 ? PULX maINH ?) @
(* [0x18DC] INC 1,X       *) (compile HCS08 ? INC (maIX1 〈x0,x1〉) ?) @
(* [0x18DE] BNE *+3       *) (compile HCS08 ? BNE (maIMM1 〈x0,x1〉) ?) @
(* [0x18E0] INC ,X        *) (compile HCS08 ? INC maIX0 ?) @
(* [0x18E1] TSX           *) (compile HCS08 ? TSX maINH ?) @
(* [0x18E2] INC 1,X       *) (compile HCS08 ? INC (maIX1 〈x0,x1〉) ?) @
(* [0x18E4] BNE *+3       *) (compile HCS08 ? BNE (maIMM1 〈x0,x1〉) ?) @
(* [0x18E6] INC ,X        *) (compile HCS08 ? INC maIX0 ?) @
(* [0x18E7] LDHX 1,SP     *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x18EA] CPHX #elems   *) (compile HCS08 ? CPHX (maIMM2 elems) ?) @ (* dimensione dei dati al massimo 0x0C00 *)
(* [0x18ED] BCS *-35;18CA *) (compile HCS08 ? BCS (maIMM1 〈xD,xB〉) ?) @

(* /* sovrascrittura di dati per produrre la versione ordinata */
   for(index=0;index<256;index++)
    {
    while(counters[index]--)
     { dati[position++]=index; }
    } *)

(* [0x18EF] TSX          *) (compile HCS08 ? TSX maINH ?) @
(* [0x18F0] CLR 1,X      *) (compile HCS08 ? CLR (maIX1 〈x0,x1〉) ?) @
(* [0x18F2] CLR ,X       *) (compile HCS08 ? CLR maIX0 ?) @
(* [0x18F3] BRA *+16     *) (compile HCS08 ? BRA (maIMM1 〈x0,xE〉) ?) @
(* [0x18F5] TSX          *) (compile HCS08 ? TSX maINH ?) @
(* [0x18F6] LDA 1,X      *) (compile HCS08 ? LDA (maIX1 〈x0,x1〉) ?) @
(* [0x18F8] LDHX 3,SP    *) (compile HCS08 ? LDHX (maSP1 〈x0,x3〉) ?) @
(* [0x18FB] STA 256,X    *) (compile HCS08 ? STA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) ?) @
(* [0x18FE] AIX #1       *) (compile HCS08 ? AIX (maIMM1 〈x0,x1〉) ?) @
(* [0x1900] STHX 3,SP    *) (compile HCS08 ? STHX (maSP1 〈x0,x3〉) ?) @
(* [0x1903] TSX          *) (compile HCS08 ? TSX maINH ?) @
(* [0x1904] LDX 1,X      *) (compile HCS08 ? LDX (maIX1 〈x0,x1〉) ?) @
(* [0x1906] LSLX         *) (compile HCS08 ? ASL maINHX ?) @
(* [0x1907] LDA 1,SP     *) (compile HCS08 ? LDA (maSP1 〈x0,x1〉) ?) @
(* [0x190A] ROLA         *) (compile HCS08 ? ROL maINHA ?) @
(* [0x190B] PSHA         *) (compile HCS08 ? PSHA maINH ?) @
(* [0x190C] PULH         *) (compile HCS08 ? PULH maINH ?) @
(* [0x190D] PSHX         *) (compile HCS08 ? PSHX maINH ?) @
(* [0x190E] LDHX 3328,X  *) (compile HCS08 ? LDHX (maIX2 〈〈x0,xD〉:〈x0,x0〉〉) ?) @
(* [0x1912] PSHX         *) (compile HCS08 ? PSHX maINH ?) @
(* [0x1913] PSHH         *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1914] AIX #-1      *) (compile HCS08 ? AIX (maIMM1 〈xF,xF〉) ?) @
(* [0x1916] PSHH         *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1917] PSHA         *) (compile HCS08 ? PSHA maINH ?) @
(* [0x1918] PULH         *) (compile HCS08 ? PULH maINH ?) @
(* [0x1919] PSHX         *) (compile HCS08 ? PSHX maINH ?) @
(* [0x191A] LDX 5,SP     *) (compile HCS08 ? LDX (maSP1 〈x0,x5〉) ?) @
(* [0x191D] PULA         *) (compile HCS08 ? PULA maINH ?) @
(* [0x191E] STA 3329,X   *) (compile HCS08 ? STA (maIX2 〈〈x0,xD〉:〈x0,x1〉〉) ?) @
(* [0x1921] PULA         *) (compile HCS08 ? PULA maINH ?) @
(* [0x1922] STA 3328,X   *) (compile HCS08 ? STA (maIX2 〈〈x0,xD〉:〈x0,x0〉〉) ?) @
(* [0x1925] PULH         *) (compile HCS08 ? PULH maINH ?) @
(* [0x1926] PULX         *) (compile HCS08 ? PULX maINH ?) @
(* [0x1927] CPHX #0x0000 *) (compile HCS08 ? CPHX (maIMM2 〈〈x0,x0〉:〈x0,x0〉〉) ?) @
(* [0x192A] PULH         *) (compile HCS08 ? PULH maINH ?) @
(* [0x192B] BNE *-54     *) (compile HCS08 ? BNE (maIMM1 〈xC,x8〉) ?) @
(* [0x192D] TSX          *) (compile HCS08 ? TSX maINH ?) @
(* [0x192E] INC 1,X      *) (compile HCS08 ? INC (maIX1 〈x0,x1〉) ?) @
(* [0x1930] BNE *+3      *) (compile HCS08 ? BNE (maIMM1 〈x0,x1〉) ?) @
(* [0x1932] INC ,X       *) (compile HCS08 ? INC maIX0 ?) @
(* [0x1933] LDHX 1,SP    *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x1936] CPHX #0x0100 *) (compile HCS08 ? CPHX (maIMM2 〈〈x0,x1〉:〈x0,x0〉〉) ?) @
(* [0x1939] BNE *-54     *) (compile HCS08 ? BNE (maIMM1 〈xC,x8〉) ?) @
(* [0x193B] STOP         *) (compile HCS08 ? STOP maINH ?)

(* [0x193C] !FINE!
            attraverso simulazione in CodeWarrior si puo' enunciare che dopo
            25700+150n si sara' entrati in stato STOP corrispondente con ordinamento
            di n byte, A=0xFF H:X=0x0100 *)
 ). napply I. nqed.

(* creazione del processore+caricamento+impostazione registri *)
ndefinition dTest_HCS08_cSort_status ≝
λt:memory_impl.
λI_op:bool.
λA_op:byte8.
λHX_op:word16.
λelems:word16.
λdata:list byte8.
 setweak_i_flag HCS08 t (* I<-I_op *)
  (set_acc_8_low_reg HCS08 t (* A<-A_op *)
   (set_z_flag HCS08 t (* Z<-true *)
    (setweak_sp_reg HCS08 t (* SP<-0x0F4B *)
     (setweak_indX_16_reg HCS08 t (* H:X<-HX_op *)
      (set_pc_reg HCS08 t (* PC<-dTest_HCS08_prog *)
       (start_of_model HCS08 MC9S08GB60 t
        (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
         (load_from_source_at t (zero_memory t) (* carica source in ROM:dTest_HCS08_prog *)
           (dTest_HCS08_cSort_source elems) (extu_w32 dTest_HCS08_prog))
          data (extu_w32 dTest_HCS08_RAM))
        (build_memory_type_of_model HCS08 MC9S08GB60 t)
        (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
        false false false false false false) (* non deterministici tutti a 0 *)
       dTest_HCS08_prog)
      HX_op)
     (mk_word16 (mk_byte8 x0 xF) (mk_byte8 x4 xB)))
    true)
   A_op)
  I_op.

(* parametrizzazione dell'enunciato del teorema parziale *)
nlemma dTest_HCS08_cSort_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) match di esecuzione su tempo in forma di upperbound *)
 (match execute HCS08 t
  (* parametri IN: t,A,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_cSort_status t true 〈x0,x0〉 〈〈x0,xF〉:〈x4,xC〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 25700+150*n *)
  (((nat256 + nat1) * nat100)+((nat50 * nat3) * (len_list ? string))) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (mem_desc HCS08 t s) dTest_zeros (extu_w32 〈〈x0,xD〉:〈x0,x0〉〉)))
   | TickOK s ⇒ None ?
   ] =
  Some ? (set_pc_reg HCS08 t
   (dTest_HCS08_cSort_status t false 〈xF,xF〉 〈〈x0,x1〉:〈x0,x0〉〉 (byte8_strlen string) (byte8_list_ordering string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x3 xC)))).

(* dimostrazione senza svolgimento degli stati *)
(*
lemma dTest_HCS08_cSort :
 dTest_HCS08_cSort_aux MEM_TREE dTest_random_32.
 unfold dTest_HCS08_cSort_aux;
 split;
 [ normalize in ⊢ (%); autobatch ]
 reflexivity.
qed.
*)

ndefinition cSortCalc ≝
λstring:list byte8.
 match execute HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_cSort_status MEM_TREE true 〈x0,x0〉 〈〈x0,xF〉:〈x4,xC〉〉 (byte8_strlen string) string))
  (((nat256 + nat1) * nat100)+((nat50 * nat3) * (len_list ? string))) with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (mem_desc HCS08 MEM_TREE s) dTest_zeros (extu_w32 〈〈x0,xD〉:〈x0,x0〉〉)))
   | TickOK s ⇒ None ?
   ].

ndefinition cSortNoCalc ≝
λstring:list byte8.
 Some ? (set_pc_reg HCS08 MEM_TREE
   (dTest_HCS08_cSort_status MEM_TREE false 〈xF,xF〉 〈〈x0,x1〉:〈x0,x0〉〉 (byte8_strlen string) (byte8_list_ordering string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x3 xC))).

ndefinition cSortCalc32   ≝ cSortCalc dTest_random_32.
ndefinition cSortCalc64   ≝ cSortCalc dTest_random_64.
ndefinition cSortCalc128  ≝ cSortCalc dTest_random_128.
ndefinition cSortCalc256  ≝ cSortCalc dTest_random_256.
ndefinition cSortCalc512  ≝ cSortCalc dTest_random_512.
ndefinition cSortCalc1024 ≝ cSortCalc dTest_random_1024.
ndefinition cSortCalc2048 ≝ cSortCalc dTest_random_2048.
ndefinition cSortCalc3072 ≝ cSortCalc dTest_random_3072.

ndefinition cSortNoCalc32   ≝ cSortNoCalc dTest_random_32.
ndefinition cSortNoCalc64   ≝ cSortNoCalc dTest_random_64.
ndefinition cSortNoCalc128  ≝ cSortNoCalc dTest_random_128.
ndefinition cSortNoCalc256  ≝ cSortNoCalc dTest_random_256.
ndefinition cSortNoCalc512  ≝ cSortNoCalc dTest_random_512.
ndefinition cSortNoCalc1024 ≝ cSortNoCalc dTest_random_1024.
ndefinition cSortNoCalc2048 ≝ cSortNoCalc dTest_random_2048.
ndefinition cSortNoCalc3072 ≝ cSortNoCalc dTest_random_3072.

(* ********************** *)
(* HCS08GB60 numeri aurei *)
(* ********************** *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
ndefinition dTest_HCS08_gNum_source : word16 → (list byte8) ≝
λelems:word16.source_to_byte8 HCS08 (
(* BEFORE: A=0x00 HX=0x1A00 PC=0x18BE SP=0x016F Z=1 (I=1) *)

(*
static unsigned int result[16]={ 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
word result[16] = 0x0100

void goldenNumbers(void)
{
unsigned int res_pos=0,tested_num=0,divisor=0;
unsigned long int acc=0;
*)

(* [0x18BE] AIS #-10   *) (compile HCS08 ? AIS (maIMM1 〈xF,x6〉) ?) @
(* [0x18C0] TSX        *) (compile HCS08 ? TSX maINH ?) @
(* [0x18C1] CLR 9,x    *) (compile HCS08 ? CLR (maIX1 〈x0,x9〉) ?) @
(* [0x18C3] CLR 8,X    *) (compile HCS08 ? CLR (maIX1 〈x0,x8〉) ?) @
(* [0x18C5] CLR 1,X    *) (compile HCS08 ? CLR (maIX1 〈x0,x1〉) ?) @
(* [0x18C7] CLR ,X     *) (compile HCS08 ? CLR maIX0 ?) @
(* [0x18C8] CLR 3,X    *) (compile HCS08 ? CLR (maIX1 〈x0,x3〉) ?) @
(* [0x18CA] CLR 2,X    *) (compile HCS08 ? CLR (maIX1 〈x0,x2〉) ?) @
(* [0x18CC] JSR 0x1951 *) (compile HCS08 ? JSR (maIMM2 〈〈x1,x9〉:〈x5,x1〉〉) ?) @

(*
for(tested_num=1;tested_num<2;tested_num++)
 {
*)

(* [0x18CF] STHX 1,SP          *) (compile HCS08 ? STHX (maSP1 〈x0,x1〉) ?) @
(* [0x18D2] BRA *+116 ; 0x1946 *) (compile HCS08 ? BRA (maIMM1 〈x7,x2〉) ?) @
(* [0x18D4] BSR *+125 ; 0x1951 *) (compile HCS08 ? BSR (maIMM1 〈x7,xB〉) ?) @
(* [0x18D6] STHX 3,SP          *) (compile HCS08 ? STHX (maSP1 〈x0,x3〉) ?) @

(*
 for(acc=0,divisor=1;divisor<tested_num;divisor++)
  {
  if(!(tested_num%divisor))
   { acc+=divisor; }
  }
*)

(* [0x18D9] BRA *+61 ; 0x1916 *) (compile HCS08 ? BRA (maIMM1 〈x3,xB〉) ?) @
(* [0x18DB] LDHX 1,SP         *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x18DE] PSHX              *) (compile HCS08 ? PSHX maINH ?) @
(* [0x18DF] PSHH              *) (compile HCS08 ? PSHH maINH ?) @
(* [0x18E0] LDHX 5,SP         *) (compile HCS08 ? LDHX (maSP1 〈x0,x5〉) ?) @
(* [0x18E3] JSR 0x1A1A        *) (compile HCS08 ? JSR (maIMM2 〈〈x1,xA〉:〈x1,xA〉〉) ?) @
(* [0x18E6] AIS #2            *) (compile HCS08 ? AIS (maIMM1 〈x0,x2〉) ?) @
(* [0x18E8] CPHX #0x0000      *) (compile HCS08 ? CPHX (maIMM2 〈〈x0,x0〉:〈x0,x0〉〉) ?) @
(* [0x18EB] BNE *+33 ; 0x190C *) (compile HCS08 ? BNE (maIMM1 〈x1,xF〉) ?) @
(* [0x18ED] TSX               *) (compile HCS08 ? TSX maINH ?) @
(* [0x18EE] LDA 3,X           *) (compile HCS08 ? LDA (maIX1 〈x0,x3〉) ?) @
(* [0x18F0] LDX 2,X           *) (compile HCS08 ? LDX (maIX1 〈x0,x2〉) ?) @
(* [0x18F2] PSHA              *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18F3] PSHX              *) (compile HCS08 ? PSHX maINH ?) @
(* [0x18F4] CLRA              *) (compile HCS08 ? CLR maINHA ?) @
(* [0x18F5] PSHA              *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18F6] PSHA              *) (compile HCS08 ? PSHA maINH ?) @
(* [0x18F7] TSX               *) (compile HCS08 ? TSX maINH ?) @
(* [0x18F8] PSHX              *) (compile HCS08 ? PSHX maINH ?) @
(* [0x19F9] PSHH              *) (compile HCS08 ? PSHH maINH ?) @
(* [0x18FA] AIX #8            *) (compile HCS08 ? AIX (maIMM1 〈x0,x8〉) ?) @
(* [0x18FC] PSHX              *) (compile HCS08 ? PSHX maINH ?) @
(* [0x18FD] PSHH              *) (compile HCS08 ? PSHH maINH ?) @
(* [0x18FE] LDHX 3,SP         *) (compile HCS08 ? LDHX (maSP1 〈x0,x3〉) ?) @
(* [0x1901] JSR 0x1A2A        *) (compile HCS08 ? JSR (maIMM2 〈〈x1,xA〉:〈x2,xA〉〉) ?) @
(* [0x1904] TSX               *) (compile HCS08 ? TSX maINH ?) @
(* [0x1905] AIX #14           *) (compile HCS08 ? AIX (maIMM1 〈x0,xE〉) ?) @
(* [0x1907] JSR 0x1A30        *) (compile HCS08 ? JSR (maIMM2 〈〈x1,xA〉:〈x3,x0〉〉) ?) @
(* [0x190A] AIS #6            *) (compile HCS08 ? AIS (maIMM1 〈x0,x6〉) ?) @
(* [0x190C] STA 0x1800  !COP! *) (compile HCS08 ? STA (maDIR2 〈〈x0,xC〉:〈x0,x0〉〉) ?) @
(* [0x190F] TSX               *) (compile HCS08 ? TSX maINH ?) @
(* [0x1910] INC 3,X           *) (compile HCS08 ? INC (maIX1 〈x0,x3〉) ?) @
(* [0x1912] BNE *+4 ; 0x1916  *) (compile HCS08 ? BNE (maIMM1 〈x0,x2〉) ?) @
(* [0x1914] INC 2,X           *) (compile HCS08 ? INC (maIX1 〈x0,x2〉) ?) @
(* [0x1916] LDHX 1,SP         *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x1919] CPHX 3,SP         *) (compile HCS08 ? CPHX (maSP1 〈x0,x3〉) ?) @
(* [0x191C] BHI *-65 ; 0x18DB *) (compile HCS08 ? BHI (maIMM1 〈xB,xD〉) ?) @

(*
 if(acc==tested_num)
  { result[res_pos++]=tested_num; }
 }
}
*)

(* [0x191E] CPHX 7,SP          *) (compile HCS08 ? CPHX (maSP1 〈x0,x7〉) ?) @
(* [0x1921] BNE *+31 ; 0x1940  *) (compile HCS08 ? BNE (maIMM1 〈x1,xD〉) ?) @
(* [0x1923] LDHX 5,SP          *) (compile HCS08 ? LDHX (maSP1 〈x0,x5〉) ?) @
(* [0x1926] BNE *+26 ; 0x1940  *) (compile HCS08 ? BNE (maIMM1 〈x1,x8〉) ?) @
(* [0x1928] LDHX 9,SP          *) (compile HCS08 ? LDHX (maSP1 〈x0,x9〉) ?) @
(* [0x192B] PSHX               *) (compile HCS08 ? PSHX maINH ?) @
(* [0x192C] AIX #1             *) (compile HCS08 ? AIX (maIMM1 〈x0,x1〉) ?) @
(* [0x192E] STHX 10,SP         *) (compile HCS08 ? STHX (maSP1 〈x0,xA〉) ?) @
(* [0x1931] PULX               *) (compile HCS08 ? PULX maINH ?) @
(* [0x1932] LSLX               *) (compile HCS08 ? ASL maINHX ?) @
(* [0x1933] LDA 2,SP           *) (compile HCS08 ? LDA (maSP1 〈x0,x2〉) ?) @
(* [0x1936] CLRH               *) (compile HCS08 ? CLR maINHH ?) @
(* [0x1937] STA 257,X          *) (compile HCS08 ? STA (maIX2 〈〈x0,x1〉:〈x0,x1〉〉) ?) @
(* [0x193A] LDA 1,SP           *) (compile HCS08 ? LDA (maSP1 〈x0,x1〉) ?) @
(* [0x193D] STA 256,X          *) (compile HCS08 ? STA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) ?) @
(* [0x1940] TSX                *) (compile HCS08 ? TSX maINH ?) @
(* [0x1941] INC 1,X            *) (compile HCS08 ? INC (maIX1 〈x0,x1〉) ?) @
(* [0x1943] BNE *+3 ; 0x1946   *) (compile HCS08 ? BNE (maIMM1 〈x0,x1〉) ?) @
(* [0x1945] INC ,X             *) (compile HCS08 ? INC maIX0 ?) @
(* [0x1946] LDHX 1,SP          *) (compile HCS08 ? LDHX (maSP1 〈x0,x1〉) ?) @
(* [0x1949] CPHX #elems        *) (compile HCS08 ? CPHX (maIMM2 elems) ?) @
(* [0x194C] BCS *-120 ; 0x18D4 *) (compile HCS08 ? BCS (maIMM1 〈x8,x6〉) ?) @
(* [0x194E] AIS #10            *) (compile HCS08 ? AIS (maIMM1 〈x0,xA〉) ?) @
(* [0x1950] STOP ->1951 !FINE! *) (compile HCS08 ? STOP maINH ?) @
(* [0x1951] CLRX               *) (compile HCS08 ? CLR maINHX ?) @
(* [0x1952] CLRH               *) (compile HCS08 ? CLR maINHH ?) @
(* [0x1953] STHX 9,SP          *) (compile HCS08 ? STHX (maSP1 〈x0,x9〉) ?) @
(* [0x1956] CLRH               *) (compile HCS08 ? CLR maINHH ?) @
(* [0x1957] STHX 7,SP          *) (compile HCS08 ? STHX (maSP1 〈x0,x7〉) ?) @
(* [0x195A] INCX               *) (compile HCS08 ? INC maINHX ?) @
(* [0x195B] RTS                *) (compile HCS08 ? RTS maINH ?) @

(*
static void _PUSH_ARGS_L(void) { ... }
*)

(* [0x195C] LDA 3,X    *) (compile HCS08 ? LDA (maIX1 〈x0,x3〉) ?) @
(* [0x195E] PSHA       *) (compile HCS08 ? PSHA maINH ?) @
(* [0x195F] LDA 2,X    *) (compile HCS08 ? LDA (maIX1 〈x0,x2〉) ?) @
(* [0x1961] PSHA       *) (compile HCS08 ? PSHA maINH ?) @
(* [0x1962] LDHX ,X    *) (compile HCS08 ? LDHX maIX0 ?) @
(* [0x1964] PSHX       *) (compile HCS08 ? PSHX maINH ?) @
(* [0x1965] PSHH       *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1966] LDHX 7,SP  *) (compile HCS08 ? LDHX (maSP1 〈x0,x7〉) ?) @
(* [0x1969] LDA 3,X    *) (compile HCS08 ? LDA (maIX1 〈x0,x3〉) ?) @
(* [0x196B] STA 17,SP  *) (compile HCS08 ? STA (maSP1 〈x1,x1〉) ?) @
(* [0x196E] LDA 2,X    *) (compile HCS08 ? LDA (maIX1 〈x0,x2〉) ?) @
(* [0x1970] STA 16,SP  *) (compile HCS08 ? STA (maSP1 〈x1,x0〉) ?) @
(* [0x1973] LDHX ,X    *) (compile HCS08 ? LDHX maIX0 ?) @
(* [0x1975] STHX 14,SP *) (compile HCS08 ? STHX (maSP1 〈x0,xE〉) ?) @
(* [0x1978] LDHX 5,SP  *) (compile HCS08 ? LDHX (maSP1 〈x0,x5〉) ?) @
(* [0x197B] JMP ,X     *) (compile HCS08 ? JMP maINHX0ADD ?) @

(*
static void _ENTER_BINARY_L(void) { ... }
*)

(* [0x197C] PSHA       *) (compile HCS08 ? PSHA maINH ?) @
(* [0x197D] PSHX       *) (compile HCS08 ? PSHX maINH ?) @
(* [0x197E] PSHH       *) (compile HCS08 ? PSHH maINH ?) @
(* [0x197F] PSHX       *) (compile HCS08 ? PSHX maINH ?) @
(* [0x1980] PSHH       *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1981] LDHX 6,SP  *) (compile HCS08 ? LDHX (maSP1 〈x0,x6〉) ?) @
(* [0x1984] PSHX       *) (compile HCS08 ? PSHX maINH ?) @
(* [0x1985] PSHH       *) (compile HCS08 ? PSHH maINH ?) @
(* [0x1986] LDHX 10,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,xA〉) ?) @
(* [0x1989] STHX 8,SP  *) (compile HCS08 ? STHX (maSP1 〈x0,x8〉) ?) @
(* [0x198C] LDHX 12,SP *) (compile HCS08 ? LDHX (maSP1 〈x0,xC〉) ?) @
(* [0x198F] JMP 0x195C *) (compile HCS08 ? JMP (maIMM2 〈〈x1,x9〉:〈x5,xC〉〉) ?) @

(*
static void _IDIVMOD (char dummy_sgn, int j, int dummy, int i, ...) { ... }
*)

(* [0x1992] TST 4,SP            *) (compile HCS08 ? TST (maSP1 〈x0,x4〉) ?) @
(* [0x1995] BNE *+28 ; 0x19B1   *) (compile HCS08 ? BNE (maIMM1 〈x1,xA〉) ?) @
(* [0x1997] TSX                 *) (compile HCS08 ? TSX maINH ?) @
(* [0x1998] LDA 7,X             *) (compile HCS08 ? LDA (maIX1 〈x0,x7〉) ?) @
(* [0x199A] LDX 4,X             *) (compile HCS08 ? LDX (maIX1 〈x0,x4〉) ?) @
(* [0x199C] CLRH                *) (compile HCS08 ? CLR maINHH ?) @
(* [0x199D] DIV                 *) (compile HCS08 ? DIV maINH ?) @
(* [0x199E] STA 4,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x4〉) ?) @
(* [0x19A1] LDA 9,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x9〉) ?) @
(* [0x19A4] DIV                 *) (compile HCS08 ? DIV maINH ?) @
(* [0x19A5] STA 5,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x5〉) ?) @
(* [0x19A8] CLR 8,SP            *) (compile HCS08 ? CLR (maSP1 〈x0,x8〉) ?) @
(* [0x19AB] PSHH                *) (compile HCS08 ? PSHH maINH ?) @
(* [0x19AC] PULA                *) (compile HCS08 ? PULA maINH ?) @
(* [0x19AD] STA 9,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x9〉) ?) @
(* [0x19B0] RTS                 *) (compile HCS08 ? RTS maINH ?) @
(* [0x19B1] CLRA                *) (compile HCS08 ? CLR maINHA ?) @
(* [0x19B2] PSHA                *) (compile HCS08 ? PSHA maINH ?) @
(* [0x19B3] LDX #0x08           *) (compile HCS08 ? LDX (maIMM1 〈x0,x8〉) ?) @
(* [0x19B5] CLC                 *) (compile HCS08 ? CLC maINH ?) @
(* [0x19B6] ROL 10,SP           *) (compile HCS08 ? ROL (maSP1 〈x0,xA〉) ?) @
(* [0x19B9] ROL 9,SP            *) (compile HCS08 ? ROL (maSP1 〈x0,x9〉) ?) @
(* [0x19BC] ROL 1,SP            *) (compile HCS08 ? ROL (maSP1 〈x0,x1〉) ?) @
(* [0x19BF] LDA 5,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x5〉) ?) @
(* [0x19C2] CMP 1,SP            *) (compile HCS08 ? CMP (maSP1 〈x0,x1〉) ?) @
(* [0x19C5] BHI *+31 ; 0x19E4   *) (compile HCS08 ? BHI (maIMM1 〈x1,xD〉) ?) @
(* [0x19C7] BNE *+10 ; 0x19D1   *) (compile HCS08 ? BNE (maIMM1 〈x0,x8〉) ?) @
(* [0x19C9] LDA 6,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x6〉) ?) @
(* [0x19CC] CMP 9,SP            *) (compile HCS08 ? CMP (maSP1 〈x0,x9〉) ?) @
(* [0x19CF] BHI *+21 ; 0x19E4   *) (compile HCS08 ? BHI (maIMM1 〈x1,x3〉) ?) @
(* [0x19D1] LDA 9,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x9〉) ?) @
(* [0x19D4] SUB 6,SP            *) (compile HCS08 ? SUB (maSP1 〈x0,x6〉) ?) @
(* [0x19D7] STA 9,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x9〉) ?) @
(* [0x19DA] LDA 1,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x1〉) ?) @
(* [0x19DD] SBC 5,SP            *) (compile HCS08 ? SBC (maSP1 〈x0,x5〉) ?) @
(* [0x19E0] STA 1,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x1〉) ?) @
(* [0x19E3] SEC                 *) (compile HCS08 ? SEC maINH ?) @
(* [0x19E4] DBNZX *-46 ; 0x19B6 *) (compile HCS08 ? DBNZ (maINHX_and_IMM1 〈xD,x0〉) ?) @
(* [0x19E6] LDA 10,SP           *) (compile HCS08 ? LDA (maSP1 〈x0,xA〉) ?) @
(* [0x19E9] ROLA                *) (compile HCS08 ? ROL maINHA ?) @
(* [0x19EA] STA 6,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x6〉) ?) @
(* [0x19ED] LDA 9,SP            *) (compile HCS08 ? LDA (maSP1 〈x0,x9〉) ?) @
(* [0x19F0] STA 10,SP           *) (compile HCS08 ? STA (maSP1 〈x0,xA〉) ?) @
(* [0x19F3] PULA                *) (compile HCS08 ? PULA maINH ?) @
(* [0x19F4] STA 8,SP            *) (compile HCS08 ? STA (maSP1 〈x0,x8〉) ?) @
(* [0x19F7] CLR 4,SP            *) (compile HCS08 ? CLR (maSP1 〈x0,x4〉) ?) @
(* [0x19FA] RTS                 *) (compile HCS08 ? RTS maINH ?) @

(*
static void _LADD_k_is_k_plus_j(_PARAM_BINARY_L) { ... }
*)

(* [0x19FB] TSX      *) (compile HCS08 ? TSX maINH ?) @
(* [0x19FC] LDA 18,X *) (compile HCS08 ? LDA (maIX1 〈x1,x2〉) ?) @
(* [0x19FE] ADD 5,X  *) (compile HCS08 ? ADD (maIX1 〈x0,x5〉) ?) @
(* [0x1A00] STA 18,X *) (compile HCS08 ? STA (maIX1 〈x1,x2〉) ?) @
(* [0x1A02] LDA 17,X *) (compile HCS08 ? LDA (maIX1 〈x1,x1〉) ?) @
(* [0x1A04] ADC 4,X  *) (compile HCS08 ? ADC (maIX1 〈x0,x4〉) ?) @
(* [0x1A06] STA 17,X *) (compile HCS08 ? STA (maIX1 〈x1,x1〉) ?) @
(* [0x1A08] LDA 16,X *) (compile HCS08 ? LDA (maIX1 〈x1,x0〉) ?) @
(* [0x1A0A] ADC 3,X  *) (compile HCS08 ? ADC (maIX1 〈x0,x3〉) ?) @
(* [0x1A0C] STA 16,X *) (compile HCS08 ? STA (maIX1 〈x1,x0〉) ?) @
(* [0x1A0E] LDA 15,X *) (compile HCS08 ? LDA (maIX1 〈x0,xF〉) ?) @
(* [0x1A10] ADC 2,X  *) (compile HCS08 ? ADC (maIX1 〈x0,x2〉) ?) @
(* [0x1A12] STA 15,X *) (compile HCS08 ? STA (maIX1 〈x0,xF〉) ?) @
(* [0x1A14] AIS #10  *) (compile HCS08 ? AIS (maIMM1 〈x0,xA〉) ?) @
(* [0x1A16] PULH     *) (compile HCS08 ? PULH maINH ?) @
(* [0x1A17] PULX     *) (compile HCS08 ? PULX maINH ?) @
(* [0x1A18] PULA     *) (compile HCS08 ? PULA maINH ?) @
(* [0x1A19] RTS      *) (compile HCS08 ? RTS maINH ?) @

(*
void _IMODU_STAR08(int i, ...) { ... }
*)

(* [0x1A1A] AIS #-2    *) (compile HCS08 ? AIS (maIMM1 〈xF,xE〉) ?) @
(* [0x1A1C] STHX 1,SP  *) (compile HCS08 ? STHX (maSP1 〈x0,x1〉) ?) @
(* [0x1A1F] PSHA       *) (compile HCS08 ? PSHA maINH ?) @
(* [0x1A20] JSR 0x1992 *) (compile HCS08 ? JSR (maIMM2 〈〈x1,x9〉:〈x9,x2〉〉) ?) @
(* [0x1A23] PULA       *) (compile HCS08 ? PULA maINH ?) @
(* [0x1A24] AIS #2     *) (compile HCS08 ? AIS (maIMM1 〈x0,x2〉) ?) @
(* [0x1A26] LDHX 3,SP  *) (compile HCS08 ? LDHX (maSP1 〈x0,x3〉) ?) @
(* [0x1A29] RTS        *) (compile HCS08 ? RTS maINH ?) @

(*
void _LADD(void) { ... }
*)

(* [0x1A2A] JSR 0x197C *) (compile HCS08 ? JSR (maIMM2 〈〈x1,x9〉:〈x7,xC〉〉) ?) @
(* [0x1A2D] JSR 0x19FB *) (compile HCS08 ? JSR (maIMM2 〈〈x1,x9〉:〈xF,xB〉〉) ?) @

(*
void _POP32(void) { ... }
*)

(* [0x1A30] PSHA     *) (compile HCS08 ? PSHA maINH ?) @
(* [0x1A31] LDA 4,SP *) (compile HCS08 ? LDA (maSP1 〈x0,x4〉) ?) @
(* [0x1A34] STA ,X   *) (compile HCS08 ? STA maIX0 ?) @
(* [0x1A35] LDA 5,SP *) (compile HCS08 ? LDA (maSP1 〈x0,x5〉) ?) @
(* [0x1A38] STA 1,X  *) (compile HCS08 ? STA (maIX1 〈x0,x1〉) ?) @
(* [0x1A3A] LDA 6,SP *) (compile HCS08 ? LDA (maSP1 〈x0,x6〉) ?) @
(* [0x1A3D] STA 2,X  *) (compile HCS08 ? STA (maIX1 〈x0,x2〉) ?) @
(* [0x1A3F] LDA 7,SP *) (compile HCS08 ? LDA (maSP1 〈x0,x7〉) ?) @
(* [0x1A42] STA 3,X  *) (compile HCS08 ? STA (maIX1 〈x0,x3〉) ?) @
(* [0x1A44] PULA     *) (compile HCS08 ? PULA maINH ?) @
(* [0x1A45] PULH     *) (compile HCS08 ? PULH maINH ?) @
(* [0x1A46] PULX     *) (compile HCS08 ? PULX maINH ?) @
(* [0x1A47] AIS #4   *) (compile HCS08 ? AIS (maIMM1 〈x0,x4〉) ?) @
(* [0x1A49] JMP ,X   *) (compile HCS08 ? JMP maINHX0ADD ?)

(* attraverso simulazione in CodeWarrior si puo' enunciare che dopo
   80+(65*n*(n+1)*(n+2))/6 si sara' entrati in stato STOP corrispondente
   AFTER: HX=num PC=0x1951 I=0 *)
 ). napply I. nqed.

(* creazione del processore+caricamento+impostazione registri *)
ndefinition dTest_HCS08_gNum_status ≝
λt:memory_impl.
λI_op:bool.
λA_op:byte8.
λHX_op:word16.
λPC_op:word16.
λaddr:word16.
λelems:word16.
λdata:list byte8.
 setweak_i_flag HCS08 t (* I<-I_op *)
  (set_acc_8_low_reg HCS08 t (* A<-A_op *)
   (set_z_flag HCS08 t (* Z<-true *)
    (setweak_sp_reg HCS08 t (* SP<-0x016F *)
     (setweak_indX_16_reg HCS08 t (* H:X<-HX_op *)
      (set_pc_reg HCS08 t (* PC<-PC_op *)
       (start_of_model HCS08 MC9S08GB60 t
        (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
         (load_from_source_at t (zero_memory t) (* carica source in ROM:addr *)
           (dTest_HCS08_cSort_source elems) (extu_w32 addr))
          data (extu_w32 dTest_HCS08_RAM))
        (build_memory_type_of_model HCS08 MC9S08GB60 t)
        (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
        false false false false false false) (* non deterministici tutti a 0 *)
       PC_op)
      HX_op)
     (mk_word16 (mk_byte8 x0 x1) (mk_byte8 x6 xF)))
    true)
   A_op)
  I_op.

(* NUMERI AUREI: Somma divisori(x)=x, fino a 0xFFFF sono 6/28/496/8128 *)
ndefinition dTest_HCS08_gNum_aurei ≝
λnum:word16.match gt_w16 num 〈〈x1,xF〉:〈xC,x0〉〉 with
 [ true ⇒ [ 〈x0,x0〉 ; 〈x0,x6〉 ; 〈x0,x0〉 ; 〈x1,xC〉 ; 〈x0,x1〉 ; 〈xF,x0〉 ; 〈x1,xF〉 ; 〈xC,x0〉 ]
 | false ⇒ match gt_w16 num 〈〈x0,x1〉:〈xF,x0〉〉 with
  [ true ⇒ [ 〈x0,x0〉 ; 〈x0,x6〉 ; 〈x0,x0〉 ; 〈x1,xC〉 ; 〈x0,x1〉 ; 〈xF,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ]
  | false ⇒ match gt_w16 num 〈〈x0,x0〉:〈x1,xC〉〉 with
   [ true ⇒ [ 〈x0,x0〉 ; 〈x0,x6〉 ; 〈x0,x0〉 ; 〈x1,xC〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ]
   | false ⇒ match gt_w16 num 〈〈x0,x0〉:〈x0,x6〉〉 with
    [ true ⇒ [ 〈x0,x0〉 ; 〈x0,x6〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ]
    | false ⇒ [ 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ]
    ]
   ]
  ]
 ] @ [ 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉
     ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉
     ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ; 〈x0,x0〉 ].

(* esecuzione execute k*(n+2) *)
nlet rec dTest_HCS08_gNum_execute1 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute1 m t (execute m t (TickOK ? s') (ntot + nat2)) n' ntot ]
  ].

(* esecuzione execute k*(n+1)*(n+2) *)
nlet rec dTest_HCS08_gNum_execute2 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute2 m t (dTest_HCS08_gNum_execute1 m t (TickOK ? s') (ntot + nat1) ntot) n' ntot ]
  ].

(* esecuzione execute k*n*(n+1)*(n+2) *)
nlet rec dTest_HCS08_gNum_execute3 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute3 m t (dTest_HCS08_gNum_execute2 m t (TickOK ? s') ntot ntot) n' ntot ]
  ].

(* esecuzione execute 80+11*n*(n+1)*(n+2) *)
ndefinition dTest_HCS08_gNum_execute4 ≝
λm:mcu_type.λt:memory_impl.λs:tick_result (any_status m t).λntot:nat.
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ execute m t (dTest_HCS08_gNum_execute3 m t (TickOK ? s') nat11 ntot) nat80
  ].

(* parametrizzazione dell'enunciato del teorema parziale *)
nlemma dTest_HCS08_gNum_aux ≝
λt:memory_impl.λnum:word16.
 (* 2) match di esecuzione su tempo in forma di upperbound *)
 match dTest_HCS08_gNum_execute4 HCS08 t
  (TickOK ? (dTest_HCS08_gNum_status t true 〈x0,x0〉 〈〈x1,xA〉:〈x0,x0〉〉 〈〈x1,x8〉:〈xB,xE〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num dTest_zeros))
  (* tempo di esecuzione 80+11*n*(n+1)*(n+2) *)
  (nat_of_w16 num) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (mem_desc HCS08 t s) dTest_zeros3K (extu_w32 〈〈x0,x1〉:〈x2,x0〉〉)))
   | TickOK s ⇒ None ?
   ] =
  Some ? (dTest_HCS08_gNum_status t false 〈x0,x0〉 num 〈〈x1,x9〉:〈x5,x1〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num (dTest_HCS08_gNum_aurei num)).

ndefinition gNumCalc ≝
λnum:word16.
 match dTest_HCS08_gNum_execute4 HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_gNum_status MEM_TREE true 〈x0,x0〉 〈〈x1,xA〉:〈x0,x0〉〉 〈〈x1,x8〉:〈xB,xE〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num dTest_zeros))
  (nat_of_w16 num) with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (mem_desc HCS08 MEM_TREE s) dTest_zeros3K (extu_w32 〈〈x0,x1〉:〈x2,x0〉〉)))
   | TickOK s ⇒ None ?
   ].

ndefinition gNumNoCalc ≝
λnum:word16.
 Some ? (dTest_HCS08_gNum_status MEM_TREE false 〈x0,x0〉 num 〈〈x1,x9〉:〈x5,x1〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num (dTest_HCS08_gNum_aurei num)).

ndefinition gNumCalc1    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x1〉〉.
ndefinition gNumCalc2    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x2〉〉.
ndefinition gNumCalc5    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x5〉〉.
ndefinition gNumCalc10   ≝ gNumCalc 〈〈x0,x0〉:〈x0,xA〉〉.
ndefinition gNumCalc20   ≝ gNumCalc 〈〈x0,x0〉:〈x1,x4〉〉.
ndefinition gNumCalc50   ≝ gNumCalc 〈〈x0,x0〉:〈x3,x2〉〉.
ndefinition gNumCalc100  ≝ gNumCalc 〈〈x0,x0〉:〈x6,x4〉〉.
ndefinition gNumCalc250  ≝ gNumCalc 〈〈x0,x0〉:〈xF,xA〉〉.
ndefinition gNumCalc500  ≝ gNumCalc 〈〈x0,x1〉:〈xF,x4〉〉.
ndefinition gNumCalc1000 ≝ gNumCalc 〈〈x0,x3〉:〈xE,x8〉〉.

ndefinition gNumNoCalc1    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x1〉〉.
ndefinition gNumNoCalc2    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x2〉〉.
ndefinition gNumNoCalc5    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x5〉〉.
ndefinition gNumNoCalc10   ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,xA〉〉.
ndefinition gNumNoCalc20   ≝ gNumNoCalc 〈〈x0,x0〉:〈x1,x4〉〉.
ndefinition gNumNoCalc50   ≝ gNumNoCalc 〈〈x0,x0〉:〈x3,x2〉〉.
ndefinition gNumNoCalc100  ≝ gNumNoCalc 〈〈x0,x0〉:〈x6,x4〉〉.
ndefinition gNumNoCalc250  ≝ gNumNoCalc 〈〈x0,x0〉:〈xF,xA〉〉.
ndefinition gNumNoCalc500  ≝ gNumNoCalc 〈〈x0,x1〉:〈xF,x4〉〉.
ndefinition gNumNoCalc1000 ≝ gNumNoCalc 〈〈x0,x3〉:〈xE,x8〉〉.
