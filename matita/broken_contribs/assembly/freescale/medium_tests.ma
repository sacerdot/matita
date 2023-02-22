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

(* include "freescale/medium_tests_tools.ma" *)
include "freescale/medium_tests_tools.ma".
 
(* ************************ *)
(* HCS08GB60 String Reverse *)
(* ************************ *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
definition dTest_HCS08_sReverse_source : word16 → (list byte8) ≝
λelems:word16.
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: A=0x00 H:X=0x0D4B SP=0x0D4A PC=0x18E0 Z=true *)

(* static unsigned char dati[3072]={...};

   void swap(unsigned char *a, unsigned char *b)
    { unsigned char tmp=*a; *a=*b; *b=tmp; return; } *)

(* [0x18C8]    allineamento *) (compile m ? NOP maINH I) @

(* argomenti: HX e [0x0D49-A], passaggio ibrido reg, stack *)
(* [0x18C9] PSHX      *) (compile m ? PSHX maINH I) @
(* [0x18CA] PSHH      *) (compile m ? PSHH maINH I) @
(* [0x18CB] LDHX 5,SP *) (compile m ? LDHX (maSP1 〈x0,x5〉) I) @
(* [0x18CE] LDA ,X    *) (compile m ? LDA maIX0 I) @
(* [0x18CF] LDHX 1,SP *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x18D2] PSHA      *) (compile m ? PSHA maINH I) @
(* [0x18D3] LDA ,X    *) (compile m ? LDA maIX0 I) @
(* [0x18D4] LDHX 6,SP *) (compile m ? LDHX (maSP1 〈x0,x6〉) I) @
(* [0x18D7] STA ,X    *) (compile m ? STA maIX0 I) @
(* [0x18D8] LDHX 2,SP *) (compile m ? LDHX (maSP1 〈x0,x2〉) I) @
(* [0x18DB] PULA      *) (compile m ? PULA maINH I) @
(* [0x18DC] STA ,X    *) (compile m ? STA maIX0 I) @
(* [0x18DD] AIS #2    *) (compile m ? AIS (maIMM1 〈x0,x2〉) I) @
(* [0x18DF] RTS       *) (compile m ? RTS maINH I) @

(* void main(void)
   {
   unsigned int pos=0,limit=0;
 
   for(limit=3072;pos<(limit/2);pos++)
    { swap(&dati[pos],&dati[limit-pos-1]); } *)

(* [0x18E0] LDHX #elems     *) (compile m ? LDHX (maIMM2 elems) I) @
(* [0x18E3] STHX 4,SP       *) (compile m ? STHX (maSP1 〈x0,x4〉) I) @
(* [0x18E6] BRA *+52 ; 191A *) (compile m ? BRA (maIMM1 〈x3,x2〉) I) @
(* [0x18E8] TSX             *) (compile m ? TSX maINH I) @
(* [0x18E9] LDA 2,X         *) (compile m ? LDA (maIX1 〈x0,x2〉) I) @
(* [0x18EB] ADD #0x00       *) (compile m ? ADD (maIMM1 〈x0,x0〉) I) @
(* [0x18ED] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x18EE] LDA 1,X         *) (compile m ? LDA (maIX1 〈x0,x1〉) I) @
(* [0x18F0] ADC #0x01       *) (compile m ? ADC (maIMM1 〈x0,x1〉) I) @
(* [0x18F2] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x18F3] LDA 4,X         *) (compile m ? LDA (maIX1 〈x0,x4〉) I) @
(* [0x18F5] SUB 2,X         *) (compile m ? SUB (maIX1 〈x0,x2〉) I) @
(* [0x18F7] STA ,X          *) (compile m ? STA maIX0 I) @
(* [0x18F8] LDA 3,X         *) (compile m ? LDA (maIX1 〈x0,x3〉) I) @
(* [0x18FA] SBC 1,X         *) (compile m ? SBC (maIX1 〈x0,x1〉) I) @
(* [0x18FC] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x18FD] LDX ,X          *) (compile m ? LDX maIX0 I) @
(* [0x18FE] PULH            *) (compile m ? PULH maINH I) @
(* [0x18FF] AIX #-1         *) (compile m ? AIX (maIMM1 〈xF,xF〉) I) @
(* [0x1901] TXA             *) (compile m ? TXA maINH I) @
(* [0x1902] ADD #0x00       *) (compile m ? ADD (maIMM1 〈x0,x0〉) I) @
(* [0x1904] PSHH            *) (compile m ? PSHH maINH I) @
(* [0x1905] TSX             *) (compile m ? TSX maINH I) @
(* [0x1906] STA 3,X         *) (compile m ? STA (maIX1 〈x0,x3〉) I) @
(* [0x1908] PULA            *) (compile m ? PULA maINH I) @
(* [0x1909] ADC #0x01       *) (compile m ? ADC (maIMM1 〈x0,x1〉) I) @
(* [0x190B] LDX 3,X         *) (compile m ? LDX (maIX1 〈x0,x3〉) I) @
(* [0x190D] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x190E] PULH            *) (compile m ? PULH maINH I) @
(* [0x190F] BSR *-70 ; 18C9 *) (compile m ? BSR (maIMM1 〈xB,x8〉) I) @
(* [0x1911] AIS #2          *) (compile m ? AIS (maIMM1 〈x0,x2〉) I) @
(* [0x1913] TSX             *) (compile m ? TSX maINH I) @
(* [0x1914] INC 2,X         *) (compile m ? INC (maIX1 〈x0,x2〉) I) @
(* [0x1916] BNE *+4 ; 191A  *) (compile m ? BNE (maIMM1 〈x0,x2〉) I) @
(* [0x1918] INC 1,X         *) (compile m ? INC (maIX1 〈x0,x1〉) I) @
(* [0x191A] TSX             *) (compile m ? TSX maINH I) @
(* [0x191B] LDA 3,X         *) (compile m ? LDA (maIX1 〈x0,x3〉) I) @
(* [0x191D] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x191E] PULH            *) (compile m ? PULH maINH I) @
(* [0x191F] LSRA            *) (compile m ? LSR maINHA I) @
(* [0x1920] TSX             *) (compile m ? TSX maINH I) @
(* [0x1921] LDX 4,X         *) (compile m ? LDX (maIX1 〈x0,x4〉) I) @
(* [0x1923] RORX            *) (compile m ? ROR maINHX I) @
(* [0x1924] PSHA            *) (compile m ? PSHA maINH I) @
(* [0x1925] PULH            *) (compile m ? PULH maINH I) @
(* [0x1926] CPHX 2,SP       *) (compile m ? CPHX (maSP1 〈x0,x2〉) I) @
(* [0x1929] BHI *-65 ; 18E8 *) (compile m ? BHI (maIMM1 〈xB,xD〉) I)

(* [0x192B] !FINE!
            attraverso simulazione in CodeWarrior si puo' enunciare che dopo
            42+79*n+5*(n>>9) ci sara' il reverse di n byte (PARI) e
            H:X=n/2 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition dTest_HCS08_sReverse_status ≝
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
     (start_of_mcu_version
      MC9S08GB60 t
      (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
       (load_from_source_at t (zero_memory t) (* carica source in ROM:dTest_HCS08_prog *)
         (dTest_HCS08_sReverse_source elems) dTest_HCS08_prog)
        data dTest_HCS08_RAM)
      (build_memory_type_of_mcu_version MC9S08GB60 t)
      (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
      false false false false false false) (* non deterministici tutti a 0 *)
     (mk_word16 (mk_byte8 x1 x8) (mk_byte8 xE x0)))
    HX_op)
   (mk_word16 (mk_byte8 x0 xD) (mk_byte8 x4 xA)))
  true)
 A_op.

(* parametrizzazione dell'enunciato del teorema *)
(* primo sbozzo: confronto esecuzione con hexdump... *)
lemma dTest_HCS08_sReverse_dump_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) la stringa deve avere lunghezza pari *)
 ((and_b8 (w16l (byte8_strlen string)) 〈x0,x1〉) = 〈x0,x0〉) ∧
 (* 3) match di esecuzione su tempo in forma di tempo esatto *)
 (match execute HCS08 t
  (* parametri IN: t,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_sReverse_status t 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 42+79*n+5*(n>>9) *)
  (42+79*(byte8_strlen string)+5*((byte8_strlen string)/512)) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (byte8_hexdump t (get_mem_desc HCS08 t s) dTest_HCS08_RAM (byte8_strlen string))
   ] =
  Some ? (byte8_reverse string)).

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
lemma dTest_HCS08_sReverse_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) la stringa deve avere lunghezza pari *)
 ((and_b8 (w16l (byte8_strlen string)) 〈x0,x1〉) = 〈x0,x0〉) ∧
 (* 3) match di esecuzione su tempo in forma di tempo esatto *)
 (match execute HCS08 t
  (* parametri IN: t,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_sReverse_status t 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 42+79*n+5*(n>>9) *)
  (42+79*(byte8_strlen string)+5*((byte8_strlen string)/512)) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (get_mem_desc HCS08 t s) dTest_zeros 〈〈x0,xD〉:〈x0,x0〉〉))
   ] =
  Some ? (set_pc_reg HCS08 t
   (dTest_HCS08_sReverse_status t (fst ?? (shr_b8 (w16h (byte8_strlen string)))) (fst ?? (shr_w16 (byte8_strlen string))) (byte8_strlen string) (byte8_reverse string)) 
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

definition sReverseCalc ≝
λstring:list byte8.
 match execute HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_sReverse_status MEM_TREE 〈x0,x0〉 〈〈x0,xD〉:〈x4,xB〉〉 (byte8_strlen string) string))
  (42+79*(byte8_strlen string)+5*((byte8_strlen string)/512)) with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ None ? 
   | TickOK s ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (get_mem_desc HCS08 MEM_TREE s) dTest_zeros 〈〈x0,xD〉:〈x0,x0〉〉))
   ]. 

definition sReverseNoCalc ≝
λstring:list byte8.
 Some ? (set_pc_reg HCS08 MEM_TREE
   (dTest_HCS08_sReverse_status MEM_TREE (fst ?? (shr_b8 (w16h (byte8_strlen string))))
                                         (fst ?? (shr_w16 (byte8_strlen string)))
                                         (byte8_strlen string) (byte8_reverse string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x2 xB))).

definition sReverseCalc32   ≝ sReverseCalc dTest_random_32.
definition sReverseCalc64   ≝ sReverseCalc dTest_random_64.
definition sReverseCalc128  ≝ sReverseCalc dTest_random_128.
definition sReverseCalc256  ≝ sReverseCalc dTest_random_256.
definition sReverseCalc512  ≝ sReverseCalc dTest_random_512.
definition sReverseCalc1024 ≝ sReverseCalc dTest_random_1024.
definition sReverseCalc2048 ≝ sReverseCalc dTest_random_2048.
definition sReverseCalc3072 ≝ sReverseCalc dTest_random_3072.

definition sReverseNoCalc32   ≝ sReverseNoCalc dTest_random_32.
definition sReverseNoCalc64   ≝ sReverseNoCalc dTest_random_64.
definition sReverseNoCalc128  ≝ sReverseNoCalc dTest_random_128.
definition sReverseNoCalc256  ≝ sReverseNoCalc dTest_random_256.
definition sReverseNoCalc512  ≝ sReverseNoCalc dTest_random_512.
definition sReverseNoCalc1024 ≝ sReverseNoCalc dTest_random_1024.
definition sReverseNoCalc2048 ≝ sReverseNoCalc dTest_random_2048.
definition sReverseNoCalc3072 ≝ sReverseNoCalc dTest_random_3072.

(* *********************** *)
(* HCS08GB60 Counting Sort *)
(* *********************** *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
definition dTest_HCS08_cSort_source : word16 → (list byte8) ≝
λelems:word16.
let m ≝ HCS08 in source_to_byte8 m (
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

(* [0x18C8] BRA *+31;18E7 *) (compile m ? BRA (maIMM1 〈x1,xD〉) I) @
(* [0x18CA] LDHX 1,SP     *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x18CD] LDA 256,X     *) (compile m ? LDA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) I) @
(* [0x18D0] LSLA          *) (compile m ? ASL maINHA I) @
(* [0x18D1] CLRX          *) (compile m ? CLR maINHX I) @
(* [0x18D2] ROLX          *) (compile m ? ROL maINHX I) @
(* [0x18D3] ADD #0x00     *) (compile m ? ADD (maIMM1 〈x0,x0〉) I) @
(* [0x18D5] PSHA          *) (compile m ? PSHA maINH I) @
(* [0x18D6] TXA           *) (compile m ? TXA maINH I) @
(* [0x18D7] ADC #0x0D     *) (compile m ? ADC (maIMM1 〈x0,xD〉) I) @
(* [0x18D9] PSHA          *) (compile m ? PSHA maINH I) @
(* [0x18DA] PULH          *) (compile m ? PULH maINH I) @
(* [0x18DB] PULX          *) (compile m ? PULX maINH I) @
(* [0x18DC] INC 1,X       *) (compile m ? INC (maIX1 〈x0,x1〉) I) @
(* [0x18DE] BNE *+3       *) (compile m ? BNE (maIMM1 〈x0,x1〉) I) @
(* [0x18E0] INC ,X        *) (compile m ? INC maIX0 I) @
(* [0x18E1] TSX           *) (compile m ? TSX maINH I) @
(* [0x18E2] INC 1,X       *) (compile m ? INC (maIX1 〈x0,x1〉) I) @
(* [0x18E4] BNE *+3       *) (compile m ? BNE (maIMM1 〈x0,x1〉) I) @
(* [0x18E6] INC ,X        *) (compile m ? INC maIX0 I) @
(* [0x18E7] LDHX 1,SP     *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x18EA] CPHX #elems   *) (compile m ? CPHX (maIMM2 elems) I) @ (* dimensione dei dati al massimo 0x0C00 *)
(* [0x18ED] BCS *-35;18CA *) (compile m ? BCS (maIMM1 〈xD,xB〉) I) @

(* /* sovrascrittura di dati per produrre la versione ordinata */
   for(index=0;index<256;index++)
    {
    while(counters[index]--)
     { dati[position++]=index; }
    } *)

(* [0x18EF] TSX          *) (compile m ? TSX maINH I) @
(* [0x18F0] CLR 1,X      *) (compile m ? CLR (maIX1 〈x0,x1〉) I) @
(* [0x18F2] CLR ,X       *) (compile m ? CLR maIX0 I) @
(* [0x18F3] BRA *+16     *) (compile m ? BRA (maIMM1 〈x0,xE〉) I) @
(* [0x18F5] TSX          *) (compile m ? TSX maINH I) @
(* [0x18F6] LDA 1,X      *) (compile m ? LDA (maIX1 〈x0,x1〉) I) @
(* [0x18F8] LDHX 3,SP    *) (compile m ? LDHX (maSP1 〈x0,x3〉) I) @
(* [0x18FB] STA 256,X    *) (compile m ? STA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) I) @
(* [0x18FE] AIX #1       *) (compile m ? AIX (maIMM1 〈x0,x1〉) I) @
(* [0x1900] STHX 3,SP    *) (compile m ? STHX (maSP1 〈x0,x3〉) I) @
(* [0x1903] TSX          *) (compile m ? TSX maINH I) @
(* [0x1904] LDX 1,X      *) (compile m ? LDX (maIX1 〈x0,x1〉) I) @
(* [0x1906] LSLX         *) (compile m ? ASL maINHX I) @
(* [0x1907] LDA 1,SP     *) (compile m ? LDA (maSP1 〈x0,x1〉) I) @
(* [0x190A] ROLA         *) (compile m ? ROL maINHA I) @
(* [0x190B] PSHA         *) (compile m ? PSHA maINH I) @
(* [0x190C] PULH         *) (compile m ? PULH maINH I) @
(* [0x190D] PSHX         *) (compile m ? PSHX maINH I) @
(* [0x190E] LDHX 3328,X  *) (compile m ? LDHX (maIX2 〈〈x0,xD〉:〈x0,x0〉〉) I) @
(* [0x1912] PSHX         *) (compile m ? PSHX maINH I) @
(* [0x1913] PSHH         *) (compile m ? PSHH maINH I) @
(* [0x1914] AIX #-1      *) (compile m ? AIX (maIMM1 〈xF,xF〉) I) @
(* [0x1916] PSHH         *) (compile m ? PSHH maINH I) @
(* [0x1917] PSHA         *) (compile m ? PSHA maINH I) @
(* [0x1918] PULH         *) (compile m ? PULH maINH I) @
(* [0x1919] PSHX         *) (compile m ? PSHX maINH I) @
(* [0x191A] LDX 5,SP     *) (compile m ? LDX (maSP1 〈x0,x5〉) I) @
(* [0x191D] PULA         *) (compile m ? PULA maINH I) @
(* [0x191E] STA 3329,X   *) (compile m ? STA (maIX2 〈〈x0,xD〉:〈x0,x1〉〉) I) @
(* [0x1921] PULA         *) (compile m ? PULA maINH I) @
(* [0x1922] STA 3328,X   *) (compile m ? STA (maIX2 〈〈x0,xD〉:〈x0,x0〉〉) I) @
(* [0x1925] PULH         *) (compile m ? PULH maINH I) @
(* [0x1926] PULX         *) (compile m ? PULX maINH I) @
(* [0x1927] CPHX #0x0000 *) (compile m ? CPHX (maIMM2 〈〈x0,x0〉:〈x0,x0〉〉) I) @
(* [0x192A] PULH         *) (compile m ? PULH maINH I) @
(* [0x192B] BNE *-54     *) (compile m ? BNE (maIMM1 〈xC,x8〉) I) @
(* [0x192D] TSX          *) (compile m ? TSX maINH I) @
(* [0x192E] INC 1,X      *) (compile m ? INC (maIX1 〈x0,x1〉) I) @
(* [0x1930] BNE *+3      *) (compile m ? BNE (maIMM1 〈x0,x1〉) I) @
(* [0x1932] INC ,X       *) (compile m ? INC maIX0 I) @
(* [0x1933] LDHX 1,SP    *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x1936] CPHX #0x0100 *) (compile m ? CPHX (maIMM2 〈〈x0,x1〉:〈x0,x0〉〉) I) @
(* [0x1939] BNE *-54     *) (compile m ? BNE (maIMM1 〈xC,x8〉) I) @
(* [0x193B] STOP         *) (compile m ? STOP maINH I)

(* [0x193C] !FINE!
            attraverso simulazione in CodeWarrior si puo' enunciare che dopo
            25700+150n si sara' entrati in stato STOP corrispondente con ordinamento
            di n byte, A=0xFF H:X=0x0100 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition dTest_HCS08_cSort_status ≝
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
       (start_of_mcu_version
        MC9S08GB60 t
        (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
         (load_from_source_at t (zero_memory t) (* carica source in ROM:dTest_HCS08_prog *)
           (dTest_HCS08_cSort_source elems) dTest_HCS08_prog)
          data dTest_HCS08_RAM)
        (build_memory_type_of_mcu_version MC9S08GB60 t)
        (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
        false false false false false false) (* non deterministici tutti a 0 *)
       dTest_HCS08_prog)
      HX_op)
     (mk_word16 (mk_byte8 x0 xF) (mk_byte8 x4 xB)))
    true)
   A_op)
  I_op.

(* parametrizzazione dell'enunciato del teorema parziale *)
lemma dTest_HCS08_cSort_aux ≝
λt:memory_impl.λstring:list byte8.
 (* 1) la stringa deve avere una lunghezza ∈ [0,3072] *)
 (byte8_bounded_strlen string 〈〈x0,xC〉:〈x0,x0〉〉) ∧
 (* 2) match di esecuzione su tempo in forma di upperbound *)
 (match execute HCS08 t
  (* parametri IN: t,A,H:X,strlen(string),string *)
  (TickOK ? (dTest_HCS08_cSort_status t true 〈x0,x0〉 〈〈x0,xF〉:〈x4,xC〉〉 (byte8_strlen string) string))
  (* tempo di esecuzione 25700+150*n *)
  ((nat_of_word16 〈〈x6,x4〉:〈x6,x4〉〉)+(nat_of_byte8 〈x9,x6〉)*(nat_of_word16 (byte8_strlen string))) with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (get_mem_desc HCS08 t s) dTest_zeros 〈〈x0,xD〉:〈x0,x0〉〉))
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

definition cSortCalc ≝
λstring:list byte8.
 match execute HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_cSort_status MEM_TREE true 〈x0,x0〉 〈〈x0,xF〉:〈x4,xC〉〉 (byte8_strlen string) string))
  ((nat_of_word16 〈〈x6,x4〉:〈x6,x4〉〉)+(nat_of_byte8 〈x9,x6〉)*(nat_of_word16 (byte8_strlen string))) with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (get_mem_desc HCS08 MEM_TREE s) dTest_zeros 〈〈x0,xD〉:〈x0,x0〉〉))
   | TickOK s ⇒ None ?
   ].

definition cSortNoCalc ≝
λstring:list byte8.
 Some ? (set_pc_reg HCS08 MEM_TREE
   (dTest_HCS08_cSort_status MEM_TREE false 〈xF,xF〉 〈〈x0,x1〉:〈x0,x0〉〉 (byte8_strlen string) (byte8_list_ordering string)) 
   (mk_word16 (mk_byte8 x1 x9) (mk_byte8 x3 xC))).

definition cSortCalc32   ≝ cSortCalc dTest_random_32.
definition cSortCalc64   ≝ cSortCalc dTest_random_64.
definition cSortCalc128  ≝ cSortCalc dTest_random_128.
definition cSortCalc256  ≝ cSortCalc dTest_random_256.
definition cSortCalc512  ≝ cSortCalc dTest_random_512.
definition cSortCalc1024 ≝ cSortCalc dTest_random_1024.
definition cSortCalc2048 ≝ cSortCalc dTest_random_2048.
definition cSortCalc3072 ≝ cSortCalc dTest_random_3072.

definition cSortNoCalc32   ≝ cSortNoCalc dTest_random_32.
definition cSortNoCalc64   ≝ cSortNoCalc dTest_random_64.
definition cSortNoCalc128  ≝ cSortNoCalc dTest_random_128.
definition cSortNoCalc256  ≝ cSortNoCalc dTest_random_256.
definition cSortNoCalc512  ≝ cSortNoCalc dTest_random_512.
definition cSortNoCalc1024 ≝ cSortNoCalc dTest_random_1024.
definition cSortNoCalc2048 ≝ cSortNoCalc dTest_random_2048.
definition cSortNoCalc3072 ≝ cSortNoCalc dTest_random_3072.

(* ********************** *)
(* HCS08GB60 numeri aurei *)
(* ********************** *)

(* versione ridotta, in cui non si riazzerano gli elementi di counters *)
definition dTest_HCS08_gNum_source : word16 → (list byte8) ≝
λelems:word16.
let m ≝ HCS08 in source_to_byte8 m (
(* BEFORE: A=0x00 HX=0x1A00 PC=0x18BE SP=0x016F Z=1 (I=1) *)

(*
static unsigned int result[16]={ 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
word result[16] = 0x0100

void goldenNumbers(void)
{
unsigned int res_pos=0,tested_num=0,divisor=0;
unsigned long int acc=0;
*)

(* [0x18BE] AIS #-10   *) (compile m ? AIS (maIMM1 〈xF,x6〉) I) @
(* [0x18C0] TSX        *) (compile m ? TSX maINH I) @
(* [0x18C1] CLR 9,x    *) (compile m ? CLR (maIX1 〈x0,x9〉) I) @
(* [0x18C3] CLR 8,X    *) (compile m ? CLR (maIX1 〈x0,x8〉) I) @
(* [0x18C5] CLR 1,X    *) (compile m ? CLR (maIX1 〈x0,x1〉) I) @
(* [0x18C7] CLR ,X     *) (compile m ? CLR maIX0 I) @
(* [0x18C8] CLR 3,X    *) (compile m ? CLR (maIX1 〈x0,x3〉) I) @
(* [0x18CA] CLR 2,X    *) (compile m ? CLR (maIX1 〈x0,x2〉) I) @
(* [0x18CC] JSR 0x1951 *) (compile m ? JSR (maIMM2 〈〈x1,x9〉:〈x5,x1〉〉) I) @

(*
for(tested_num=1;tested_num<2;tested_num++)
 {
*)

(* [0x18CF] STHX 1,SP          *) (compile m ? STHX (maSP1 〈x0,x1〉) I) @
(* [0x18D2] BRA *+116 ; 0x1946 *) (compile m ? BRA (maIMM1 〈x7,x2〉) I) @
(* [0x18D4] BSR *+125 ; 0x1951 *) (compile m ? BSR (maIMM1 〈x7,xB〉) I) @
(* [0x18D6] STHX 3,SP          *) (compile m ? STHX (maSP1 〈x0,x3〉) I) @

(*
 for(acc=0,divisor=1;divisor<tested_num;divisor++)
  {
  if(!(tested_num%divisor))
   { acc+=divisor; }
  }
*)

(* [0x18D9] BRA *+61 ; 0x1916 *) (compile m ? BRA (maIMM1 〈x3,xB〉) I) @
(* [0x18DB] LDHX 1,SP         *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x18DE] PSHX              *) (compile m ? PSHX maINH I) @
(* [0x18DF] PSHH              *) (compile m ? PSHH maINH I) @
(* [0x18E0] LDHX 5,SP         *) (compile m ? LDHX (maSP1 〈x0,x5〉) I) @
(* [0x18E3] JSR 0x1A1A        *) (compile m ? JSR (maIMM2 〈〈x1,xA〉:〈x1,xA〉〉) I) @
(* [0x18E6] AIS #2            *) (compile m ? AIS (maIMM1 〈x0,x2〉) I) @
(* [0x18E8] CPHX #0x0000      *) (compile m ? CPHX (maIMM2 〈〈x0,x0〉:〈x0,x0〉〉) I) @
(* [0x18EB] BNE *+33 ; 0x190C *) (compile m ? BNE (maIMM1 〈x1,xF〉) I) @
(* [0x18ED] TSX               *) (compile m ? TSX maINH I) @
(* [0x18EE] LDA 3,X           *) (compile m ? LDA (maIX1 〈x0,x3〉) I) @
(* [0x18F0] LDX 2,X           *) (compile m ? LDX (maIX1 〈x0,x2〉) I) @
(* [0x18F2] PSHA              *) (compile m ? PSHA maINH I) @
(* [0x18F3] PSHX              *) (compile m ? PSHX maINH I) @
(* [0x18F4] CLRA              *) (compile m ? CLR maINHA I) @
(* [0x18F5] PSHA              *) (compile m ? PSHA maINH I) @
(* [0x18F6] PSHA              *) (compile m ? PSHA maINH I) @
(* [0x18F7] TSX               *) (compile m ? TSX maINH I) @
(* [0x18F8] PSHX              *) (compile m ? PSHX maINH I) @
(* [0x19F9] PSHH              *) (compile m ? PSHH maINH I) @
(* [0x18FA] AIX #8            *) (compile m ? AIX (maIMM1 〈x0,x8〉) I) @
(* [0x18FC] PSHX              *) (compile m ? PSHX maINH I) @
(* [0x18FD] PSHH              *) (compile m ? PSHH maINH I) @
(* [0x18FE] LDHX 3,SP         *) (compile m ? LDHX (maSP1 〈x0,x3〉) I) @
(* [0x1901] JSR 0x1A2A        *) (compile m ? JSR (maIMM2 〈〈x1,xA〉:〈x2,xA〉〉) I) @
(* [0x1904] TSX               *) (compile m ? TSX maINH I) @
(* [0x1905] AIX #14           *) (compile m ? AIX (maIMM1 〈x0,xE〉) I) @
(* [0x1907] JSR 0x1A30        *) (compile m ? JSR (maIMM2 〈〈x1,xA〉:〈x3,x0〉〉) I) @
(* [0x190A] AIS #6            *) (compile m ? AIS (maIMM1 〈x0,x6〉) I) @
(* [0x190C] STA 0x1800  !COP! *) (compile m ? STA (maDIR2 〈〈x0,xC〉:〈x0,x0〉〉) I) @
(* [0x190F] TSX               *) (compile m ? TSX maINH I) @
(* [0x1910] INC 3,X           *) (compile m ? INC (maIX1 〈x0,x3〉) I) @
(* [0x1912] BNE *+4 ; 0x1916  *) (compile m ? BNE (maIMM1 〈x0,x2〉) I) @
(* [0x1914] INC 2,X           *) (compile m ? INC (maIX1 〈x0,x2〉) I) @
(* [0x1916] LDHX 1,SP         *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x1919] CPHX 3,SP         *) (compile m ? CPHX (maSP1 〈x0,x3〉) I) @
(* [0x191C] BHI *-65 ; 0x18DB *) (compile m ? BHI (maIMM1 〈xB,xD〉) I) @

(*
 if(acc==tested_num)
  { result[res_pos++]=tested_num; }
 }
}
*)

(* [0x191E] CPHX 7,SP          *) (compile m ? CPHX (maSP1 〈x0,x7〉) I) @
(* [0x1921] BNE *+31 ; 0x1940  *) (compile m ? BNE (maIMM1 〈x1,xD〉) I) @
(* [0x1923] LDHX 5,SP          *) (compile m ? LDHX (maSP1 〈x0,x5〉) I) @
(* [0x1926] BNE *+26 ; 0x1940  *) (compile m ? BNE (maIMM1 〈x1,x8〉) I) @
(* [0x1928] LDHX 9,SP          *) (compile m ? LDHX (maSP1 〈x0,x9〉) I) @
(* [0x192B] PSHX               *) (compile m ? PSHX maINH I) @
(* [0x192C] AIX #1             *) (compile m ? AIX (maIMM1 〈x0,x1〉) I) @
(* [0x192E] STHX 10,SP         *) (compile m ? STHX (maSP1 〈x0,xA〉) I) @
(* [0x1931] PULX               *) (compile m ? PULX maINH I) @
(* [0x1932] LSLX               *) (compile m ? ASL maINHX I) @
(* [0x1933] LDA 2,SP           *) (compile m ? LDA (maSP1 〈x0,x2〉) I) @
(* [0x1936] CLRH               *) (compile m ? CLR maINHH I) @
(* [0x1937] STA 257,X          *) (compile m ? STA (maIX2 〈〈x0,x1〉:〈x0,x1〉〉) I) @
(* [0x193A] LDA 1,SP           *) (compile m ? LDA (maSP1 〈x0,x1〉) I) @
(* [0x193D] STA 256,X          *) (compile m ? STA (maIX2 〈〈x0,x1〉:〈x0,x0〉〉) I) @
(* [0x1940] TSX                *) (compile m ? TSX maINH I) @
(* [0x1941] INC 1,X            *) (compile m ? INC (maIX1 〈x0,x1〉) I) @
(* [0x1943] BNE *+3 ; 0x1946   *) (compile m ? BNE (maIMM1 〈x0,x1〉) I) @
(* [0x1945] INC ,X             *) (compile m ? INC maIX0 I) @
(* [0x1946] LDHX 1,SP          *) (compile m ? LDHX (maSP1 〈x0,x1〉) I) @
(* [0x1949] CPHX #elems        *) (compile m ? CPHX (maIMM2 elems) I) @
(* [0x194C] BCS *-120 ; 0x18D4 *) (compile m ? BCS (maIMM1 〈x8,x6〉) I) @
(* [0x194E] AIS #10            *) (compile m ? AIS (maIMM1 〈x0,xA〉) I) @
(* [0x1950] STOP ->1951 !FINE! *) (compile m ? STOP maINH I) @
(* [0x1951] CLRX               *) (compile m ? CLR maINHX I) @
(* [0x1952] CLRH               *) (compile m ? CLR maINHH I) @
(* [0x1953] STHX 9,SP          *) (compile m ? STHX (maSP1 〈x0,x9〉) I) @
(* [0x1956] CLRH               *) (compile m ? CLR maINHH I) @
(* [0x1957] STHX 7,SP          *) (compile m ? STHX (maSP1 〈x0,x7〉) I) @
(* [0x195A] INCX               *) (compile m ? INC maINHX I) @
(* [0x195B] RTS                *) (compile m ? RTS maINH I) @

(*
static void _PUSH_ARGS_L(void) { ... }
*)

(* [0x195C] LDA 3,X    *) (compile m ? LDA (maIX1 〈x0,x3〉) I) @
(* [0x195E] PSHA       *) (compile m ? PSHA maINH I) @
(* [0x195F] LDA 2,X    *) (compile m ? LDA (maIX1 〈x0,x2〉) I) @
(* [0x1961] PSHA       *) (compile m ? PSHA maINH I) @
(* [0x1962] LDHX ,X    *) (compile m ? LDHX maIX0 I) @
(* [0x1964] PSHX       *) (compile m ? PSHX maINH I) @
(* [0x1965] PSHH       *) (compile m ? PSHH maINH I) @
(* [0x1966] LDHX 7,SP  *) (compile m ? LDHX (maSP1 〈x0,x7〉) I) @
(* [0x1969] LDA 3,X    *) (compile m ? LDA (maIX1 〈x0,x3〉) I) @
(* [0x196B] STA 17,SP  *) (compile m ? STA (maSP1 〈x1,x1〉) I) @
(* [0x196E] LDA 2,X    *) (compile m ? LDA (maIX1 〈x0,x2〉) I) @
(* [0x1970] STA 16,SP  *) (compile m ? STA (maSP1 〈x1,x0〉) I) @
(* [0x1973] LDHX ,X    *) (compile m ? LDHX maIX0 I) @
(* [0x1975] STHX 14,SP *) (compile m ? STHX (maSP1 〈x0,xE〉) I) @
(* [0x1978] LDHX 5,SP  *) (compile m ? LDHX (maSP1 〈x0,x5〉) I) @
(* [0x197B] JMP ,X     *) (compile m ? JMP maINHX0ADD I) @

(*
static void _ENTER_BINARY_L(void) { ... }
*)

(* [0x197C] PSHA       *) (compile m ? PSHA maINH I) @
(* [0x197D] PSHX       *) (compile m ? PSHX maINH I) @
(* [0x197E] PSHH       *) (compile m ? PSHH maINH I) @
(* [0x197F] PSHX       *) (compile m ? PSHX maINH I) @
(* [0x1980] PSHH       *) (compile m ? PSHH maINH I) @
(* [0x1981] LDHX 6,SP  *) (compile m ? LDHX (maSP1 〈x0,x6〉) I) @
(* [0x1984] PSHX       *) (compile m ? PSHX maINH I) @
(* [0x1985] PSHH       *) (compile m ? PSHH maINH I) @
(* [0x1986] LDHX 10,SP *) (compile m ? LDHX (maSP1 〈x0,xA〉) I) @
(* [0x1989] STHX 8,SP  *) (compile m ? STHX (maSP1 〈x0,x8〉) I) @
(* [0x198C] LDHX 12,SP *) (compile m ? LDHX (maSP1 〈x0,xC〉) I) @
(* [0x198F] JMP 0x195C *) (compile m ? JMP (maIMM2 〈〈x1,x9〉:〈x5,xC〉〉) I) @

(*
static void _IDIVMOD (char dummy_sgn, int j, int dummy, int i, ...) { ... }
*)

(* [0x1992] TST 4,SP            *) (compile m ? TST (maSP1 〈x0,x4〉) I) @
(* [0x1995] BNE *+28 ; 0x19B1   *) (compile m ? BNE (maIMM1 〈x1,xA〉) I) @
(* [0x1997] TSX                 *) (compile m ? TSX maINH I) @
(* [0x1998] LDA 7,X             *) (compile m ? LDA (maIX1 〈x0,x7〉) I) @
(* [0x199A] LDX 4,X             *) (compile m ? LDX (maIX1 〈x0,x4〉) I) @
(* [0x199C] CLRH                *) (compile m ? CLR maINHH I) @
(* [0x199D] DIV                 *) (compile m ? DIV maINH I) @
(* [0x199E] STA 4,SP            *) (compile m ? STA (maSP1 〈x0,x4〉) I) @
(* [0x19A1] LDA 9,SP            *) (compile m ? LDA (maSP1 〈x0,x9〉) I) @
(* [0x19A4] DIV                 *) (compile m ? DIV maINH I) @
(* [0x19A5] STA 5,SP            *) (compile m ? STA (maSP1 〈x0,x5〉) I) @
(* [0x19A8] CLR 8,SP            *) (compile m ? CLR (maSP1 〈x0,x8〉) I) @
(* [0x19AB] PSHH                *) (compile m ? PSHH maINH I) @
(* [0x19AC] PULA                *) (compile m ? PULA maINH I) @
(* [0x19AD] STA 9,SP            *) (compile m ? STA (maSP1 〈x0,x9〉) I) @
(* [0x19B0] RTS                 *) (compile m ? RTS maINH I) @
(* [0x19B1] CLRA                *) (compile m ? CLR maINHA I) @
(* [0x19B2] PSHA                *) (compile m ? PSHA maINH I) @
(* [0x19B3] LDX #0x08           *) (compile m ? LDX (maIMM1 〈x0,x8〉) I) @
(* [0x19B5] CLC                 *) (compile m ? CLC maINH I) @
(* [0x19B6] ROL 10,SP           *) (compile m ? ROL (maSP1 〈x0,xA〉) I) @
(* [0x19B9] ROL 9,SP            *) (compile m ? ROL (maSP1 〈x0,x9〉) I) @
(* [0x19BC] ROL 1,SP            *) (compile m ? ROL (maSP1 〈x0,x1〉) I) @
(* [0x19BF] LDA 5,SP            *) (compile m ? LDA (maSP1 〈x0,x5〉) I) @
(* [0x19C2] CMP 1,SP            *) (compile m ? CMP (maSP1 〈x0,x1〉) I) @
(* [0x19C5] BHI *+31 ; 0x19E4   *) (compile m ? BHI (maIMM1 〈x1,xD〉) I) @
(* [0x19C7] BNE *+10 ; 0x19D1   *) (compile m ? BNE (maIMM1 〈x0,x8〉) I) @
(* [0x19C9] LDA 6,SP            *) (compile m ? LDA (maSP1 〈x0,x6〉) I) @
(* [0x19CC] CMP 9,SP            *) (compile m ? CMP (maSP1 〈x0,x9〉) I) @
(* [0x19CF] BHI *+21 ; 0x19E4   *) (compile m ? BHI (maIMM1 〈x1,x3〉) I) @
(* [0x19D1] LDA 9,SP            *) (compile m ? LDA (maSP1 〈x0,x9〉) I) @
(* [0x19D4] SUB 6,SP            *) (compile m ? SUB (maSP1 〈x0,x6〉) I) @
(* [0x19D7] STA 9,SP            *) (compile m ? STA (maSP1 〈x0,x9〉) I) @
(* [0x19DA] LDA 1,SP            *) (compile m ? LDA (maSP1 〈x0,x1〉) I) @
(* [0x19DD] SBC 5,SP            *) (compile m ? SBC (maSP1 〈x0,x5〉) I) @
(* [0x19E0] STA 1,SP            *) (compile m ? STA (maSP1 〈x0,x1〉) I) @
(* [0x19E3] SEC                 *) (compile m ? SEC maINH I) @
(* [0x19E4] DBNZX *-46 ; 0x19B6 *) (compile m ? DBNZ (maINHX_and_IMM1 〈xD,x0〉) I) @
(* [0x19E6] LDA 10,SP           *) (compile m ? LDA (maSP1 〈x0,xA〉) I) @
(* [0x19E9] ROLA                *) (compile m ? ROL maINHA I) @
(* [0x19EA] STA 6,SP            *) (compile m ? STA (maSP1 〈x0,x6〉) I) @
(* [0x19ED] LDA 9,SP            *) (compile m ? LDA (maSP1 〈x0,x9〉) I) @
(* [0x19F0] STA 10,SP           *) (compile m ? STA (maSP1 〈x0,xA〉) I) @
(* [0x19F3] PULA                *) (compile m ? PULA maINH I) @
(* [0x19F4] STA 8,SP            *) (compile m ? STA (maSP1 〈x0,x8〉) I) @
(* [0x19F7] CLR 4,SP            *) (compile m ? CLR (maSP1 〈x0,x4〉) I) @
(* [0x19FA] RTS                 *) (compile m ? RTS maINH I) @

(*
static void _LADD_k_is_k_plus_j(_PARAM_BINARY_L) { ... }
*)

(* [0x19FB] TSX      *) (compile m ? TSX maINH I) @
(* [0x19FC] LDA 18,X *) (compile m ? LDA (maIX1 〈x1,x2〉) I) @
(* [0x19FE] ADD 5,X  *) (compile m ? ADD (maIX1 〈x0,x5〉) I) @
(* [0x1A00] STA 18,X *) (compile m ? STA (maIX1 〈x1,x2〉) I) @
(* [0x1A02] LDA 17,X *) (compile m ? LDA (maIX1 〈x1,x1〉) I) @
(* [0x1A04] ADC 4,X  *) (compile m ? ADC (maIX1 〈x0,x4〉) I) @
(* [0x1A06] STA 17,X *) (compile m ? STA (maIX1 〈x1,x1〉) I) @
(* [0x1A08] LDA 16,X *) (compile m ? LDA (maIX1 〈x1,x0〉) I) @
(* [0x1A0A] ADC 3,X  *) (compile m ? ADC (maIX1 〈x0,x3〉) I) @
(* [0x1A0C] STA 16,X *) (compile m ? STA (maIX1 〈x1,x0〉) I) @
(* [0x1A0E] LDA 15,X *) (compile m ? LDA (maIX1 〈x0,xF〉) I) @
(* [0x1A10] ADC 2,X  *) (compile m ? ADC (maIX1 〈x0,x2〉) I) @
(* [0x1A12] STA 15,X *) (compile m ? STA (maIX1 〈x0,xF〉) I) @
(* [0x1A14] AIS #10  *) (compile m ? AIS (maIMM1 〈x0,xA〉) I) @
(* [0x1A16] PULH     *) (compile m ? PULH maINH I) @
(* [0x1A17] PULX     *) (compile m ? PULX maINH I) @
(* [0x1A18] PULA     *) (compile m ? PULA maINH I) @
(* [0x1A19] RTS      *) (compile m ? RTS maINH I) @

(*
void _IMODU_STAR08(int i, ...) { ... }
*)

(* [0x1A1A] AIS #-2    *) (compile m ? AIS (maIMM1 〈xF,xE〉) I) @
(* [0x1A1C] STHX 1,SP  *) (compile m ? STHX (maSP1 〈x0,x1〉) I) @
(* [0x1A1F] PSHA       *) (compile m ? PSHA maINH I) @
(* [0x1A20] JSR 0x1992 *) (compile m ? JSR (maIMM2 〈〈x1,x9〉:〈x9,x2〉〉) I) @
(* [0x1A23] PULA       *) (compile m ? PULA maINH I) @
(* [0x1A24] AIS #2     *) (compile m ? AIS (maIMM1 〈x0,x2〉) I) @
(* [0x1A26] LDHX 3,SP  *) (compile m ? LDHX (maSP1 〈x0,x3〉) I) @
(* [0x1A29] RTS        *) (compile m ? RTS maINH I) @

(*
void _LADD(void) { ... }
*)

(* [0x1A2A] JSR 0x197C *) (compile m ? JSR (maIMM2 〈〈x1,x9〉:〈x7,xC〉〉) I) @
(* [0x1A2D] JSR 0x19FB *) (compile m ? JSR (maIMM2 〈〈x1,x9〉:〈xF,xB〉〉) I) @

(*
void _POP32(void) { ... }
*)

(* [0x1A30] PSHA     *) (compile m ? PSHA maINH I) @
(* [0x1A31] LDA 4,SP *) (compile m ? LDA (maSP1 〈x0,x4〉) I) @
(* [0x1A34] STA ,X   *) (compile m ? STA maIX0 I) @
(* [0x1A35] LDA 5,SP *) (compile m ? LDA (maSP1 〈x0,x5〉) I) @
(* [0x1A38] STA 1,X  *) (compile m ? STA (maIX1 〈x0,x1〉) I) @
(* [0x1A3A] LDA 6,SP *) (compile m ? LDA (maSP1 〈x0,x6〉) I) @
(* [0x1A3D] STA 2,X  *) (compile m ? STA (maIX1 〈x0,x2〉) I) @
(* [0x1A3F] LDA 7,SP *) (compile m ? LDA (maSP1 〈x0,x7〉) I) @
(* [0x1A42] STA 3,X  *) (compile m ? STA (maIX1 〈x0,x3〉) I) @
(* [0x1A44] PULA     *) (compile m ? PULA maINH I) @
(* [0x1A45] PULH     *) (compile m ? PULH maINH I) @
(* [0x1A46] PULX     *) (compile m ? PULX maINH I) @
(* [0x1A47] AIS #4   *) (compile m ? AIS (maIMM1 〈x0,x4〉) I) @
(* [0x1A49] JMP ,X   *) (compile m ? JMP maINHX0ADD I)

(* attraverso simulazione in CodeWarrior si puo' enunciare che dopo
   80+(65*n*(n+1)*(n+2))/6 si sara' entrati in stato STOP corrispondente
   AFTER: HX=num PC=0x1951 I=0 *)
 ).

(* creazione del processore+caricamento+impostazione registri *)
definition dTest_HCS08_gNum_status ≝
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
       (start_of_mcu_version
        MC9S08GB60 t
        (load_from_source_at t (* carica data in RAM:dTest_HCS08_RAM *)
         (load_from_source_at t (zero_memory t) (* carica source in ROM:addr *)
           (dTest_HCS08_cSort_source elems) addr)
          data dTest_HCS08_RAM)
        (build_memory_type_of_mcu_version MC9S08GB60 t)
        (mk_byte8 x0 x0) (mk_byte8 x0 x0) (* non deterministici tutti a 0 *)
        false false false false false false) (* non deterministici tutti a 0 *)
       PC_op)
      HX_op)
     (mk_word16 (mk_byte8 x0 x1) (mk_byte8 x6 xF)))
    true)
   A_op)
  I_op.

(* NUMERI AUREI: Somma divisori(x)=x, fino a 0xFFFF sono 6/28/496/8128 *)
definition dTest_HCS08_gNum_aurei ≝
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
let rec dTest_HCS08_gNum_execute1 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute1 m t (execute m t (TickOK ? s') (ntot+2)) n' ntot ]
  ].

(* esecuzione execute k*(n+1)*(n+2) *)
let rec dTest_HCS08_gNum_execute2 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute2 m t (dTest_HCS08_gNum_execute1 m t (TickOK ? s') (ntot+1) ntot) n' ntot ]
  ].

(* esecuzione execute k*n*(n+1)*(n+2) *)
let rec dTest_HCS08_gNum_execute3 (m:mcu_type) (t:memory_impl) (s:tick_result (any_status m t)) (n,ntot:nat) on n ≝
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ match n with
   [ O ⇒ TickOK ? s'
   | S n' ⇒ dTest_HCS08_gNum_execute3 m t (dTest_HCS08_gNum_execute2 m t (TickOK ? s') ntot ntot) n' ntot ]
  ].

(* esecuzione execute 80+11*n*(n+1)*(n+2) *)
definition dTest_HCS08_gNum_execute4 ≝
λm:mcu_type.λt:memory_impl.λs:tick_result (any_status m t).λntot:nat.
 match s with
  [ TickERR s' error ⇒ TickERR ? s' error
  | TickSUSP s' susp ⇒ TickSUSP ? s' susp
  | TickOK s' ⇒ execute m t (dTest_HCS08_gNum_execute3 m t (TickOK ? s') 11 ntot) 80
  ].

(* parametrizzazione dell'enunciato del teorema parziale *)
lemma dTest_HCS08_gNum_aux ≝
λt:memory_impl.λnum:word16.
 (* 2) match di esecuzione su tempo in forma di upperbound *)
 match dTest_HCS08_gNum_execute4 HCS08 t
  (TickOK ? (dTest_HCS08_gNum_status t true 〈x0,x0〉 〈〈x1,xA〉:〈x0,x0〉〉 〈〈x1,x8〉:〈xB,xE〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num dTest_zeros))
  (* tempo di esecuzione 80+11*n*(n+1)*(n+2) *)
  num with
   [ TickERR s _ ⇒ None ?
   (* azzeramento tutta RAM tranne dati *)
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 t s (load_from_source_at t (get_mem_desc HCS08 t s) dTest_zeros3K 〈〈x0,x1〉:〈x2,x0〉〉))
   | TickOK s ⇒ None ?
   ] =
  Some ? (dTest_HCS08_gNum_status t false 〈x0,x0〉 num 〈〈x1,x9〉:〈x5,x1〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num (dTest_HCS08_gNum_aurei num)).

definition gNumCalc ≝
λnum:word16.
 match dTest_HCS08_gNum_execute4 HCS08 MEM_TREE
  (TickOK ? (dTest_HCS08_gNum_status MEM_TREE true 〈x0,x0〉 〈〈x1,xA〉:〈x0,x0〉〉 〈〈x1,x8〉:〈xB,xE〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num dTest_zeros))
  num with
   [ TickERR s _ ⇒ None ?
   | TickSUSP s _ ⇒ Some ? (set_mem_desc HCS08 MEM_TREE s (load_from_source_at MEM_TREE (get_mem_desc HCS08 MEM_TREE s) dTest_zeros3K 〈〈x0,x1〉:〈x2,x0〉〉))
   | TickOK s ⇒ None ?
   ].

definition gNumNoCalc ≝
λnum:word16.
 Some ? (dTest_HCS08_gNum_status MEM_TREE false 〈x0,x0〉 num 〈〈x1,x9〉:〈x5,x1〉〉 〈〈x1,x8〉:〈xB,xE〉〉 num (dTest_HCS08_gNum_aurei num)).

definition gNumCalc1    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x1〉〉.
definition gNumCalc2    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x2〉〉.
definition gNumCalc5    ≝ gNumCalc 〈〈x0,x0〉:〈x0,x5〉〉.
definition gNumCalc10   ≝ gNumCalc 〈〈x0,x0〉:〈x0,xA〉〉.
definition gNumCalc20   ≝ gNumCalc 〈〈x0,x0〉:〈x1,x4〉〉.
definition gNumCalc50   ≝ gNumCalc 〈〈x0,x0〉:〈x3,x2〉〉.
definition gNumCalc100  ≝ gNumCalc 〈〈x0,x0〉:〈x6,x4〉〉.
definition gNumCalc250  ≝ gNumCalc 〈〈x0,x0〉:〈xF,xA〉〉.
definition gNumCalc500  ≝ gNumCalc 〈〈x0,x1〉:〈xF,x4〉〉.
definition gNumCalc1000 ≝ gNumCalc 〈〈x0,x3〉:〈xE,x8〉〉.

definition gNumNoCalc1    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x1〉〉.
definition gNumNoCalc2    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x2〉〉.
definition gNumNoCalc5    ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,x5〉〉.
definition gNumNoCalc10   ≝ gNumNoCalc 〈〈x0,x0〉:〈x0,xA〉〉.
definition gNumNoCalc20   ≝ gNumNoCalc 〈〈x0,x0〉:〈x1,x4〉〉.
definition gNumNoCalc50   ≝ gNumNoCalc 〈〈x0,x0〉:〈x3,x2〉〉.
definition gNumNoCalc100  ≝ gNumNoCalc 〈〈x0,x0〉:〈x6,x4〉〉.
definition gNumNoCalc250  ≝ gNumNoCalc 〈〈x0,x0〉:〈xF,xA〉〉.
definition gNumNoCalc500  ≝ gNumNoCalc 〈〈x0,x1〉:〈xF,x4〉〉.
definition gNumNoCalc1000 ≝ gNumNoCalc 〈〈x0,x3〉:〈xE,x8〉〉.
