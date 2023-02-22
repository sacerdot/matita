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

include "freescale/status.ma".

(* *********************************** *)
(* IMPOSTAZIONI SPECIFICHE DEI MODELLI *)
(* *********************************** *)

(* modelli di HC05 *)
inductive HC05_mcu_model : Type ≝
  MC68HC05J5A: HC05_mcu_model
  (*..*).   

(* modelli di HC08 *)
inductive HC08_mcu_model : Type ≝
  MC68HC08AB16A: HC08_mcu_model
  (*..*). 

(* modelli di HCS08 *)
inductive HCS08_mcu_model : Type ≝
  MC9S08AW60  : HCS08_mcu_model
| MC9S08GB60  : HCS08_mcu_model
| MC9S08GT60  : HCS08_mcu_model
| MC9S08GB32  : HCS08_mcu_model
| MC9S08GT32  : HCS08_mcu_model
| MC9S08GT16  : HCS08_mcu_model
| MC9S08GB60A : HCS08_mcu_model
| MC9S08GT60A : HCS08_mcu_model
| MC9S08GB32A : HCS08_mcu_model
| MC9S08GT32A : HCS08_mcu_model
| MC9S08GT16A : HCS08_mcu_model
| MC9S08GT8A  : HCS08_mcu_model
| MC9S08LC60  : HCS08_mcu_model
| MC9S08LC36  : HCS08_mcu_model
| MC9S08QD4   : HCS08_mcu_model
| MC9S08QD2   : HCS08_mcu_model
| MC9S08QG8   : HCS08_mcu_model
| MC9S08QG4   : HCS08_mcu_model
| MC9S08RC60  : HCS08_mcu_model
| MC9S08RD60  : HCS08_mcu_model
| MC9S08RE60  : HCS08_mcu_model
| MC9S08RG60  : HCS08_mcu_model
| MC9S08RC32  : HCS08_mcu_model
| MC9S08RD32  : HCS08_mcu_model
| MC9S08RE32  : HCS08_mcu_model
| MC9S08RG32  : HCS08_mcu_model
| MC9S08RC16  : HCS08_mcu_model
| MC9S08RD16  : HCS08_mcu_model
| MC9S08RE16  : HCS08_mcu_model
| MC9S08RC8   : HCS08_mcu_model
| MC9S08RD8   : HCS08_mcu_model
| MC9S08RE8   : HCS08_mcu_model.

(* modelli di RS08 *)
inductive RS08_mcu_model : Type ≝
  MC9RS08KA1 : RS08_mcu_model
| MC9RS08KA2 : RS08_mcu_model.

(* raggruppamento dei modelli *)
inductive any_mcu_model : Type ≝
  FamilyHC05  : HC05_mcu_model → any_mcu_model
| FamilyHC08  : HC08_mcu_model → any_mcu_model
| FamilyHCS08 : HCS08_mcu_model → any_mcu_model
| FamilyRS08  : RS08_mcu_model → any_mcu_model.

definition c_FamilyHC05:= FamilyHC05.
definition c_FamilyHC08:= FamilyHC08.
definition c_FamilyHCS08:=FamilyHCS08.
definition c_FamilyRS08:= FamilyRS08.

coercion c_FamilyHC05.
coercion c_FamilyHC08.
coercion c_FamilyHCS08.
coercion c_FamilyRS08.

(* 
condizioni errore interne alla MCU
(Il programma viene caricato dal produttore in ROM o impostato in EEPROM)
HC05: +illegal address during opcode fetch
HC08: +illegal address duting opcode fetch (ILAD mascherabile)
      +illegal opcode (ILOP mascherabile)

(Il programma viene programmato nella FLASH)       
HCS08: +illegal address during opcode fetch (ILAD mascherabile)
       +illegal opcode (ILOP mascherabile)
       +security = accesso a RAM e zone FLASH dichiarate sicure da zone sicure
                   da' 0 in lettura e ignore in scrittura, [FLASH]SEC00:SEC01 (1,0)
                   corrisponde a OFF, altre ON, disattivabile solo da modalita' sicura se
                   opzione [FLASH]KEYEN e' 1 passando chiave a 8byte da modalita' sicura.
                   Altrimenti disattivabile solo con FLASH mass erase. Obbiettivo
                   e' impedire duplicazione di software di controllo, dato che esiste
                   modalita' debugging. A restart viene ricaricata da FLASH impostazione
                   sicurezza!
RS08: +illegal address durting opcode fetch (ILAD) mascherabile
      +illegal opcode (ILOP mascherabile)
      +security = solo la FLASH e' considerata sicura. Stesso meccanismo di HCS08
                  ma governato solo da [FLASH]SECD (0) OFF.Una volta attivato l'unica
                  disattivazione e' la cancellazione della FLASH.
*)

(* memoria degli HC05 *)
definition memory_type_of_FamilyHC05 ≝
λm:HC05_mcu_model.match m with
  [ MC68HC05J5A ⇒
   [
  (* astraggo molto *)
  (* 0x0000-0x001F,0x0FF0: sarebbe memory mapped IO *)
   
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 MEM_READ_WRITE (* 128B RAM+STACK *)
   ; tripleT ??? 〈〈x0,x3〉:〈x0,x0〉〉 〈〈x0,xC〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 2560B USER ROM *)
   ; tripleT ??? 〈〈x0,xE〉:〈x0,x0〉〉 〈〈x0,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 512B INTERNAL ROM *)
    ]
   (*..*)
  ].

(* memoria degli HC08 *)
definition memory_type_of_FamilyHC08 ≝
λm:HC08_mcu_model.match m with
  [ MC68HC08AB16A ⇒
   [
  (* astraggo molto *) 
  (* 0x0000-0x004F,0xFE00-0xFE01,0xFE03,
     0xFE0C-0xFE11,0xFE1A-0xFE1D,0xFE1F: sarebbe memory mapped IO *)
  (* 0x0500-0x057F,0xFE02,0xFE04-0xFE07,
     0xFE09-0xFE0B,0xFE12-0xFE19,0xFE1E,0xFFC0-0xFFCF : sarebbe reserved *)
      
     tripleT ??? 〈〈x0,x0〉:〈x5,x0〉〉 〈〈x0,x2〉:〈x4,xF〉〉 MEM_READ_WRITE (* 512B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x0,x0〉〉 〈〈x0,x9〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 512B EEPROM *)
   ; tripleT ??? 〈〈xB,xE〉:〈x0,x0〉〉 〈〈xF,xD〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B ROM *)
   ; tripleT ??? 〈〈xF,xE〉:〈x2,x0〉〉 〈〈xF,xF〉:〈x5,x2〉〉 MEM_READ_ONLY  (* 307B ROM *)
   ; tripleT ??? 〈〈xF,xF〉:〈xD,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 48B ROM *) ]
   (*..*)
  ].

(* memoria degli HCS08 *)
definition memory_type_of_FamilyHCS08 ≝
λm:HCS08_mcu_model.match m with
  [ MC9S08AW60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x006F,0x1800-0x185F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x7,x0〉〉 〈〈x0,x8〉:〈x6,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x7,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 3984B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x6,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59296B FLASH *) ]
  | MC9S08GB60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x1,x0〉:〈x7,xF〉〉 MEM_READ_WRITE (* 4096B RAM *)
   ; tripleT ??? 〈〈x1,x0〉:〈x8,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1920B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08GT60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x1,x0〉:〈x7,xF〉〉 MEM_READ_WRITE (* 4096B RAM *)
   ; tripleT ??? 〈〈x1,x0〉:〈x8,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1920B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08GB32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08GT32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08GT16 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x4〉:〈x7,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08GB60A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x1,x0〉:〈x7,xF〉〉 MEM_READ_WRITE (* 4096B RAM *)
   ; tripleT ??? 〈〈x1,x0〉:〈x8,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1920B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08GT60A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x1,x0〉:〈x7,xF〉〉 MEM_READ_WRITE (* 4096B RAM *)
   ; tripleT ??? 〈〈x1,x0〉:〈x8,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1920B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08GB32A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08GT32A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08GT16A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08GT8A ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x007F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x8,x0〉〉 〈〈x0,x8〉:〈x7,xF〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08LC60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x186F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x1,x0〉:〈x5,xF〉〉 MEM_READ_WRITE (* 4096B RAM *)
   ; tripleT ??? 〈〈x1,x0〉:〈x6,x0〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1952B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x7,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59280B FLASH *) ]
  | MC9S08LC36 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x186F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x0,xA〉:〈x5,xF〉〉 MEM_READ_WRITE (* 2560B RAM *)
   ; tripleT ??? 〈〈x1,x8〉:〈x7,x0〉〉 〈〈x4,x8〉:〈x6,xF〉〉 MEM_READ_ONLY  (* 12288B FLASH *)
   ; tripleT ??? 〈〈xA,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 24576B FLASH *) ]
  | MC9S08QD4 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x184F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x0,x1〉:〈x5,xF〉〉 MEM_READ_WRITE (* 256B RAM *)
   ; tripleT ??? 〈〈xF,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4096B FLASH *) ]
  | MC9S08QD2 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x184F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x0,x1〉:〈x5,xF〉〉 MEM_READ_WRITE (* 256B RAM *)
   ; tripleT ??? 〈〈xF,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4096B FLASH *) ]
  | MC9S08QG8 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x184F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x0,x2〉:〈x5,xF〉〉 MEM_READ_WRITE (* 512B RAM *)
   ; tripleT ??? 〈〈xE,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 8192B FLASH *) ]
  | MC9S08QG4 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x005F,0x1800-0x184F: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x6,x0〉〉 〈〈x0,x2〉:〈x5,xF〉〉 MEM_READ_WRITE (* 512B RAM *)
   ; tripleT ??? 〈〈xE,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 8192B FLASH *) ]
  | MC9S08RC60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x4,x6〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4026B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08RD60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x4,x6〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4026B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08RE60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x4,x6〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4026B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08RG60 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x0,x8〉:〈x4,x6〉〉 〈〈x1,x7〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 4026B FLASH *)
   ; tripleT ??? 〈〈x1,x8〉:〈x2,xC〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 59348B FLASH *) ]
  | MC9S08RC32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08RD32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08RE32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08RG32 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x0045,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x6〉〉 〈〈x0,x8〉:〈x4,x5〉〉 MEM_READ_WRITE (* 2048B RAM *)
   ; tripleT ??? 〈〈x8,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 32768B FLASH *) ]
  | MC9S08RC16 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08RD16 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08RE16 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xC,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 16384B FLASH *) ]
  | MC9S08RC8 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xE,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 8192B FLASH *) ]
  | MC9S08RD8 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xE,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 8192B FLASH *) ]
  | MC9S08RE8 ⇒
   [ 
  (* astraggo molto *)
  (* 0x0000-0x003F,0x1800-0x182B: sarebbe memory mapped IO *)
  
     tripleT ??? 〈〈x0,x0〉:〈x4,x0〉〉 〈〈x0,x4〉:〈x3,xF〉〉 MEM_READ_WRITE (* 1024B RAM *)
   ; tripleT ??? 〈〈xE,x0〉:〈x0,x0〉〉 〈〈xF,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 8192B FLASH *) ]
  ].

(* memoria dei RS08 *)
definition memory_type_of_FamilyRS08 ≝
λm:RS08_mcu_model.match m with
  [ MC9RS08KA1 ⇒
   [
     tripleT ??? 〈〈x0,x0〉:〈x0,x0〉〉 〈〈x0,x0〉:〈x0,xE〉〉 MEM_READ_WRITE (* 15B RAM *)
  (* [000F] e' il registro X *)
  (* 0x0010-0x001E sarebbe memory mapped IO, proviamo per completezza con RAM *)
   ; tripleT ??? 〈〈x0,x0〉:〈x1,x0〉〉 〈〈x0,x0〉:〈x1,xE〉〉 MEM_READ_WRITE (* 15B MEMORY MAPPED IO *)
  (* [001F] e' il registro PAGESEL *)
   ; tripleT ??? 〈〈x0,x0〉:〈x2,x0〉〉 〈〈x0,x0〉:〈x4,xF〉〉 MEM_READ_WRITE (* 48B RAM *)
  (* [00C0-00FF] mappato da PAGESEL su [00pp pppp ppxx xxxx] *)
   ; tripleT ??? 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 MEM_READ_WRITE (* 64B RAM PAGING *)
  (* 0x0200-0x023F sarebbe memory mapped IO, proviamo per completezza con RAM *)
   ; tripleT ??? 〈〈x0,x2〉:〈x0,x0〉〉 〈〈x0,x2〉:〈x3,xF〉〉 MEM_READ_WRITE (* 64B MEMORY MAPPED IO *)
   ; tripleT ??? 〈〈x3,xC〉:〈x0,x0〉〉 〈〈x3,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 1024B FLASH *) ]
  | MC9RS08KA2 ⇒
   [ 
     tripleT ??? 〈〈x0,x0〉:〈x0,x0〉〉 〈〈x0,x0〉:〈x0,xE〉〉 MEM_READ_WRITE (* 15B RAM *)
  (* [000F] e' il registro X *)
  (* 0x0010-0x001E sarebbe memory mapped IO, proviamo per completezza con RAM *)
   ; tripleT ??? 〈〈x0,x0〉:〈x1,x0〉〉 〈〈x0,x0〉:〈x1,xE〉〉 MEM_READ_WRITE (* 15B MEMORY MAPPED IO *)
  (* [001F] e' il registro PAGESEL *)
   ; tripleT ??? 〈〈x0,x0〉:〈x2,x0〉〉 〈〈x0,x0〉:〈x4,xF〉〉 MEM_READ_WRITE (* 48B RAM *)
  (* [00C0-00FF] mappato da PAGESEL su [00pp pppp ppxx xxxx] *)
   ; tripleT ??? 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 MEM_READ_WRITE (* 64B RAM PAGING *)
  (* 0x0200-0x023F sarebbe memory mapped IO, proviamo per completezza con RAM *)
   ; tripleT ??? 〈〈x0,x2〉:〈x0,x0〉〉 〈〈x0,x2〉:〈x3,xF〉〉 MEM_READ_WRITE (* 64B MEMORY MAPPED IO *)
   ; tripleT ??? 〈〈x3,x8〉:〈x0,x0〉〉 〈〈x3,xF〉:〈xF,xF〉〉 MEM_READ_ONLY  (* 2048B FLASH *) ]
  ].

(* ∀modello.descrizione della memoria installata *)
definition memory_type_of_mcu_version ≝
λmcu:any_mcu_model.match mcu with
 [ FamilyHC05  m ⇒ memory_type_of_FamilyHC05 m
 | FamilyHC08  m ⇒ memory_type_of_FamilyHC08 m
 | FamilyHCS08 m ⇒ memory_type_of_FamilyHCS08 m
 | FamilyRS08  m ⇒ memory_type_of_FamilyRS08 m
 ].

(* dato un modello costruisce un descrittore a partire dalla lista precedente *)
definition build_memory_type_of_mcu_version ≝
λmcu:any_mcu_model.λt:memory_impl.
 let rec aux param result ≝
  match param with
   [ nil ⇒ result
   | cons hd tl ⇒ 
    aux tl (check_update_ranged t result (fst3T ??? hd) (snd3T ??? hd) (thd3T ??? hd)) ]
 in aux (memory_type_of_mcu_version mcu) (out_of_bound_memory t).

(* sarebbe programma da caricare/zero_memory, ora test *)
definition memory_of_mcu_version ≝
λmcu:any_mcu_model.λt:memory_impl.match mcu with
 [ FamilyHC05 m ⇒ match m with
  [ MC68HC05J5A ⇒ zero_memory t
    (*..*)
  ]
 | FamilyHC08 m ⇒ match m with
  [ MC68HC08AB16A ⇒ zero_memory t
    (*..*)
  ]
 (* tralascio l'enumerazione dei casi, per ora e' tutto 0 *)
 | FamilyHCS08 _ ⇒ zero_memory t
 | FamilyRS08 _ ⇒ zero_memory t
 ].

(* inferire la mcu a partire dal modello *)
definition mcu_of_model ≝
λm:any_mcu_model.match m with
 [ FamilyHC05  _ ⇒ HC05
 | FamilyHC08  _ ⇒ HC08
 | FamilyHCS08 _ ⇒ HCS08
 | FamilyRS08  _ ⇒ RS08
 ].

(* 
   parametrizzati i non deterministici rispetto a tutti i valori casuali
   che verranno dati dall'esterno di tipo byte8 (ndby1-2) e bool (ndbo1-5).
   l'ACCENSIONE e' totalmente equivalente ad un reset causato da calo di tensione
   (reset V-low), la memoria ed il check puo' essere passata, per esempio da
   - (memory_of_mcu_version MC68HC05J5A)
   - (build_memory_type_of_mcu_version MC68HC05J5A)
*)
definition start_of_mcu_version ≝
λmcu:any_mcu_model.λt:memory_impl.
let pc_reset_h ≝ 〈〈xF,xF〉:〈xF,xE〉〉 in
let pc_reset_l ≝ 〈〈xF,xF〉:〈xF,xF〉〉 in
let pc_RS08_reset ≝ 〈〈xF,xF〉:〈xF,xD〉〉 in
let sp_reset ≝ 〈〈x0,x0〉:〈xF,xF〉〉 in
match mcu
 return λmcu:any_mcu_model.(aux_mem_type t) → (aux_chk_type t) → byte8 → byte8 →
        bool → bool → bool → bool → bool → bool → any_status (mcu_of_model mcu) t
with
(* HC05: parzialmente non deterministico *)
 [ FamilyHC05 m ⇒ λmem:aux_mem_type t.λchk:aux_chk_type t.
                  λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
  let build ≝ λspm,spf,pcm.
  let fetched_pc ≝ mk_word16 (mem_read_abs t mem (and_w16 pc_reset_h pcm)) 
                             (mem_read_abs t mem (and_w16 pc_reset_l pcm)) in
   mk_any_status HC05 t
    (mk_alu_HC05
     (* acc_low: ? *) ndby1 (* indx_low: ? *) ndby2 
     (* sp: reset *) (or_w16 (and_w16 sp_reset spm) spf) spm spf
     (* pc: reset+fetch *) (and_w16 fetched_pc pcm) pcm
     (* H: ? *) ndbo1 (* I: reset *) true (* N: ? *) ndbo2
     (* Z: ? *) ndbo3 (* C: ? *) ndbo4 (* IRQ: ? *) irqfl)
     (* mem *) mem
     (* chk *) chk
     (* clk: reset *) (None ?) in
  match m with
   [ MC68HC05J5A ⇒ build 〈〈x0,x0〉:〈x3,xF〉〉 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,xF〉:〈xF,xF〉〉
     (*..*)
   ]

(* HC08: parzialmente non deterministico *)
 | FamilyHC08 m ⇒ λmem:aux_mem_type t.λchk:aux_chk_type t.
                  λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
  let build ≝
  let fetched_pc ≝ mk_word16 (mem_read_abs t mem pc_reset_h) 
                             (mem_read_abs t mem pc_reset_l) in
   mk_any_status HC08 t
    (mk_alu_HC08
     (* acc_low: ? *) ndby1 (* indw_low: ? *) ndby2 (* indx_high: reset *)  〈x0,x0〉
     (* sp: reset *) sp_reset (* pc: reset+fetch *) fetched_pc
     (* V: ? *) ndbo1 (* H: ? *) ndbo2 (* I: reset *) true
     (* N: ? *) ndbo3 (* Z: ? *) ndbo4 (* C: ? *) ndbo5 (* IRQ: ? *) irqfl)
     (* mem *) mem
     (* chk *) chk
     (* clk: reset *) (None ?) in
  (* tralascio l'enumerazione dei casi, tanto non ci sono maschere da impostare *)
  build

(* HCS08: parzialmente non deterministico *)
 | FamilyHCS08 m ⇒ λmem:aux_mem_type t.λchk:aux_chk_type t.
                   λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
  let build ≝
  let fetched_pc ≝ mk_word16 (mem_read_abs t mem pc_reset_h)
                             (mem_read_abs t mem pc_reset_l) in
   mk_any_status HCS08 t
    (mk_alu_HC08
     (* acc_low: ? *) ndby1 (* indw_low: ? *) ndby2 (* indx_high: reset *)  〈x0,x0〉
     (* sp: reset *) sp_reset (* pc: reset+fetch *) fetched_pc
     (* V: ? *) ndbo1 (* H: ? *) ndbo2 (* I: reset *) true
     (* N: ? *) ndbo3 (* Z: ? *) ndbo4 (* C: ? *) ndbo5 (* IRQ: ? *) irqfl)
     (* mem *) mem
     (* chk *) chk
     (* clk: reset *) (None ?) in
  (* tralascio l'enumerazione dei casi, tanto non ci sono maschere da impostare *)
  build

(* RS08: deterministico *)
 | FamilyRS08 m ⇒ λmem:aux_mem_type t.λchk:aux_chk_type t.
                  λndby1,ndby2:byte8.λirqfl,ndbo1,ndbo2,ndbo3,ndbo4,ndbo5:bool.
  let build ≝ λpcm.
   mk_any_status RS08 t
    (mk_alu_RS08
     (* acc_low: reset *)  〈x0,x0〉
     (* pc: reset *) (and_w16 pc_RS08_reset pcm) pcm
     (* spc: reset *) (and_w16 pc_RS08_reset pcm)
     (* xm: reset *) 〈x0,x0〉 (* psm: *) 〈x8,x0〉
     (* Z: reset *) false (* C: reset *) false)
     (* mem *) mem
     (* chk *) chk
     (* clk: reset *) (None ?) in
  (* tralascio l'enumerazione dei casi, tanto i valori sono uguali *)
  build 〈〈x3,xF〉:〈xF,xF〉〉
 ].

(* 
   cio' che non viene resettato mantiene il valore precedente: nella documentazione
   viene riportato come "unaffected"/"indeterminate"/"unpredictable"
   il soft RESET e' diverso da un calo di tensione e la ram non variera'
*)
definition reset_of_mcu ≝
λm:mcu_type.λt:memory_impl.
let pc_reset_h ≝ 〈〈xF,xF〉:〈xF,xE〉〉 in
let pc_reset_l ≝ 〈〈xF,xF〉:〈xF,xF〉〉 in
let pc_RS08_reset ≝ 〈〈xF,xF〉:〈xF,xD〉〉 in
let sp_reset ≝ 〈〈x0,x0〉:〈xF,xF〉〉 in
 match m return λm:mcu_type.(any_status m t) → (any_status m t) with
(* HC05: parzialmente non deterministico *)
  [ HC05 ⇒ λs:any_status HC05 t.match s with
   [ mk_any_status alu mem chk clk ⇒ match alu with
    [ mk_alu_HC05 acclow indxlow _ spm spf _ pcm hfl _ nfl zfl cfl irqfl ⇒
    let fetched_pc ≝ mk_word16 (mem_read_abs t mem (and_w16 pc_reset_h pcm))
                               (mem_read_abs t mem (and_w16 pc_reset_l pcm)) in
    mk_any_status HC05 t
     (mk_alu_HC05
      (* acc_low: inv. *) acclow (* indx_low: inv. *) indxlow
      (* sp: reset *) (or_w16 (and_w16 sp_reset spm) spf) spm spf
      (* pc: reset+fetch *) (and_w16 fetched_pc pcm) pcm
      (* H: inv. *) hfl (* I: reset *) true (* N: inv. *) nfl
      (* Z: inv. *) zfl (* C: inv. *) cfl (* IRQ: inv *) irqfl)
      (* mem: inv. *) mem
      (* chk: inv. *) chk
      (* clk: reset *) (None ?) ]]
(* HC08: parzialmente non deterministico *)
  | HC08 ⇒ λs:any_status HC08 t.match s with
   [ mk_any_status alu mem chk clk ⇒ match alu with
    [ mk_alu_HC08 acclow indxlow _ _ _ vfl hfl _ nfl zfl cfl irqfl ⇒ 
    let fetched_pc ≝ mk_word16 (mem_read_abs t mem pc_reset_h)
                               (mem_read_abs t mem pc_reset_l) in
    mk_any_status HC08 t
     (mk_alu_HC08
      (* acc_low: inv. *) acclow (* indx_low: inv. *) indxlow (* indx_high: reset *) 〈x0,x0〉
      (* sp: reset *) sp_reset (* pc: reset+fetch *) fetched_pc
      (* V: inv. *) vfl (* H: inv. *) hfl (* I: reset *) true
      (* N: inv. *) nfl (* Z: inv. *) zfl (* C: inv. *) cfl (* IRQ: inv *) irqfl)
      (* mem: inv. *) mem
      (* chk: inv. *) chk
      (* clk: reset *) (None ?) ]]
(* HCS08: parzialmente non deterministico *)
  | HCS08 ⇒ λs:any_status HCS08 t.match s with
   [ mk_any_status alu mem chk clk ⇒ match alu with
    [ mk_alu_HC08 acclow indxlow _ _ _ vfl hfl _ nfl zfl cfl irqfl ⇒ 
    let fetched_pc ≝ mk_word16 (mem_read_abs t mem pc_reset_h)
                               (mem_read_abs t mem pc_reset_l) in
    mk_any_status HCS08 t
     (mk_alu_HC08
      (* acc_low: inv. *) acclow (* indx_low: inv. *) indxlow (* indx_high: reset *) 〈x0,x0〉
      (* sp: reset *) sp_reset (* pc: reset+fetch *) fetched_pc
      (* V: inv. *) vfl (* H: inv. *) hfl (* I: reset *) true
      (* N: inv. *) nfl (* Z: inv. *) zfl (* C: inv. *) cfl (* IRQ: inv *) irqfl)
      (* mem: inv. *) mem
      (* chk: inv. *) chk
      (* clk: reset *) (None ?) ]]
(* RS08: deterministico *)
  | RS08 ⇒ λs:any_status RS08 t.match s with
   [ mk_any_status alu mem chk clk ⇒ match alu with
    [ mk_alu_RS08 _ _ pcm _ _ _ _ _ ⇒
    mk_any_status RS08 t
     (mk_alu_RS08 
      (* acc_low: reset *) 〈x0,x0〉
      (* pc: reset *) (and_w16 pc_RS08_reset pcm) pcm
      (* spc: reset *) (and_w16 pc_RS08_reset pcm)
      (* xm: reset *) 〈x0,x0〉 (* psm: reset *) 〈x8,x0〉
      (* Z: reset *) false (* C: reset *) false)
      (* mem: inv. *) mem
      (* chk: inv. *) chk
      (* clk: reset *) (None ?) ]]
  ].
