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

include "projdat/tuples2.ma".

(* Funzione di unione tra tuple di tipo 1 *)
definition tup1_union: ∀S,T. tuple S → tuple T → tuple (S @T).
* 
  [*
    [ #u #_ @u
    | #d #l #t #r @r
    ]
  | #d #ld #ts1 * #e1 #p1 * #e2 #p2 %
    [ @(e1@e2) | >p1 >p2 normalize // 
    ]
  ]
qed.

(* Definizione della funzione di proiezione n-esima su valori *)
let rec tup1_projval (l:DeqList DeqNat) s (t:tuple s) : DeqList DeqCoer≝ 
  match l with
  [ nil ⇒ []
  | cons a b ⇒ match (nth_opt ? a (Sig_fst ? ? t) ) with
            [None ⇒ tup1_projval b s t
            |Some w ⇒ w::(tup1_projval b s t)]
  ].

(* Definizione della funzione di proiezione n-aria *)
definition tup1_projection ≝  λl,s,t. mk_tuple (getSchema (tup1_projval l s t)) (tup1_projval l s t) (refl ? ? ).

(******************************************************************************)

lemma gSchema_merge: ∀s1,i1,s2,i2.
(s1=getSchema i1)→(s2=getSchema i2)→(s1@s2=getSchema(i1@i2)).
#a #b #c#d #Hp #Hp2 >Hp >Hp2 normalize // qed.

definition tup2_union : tuple_cast→tuple_cast→tuple_cast.
* #s1 * #i1 #p1 * #s2 * #i2 #p2 % 
  [ @(s1@s2)
  | lapply(gSchema_merge … p1 p2) -p1 -p2 #P %
    [ @(i1@i2)
    | @P
    ]
  ]
qed.

definition tup2_projval  ≝ λl,c. tup1_projval l (Schema c) (Tuple c).

definition tup2_projection : list DeqNat→tuple_cast→tuple_cast.
#ids #tc %
  [ @(getSchema (tup2_projval ids tc))
  | % [ @(tup2_projval ids tc) | // ]]
qed.
  
(******************************************************************************)
lemma gSchema_unpack:
∀X,lX. (tail DeqType []=getSchema (tail DeqCoer (X::lX)))→([]=getSchema lX).
#dc #ldc normalize // qed.


lemma lemmata_tl_void0: ∀n,ld,dc,l,P. 

(tup1_projval (n::ld) [] «dc::l,P»=tup1_projval (ld) [] «dc::l,?»).
[ 2: @P
| #n #ln #d #ld #p lapply (gSchema_void2 … p) #pp >pp in p;
  #e normalize //
]
qed.

lemma lemmata_t1_void1: ∀dc, ldc,p,rpl. tup1_projval rpl [] «dc::ldc,p»=[].
#dc #l #P #m elim m -m 
  [ //
  | #n #ld #IH >lemmata_tl_void0 @IH]
qed.

lemma lemmata_t1_void2: ∀ ldc,p,rpl. tup1_projval rpl [] «ldc,p»=[].
#l #P #m elim m -m 
  [ //
  | #n #ld #IH lapply (gSchema_void2 … P) #pp >pp in P; #P normalize
    elim ld -ld
      [ //
      | #dn #ldn #IH normalize @IH]
  ]
qed.

lemma tup1_void_tl:
∀rpl,X,lX,P. (tup1_projval rpl [] «X::lX,P»=tup1_projval rpl [] «lX,?»).
  [ 2: lapply (gSchema_tltl … P) #Hp 
       lapply (gSchema_unpack … Hp) -Hp #Hp @Hp
  | #rpl #dc #ldc #p >lemmata_t1_void1 >lemmata_t1_void2 //
  ]
qed.

lemma tup1_voidt: ∀t,plist. (tup1_projval plist [] t) = [].
#t elim t -t #p elim p -p 
  [ normalize #u #pl elim pl -pl
    [ normalize //
    | #n #ln #IH normalize @IH
    ]
  | #X  #lX #IH #P #rpl 
    lapply (gSchema_tltl … P) #tl lapply (gSchema_unpack … tl) -tl #tl
    lapply (IH tl) -IH #IH lapply (IH … rpl) -IH #IH 
    >lemmata_t1_void2 //]
qed.


(******************************************************************************)
(* Dimostrazioni delle proprietà della seconda proiezione *)

lemma voideton_proj_list_indiff:
∀l,n.
(tup2_projection (l::n) voideton2=tup2_projection (n) voideton2).
#l #d normalize // qed.


lemma voideton_proj : ∀plist. tup2_projection plist voideton2 = voideton2.
#p elim p -p
  [ normalize //
  | #dn #ldn #HP >voideton_proj_list_indiff @HP] qed.


(******************************************************************************)
(* Lemmi accessori *)

lemma gSchema_t1: ∀plist,t. (getSchema (tup1_projval plist [] t))=[].
#p #t >tup1_voidt  normalize // qed.


lemma gSchema_null: getSchema [] = [].
normalize // qed.

lemma t_to_tcV:
∀plist,t.
t_to_tc (getSchema (tup1_projval plist [] t)) (tup1_projection plist [] t)=
t_to_tc (getSchema []) ?.
[ 2: >gSchema_null @t
| #pl * #p #n  >gSchema_null lapply (gSchema_void2 … n) #N destruct
  elim pl -pl
    [ //
    | #dn #ld #IH normalize  normalize in IH; @IH
    ]
qed.

(******************************************************************************)

(*
  Si dimostra che le funzioni di proiezione preservano i contenuti delle tuple,
  mantenendolo inalterato a meno di proiezione.
 *)

theorem preservation3: ∀s,t,l. tup2_projection l (t_to_tc s t)  = (t_to_tc ? (tup1_projection l s t )).
#s elim s -s
  [ #t #plist >t_to_tc_void_as_voideton2
              >voideton_proj
              >t_to_tcV
              normalize
              elim t #p #gs
              lapply (gSchema_void2 … gs)
              #L destruct //
  | #dt #ldt #IH
    * #p #prop #ln
    normalize //
  ]
qed.

theorem preservation4: ∀t,l. 
(tup1_projection l (Schema t) (Tuple t)) = tc_to_t (tup2_projection l t ).
normalize // qed.

(* Si può notare come le funzioni che sono state qui fornite rendono confrontabili
   le tuple, non rendendo più necessarie funzioni di coercizione, come invece
   era necessario per i singoletti di tuple.
 *)