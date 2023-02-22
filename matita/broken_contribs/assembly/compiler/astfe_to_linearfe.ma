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
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "compiler/linearfe.ma".

(* ***************************** *)
(* PASSO 3 : da ASTFE a LINEARFE *)
(* ***************************** *)

(*
  ASTFE_STM_ASG: ∀t:ast_type.
                 astfe_var e false t → astfe_expr e t → astfe_stm e
| ASTFE_STM_INIT: ∀b:bool.∀t:ast_type.
                  astfe_id e b t → astfe_init e t → astfe_stm e
| ASTFE_STM_WHILE: astfe_base_expr e → astfe_body e → astfe_stm e
| ASTFE_STM_IF: ne_list (Prod (astfe_base_expr e) (astfe_body e)) → option (astfe_body e) → astfe_stm e
*)
inductive astfe_to_linearfe_stm_record (fe:aux_flatEnv_type) : Type ≝
  ASTFE_TO_LINEARFE_STM_RECORD_SINGLE: linearfe_stm fe → astfe_to_linearfe_stm_record fe
| ASTFE_TO_LINEARFE_STM_RECORD_MULTI: nat → jumpBlock fe → linearfe_prog fe → astfe_to_linearfe_stm_record fe.

definition defined_astfetolinearfe ≝
λfe.λl:linearfe_prog fe.match l with [ nil ⇒ False | cons _ _ ⇒ True ].

inductive astfe_to_linearfe_stm_record_aux (fe:aux_flatEnv_type) : Type ≝
 ASTFE_TO_LINEARFE_STM_RECORD_AUX: nat → ∀prg:linearfe_prog fe.defined_astfetolinearfe fe prg → astfe_to_linearfe_stm_record_aux fe.

lemma append_to_definedAstfetolinearfe :
 ∀fe.∀h:linearfe_elem fe.∀t:linearfe_prog fe.
  defined_astfetolinearfe fe (cons ? h t).
 intros;
 simplify;
 apply I.
qed.

let rec astfe_to_linearfe_stm fe (ast:astfe_stm fe) (nextL:nat) on ast
 : astfe_to_linearfe_stm_record fe ≝
 match ast with
  [ ASTFE_STM_ASG sType sVar sExpr ⇒
   ASTFE_TO_LINEARFE_STM_RECORD_SINGLE fe (LINEARFE_STM_ASG fe sType sVar sExpr)

  | ASTFE_STM_INIT sB sType sId sInit ⇒
   ASTFE_TO_LINEARFE_STM_RECORD_SINGLE fe (LINEARFE_STM_INIT fe sB sType sId sInit)

  | ASTFE_STM_WHILE sExpr sBody ⇒
  (* while(EXP) { ... } diventa if(EXP) { do { ... } while (EXP); } *)
   match astfe_to_linearfe_body fe sBody (S nextL) (JUMPBLOCK_COND fe sExpr (LABEL_N (N_LABEL (S nextL))) (LABEL_N (N_LABEL nextL))) (S (S nextL)) with
    [ pair resNextL resProg ⇒
     ASTFE_TO_LINEARFE_STM_RECORD_MULTI fe resNextL (JUMPBLOCK_COND fe sExpr (LABEL_N (N_LABEL (S nextL))) (LABEL_N (N_LABEL nextL))) resProg ]

  | ASTFE_STM_IF sNelExprBody sOptBody ⇒
   let rec aux (pNelExprBody:ne_list (Prod (astfe_base_expr fe) (astfe_body fe)))
               (pBeginL:nat) (pNextL:nat) on pNelExprBody
               : astfe_to_linearfe_stm_record_aux fe ≝
    match pNelExprBody with
     [ ne_nil h ⇒
      match sOptBody with
       [ None ⇒
        match astfe_to_linearfe_body fe (snd ?? h) pNextL (JUMPBLOCK_ABS fe (LABEL_N (N_LABEL nextL))) (S pNextL) with
         [ pair resNextL resProg ⇒
          ASTFE_TO_LINEARFE_STM_RECORD_AUX fe resNextL
                                           (cons ? (LINEARFE_ELEM fe (N_LABEL pBeginL) [] (JUMPBLOCK_COND fe (fst ?? h) (LABEL_N (N_LABEL pNextL)) (LABEL_N (N_LABEL nextL)))) (resProg))
                                           (append_to_definedAstfetolinearfe ???) ]

       | Some optBody ⇒
        match astfe_to_linearfe_body fe (snd ?? h) pNextL (JUMPBLOCK_ABS fe (LABEL_N (N_LABEL nextL))) (S (S pNextL)) with
         [ pair resNextL resProg ⇒
          match astfe_to_linearfe_body fe optBody (S pNextL) (JUMPBLOCK_ABS fe (LABEL_N (N_LABEL nextL))) resNextL with
           [ pair resNextL' resProg' ⇒
            ASTFE_TO_LINEARFE_STM_RECORD_AUX fe resNextL'
                                             (cons ? (LINEARFE_ELEM fe (N_LABEL pBeginL) [] (JUMPBLOCK_COND fe (fst ?? h) (LABEL_N (N_LABEL pNextL)) (LABEL_N (N_LABEL (S pNextL))))) (resProg@resProg'))
                                             (append_to_definedAstfetolinearfe ???) ]]

       ]

     | ne_cons h t ⇒
      match astfe_to_linearfe_body fe (snd ?? h) pNextL (JUMPBLOCK_ABS fe (LABEL_N (N_LABEL nextL))) (S (S pNextL)) with
       [ pair resNextL resProg ⇒
        match aux t (S pNextL) resNextL with
         [ ASTFE_TO_LINEARFE_STM_RECORD_AUX resNextL' resProg' _ ⇒
          ASTFE_TO_LINEARFE_STM_RECORD_AUX fe resNextL'
                                           (cons ? (LINEARFE_ELEM fe (N_LABEL pBeginL) [] (JUMPBLOCK_COND fe (fst ?? h) (LABEL_N (N_LABEL pNextL)) (LABEL_N (N_LABEL (S pNextL))))) (resProg@resProg'))
                                           (append_to_definedAstfetolinearfe ???) ]]

     ] in
    match aux sNelExprBody O (S nextL) with
     [ ASTFE_TO_LINEARFE_STM_RECORD_AUX resNextL resProg resDefined ⇒
      match resProg
       return λX:linearfe_prog fe.defined_astfetolinearfe fe X → astfe_to_linearfe_stm_record fe
      with
       (* caso dummy: impossibile! *)
       [ nil ⇒ λp:(defined_astfetolinearfe fe (nil ?)).False_rect ? p

       | cons h t ⇒ λp:(defined_astfetolinearfe fe (cons ? h t)).
        match h with
         [ LINEARFE_ELEM _ _ resJump ⇒
          ASTFE_TO_LINEARFE_STM_RECORD_MULTI fe resNextL resJump t ]

       ] resDefined
     ]
  ]
(*
  ASTFE_BODY: list (astfe_stm e) → astfe_body e
*)
and astfe_to_linearfe_body fe (ast:astfe_body fe)
                              (beginL:nat) (endJump:jumpBlock fe) (nextL:nat) on ast
                              : Prod nat (linearfe_prog fe) ≝
 match ast with
  [ ASTFE_BODY sLStm ⇒
   let rec aux (pLStm:list (astfe_stm fe)) (pRes:list (linearfe_stm fe))
               (pBeginL:nat) (pEndJump:jumpBlock fe) (pNextL:nat)
               on pLStm : Prod nat (linearfe_prog fe) ≝
    match pLStm with
     [ nil ⇒
      pair ?? pNextL [ LINEARFE_ELEM fe (N_LABEL pBeginL) pRes pEndJump ]

     | cons h t ⇒
      match astfe_to_linearfe_stm fe h pNextL with
       [ ASTFE_TO_LINEARFE_STM_RECORD_SINGLE resStm ⇒
        aux t (pRes@[ resStm ]) pBeginL pEndJump pNextL
       | ASTFE_TO_LINEARFE_STM_RECORD_MULTI resNextL resEndJump resProg ⇒
        match aux t [] pNextL pEndJump resNextL with
         [ pair resNextL' resProg' ⇒
          pair ?? resNextL' ([ LINEARFE_ELEM fe (N_LABEL pBeginL) pRes resEndJump ] @ resProg @ resProg') ]]

     ] in aux sLStm [] beginL endJump nextL
  ].

(*
  ASTFE_ROOT: astfe_body e → astfe_root e
*)
definition astfe_to_linearfe ≝
λfe.λast:astfe_root fe.match ast with
 [ ASTFE_ROOT body ⇒ astfe_to_linearfe_body fe body O (JUMPBLOCK_ABS fe LABEL_END) 1 ].

(* ***** OTTIMIZZAZIONE ***** *)

(* individuare gli elementi "x : [] : ABS ..." *)
let rec get_useless_linearfeElem fe (prog:linearfe_prog fe) (res:list (Prod nat nat)) on prog ≝
 match prog with
  [ nil ⇒ res
  | cons h t ⇒ get_useless_linearfeElem fe t (res@(match h with
   [ LINEARFE_ELEM lbl lStm jmpB ⇒ match lStm with
    [ nil ⇒ match jmpB with
     [ JUMPBLOCK_ABS jlbl ⇒ match lbl with
      [ N_LABEL n ⇒ match jlbl with
       [ LABEL_N jlbl' ⇒ match jlbl' with
        [ N_LABEL n' ⇒ [ pair ?? n n' ] ]
       | LABEL_END ⇒ []
       ]]
     | JUMPBLOCK_COND _ _ _ ⇒ [] ]
    | cons _ _ ⇒  [] ]]))
  ].

(* applicare una singola trasformazione *)
let rec useless_linearfeElem_trsf (ul:list (Prod nat nat)) (trsf:Prod nat nat) on ul ≝
 match ul with
  [ nil ⇒ []
  | cons h t ⇒ (match eqb (snd ?? h) (fst ?? trsf) with [ true ⇒ pair ?? (fst ?? h) (snd ?? trsf) | false ⇒ h ]
               )::(useless_linearfeElem_trsf t trsf)
  ].

(* applicare una passata completa di chiusura *)
let rec useless_linearfeElem_closure_aux (preUl,ul:list (Prod nat nat)) on ul ≝
 match ul with
  [ nil ⇒ preUl
  | cons h t ⇒ useless_linearfeElem_closure_aux ((useless_linearfeElem_trsf preUl h)@[h]) t
  ].

definition useless_linearfeElem_closure ≝
λul:list (Prod nat nat).
 reverse_list ? (useless_linearfeElem_closure_aux [] (reverse_list ? (useless_linearfeElem_closure_aux [] ul))).

inductive useless_linearfeElem_res : Type ≝
  USELESS_LINEARFEELEM_RES_DISCARD: nat → useless_linearfeElem_res
| USELESS_LINEARFEELEM_RES_DIFF: nat → useless_linearfeElem_res.

(* interrogazione della mappa di trasformazione sottoposta a chiusura *)
let rec useless_linearfeElem_elim (ul:list (Prod nat nat)) (n:nat) (acc:nat) on ul ≝
 match ul with
  [ nil ⇒ USELESS_LINEARFEELEM_RES_DIFF acc
  | cons h t ⇒ match eqb n (fst ?? h) with
   [ true ⇒ USELESS_LINEARFEELEM_RES_DISCARD (snd ?? h)
   | false ⇒ useless_linearfeElem_elim t n (match gtb n (fst ?? h) with [ true ⇒ S acc | false ⇒ acc])
   ]
  ].

(* eliminazione delle triple useless e compattazione delle label *)
definition useless_linearfeProg_elim_aux ≝
λjmpL:jumpLabel.λul:list (Prod nat nat).
 match jmpL with
  [ LABEL_N lbl ⇒ match lbl with
   [ N_LABEL n ⇒ match useless_linearfeElem_elim ul n O with
    [ USELESS_LINEARFEELEM_RES_DISCARD new ⇒ LABEL_N (N_LABEL new)
    | USELESS_LINEARFEELEM_RES_DIFF diff ⇒ LABEL_N (N_LABEL (n-diff))
    ]]
  | LABEL_END ⇒ LABEL_END
  ].

definition eqLabel ≝
λl1,l2.match l1 with
 [ LABEL_N lbl1 ⇒ match l2 with
  [ LABEL_N lbl2 ⇒ match lbl1 with
   [ N_LABEL n1 ⇒ match lbl2 with
    [ N_LABEL n2 ⇒ eqb n1 n2 ]]
  | LABEL_END ⇒ false ]
 | LABEL_END ⇒ match l2 with
  [ LABEL_N _ ⇒ false | LABEL_END ⇒ true ]
 ].

lemma eq_to_eqlabel : ∀l1,l2.l1 = l2 → eqLabel l1 l2 = true.
 intros 2;
 elim l1 0;
 elim l2 0;
 [ intros;
   destruct H;
   elim j;
   simplify;
   rewrite > eq_to_eqb_true;
   reflexivity
 | intros;
   destruct H
 | intros;
   destruct H
 | intros;
   simplify;
   reflexivity
 ].
qed.

lemma eqlabel_to_eq : ∀l1,l2.eqLabel l1 l2 = true → l1 = l2.
 intros 2;
 elim l1 0;
 elim l2 0;
 [ intros 2;
   elim j 0;
   elim j1 0;
   intros;
   simplify in H:(%);
   rewrite > (eqb_true_to_eq ?? H);
   reflexivity
 | intros;
   simplify in H:(%);
   destruct H
 | intros;
   simplify in H:(%);
   destruct H
 | intros;
   reflexivity
 ].
qed.

let rec useless_linearfeProg_elim fe (prog:linearfe_prog fe) (ul:list (Prod nat nat)) on prog ≝
 match prog with
  [ nil ⇒ []
  | cons h t ⇒ match h with
   [ LINEARFE_ELEM lbl lStm jmpB ⇒ match lbl with
    [ N_LABEL n ⇒ match useless_linearfeElem_elim ul n O with
     (* intero elemento ridondante *)
     [ USELESS_LINEARFEELEM_RES_DISCARD _ ⇒ []
     (* la label e il salto possono necessitare di compattazione *)
     | USELESS_LINEARFEELEM_RES_DIFF diff ⇒
      [ LINEARFE_ELEM fe (N_LABEL (n-diff)) lStm (match jmpB with
       [ JUMPBLOCK_ABS jlbl ⇒ JUMPBLOCK_ABS fe (useless_linearfeProg_elim_aux jlbl ul)
       | JUMPBLOCK_COND expr jlbl1 jlbl2 ⇒
        (* NB: il linguaggio non ha effetti collaterali quindi COND expr x x diventa ABS x *)
        let jlbl1' ≝ useless_linearfeProg_elim_aux jlbl1 ul in
        let jlbl2' ≝ useless_linearfeProg_elim_aux jlbl2 ul in
        match eqLabel jlbl1' jlbl2' with
         [ true ⇒ JUMPBLOCK_ABS fe jlbl1'
         | false ⇒ JUMPBLOCK_COND fe expr jlbl1' jlbl2'
         ]
       ]
      )]]]]@(useless_linearfeProg_elim fe t ul)
  ].

definition useless_linearfeProg ≝
λfe.λmaxProg:Prod nat (linearfe_prog fe).
 match maxProg with
  [ pair max prog ⇒
   let ul ≝ useless_linearfeElem_closure (get_useless_linearfeElem fe prog []) in
   pair ?? (max-(len_list ? ul)) (useless_linearfeProg_elim fe prog ul) ]. 

(* 
   CONSIDERAZIONE:
   - il livello di annidamento medio non supera mai i 10 livelli
   - ogni passata puo' rimuovere un "dead" jmp COND x x
   - per assorbire la trasformazione serve una nuova passata
   - applichiamo quindi N=10 passate
*)
definition useless_linearfeProgMulti ≝
λfe.λmaxProg:Prod nat (linearfe_prog fe).
 let rec aux pMaxProg n on n ≝
  match n with
   [ O ⇒ pMaxProg
   | S n' ⇒ aux (useless_linearfeProg fe pMaxProg) n'
   ] in aux maxProg 10. 

(* ************* TEST ************* *)

(*
definition tfe ≝
 snd ?? (build_trasfEnv_mapFe O [ tripleT ??? [ ch_A ] false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) ]
                              (pair ?? empty_map empty_flatEnv)).

lemma tid : astfe_id tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8).
 lapply (ASTFE_ID tfe (STR_ID [ ch_A ] O));
 [ apply Hletin | apply I ].
qed.

definition texp ≝
λval.
 ASTFE_EXPR_ADD tfe AST_BASE_TYPE_BYTE8
                (ASTFE_EXPR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
                               (ASTFE_VAR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) tid))
                (ASTFE_EXPR_BYTE8 tfe val).

definition tasg ≝
λval.
 ASTFE_STM_ASG tfe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
                   (ASTFE_VAR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) tid)
                   (texp val).

definition lasg ≝
λval.
 LINEARFE_STM_ASG tfe (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
                  (ASTFE_VAR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) tid)
                  (texp val).

definition tbexp ≝
λval.
 ASTFE_BASE_EXPR tfe AST_BASE_TYPE_BYTE8
                     (ASTFE_EXPR_GT tfe AST_BASE_TYPE_BYTE8
                                    (ASTFE_EXPR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
                                                   (ASTFE_VAR_ID tfe false (AST_TYPE_BASE AST_BASE_TYPE_BYTE8) tid))
                                    (ASTFE_EXPR_BYTE8 tfe val)).
*)

(* senza (SX) e con (DX) ottimizzazione: da 0-24,25new a 0-15,16new
  lasg 0; lasg 1;
  if(tbexp 0)
    {
    while(tbexp 1)
      { if(tbexp 2) { lasg 2; } }
    lasg 3;
    }
   O : [ lasg 0 ; lasg 1 ] : COND (tbexp 0) 2 3 ;   *  O : [ lasg 0 ; lasg 1 ] : COND (tbexp 0) 2 3 ;
   2 : []                  : COND (tbexp 1) 5 4 ;   *  2 : []                  : COND (tbexp 1) 5 4 ;
   5 : []                  : COND (tbexp 2) 7 6 ;   *  5 : []                  : COND (tbexp 2) 7 6 ;
   7 : [ lasg 2 ]          : ABS 6 ;                *  7 : [ lasg 2 ]          : ABS 6 ;
   6 : []                  : COND (tbexp 1) 5 4 ;   *  6 : []                  : COND (tbexp 1) 5 4 ;
   4 : [ lasg 3 ]          : ABS 1 ;                *  4 : [ lasg 3 ]          : ABS 1 ;

  else if(tbexp 3)
    {
    if(tbexp 4) {}
    else if(tbexp 5) {}
    }
   3 : []                  : COND (tbexp 3) 8 9 ;   *  3 : []                  : COND (tbexp 3) 1 8 ;
   8 : []                  : COND (tbexp 4) 11 12 ; *
  11 : []                  : ABS 10 ;               *
  12 : []                  : COND (tbexp 5) 13 10 ; *
  13 : []                  : ABS 10 ;               *
  10 : []                  : ABS 1 ;                *

  else if(tbexp 6)
    {
    lasg 4;
    lasg 5;
    if(tbexp 7)
      {
      if(tbexp 8) { lasg 6; }
      lasg 7;
      }
    lasg 8;
    }
   9 : []                  : COND (tbexp 6) 14 15 ; *  8 : []                  : COND (tbexp 6) 9 10 ;
  14 : [ lasg 4 ; lasg 5 ] : COND (tbexp 7) 17 16 ; *  9 : [ lasg 4 ; lasg 5 ] : COND (tbexp 7) 12 11 ;
  17 : []                  : COND (tbexp 8) 19 18 ; * 12 : []                  : COND (tbexp 8) 14 13 ;
  19 : [ lasg 6 ]          : ABS 18 ;               * 14 : [ lasg 6 ]          : ABS 13 ;
  18 : [ lasg 7 ]          : ABS 16 ;               * 13 : [ lasg 7 ]          : ABS 11 ;
  16 : [ lasg 8 ]          : ABS 1 ;                * 11 : [ lasg 8 ]          : ABS 1 ;

  else
    {
    if(tbexp 9) { lasg 9; }
    else if(tbexp A) {}
    }
  15 : []                  : COND (tbexp 9) 21 22 ; * 10 : []                  : COND (tbexp 9) 15 1 ;
  21 : [ lasg 9 ]          : ABS 20 ;               * 15 : [ lasg 9 ]          : ABS 1 ;
  22 : []                  : COND (tbexp A) 23 24 ; *
  23 : []                  : ABS 20 ;               *
  24 : []                  : ABS 20 ;               *
  20 : []                  : ABS 1 ;                *

  ... fine dell'if principale ...
   1 : []                  : ABS LABEL_END ]        * ... l'ottimizzazione qui si ferma ...
*)

(*
definition tprog ≝
 ASTFE_ROOT tfe (
  ASTFE_BODY tfe [
   (tasg 〈x0,x0〉) ;
   (tasg 〈x0,x1〉) ;
   (ASTFE_STM_IF tfe («
    (pair ?? (tbexp 〈x0,x0〉)
     (ASTFE_BODY tfe [
      (ASTFE_STM_WHILE tfe (tbexp 〈x0,x1〉) (ASTFE_BODY tfe [
       (ASTFE_STM_IF tfe («£(pair ?? (tbexp 〈x0,x2〉) (ASTFE_BODY tfe [ tasg 〈x0,x2〉 ]))») (None ?)) ])) ;
      (tasg 〈x0,x3〉) ])) ;
    (pair ?? (tbexp 〈x0,x3〉) (ASTFE_BODY tfe [
     (ASTFE_STM_IF tfe («(pair ?? (tbexp 〈x0,x4〉) (ASTFE_BODY tfe []))£(pair ?? (tbexp 〈x0,x5〉) (ASTFE_BODY tfe []))») (None ?)) ])) £
    (pair ?? (tbexp 〈x0,x6〉)
     (ASTFE_BODY tfe [
      (tasg 〈x0,x4〉) ;
      (tasg 〈x0,x5〉) ;
      (ASTFE_STM_IF tfe («£(pair ?? (tbexp 〈x0,x7〉) (ASTFE_BODY tfe [
       (ASTFE_STM_IF tfe («£(pair ?? (tbexp 〈x0,x8〉) (ASTFE_BODY tfe [ tasg 〈x0,x6〉 ]))») (None ?)) ;
       (tasg 〈x0,x7〉) ]))») (None ?)) ;
      (tasg 〈x0,x8〉) ])) »)
    (Some ? (ASTFE_BODY tfe [
     (ASTFE_STM_IF tfe («(pair ?? (tbexp 〈x0,x9〉) (ASTFE_BODY tfe [ tasg 〈x0,x9〉 ]))£
      (pair ?? (tbexp 〈x0,xA〉) (ASTFE_BODY tfe []))»)
      (Some ? (ASTFE_BODY tfe [])))])))
   ]).

lemma pippo : ∃b.b=useless_linearfeProgMulti tfe (astfe_to_linearfe tfe tprog).
 unfold useless_linearfeProgMulti;
 simplify;
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? %)))))))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? %))))))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? (? ? (? ? (? ? %)))))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? (? ? (? ? %))))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? (? ? %)))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? (? ? %))))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? (? ? %)))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? (? ? %))));
 normalize in ⊢ (? ? (λ_:?.? ? ? (? ? %)));
 normalize in ⊢ (? ? (λ_:?.? ? ? %));
 fold normalize tfe;
 fold normalize (lasg 〈x0,x0〉);
 fold normalize (lasg 〈x0,x1〉);
 fold normalize (lasg 〈x0,x2〉);
 fold normalize (lasg 〈x0,x3〉);
 fold normalize (lasg 〈x0,x4〉);
 fold normalize (lasg 〈x0,x5〉);
 fold normalize (lasg 〈x0,x6〉);
 fold normalize (lasg 〈x0,x7〉);
 fold normalize (lasg 〈x0,x8〉);
 fold normalize (lasg 〈x0,x9〉);
 fold normalize (tbexp 〈x0,x0〉);
 fold normalize (tbexp 〈x0,x1〉);
 fold normalize (tbexp 〈x0,x2〉);
 fold normalize (tbexp 〈x0,x3〉);
 fold normalize (tbexp 〈x0,x4〉);
 fold normalize (tbexp 〈x0,x5〉);
 fold normalize (tbexp 〈x0,x6〉);
 fold normalize (tbexp 〈x0,x7〉);
 fold normalize (tbexp 〈x0,x8〉);
 fold normalize (tbexp 〈x0,x9〉);
 fold normalize (tbexp 〈x0,xA〉);
 elim daemon.
qed.
*)
