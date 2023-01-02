(* Copyright (C) 2004, HELM Team.
 *
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 *
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 *
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open GrafiteAst
open Printf

let tactical_terminator = ""
let tactic_terminator = tactical_terminator
let command_terminator = tactical_terminator

let pp_tactic_pattern status ~map_unicode_to_tex (what, hyp, goal) =
  if what = None && hyp = [] && goal = None then "" else
  let what_text =
    match what with
    | None -> ""
    | Some t -> Printf.sprintf "in match (%s) " (NotationPp.pp_term status t) in
  let hyp_text =
    String.concat " "
      (List.map (fun (name, p) -> Printf.sprintf "%s:(%s)" name
       (NotationPp.pp_term status p)) hyp) in
  let goal_text =
    match goal with
    | None -> ""
    | Some t ->
       let vdash = if map_unicode_to_tex then "\\vdash" else "⊢" in
        Printf.sprintf "%s (%s)" vdash (NotationPp.pp_term status t)
  in
   Printf.sprintf "%sin %s%s" what_text hyp_text goal_text

let pp_auto_params params status =
    match params with
    | (None,flags) -> String.concat " " (List.map (fun (a,b) -> a ^ "=" ^ b) flags)
    | (Some l,flags) -> (String.concat "," (List.map (NotationPp.pp_term status) l)) ^
    String.concat " " (List.map (fun (a,b) -> a ^ "=" ^ b) flags)
;;

let pp_just status just =
 match just with
    `Term term -> "using (" ^ NotationPp.pp_term status term ^ ") "
  | `Auto params ->
          match params with
          | (None,[]) -> ""
          | params -> "by " ^ pp_auto_params params status ^ " "
;;

let rec pp_ntactic status ~map_unicode_to_tex =
 let pp_tactic_pattern = pp_tactic_pattern ~map_unicode_to_tex in
 function
  | NApply (_,t) -> "@" ^ NotationPp.pp_term status t
  | NSmartApply (_,_t) -> "fixme"
  | NAuto (_,(None,flgs)) ->
      "nautobatch" ^
        String.concat " " (List.map (fun (a,b) -> a ^ "=" ^ b) flgs)
  | NAuto (_,(Some l,flgs)) ->
      "nautobatch" ^ " by " ^
         (String.concat "," (List.map (NotationPp.pp_term status) l)) ^
        String.concat " " (List.map (fun (a,b) -> a ^ "=" ^ b) flgs)
  | NCases (_,what,_where) -> "ncases " ^ NotationPp.pp_term status what ^
      "...to be implemented..." ^ " " ^ "...to be implemented..."
  | NConstructor (_,None,l) -> "@ " ^
      String.concat " " (List.map (NotationPp.pp_term status) l)
  | NConstructor (_,Some x,l) -> "@" ^ string_of_int x ^ " " ^
      String.concat " " (List.map (NotationPp.pp_term status) l)
  | NCase1 (_,n) -> "*" ^ n ^ ":"
  | NChange (_,_what,wwhat) -> "nchange " ^ "...to be implemented..." ^ 
      " with " ^ NotationPp.pp_term status wwhat
  | NCut (_,t) -> "ncut " ^ NotationPp.pp_term status t
(*| NDiscriminate (_,t) -> "ndiscriminate " ^ NotationPp.pp_term status t
  | NSubst (_,t) -> "nsubst " ^ NotationPp.pp_term status t *)
  | NClear (_,l) -> "nclear " ^ String.concat " " l
  | NDestruct (_,_dom,_skip) -> "ndestruct ..." 
  | NElim (_,what,_where) -> "nelim " ^ NotationPp.pp_term status what ^
      "...to be implemented..." ^ " " ^ "...to be implemented..."
  | NId _ -> "nid"
  | NIntro (_,n) -> "#" ^ n
  | NIntros (_,l) -> "#" ^ String.concat " " l
  | NInversion (_,what,_where) -> "ninversion " ^ NotationPp.pp_term status what ^
      "...to be implemented..." ^ " " ^ "...to be implemented..."
  | NLApply (_,t) -> "lapply " ^ NotationPp.pp_term status t
  | NRewrite (_,dir,n,where) -> "nrewrite " ^
     (match dir with `LeftToRight -> ">" | `RightToLeft -> "<") ^
     " " ^ NotationPp.pp_term status n ^ " " ^ pp_tactic_pattern status where
  | NReduce _ | NGeneralize _ | NLetIn _ | NAssert _ -> "TO BE IMPLEMENTED"
  | NDot _ -> "."
  | NSemicolon _ -> ";"
  | NBranch _ -> "["
  | NShift _ -> "|"
  | NPos (_, l) -> String.concat "," (List.map string_of_int l)^ ":"
  | NPosbyname (_, s) -> s ^ ":"
  | NWildcard _ -> "*:"
  | NMerge _ -> "]"
  | NFocus (_,l) ->
      Printf.sprintf "focus %s"
        (String.concat " " (List.map string_of_int l))
  | NUnfocus _ -> "unfocus"
  | NSkip _ -> "skip"
  | NTry (_,tac) -> "ntry " ^ pp_ntactic status ~map_unicode_to_tex tac
  | NAssumption _ -> "nassumption"
  | NBlock (_,l) ->
     "(" ^ String.concat " " (List.map (pp_ntactic status ~map_unicode_to_tex) l)^ ")"
  | NRepeat (_,t) -> "nrepeat " ^ pp_ntactic status ~map_unicode_to_tex t
  | Assume (_, ident, term) -> "assume " ^ ident ^ ":(" ^ (NotationPp.pp_term status term) ^ ")"
  | Suppose (_,term,ident) -> "suppose (" ^ (NotationPp.pp_term status term) ^ ") (" ^ ident ^ ") "
  | By_just_we_proved (_, just, term1, ident) -> pp_just status just  ^ " we proved (" ^
                                                 (NotationPp.pp_term status term1) ^ ")" ^ (match ident with
        None -> "" | Some ident -> "(" ^ident^ ")")
  | We_need_to_prove (_,term,ident) -> "we need to prove (" ^ (NotationPp.pp_term status term) ^ ") " ^
                                         (match ident with None -> "" | Some id -> "(" ^ id ^ ")")
  | BetaRewritingStep (_,t) -> "that is equivalent to (" ^ (NotationPp.pp_term status t) ^ ")"
  | Bydone (_, just) -> pp_just status just ^ "done"
  | ExistsElim (_, just, ident, term, term1, ident1) -> pp_just status just ^ "let " ^ ident ^ ": ("
  ^ (NotationPp.pp_term status term) ^ ") such that (" ^ (NotationPp.pp_term status term1) ^ ") (" ^ ident1 ^ ")"
  | AndElim (_, just, term1, ident1, term2, ident2) -> pp_just status just ^ " we have (" ^
  (NotationPp.pp_term status term1) ^ ") (" ^ ident1 ^ ") " ^ "and (" ^ (NotationPp.pp_term status
  term2)
  ^ ") (" ^ ident2 ^ ")"
  | Thesisbecomes (_, t) -> "the thesis becomes (" ^ (NotationPp.pp_term status t) ^ ")"
  | RewritingStep (_, rhs, just, cont) ->
      "= (" ^
      (NotationPp.pp_term status rhs) ^ ")" ^
      (match just with
      | `Auto params -> let s = pp_auto_params params status in
                        if s <> "" then " by " ^ s
                        else ""
      | `Term t -> " exact (" ^ (NotationPp.pp_term status t) ^ ")"
      | `Proof -> " proof"
      | `SolveWith t -> " using (" ^ (NotationPp.pp_term status t) ^ ")"
      )
      ^ (if cont then " done" else "")
  | Obtain (_,id,t1) -> "obtain (" ^ id ^ ")" ^ " (" ^ (NotationPp.pp_term status t1) ^ ")"
  | Conclude (_,t1) -> "conclude (" ^ (NotationPp.pp_term status t1) ^ ")"
  | We_proceed_by_cases_on (_, term, term1) -> "we proceed by cases on (" ^ NotationPp.pp_term
  status term ^ ") to prove (" ^ NotationPp.pp_term status  term1 ^ ")"
  | We_proceed_by_induction_on (_, term, term1) -> "we proceed by induction on (" ^
  NotationPp.pp_term status  term ^ ") to prove (" ^ NotationPp.pp_term status  term1 ^ ")"
  | Byinduction (_, term, ident) -> "by induction hypothesis we know (" ^ NotationPp.pp_term status
  term ^ ") (" ^ ident ^ ")"
  | Case (_, id, args) ->
     "case " ^ id ^
       String.concat " "
        (List.map (function (id,term) -> "(" ^ id ^ ": (" ^ NotationPp.pp_term status  term ^  "))")
	  args)
  | PrintStack _ -> "print_stack"
;;

let pp_nmacro status = function
  | NCheck (_, term) -> Printf.sprintf "ncheck %s" (NotationPp.pp_term status term)
  | Screenshot (_, name) -> Printf.sprintf "screenshot \"%s\"" name
  | NAutoInteractive _
  | NIntroGuess _ -> assert false (* TODO *)
;;

let pp_l1_pattern = NotationPp.pp_term
let pp_l2_pattern = NotationPp.pp_term

let pp_alias = function
  | Ident_alias (id, uri) -> sprintf "alias id \"%s\" = \"%s\"." id uri
  | Symbol_alias (symb, instance, desc) ->
      sprintf "alias symbol \"%s\" %s= \"%s\"."
        symb
        (if instance=0 then "" else "(instance "^ string_of_int instance ^ ") ")
        desc
  | Number_alias (instance,desc) ->
      sprintf "alias num (instance %d) = \"%s\"." instance desc

let pp_associativity = function
  | Gramext.LeftA -> "left associative"
  | Gramext.RightA -> "right associative"
  | Gramext.NonA -> "non associative"

let pp_precedence i = sprintf "with precedence %d" i

let pp_argument_pattern = function
  | NotationPt.IdentArg (eta_depth, name) ->
      let eta_buf = Buffer.create 5 in
      for _i = 1 to eta_depth do
        Buffer.add_string eta_buf "\\eta."
      done;
      sprintf "%s%s" (Buffer.contents eta_buf) name

let pp_interpretation dsc symbol arg_patterns cic_appl_pattern =
  sprintf "interpretation \"%s\" '%s %s = %s."
    dsc symbol
    (String.concat " " (List.map pp_argument_pattern arg_patterns))
    (NotationPp.pp_cic_appl_pattern cic_appl_pattern)

let pp_dir_opt = function
  | None -> ""
  | Some `LeftToRight -> "> "
  | Some `RightToLeft -> "< "

let pp_notation status dir_opt l1_pattern assoc prec l2_pattern =
  sprintf "notation %s\"%s\" %s %s for %s."
    (pp_dir_opt dir_opt)
    (pp_l1_pattern status l1_pattern)
    (pp_associativity assoc)
    (pp_precedence prec)
    (pp_l2_pattern status l2_pattern)

let pp_ncommand status = function
  | UnificationHint (_,t, n) ->
      "unification hint " ^ string_of_int n ^ " " ^ NotationPp.pp_term status t
  | NDiscriminator (_,_)
  | NInverter (_,_,_,_,_)
  | NUnivConstraint (_) -> "not supported"
  | NCoercion (_) -> "not supported"
  | NObj (_,obj,index) ->
      (if not index then "-" else "") ^
        NotationPp.pp_obj (NotationPp.pp_term status) obj
  | NQed (_,true) -> "qed"
  | NQed (_,false) -> "qed-"
  | NCopy (_,name,uri,map) ->
      "copy " ^ name ^ " from " ^ NUri.string_of_uri uri ^ " with " ^
        String.concat " and "
          (List.map
            (fun (a,b) -> NUri.string_of_uri a ^ " ↦ " ^ NUri.string_of_uri b)
            map)
  | Include (_,mode,path) -> (* not precise, since path is absolute *)
      if mode = WithPreferences then
        "include \"" ^ path ^ "\""
      else
        "include' \"" ^ path ^ "\""
  | Alias (_,s) -> pp_alias s
  | Interpretation (_, dsc, (symbol, arg_patterns), cic_appl_pattern) ->
      pp_interpretation dsc symbol arg_patterns cic_appl_pattern
  | Notation (_, dir_opt, l1_pattern, assoc, prec, l2_pattern) ->
      pp_notation status dir_opt l1_pattern assoc prec l2_pattern
;;

let pp_executable status ~map_unicode_to_tex =
  function
  | NMacro (_, macro) -> pp_nmacro status macro ^ "."
  | NTactic (_,tacl) ->
      String.concat " " (List.map (pp_ntactic status ~map_unicode_to_tex) tacl)
  | NCommand (_, cmd) -> pp_ncommand status cmd ^ "."

let pp_comment status ~map_unicode_to_tex =
  function
  | Note (_,"") -> Printf.sprintf "\n"
  | Note (_,str) -> Printf.sprintf "\n(* %s *)" str
  | Code (_,code) ->
      Printf.sprintf "\n(** %s. **)" (pp_executable status ~map_unicode_to_tex code)

let pp_statement status =
  function
  | Executable (_, ex) -> pp_executable status ex
  | Comment (_, c) -> pp_comment status c
