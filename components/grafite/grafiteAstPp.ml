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

let tactical_terminator = ""
let tactic_terminator = tactical_terminator
let command_terminator = tactical_terminator

let pp_idents idents = 
   let map = function Some s -> s | None -> "_" in
   "(" ^ String.concat " " (List.map map idents) ^ ")"
let pp_hyps idents = String.concat " " idents

let pp_reduction_kind ~term_pp = function
  | `Normalize -> "normalize"
  | `Reduce -> "reduce"
  | `Simpl -> "simplify"
  | `Unfold (Some t) -> "unfold " ^ term_pp t
  | `Unfold None -> "unfold"
  | `Whd -> "whd"
 
let pp_tactic_pattern ~map_unicode_to_tex ~term_pp ~lazy_term_pp (what, hyp, goal) = 
  if what = None && hyp = [] && goal = None then "" else 
  let what_text =
    match what with
    | None -> ""
    | Some t -> Printf.sprintf "in match (%s) " (lazy_term_pp t) in
  let hyp_text =
    String.concat " "
      (List.map (fun (name, p) -> Printf.sprintf "%s:(%s)" name (term_pp p)) hyp) in
  let goal_text =
    match goal with
    | None -> ""
    | Some t ->
       let vdash = if map_unicode_to_tex then "\\vdash" else "⊢" in
        Printf.sprintf "%s (%s)" vdash (term_pp t)
  in
   Printf.sprintf "%sin %s%s" what_text hyp_text goal_text

let pp_intros_specs s = function
   | None, []         -> ""
   | Some num, []     -> Printf.sprintf " %s%i" s num
   | None, idents     -> Printf.sprintf " %s%s" s (pp_idents idents)
   | Some num, idents -> Printf.sprintf " %s%i %s" s num (pp_idents idents)

let pp_terms ~term_pp terms = String.concat ", " (List.map term_pp terms)

let opt_string_pp = function
   | None -> ""
   | Some what -> what ^ " "
 
let pp_auto_params ~term_pp (univ, params) = 
   String.concat " " 
     (List.map (fun (k,v) -> if v <> "" then k ^ "=" ^ v else k) params) ^
     match univ with
       | None -> ""
       | Some l -> (if params <> [] then " " else "") ^ "by " ^ 
	   String.concat " " (List.map term_pp l)
;;

let pp_just ~term_pp =
 function
    `Term term -> "exact " ^ term_pp term
  | `Auto params -> pp_auto_params ~term_pp params
;;

let rec pp_ntactic ~map_unicode_to_tex =
 let term_pp = CicNotationPp.pp_term in
 let lazy_term_pp = fun _ -> assert false in
 let pp_tactic_pattern =
  pp_tactic_pattern ~map_unicode_to_tex ~lazy_term_pp ~term_pp in
 function
  | NApply (_,t) -> "napply " ^ CicNotationPp.pp_term t
  | NSmartApply (_,t) -> "fixme"
  | NAuto (_,(None,flgs)) ->
      "nautobatch" ^
        String.concat " " (List.map (fun a,b -> a ^ "=" ^ b) flgs)
  | NAuto (_,(Some l,flgs)) ->
      "nautobatch" ^ " by " ^
         (String.concat "," (List.map CicNotationPp.pp_term l)) ^
        String.concat " " (List.map (fun a,b -> a ^ "=" ^ b) flgs)
  | NCases (_,what,where) -> "ncases " ^ CicNotationPp.pp_term what ^
      assert false ^ " " ^ assert false
  | NConstructor (_,None,l) -> "@ " ^
      String.concat " " (List.map CicNotationPp.pp_term l)
  | NConstructor (_,Some x,l) -> "@" ^ string_of_int x ^ " " ^
      String.concat " " (List.map CicNotationPp.pp_term l)
  | NCase1 (_,n) -> "*" ^ n ^ ":"
  | NChange (_,what,wwhat) -> "nchange " ^ assert false ^ 
      " with " ^ CicNotationPp.pp_term wwhat
  | NCut (_,t) -> "ncut " ^ CicNotationPp.pp_term t
(*| NDiscriminate (_,t) -> "ndiscriminate " ^ CicNotationPp.pp_term t
  | NSubst (_,t) -> "nsubst " ^ CicNotationPp.pp_term t *)
  | NDestruct (_,dom,skip) -> "ndestruct ..." 
  | NElim (_,what,where) -> "nelim " ^ CicNotationPp.pp_term what ^
      assert false ^ " " ^ assert false
  | NId _ -> "nid"
  | NIntro (_,n) -> "#" ^ n
  | NInversion (_,what,where) -> "ninversion " ^ CicNotationPp.pp_term what ^
      assert false ^ " " ^ assert false
  | NLApply (_,t) -> "lapply " ^ CicNotationPp.pp_term t
  | NRewrite (_,dir,n,where) -> "nrewrite " ^
     (match dir with `LeftToRight -> ">" | `RightToLeft -> "<") ^
     " " ^ CicNotationPp.pp_term n ^ " " ^ pp_tactic_pattern where
  | NReduce _ | NGeneralize _ | NLetIn _ | NAssert _ -> "TO BE IMPLEMENTED"
  | NDot _ -> "##."
  | NSemicolon _ -> "##;"
  | NBranch _ -> "##["
  | NShift _ -> "##|"
  | NPos (_, l) -> "##" ^String.concat "," (List.map string_of_int l)^ ":"
  | NPosbyname (_, s) -> "##" ^ s ^ ":"
  | NWildcard _ -> "##*:"
  | NMerge _ -> "##]"
  | NFocus (_,l) -> 
      Printf.sprintf "##focus %s" 
        (String.concat " " (List.map string_of_int l))
  | NUnfocus _ -> "##unfocus"
  | NSkip _ -> "##skip"
  | NTry (_,tac) -> "ntry " ^ pp_ntactic ~map_unicode_to_tex tac
  | NAssumption _ -> "nassumption"
  | NBlock (_,l) -> 
     "(" ^ String.concat " " (List.map (pp_ntactic ~map_unicode_to_tex) l)^ ")"
  | NRepeat (_,t) -> "nrepeat " ^ pp_ntactic ~map_unicode_to_tex t
;;

let rec pp_tactic ~map_unicode_to_tex ~term_pp ~lazy_term_pp =
 let pp_terms = pp_terms ~term_pp in
 let pp_tactics = pp_tactics ~map_unicode_to_tex ~term_pp ~lazy_term_pp in
 let pp_reduction_kind = pp_reduction_kind ~term_pp in
 let pp_tactic_pattern =
  pp_tactic_pattern ~map_unicode_to_tex ~lazy_term_pp ~term_pp in
 let rec pp_tactic =
  function
  (* Higher order tactics *)
  | Do (_, count, tac) ->
      Printf.sprintf "do %d %s" count (pp_tactic tac)
  | Repeat (_, tac) -> "repeat " ^ pp_tactic tac
  | Seq (_, tacs) -> pp_tactics ~sep:"; " tacs
  | Then (_, tac, tacs) ->
      Printf.sprintf "%s; [%s]" (pp_tactic tac)
        (pp_tactics ~sep:" | " tacs)
  | First (_, tacs) ->
     Printf.sprintf "tries [%s]" (pp_tactics ~sep:" | " tacs)
  | Try (_, tac) -> "try " ^ pp_tactic tac
  | Solve (_, tac) ->
     Printf.sprintf "solve [%s]" (pp_tactics ~sep:" | " tac)
  | Progress (_, tac) -> "progress " ^ pp_tactic tac
  (* First order tactics *)
  | Absurd (_, term) -> "absurd" ^ term_pp term
  | Apply (_, term) -> "apply " ^ term_pp term
  | ApplyRule (_, term) -> "apply rule " ^ term_pp term
  | ApplyP (_, term) -> "applyP " ^ term_pp term
  | ApplyS (_, term, params) ->
     "applyS " ^ term_pp term ^ pp_auto_params ~term_pp params
  | AutoBatch (_,params) -> "autobatch " ^ 
      pp_auto_params ~term_pp params
  | Assumption _ -> "assumption"
  | Cases (_, term, pattern, specs) -> 
      Printf.sprintf "cases %s %s%s" 
      (term_pp term)
      (pp_tactic_pattern pattern)
      (pp_intros_specs "names " specs)
  | Change (_, where, with_what) ->
      Printf.sprintf "change %s with %s" (pp_tactic_pattern where) (lazy_term_pp with_what)
  | Clear (_,ids) -> Printf.sprintf "clear %s" (pp_hyps ids)
  | ClearBody (_,id) -> Printf.sprintf "clearbody %s" (pp_hyps [id])
  | Constructor (_,n) -> "constructor " ^ string_of_int n
  | Compose (_,t1, t2, times, intro_specs) -> 
      Printf.sprintf "compose %s%s %s%s" 
        (if times > 0 then string_of_int times ^ " " else "")
        (term_pp t1) (match t2 with None -> "" | Some t2 -> "with "^term_pp t2)
        (pp_intros_specs " as " intro_specs)
  | Contradiction _ -> "contradiction"
  | Cut (_, ident, term) ->
     "cut " ^ term_pp term ^
      (match ident with None -> "" | Some id -> " as " ^ id)
  | Decompose (_, names) ->
      Printf.sprintf "decompose%s" 
      (pp_intros_specs "names " (None, names)) 
  | Demodulate (_, params) -> "demodulate " ^ pp_auto_params ~term_pp params
  | Destruct (_, None) -> "destruct" 
  | Destruct (_, Some terms) -> "destruct " ^ pp_terms terms
  | Elim (_, what, using, pattern, specs) ->
      Printf.sprintf "elim %s%s %s%s" 
      (term_pp what)
      (match using with None -> "" | Some term -> " using " ^ term_pp term)
      (pp_tactic_pattern pattern)
      (pp_intros_specs "names " specs) 
  | ElimType (_, term, using, specs) ->
      Printf.sprintf "elim type %s%s%s" 
      (term_pp term)
      (match using with None -> "" | Some term -> " using " ^ term_pp term)
      (pp_intros_specs "names " specs)
  | Exact (_, term) -> "exact " ^ term_pp term
  | Exists _ -> "exists"
  | Fold (_, kind, term, pattern) ->
      Printf.sprintf "fold %s %s %s" (pp_reduction_kind kind)
       (lazy_term_pp term) (pp_tactic_pattern pattern)
  | FwdSimpl (_, hyp, names) -> 
      Printf.sprintf "fwd %s%s" hyp (pp_intros_specs "names " (None, names))
  | Generalize (_, pattern, ident) ->
     Printf.sprintf "generalize %s%s" (pp_tactic_pattern pattern)
      (match ident with None -> "" | Some id -> " as " ^ id)
  | Fail _ -> "fail"
  | Fourier _ -> "fourier"
  | IdTac _ -> "id"
  | Intros (_, specs) -> Printf.sprintf "intros%s" (pp_intros_specs "" specs)
  | Inversion (_, term) -> "inversion " ^ term_pp term
  | LApply (_, linear, level_opt, terms, term, ident_opt) -> 
      Printf.sprintf "lapply %s%s%s%s%s" 
        (if linear then " linear " else "")
	(match level_opt with None -> "" | Some i -> " depth = " ^ string_of_int i ^ " ")  
        (term_pp term) 
        (match terms with [] -> "" | _ -> " to " ^ pp_terms terms)
        (match ident_opt with None -> "" | Some ident -> " as " ^ ident)
  | Left _ -> "left"
  | LetIn (_, term, ident) -> 
     Printf.sprintf "letin %s \\def %s" ident (term_pp term)
  | Reduce (_, kind, pat) ->
      Printf.sprintf "%s %s" (pp_reduction_kind kind) (pp_tactic_pattern pat)
  | Reflexivity _ -> "reflexivity"
  | Replace (_, pattern, t) ->
      Printf.sprintf "replace %s with %s" (pp_tactic_pattern pattern) (lazy_term_pp t)
  | Rewrite (_, pos, t, pattern, names) -> 
      Printf.sprintf "rewrite %s %s %s%s" 
        (if pos = `LeftToRight then ">" else "<")
        (term_pp t)
        (pp_tactic_pattern pattern)
	(if names = [] then "" else " as " ^ pp_idents names)
  | Right _ -> "right"
  | Ring _ -> "ring"
  | Split _ -> "split"
  | Symmetry _ -> "symmetry"
  | Transitivity (_, term) -> "transitivity " ^ term_pp term
  (* Tattiche Aggiunte *)
  | Assume (_, ident , term) -> "assume" ^ ident ^ ":" ^ term_pp term 
  | Suppose (_, term, ident,term1) -> "suppose" ^ term_pp term ^ "("  ^ ident ^ ")" ^ (match term1 with None -> " " | Some term1 -> term_pp term1)
  | Bydone (_, just) ->  pp_just ~term_pp just ^ "done"
  | By_just_we_proved (_, just, term1, ident, term2) -> pp_just ~term_pp just  ^ "we proved" ^ term_pp term1 ^ (match ident with None -> "" | Some ident -> "(" ^ident^ ")") ^
       (match term2 with  None -> " " | Some term2 -> term_pp term2)
  | We_need_to_prove (_, term, ident, term1) -> "we need to prove" ^ term_pp term ^ (match ident with None -> "" | Some ident -> "(" ^ ident ^ ")") ^ (match term1 with None -> " " | Some term1 -> term_pp term1)
  | We_proceed_by_cases_on (_, term, term1) -> "we proceed by cases on" ^ term_pp term ^ "to prove" ^ term_pp term1
  | We_proceed_by_induction_on (_, term, term1) -> "we proceed by induction on" ^ term_pp term ^ "to prove" ^ term_pp term1
  | Byinduction (_, term, ident) -> "by induction hypothesis we know" ^ term_pp term ^ "(" ^ ident ^ ")"
  | Thesisbecomes (_, term) -> "the thesis becomes " ^ term_pp term
  | ExistsElim (_, just, ident, term, ident1, term1) -> pp_just ~term_pp just ^ "let " ^ ident ^ ":" ^ term_pp term ^ "such that " ^ lazy_term_pp term1 ^ "(" ^ ident1 ^ ")"
  | AndElim (_, just, ident1, term1, ident2, term2) -> pp_just ~term_pp just ^ "we have " ^ term_pp term1 ^ " (" ^ ident1 ^ ") " ^ "and " ^ term_pp term2 ^ " (" ^ ident2 ^ ")" 
  | RewritingStep (_, term, term1, term2, cont) -> 
      (match term with 
      | None -> " " 
      | Some (None,term) -> "conclude " ^ term_pp term 
      | Some (Some name,term) -> 
          "obtain (" ^ name ^ ") " ^ term_pp term) 
      ^ "=" ^
      term_pp term1 ^ 
      (match term2 with 
      | `Auto params -> pp_auto_params ~term_pp params
      | `Term term2 -> " exact " ^ term_pp term2 
      | `Proof -> " proof"
      | `SolveWith term -> " using " ^ term_pp term)
      ^ (if cont then " done" else "")
  | Case (_, id, args) ->
     "case" ^ id ^
       String.concat " "
        (List.map (function (id,term) -> "(" ^ id ^ ": " ^ term_pp term ^  ")")
	  args)
 in pp_tactic

and pp_tactics ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~sep tacs =
  String.concat sep
   (List.map (pp_tactic ~map_unicode_to_tex ~lazy_term_pp ~term_pp) tacs)

 let pp_search_kind = function
  | `Locate -> "locate"
  | `Hint -> "hint"
  | `Match -> "match"
  | `Elim -> "elim"
  | `Instance -> "instance"

let pp_arg ~term_pp arg = 
  let s = term_pp arg in
   if s = "" || (s.[0] = '(' && s.[String.length s - 1] = ')') then
     (* _nice_ heuristic *)
     s
   else
     "(" ^ s ^ ")"
  
let pp_nmacro = function
  | NCheck (_, term) -> Printf.sprintf "ncheck %s" (CicNotationPp.pp_term term)
  | Screenshot (_, name) -> Printf.sprintf "screenshot \"%s\"" name
;;

let pp_macro ~term_pp ~lazy_term_pp = 
  let term_pp = pp_arg ~term_pp in
  let flavour_pp = function
     | `Definition       -> "definition"
     | `Fact             -> "fact"
     | `Lemma            -> "lemma"
     | `Remark           -> "remark"
     | `Theorem          -> "theorem"
     | `Variant          -> "variant"
     | `Axiom            -> "axiom"
     | `MutualDefinition -> assert false
  in
  let pp_inline_params l =
     let pp_param = function
        | IPPrefix prefix -> "prefix = \"" ^ prefix ^ "\""
	| IPAs flavour  -> flavour_pp flavour
	| IPCoercions   -> "coercions"
	| IPDebug debug -> "debug = " ^ string_of_int debug
	| IPProcedural  -> "procedural"
	| IPNoDefaults  -> "nodefaults"
	| IPDepth depth -> "depth = " ^ string_of_int depth
	| IPLevel level -> "level = " ^ string_of_int level
	| IPComments    -> "comments"
	| IPCR          -> "cr"
     in
     let s = String.concat " " (List.map pp_param l) in
     if s = "" then s else " " ^ s
  in
  let pp_reduction_kind = pp_reduction_kind ~term_pp:lazy_term_pp in
  function 
  (* Whelp *)
  | WInstance (_, term) -> "whelp instance " ^ term_pp term
  | WHint (_, t) -> "whelp hint " ^ term_pp t
  | WLocate (_, s) -> "whelp locate \"" ^ s ^ "\""
  | WElim (_, t) -> "whelp elim " ^ term_pp t
  | WMatch (_, term) -> "whelp match " ^ term_pp term
  (* real macros *)
  | Eval (_, kind, term) -> 
      Printf.sprintf "eval %s on %s" (pp_reduction_kind kind) (term_pp term) 
  | Check (_, term) -> Printf.sprintf "check %s" (term_pp term)
  | Hint (_, true) -> "hint rewrite"
  | Hint (_, false) -> "hint"
  | AutoInteractive (_,params) -> "auto " ^ pp_auto_params ~term_pp params
  | Inline (_, suri, params) ->  
      Printf.sprintf "inline \"%s\"%s" suri (pp_inline_params params) 

let pp_associativity = function
  | Gramext.LeftA -> "left associative"
  | Gramext.RightA -> "right associative"
  | Gramext.NonA -> "non associative"

let pp_precedence i = Printf.sprintf "with precedence %d" i

let pp_default what uris = 
  Printf.sprintf "default \"%s\" %s" what
    (String.concat " " (List.map UriManager.string_of_uri uris))

let pp_coercion ~term_pp t do_composites arity saturations=
   Printf.sprintf "coercion %s %d %d %s"
    (term_pp t) arity saturations
    (if do_composites then "" else "nocomposites")

let pp_ncommand ~obj_pp = function
  | UnificationHint (_,t, n) -> 
      "unification hint " ^ string_of_int n ^ " " ^ CicNotationPp.pp_term t
  | NDiscriminator (_,_)
  | NInverter (_,_,_,_,_)
  | NUnivConstraint (_) -> "not supported"
  | NCoercion (_) -> "not supported"
  | NObj (_,obj) -> obj_pp obj
  | NQed (_) -> "nqed"
  | NCopy (_,name,uri,map) -> 
      "copy " ^ name ^ " from " ^ NUri.string_of_uri uri ^ " with " ^ 
        String.concat " and " 
          (List.map 
            (fun (a,b) -> NUri.string_of_uri a ^ " ↦ " ^ NUri.string_of_uri b) 
            map)
;;
    
let pp_command ~term_pp ~obj_pp = function
  | Index (_,_,uri) -> "Indexing " ^ UriManager.string_of_uri uri
  | Select (_,uri) -> "Selecting " ^ UriManager.string_of_uri uri
  | Coercion (_, t, do_composites, i, j) ->
     pp_coercion ~term_pp t do_composites i j
  | PreferCoercion (_,t) -> 
     "prefer coercion " ^ term_pp t
  | Inverter (_,n,ty,params) ->
     "inverter " ^ n ^ " for " ^ term_pp ty ^ " " ^ List.fold_left (fun acc x -> acc ^ (match x with true -> "%" | _ -> "?")) "" params
  | Default (_,what,uris) -> pp_default what uris
  | Drop _ -> "drop"
  | Include (_,true,`OldAndNew,path) -> "include \"" ^ path ^ "\""
  | Include (_,false,`OldAndNew,path) -> "include source \"" ^ path ^ "\""
  | Include (_,_,`New,path) -> "RECURSIVELY INCLUDING " ^ path
  | Obj (_,obj) -> obj_pp obj
  | Qed _ -> "qed"
  | Relation (_,id,a,aeq,refl,sym,trans) ->
     "relation " ^ term_pp aeq ^ " on " ^ term_pp a ^
     (match refl with
         Some r -> " reflexivity proved by " ^ term_pp r
       | None -> "") ^
     (match sym with
         Some r -> " symmetry proved by " ^ term_pp r
       | None -> "") ^
     (match trans with
         Some r -> " transitivity proved by " ^ term_pp r
       | None -> "")
  | Print (_,s) -> "print " ^ s
  | Set (_, name, value) -> Printf.sprintf "set \"%s\" \"%s\"" name value
  | Pump (_) -> "not supported"

let pp_punctuation_tactical =
  function
  | Dot _ -> "."
  | Semicolon _ -> ";"
  | Branch _ -> "["
  | Shift _ -> "|"
  | Pos (_, i) -> Printf.sprintf "%s:" (String.concat "," (List.map string_of_int i))
  | Wildcard _ -> "*:"
  | Merge _ -> "]"

let pp_non_punctuation_tactical =
  function
  | Focus (_, goals) ->
      Printf.sprintf "focus %s" (String.concat " " (List.map string_of_int goals))
  | Unfocus _ -> "unfocus"
  | Skip _ -> "skip"

let pp_executable ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~obj_pp =
  function
  | NMacro (_, macro) -> pp_nmacro macro ^ "."
  | Macro (_, macro) -> pp_macro ~term_pp ~lazy_term_pp macro ^ "."
  | Tactic (_, Some tac, punct) ->
      pp_tactic ~map_unicode_to_tex ~term_pp ~lazy_term_pp tac
      ^ pp_punctuation_tactical punct
  | Tactic (_, None, punct) ->
     pp_punctuation_tactical punct
  | NTactic (_,tacl) ->
      String.concat " " (List.map (pp_ntactic ~map_unicode_to_tex) tacl)
  | NonPunctuationTactical (_, tac, punct) ->
     pp_non_punctuation_tactical tac
     ^ pp_punctuation_tactical punct
  | Command (_, cmd) -> pp_command ~term_pp ~obj_pp cmd ^ "."
  | NCommand (_, cmd) -> 
      let obj_pp = Obj.magic obj_pp in
      pp_ncommand ~obj_pp cmd ^ "."
                      
let pp_comment ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~obj_pp =
  function
  | Note (_,"") -> Printf.sprintf "\n"
  | Note (_,str) -> Printf.sprintf "\n(* %s *)" str
  | Code (_,code) ->
      Printf.sprintf "\n(** %s. **)" (pp_executable ~map_unicode_to_tex ~term_pp ~lazy_term_pp ~obj_pp code)

let pp_statement ~term_pp ~lazy_term_pp ~obj_pp =
  function
  | Executable (_, ex) -> pp_executable ~lazy_term_pp ~term_pp ~obj_pp ex 
  | Comment (_, c) -> pp_comment ~term_pp ~lazy_term_pp ~obj_pp c
