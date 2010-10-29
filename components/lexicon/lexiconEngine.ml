(* Copyright (C) 2004-2005, HELM Team.
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

module L = LexiconAst

let debug = ref false

(* lexicon file name * ma file name *)
exception IncludedFileNotCompiled of string * string 
exception MetadataNotFound of string        (* file name *)

type lexicon_status = {
  aliases: L.alias_spec DisambiguateTypes.Environment.t;
  multi_aliases: L.alias_spec list DisambiguateTypes.Environment.t;
  lexicon_content_rev: LexiconMarshal.lexicon;
  notation_ids: CicNotation.notation_id list;      (** in-scope notation ids *)
}

let initial_status = {
  aliases = DisambiguateTypes.Environment.empty;
  multi_aliases = DisambiguateTypes.Environment.empty;
  lexicon_content_rev = [];
  notation_ids = [];
}

class type g_status =
 object
  inherit CicNotation.g_status
  method lstatus: lexicon_status
 end

class status =
 object(self)
  inherit CicNotation.status
  val lstatus = initial_status
  method lstatus = lstatus
  method set_lstatus v = {< lstatus = v >}
  method set_lexicon_engine_status : 'status. #g_status as 'status -> 'self
   = fun o -> (self#set_lstatus o#lstatus)#set_notation_status o
 end

let dump_aliases out msg status =
   out (if msg = "" then "aliases dump:" else msg ^ ": aliases dump:");
   DisambiguateTypes.Environment.iter
      (fun _ x -> out (LexiconAstPp.pp_alias x))
      status#lstatus.aliases
   
let add_lexicon_content cmds status =
  let content = status#lstatus.lexicon_content_rev in
  let content' =
    List.fold_right
     (fun cmd acc -> 
        match cmd with
        | L.Alias _ 
        | L.Include _ 
        | L.Notation _ -> cmd :: (List.filter ((<>) cmd) acc)
        | L.Interpretation _ -> if List.exists ((=) cmd) acc then acc else cmd::acc)
     cmds content
  in
(*   
  prerr_endline ("new lexicon content: " ^ 
     String.concat "; " (List.map LexiconAstPp.pp_command content')
  );
*)
  status#set_lstatus
   { status#lstatus with lexicon_content_rev = content' }

let set_proof_aliases mode status new_aliases =
 if mode = L.WithoutPreferences then
   status 
 else
   let commands_of_aliases =
     List.map
      (fun _,alias -> L.Alias (HExtlib.dummy_floc, alias))
   in
   let aliases =
    List.fold_left (fun acc (d,c) -> DisambiguateTypes.Environment.add d c acc)
     status#lstatus.aliases new_aliases in
   let multi_aliases =
    List.fold_left (fun acc (d,c) -> 
      DisambiguateTypes.Environment.cons L.description_of_alias 
         d c acc)
     status#lstatus.multi_aliases new_aliases
   in
   let new_status =
     { status#lstatus with
        multi_aliases = multi_aliases ; aliases = aliases} in
   let new_status = status#set_lstatus new_status in
    if new_aliases = [] then
      new_status
    else
      add_lexicon_content (commands_of_aliases new_aliases) new_status 

let rec eval_command ?(mode=L.WithPreferences) sstatus cmd =
(*
 let bmode = match mode with L.WithPreferences -> true | _ -> false in
 Printf.eprintf "Include preferences: %b\n" bmode;
*) 
 let status = sstatus#lstatus in
 let cmd =
  match cmd with
  | L.Interpretation (loc, dsc, (symbol, args), cic_appl_pattern) ->
     let rec disambiguate =
      function
         NotationPt.ApplPattern l ->
          NotationPt.ApplPattern (List.map disambiguate l)
       | NotationPt.VarPattern id
          when not
           (List.exists
            (function (NotationPt.IdentArg (_,id')) -> id'=id) args)
          ->
           let item = DisambiguateTypes.Id id in
            begin try
              match DisambiguateTypes.Environment.find item status.aliases with
                 L.Ident_alias (_, uri) ->
                  NotationPt.NRefPattern (NReference.reference_of_string uri)
               | _ -> assert false
             with Not_found -> 
              prerr_endline ("LexiconEngine.eval_command: domain item not found: " ^ 
               (DisambiguateTypes.string_of_domain_item item));
	      dump_aliases prerr_endline "" sstatus;
              raise (Failure (
                      (DisambiguateTypes.string_of_domain_item item) ^ 
                      " not found"));
	    end
       | p -> p
     in
      L.Interpretation
       (loc, dsc, (symbol, args), disambiguate cic_appl_pattern)
  | _-> cmd
 in
 let sstatus,notation_ids' = CicNotation.process_notation sstatus cmd in
 let status =
   { status with notation_ids = notation_ids' @ status.notation_ids } in
 let sstatus = sstatus#set_lstatus status in
  match cmd with
  | L.Include (loc, baseuri, mode, fullpath) ->
     let lexiconpath_rw, lexiconpath_r = 
       LibraryMisc.lexicon_file_of_baseuri 
         ~must_exist:false ~writable:true ~baseuri,
       LibraryMisc.lexicon_file_of_baseuri 
         ~must_exist:false ~writable:false ~baseuri
     in
     let lexiconpath = 
       if Sys.file_exists lexiconpath_rw then lexiconpath_rw else
         if Sys.file_exists lexiconpath_r then lexiconpath_r else
          raise (IncludedFileNotCompiled (lexiconpath_rw,fullpath))
     in
     let lexicon = LexiconMarshal.load_lexicon lexiconpath in
      List.fold_left (eval_command ~mode) sstatus lexicon
  | L.Alias (loc, spec) -> 
     let diff =
      (*CSC: Warning: this code should be factorized with the corresponding
             code in DisambiguatePp *)
      match spec with
      | L.Ident_alias (id,uri) -> 
         [DisambiguateTypes.Id id,spec]
      | L.Symbol_alias (symb, instance, desc) ->
         [DisambiguateTypes.Symbol (symb,instance),spec]
      | L.Number_alias (instance,desc) ->
         [DisambiguateTypes.Num instance,spec]
     in
      set_proof_aliases mode sstatus diff
  | L.Interpretation (_, dsc, (symbol, _), _) as stm ->
      let sstatus = add_lexicon_content [stm] sstatus in
      let diff =
       try
        [DisambiguateTypes.Symbol (symbol, 0),
          L.Symbol_alias (symbol,0,dsc)]
       with
        DisambiguateChoices.Choice_not_found msg ->
          prerr_endline (Lazy.force msg);
          assert false
      in
      let sstatus = set_proof_aliases mode sstatus diff in
      sstatus
  | L.Notation _ as stm ->
      add_lexicon_content [stm] sstatus

let eval_command status cmd = 
   if !debug then dump_aliases prerr_endline "before eval_command" status;
   let status = eval_command ?mode:None status cmd in
   if !debug then dump_aliases prerr_endline "after eval_command" status;
   status

let set_proof_aliases status aliases =
   if !debug then dump_aliases prerr_endline "before set_proof_aliases" status;
   let status = set_proof_aliases L.WithPreferences status aliases in
   if !debug then dump_aliases prerr_endline "after set_proof_aliases" status;
   status
