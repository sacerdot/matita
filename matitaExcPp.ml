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

open Printf

let rec to_string = 
  function
  | HExtlib.Localized (floc,exn) ->
      let _,msg = to_string exn in
      let (x, y) = HExtlib.loc_of_floc floc in
       Some floc, sprintf "Error at %d-%d: %s" x y msg
  | GrafiteTypes.Option_error ("baseuri", "not found" ) -> 
      None,
      "Baseuri not set for this script. "
      ^ "Use 'set \"baseuri\" \"<uri>\".' to set it."
  | GrafiteTypes.Command_error msg -> None, "Error: " ^ msg
  | CicNotationParser.Parse_error err ->
      None, sprintf "Parse error: %s" err
  | UriManager.IllFormedUri uri -> None, sprintf "invalid uri: %s" uri
  | CicEnvironment.Object_not_found uri ->
      None, sprintf "object not found: %s" (UriManager.string_of_uri uri)
  | Unix.Unix_error (code, api, param) ->
      let err = Unix.error_message code in
      None, "Unix Error (" ^ api ^ "): " ^ err
  | HMarshal.Corrupt_file fname -> None, sprintf "file '%s' is corrupt" fname
  | HMarshal.Format_mismatch fname
  | HMarshal.Version_mismatch fname ->
      None,
      sprintf "format/version mismatch for file '%s', please recompile it'"
        fname
  | ProofEngineTypes.Fail msg -> None, "Tactic error: " ^ Lazy.force msg
  | Continuationals.Error s -> None, "Tactical error: " ^ Lazy.force s
  | CicTypeChecker.TypeCheckerFailure msg ->
     None, "Type checking error: " ^ Lazy.force msg
  | CicTypeChecker.AssertFailure msg ->
     None, "Type checking assertion failed: " ^ Lazy.force msg
  | LibrarySync.AlreadyDefined s -> 
     None, "Already defined: " ^ UriManager.string_of_uri s
  | GrafiteDisambiguator.DisambiguationError (offset,errorll) ->
     let rec aux n ?(dummy=false) (prev_msg,phases) =
      function
         [] -> [prev_msg,phases]
       | phase::tl ->
          let msg =
           String.concat "\n\n\n"
            (List.map (fun (floc,msg) ->
              let loc_descr =
               match floc with
                  None -> ""
                | Some floc ->
                   let (x, y) = HExtlib.loc_of_floc floc in
                    sprintf " at %d-%d" (x+offset) (y+offset)
              in
               "*Error" ^ loc_descr ^ ": " ^ Lazy.force msg) phase)
          in
           if msg = prev_msg then
            aux (n+1) (msg,phases@[n]) tl
           else
            (if not dummy then [prev_msg,phases] else []) @
             (aux (n+1) (msg,[n]) tl) in
     let loc =
      match errorll with
         ((Some floc,_)::_)::_ ->
          let (x, y) = HExtlib.loc_of_floc floc in
          let x = x + offset in
          let y = y + offset in
          let flocb,floce = floc in
          let floc =
           {flocb with Lexing.pos_cnum = x}, {floce with Lexing.pos_cnum = y}
          in
           Some floc
       | _ -> None in
     let rec explain =
      function
         [] -> ""
       | (msg,phases)::tl ->
           explain tl ^
           "***** Errors obtained during phase" ^
            (if phases = [] then " " else "s ") ^
            String.concat "," (List.map string_of_int phases) ^": *****\n"^
            msg ^ "\n\n"
     in
      loc,
       "********** DISAMBIGUATION ERRORS: **********\n" ^
        explain (aux 1 ~dummy:true ("",[]) errorll)
  | exn -> None, "Uncaught exception: " ^ Printexc.to_string exn

