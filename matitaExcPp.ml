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

let compact_disambiguation_errors all_passes errorll =
  let choices =
   List.flatten
    (List.map
      (fun (pass,l) ->
        List.map
         (fun (env,diff,offset,msg,significant) ->
           offset, [[pass], [[pass], env, diff], msg, significant]) l
      ) errorll) in
  (* Here we are doing a stable sort and list_uniq returns the latter
     "equal" element. I.e. we are showing the error corresponding to the
     most advanced disambiguation pass *)
  let choices =
   let choices_compare (o1,_) (o2,_) = compare o1 o2 in
   let choices_compare_by_passes (p1,_,_,_) (p2,_,_,_) =
    compare p1 p2 in
   let rec uniq =
    function
       [] -> []
     | h::[] -> [h]
     | (o1,res1)::(o2,res2)::tl when o1 = o2 ->
        let merge_by_name errors =
         let merge_by_env errors =
          let choices_compare_by_env (_,e1,_) (_,e2,_) = compare e1 e2 in
          let choices_compare_by_passes (p1,_,_) (p2,_,_) =
           compare p1 p2 in
          let rec uniq_by_env =
           function
              [] -> []
            | h::[] -> [h]
            | (p1,e1,_)::(p2,e2,d2)::tl when e1 = e2 ->
                uniq_by_env ((p1@p2,e2,d2) :: tl) 
            | h1::tl -> h1 :: uniq_by_env tl
          in
           List.sort choices_compare_by_passes
            (uniq_by_env (List.stable_sort choices_compare_by_env errors))
         in
         let choices_compare_by_msg (_,_,m1,_) (_,_,m2,_) =
          compare (Lazy.force m1) (Lazy.force m2) in
         let rec uniq_by_msg =
          function
             [] -> []
           | h::[] -> [h]
           | (p1,i1,m1,s1)::(p2,i2,m2,s2)::tl
             when Lazy.force m1 = Lazy.force m2 && s1 = s2 ->
               uniq_by_msg ((p1@p2,merge_by_env (i1@i2),m2,s2) :: tl)
           | h1::tl -> h1 :: uniq_by_msg tl
         in
          List.sort choices_compare_by_msg
           (uniq_by_msg (List.stable_sort choices_compare_by_msg errors))
        in
         let res = merge_by_name (res1@res2) in
          uniq ((o1,res) :: tl)
     | h1::tl -> h1 :: uniq tl
   in
   (* Errors in phase 3 that are not also in phase 4 are filtered out *)
   let filter_phase_3 choices =
    if all_passes then choices
    else
     let filter =
      HExtlib.filter_map
       (function
           (loffset,messages) ->
              let filtered_messages =
               HExtlib.filter_map
                (function
                    [3],_,_,_ -> None
                  | item -> Some item
                ) messages
              in
               if filtered_messages = [] then
                None
               else
                Some (loffset,filtered_messages))
     in
      filter choices
   in
    filter_phase_3
     (List.map (fun o,l -> o,List.sort choices_compare_by_passes l)
       (uniq (List.stable_sort choices_compare choices)))
  in
   choices
;;

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
  | ProofEngineHelpers.Bad_pattern msg ->
     None, "Bad pattern: " ^ Lazy.force msg
  | CicRefine.RefineFailure msg
  | CicRefine.AssertFailure msg ->
     None, "Refiner error: " ^ Lazy.force msg
  | CicTypeChecker.TypeCheckerFailure msg ->
     None, "Type checking error: " ^ Lazy.force msg
  | CicTypeChecker.AssertFailure msg ->
     None, "Type checking assertion failed: " ^ Lazy.force msg
  | LibrarySync.AlreadyDefined s -> 
     None, "Already defined: " ^ UriManager.string_of_uri s
  | CoercDb.EqCarrNotImplemented msg ->
     None, ("EqCarrNotImplemented: " ^ Lazy.force msg)
  | GrafiteDisambiguator.DisambiguationError (offset,errorll) ->
     let loc =
      match errorll with
         ((_,_,Some floc,_,_)::_)::_ ->
          let (x, y) = HExtlib.loc_of_floc floc in
          let x = x + offset in
          let y = y + offset in
          let floc = HExtlib.floc_of_loc (x,y) in
           Some floc
       | _ -> None in
     let annotated_errorll =
      List.rev
       (snd
         (List.fold_left (fun (pass,res) item -> pass+1,(pass+1,item)::res)
           (0,[]) errorll)) in
     let choices = compact_disambiguation_errors true annotated_errorll in
     let errorll =
      (List.map
       (function (loffset,l) ->
         List.map
          (function
            passes,envs_and_diffs,msg,significant ->
             let _,env,diff = List.hd envs_and_diffs in
              passes,env,diff,loffset,msg,significant
          ) l
        ) choices) in
     let rec aux =
      function
         [] -> []
       | phase::tl ->
          let msg =
            (List.map (fun (passes,_,_,floc,msg,significant) ->
              let loc_descr =
               match floc with
                  None -> ""
                | Some floc ->
                   let (x, y) = HExtlib.loc_of_floc floc in
                    sprintf " at %d-%d" (x+offset) (y+offset)
              in
               "*" ^ (if not significant then "(Spurious?) " else "")
               ^ "Error" ^ loc_descr ^ ": " ^ Lazy.force msg,
             passes) phase)
          in
           msg@aux tl in
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
        explain (aux errorll)
  | exn -> None, "Uncaught exception: " ^ Printexc.to_string exn

