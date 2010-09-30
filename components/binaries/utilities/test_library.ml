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

let trust = true
let deadline = 30
let conffile = "../../../matita/matita.conf.xml"

let _ = CicEnvironment.set_trust (fun _ -> trust);;
let _ = Helm_registry.load_from conffile;;

let old_total = ref 0.0
let new_total = ref 0.0

let separator = "=============" 

let perc newt oldt = (newt -. oldt) /. oldt *. 100.0

let _ =
 Sys.catch_break true;
 at_exit
  (fun () ->
    Printf.printf "%s\n" separator;
    Printf.printf "Total: %.2f\n" !new_total;
    if !old_total <> 0.0 then
     Printf.printf "Old: %.2f (%.2f%%)\n" !old_total (perc !new_total !old_total))
;;

let timeout = ref false;;

let _ =
 Sys.set_signal 14 (* SIGALRM *)
  (Sys.Signal_handle (fun _ ->
    timeout := true;
    raise Sys.Break))
;;

let urifname =
  try
    Sys.argv.(1)
  with Invalid_argument _ ->
   prerr_endline "You must supply a file with the list of URIs to check";
   exit (-1)

let ic = open_in urifname

exception Done;;

let _ =
  try
    while true do
      try
        let uri = input_line ic in
        if uri = separator then raise End_of_file;
        let uri,res,time =
         match Str.split (Str.regexp " ") uri with
            uri::res::time::_ -> uri, Some res, Some (float_of_string time)
          | [uri;res] -> uri, Some res, None
          | [ uri ] -> uri, None, None
          | _ -> assert false
        in
        Printf.printf "%s " uri;
        flush stdout;
        let uri = UriManager.uri_of_string uri in
        let obj,_ = CicEnvironment.get_obj CicUniv.empty_ugraph uri in
        ignore (Unix.alarm deadline);
        CicTypeChecker.typecheck_obj uri obj;
        ignore (Unix.alarm 0);
        CicEnvironment.remove_obj uri;
        let before = Unix.times () in
        ignore (Unix.alarm deadline);
        ignore (CicTypeChecker.typecheck_obj uri obj);
        ignore (Unix.alarm 0);
        let memusage = (Gc.stat ()).Gc.live_words * 4 / 1024 / 1024 in
        if memusage > 500 then
         begin
          prerr_endline ("MEMORIA ALLOCATA: " ^ string_of_int memusage ^ "Mb");
          CicEnvironment.empty ();
          Gc.compact ();
          let memusage = (Gc.stat ()).Gc.live_words * 4 / 1024 / 1024 in
            prerr_endline ("DOPO CicEnvironment.empty: " ^ string_of_int memusage ^ "Mb");
         end;
        let after = Unix.times () in
        let diff = after.Unix.tms_utime +. after.Unix.tms_stime -. before.Unix.tms_utime -. before.Unix.tms_stime in
        new_total := !new_total +. diff;
        Printf.printf "[0;32mOK[0m %.2f" diff;
        (match time with
           None -> Printf.printf "\n"
         | Some time ->
            old_total := !old_total +. time;
             Printf.printf " %.2f%%\n" (perc diff time))
      with
        | End_of_file as exn -> raise exn
        | Sys.Break ->
           let rec skip_break prompt =
            try
             if prompt then
              begin
               Printf.printf "[0;31mSKIPPED[0m\n";
               flush stdout;
               if not !timeout then
                begin
                 Printf.eprintf "[0;31mContinue with next URI? [y/_][0m";
                 flush stderr;
                end;
              end;
             if not !timeout then
              (match input_line stdin with
                  "y" -> ()
                | _ -> raise Done)
             else
              timeout := false
            with
             Sys.Break -> skip_break false
           in
            skip_break true
        | CicEnvironment.CircularDependency _ ->
           Printf.printf "[0;31mCIRCULARDEP[0m\n"
        | exn ->
           Printf.printf "[0;31mFAIL[0m\n";
           flush stdout;
           prerr_endline
            (match exn with
                CicTypeChecker.TypeCheckerFailure msg ->
                 "TypeCheckerFailure: " ^ Lazy.force msg
              | CicTypeChecker.AssertFailure msg ->
                 "TypeCheckerAssertion: " ^ Lazy.force msg
              | _ -> Printexc.to_string exn)
    done
  with
     End_of_file
   | Done -> ()
