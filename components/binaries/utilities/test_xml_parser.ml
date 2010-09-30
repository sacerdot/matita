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

let _ =
  Helm_registry.set "getter.mode" "remote";
  Helm_registry.set "getter.url" "http://mowgli.cs.unibo.it:58081/"

let body_RE = Str.regexp "^.*\\.body$"
let con_RE = Str.regexp "^.*\\.con$"

let unlink f =
  if Sys.file_exists f then
    Unix.unlink f

let rec parse uri tmpfile1 tmpfile2 =
(*prerr_endline (sprintf "%s %s" tmpfile1 (match tmpfile2 with None -> "None" | Some f -> "Some " ^ f));*)
  (try
    let uri' = UriManager.uri_of_string uri in
    let time_new0 = Unix.gettimeofday () in
(*    let obj_new = CicPushParser.CicParser.annobj_of_xml tmpfile1 tmpfile2 in*)
    let obj_new = CicParser.annobj_of_xml uri' tmpfile1 tmpfile2 in
    let time_new1 = Unix.gettimeofday () in

    let time_old0 = Unix.gettimeofday () in
    ignore (Unix.system (sprintf "gunzip -c %s > test.tmp && mv test.tmp %s"
      tmpfile1 tmpfile1));
    (match tmpfile2 with
    | Some tmpfile2 ->
        ignore (Unix.system (sprintf "gunzip -c %s > test.tmp && mv test.tmp %s"
          tmpfile2 tmpfile2));
    | None -> ());
    let obj_old = CicPxpParser.CicParser.annobj_of_xml uri' tmpfile1 tmpfile2 in
    let time_old1 = Unix.gettimeofday () in

    let time_old = time_old1 -. time_old0 in
    let time_new = time_new1 -. time_new0 in
    let are_equal = (obj_old = obj_new) in
    printf "%s\t%b\t%f\t%f\t%f\n"
      uri are_equal time_old time_new (time_new /. time_old *. 100.);
    flush stdout;
  with
  | CicParser.Getter_failure ("key_not_found", uri)
    when Str.string_match body_RE uri 0 ->
      parse uri tmpfile1 None
  | CicParser.Parser_failure msg ->
      printf "%s FAILED (%s)\n" uri msg; flush stdout)

let _ =
  try
    while true do
      let uri = input_line stdin in
      let tmpfile1 = Http_getter.getxml uri in
      let tmpfile2 =
        if Str.string_match con_RE uri 0 then begin
          Some (Http_getter.getxml (uri ^ ".body"))
        end else
          None
      in
      parse uri tmpfile1 tmpfile2
    done
  with End_of_file -> ()

