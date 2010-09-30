(*
 * Copyright (C) 2003:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open Printf;;

let rec hashtbl_remove_all tbl key =
  if Hashtbl.mem tbl key then begin
    Hashtbl.remove tbl key;
    hashtbl_remove_all tbl key
  end else
    ()

  (** follows cut and paste from zack's Http_client_smart module *)

exception Malformed_URL of string;;
exception Malformed_HTTP_response of string;;

let bufsiz = 16384;;
let tcp_bufsiz = 4096;;

let body_sep_RE = Pcre.regexp "\r\n\r\n";;
let http_scheme_RE = Pcre.regexp ~flags:[`CASELESS] "^http://";;
let url_RE = Pcre.regexp "^([\\w.]+)(:(\\d+))?(/.*)?$";;
let parse_url url =
  try
    let subs =
      Pcre.extract ~rex:url_RE (Pcre.replace ~rex:http_scheme_RE url)
    in
    (subs.(1),
    (if subs.(2) = "" then 80 else int_of_string subs.(3)),
    (if subs.(4) = "" then "/" else subs.(4)))
  with exc -> raise (Malformed_URL url)
;;
let get_body answer =
  match Pcre.split ~rex:body_sep_RE answer with
  | [_; body] -> body
  | _ -> raise (Malformed_HTTP_response answer)
;;

let init_socket addr port =
  let inet_addr = (Unix.gethostbyname addr).Unix.h_addr_list.(0) in
  let sockaddr = Unix.ADDR_INET (inet_addr, port) in
  let suck = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
  Unix.connect suck sockaddr;
  let outchan = Unix.out_channel_of_descr suck in
  let inchan = Unix.in_channel_of_descr suck in
  (inchan, outchan)
;;
let rec retrieve inchan buf =
  Buffer.add_string buf (input_line inchan ^ "\n");
  retrieve inchan buf
;;

let http_get_iter_buf ~callback url =
  let (address, port, path) = parse_url url in
  let buf = String.create tcp_bufsiz in
  let (inchan, outchan) = init_socket address port in
  output_string outchan (sprintf "GET %s\r\n" path);
  flush outchan;
  (try
    while true do
      match input inchan buf 0 tcp_bufsiz with
      | 0 -> raise End_of_file
      | bytes when bytes = tcp_bufsiz ->  (* buffer full, no need to slice it *)
          callback buf
      | bytes when bytes < tcp_bufsiz ->  (* buffer not full, slice it *)
          callback (String.sub buf 0 bytes)
      | _ -> (* ( bytes < 0 ) || ( bytes > tcp_bufsiz ) *)
          assert false
    done
  with End_of_file -> ());
  close_in inchan (* close also outchan, same fd *)
;;

let http_get url =
  let buf = Buffer.create (tcp_bufsiz * 10) in
  http_get_iter_buf (fun data -> Buffer.add_string buf data) url;
  get_body (Buffer.contents buf)
;;

let http_post ?(body = "") url =
  let (address, port, path) = parse_url url in
  let (inchan, outchan) = init_socket address port in
  output_string outchan (sprintf "POST %s HTTP/1.0\r\n" path);
  output_string outchan (sprintf "Content-Length: %d\r\n" (String.length body));
  output_string outchan "\r\n";
  output_string outchan body;
  flush outchan;
  let buf = Buffer.create bufsiz in
  (try
    retrieve inchan buf
  with End_of_file -> close_in inchan); (* close also outchan, same fd *)
  get_body (Buffer.contents buf)
;;

