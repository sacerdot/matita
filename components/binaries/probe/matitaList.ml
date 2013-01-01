(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

module A = Array
module F = Filename
module P = Printf
module S = String
module Y = Sys

module U = NUri

module O = Options

let unsupported protocol =
   failwith (P.sprintf "probe: unsupported protocol: %s" protocol)

let missing path =
   failwith (P.sprintf "probe: missing path: %s" path)

let mk_file path =
   if F.check_suffix path "/" then S.sub path 0 (pred (S.length path))
   else path ^ ".ng"

let add_obj path =
   let path = F.chop_extension path in   
   let str = F.concat "cic:" path in
   O.objs := U.uri_of_string str :: !O.objs

let add_src path =
   let path = F.chop_extension path in   
   let str = F.concat "cic:" path ^ "/" in
   O.srcs := U.uri_of_string str :: !O.srcs

let rec scan_entry base path =
   if F.check_suffix path ".con.ng" then add_obj path else
   if F.check_suffix path ".ind.ng" then add_obj path else
   if F.check_suffix path ".var.ng" then add_obj path else 
   if F.check_suffix path ".ng" then add_src path else
   let files = Y.readdir (F.concat base path) in
   let map base file = scan_entry base (F.concat path file) in
   A.iter (map base) files

let from_uri base uri =
   let str = U.string_of_uri uri in
   let i = S.index str '/' in
   let protocol = S.sub str 0 i in
   if protocol = "cic:" then 
      let path = S.sub str (succ i) (S.length str - succ i) in
      let file = mk_file path in
      if Y.file_exists (F.concat base file) then scan_entry base file
      else missing path
   else unsupported protocol

let from_string base s =
   from_uri base (U.uri_of_string s)
