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

module U  = NUri
module US = U.UriSet
module H  = HExtlib

module O = Options
module E = Engine

let chop_extension file =
   try F.chop_extension file
   with Invalid_argument("Filename.chop_extension") -> file

let src_exists path = !O.no_devel || Y.file_exists path

let is_obj base path = 
   if H.is_regular (F.concat base path) then
      F.check_suffix path ".con.ng" ||
      F.check_suffix path ".ind.ng" ||
      F.check_suffix path ".var.ng"
  else false

let is_src base path = 
   H.is_regular (F.concat base path) &&
   F.check_suffix path ".ng"

let is_dir base path =
   H.is_dir (F.concat base path)

let is_script devel =
   src_exists (chop_extension devel ^ ".ma")

let mk_file path =
   if F.check_suffix path "/" then S.sub path 0 (pred (S.length path))
   else path ^ ".ng"

let add_obj path =
   let path = F.chop_extension path in   
   let str = F.concat "cic:" path in
   O.objs := US.add (U.uri_of_string str) !O.objs

let add_src devel path =
   let path = F.chop_extension path in   
   let str = F.concat "cic:" path ^ "/" in
   O.srcs := US.add (U.uri_of_string str) !O.srcs

let add_remove base path =
   O.remove := F.concat base path :: !O.remove

let rec scan_entry inner base devel path =
(*   Printf.eprintf "%b %s %s%!\n" inner devel path; *)
   if is_obj base path && inner then add_obj path else
   if is_src base path && is_script devel then add_src devel path else 
   if is_dir base path && is_script devel then scan_dir true base devel path else
   if is_dir base path && src_exists devel then scan_dir false base devel path else
   add_remove base path

and scan_dir inner base devel path =
   let files = Y.readdir (F.concat base path) in
   let map base file = scan_entry inner base (F.concat devel file) (F.concat path file) in
   A.iter (map base) files

let from_uri base devel uri =
   O.no_devel := devel = "";
   let str = U.string_of_uri uri in
   let i = S.index str '/' in
   let protocol = S.sub str 0 i in
   if protocol = "cic:" then 
      let path = S.sub str (succ i) (S.length str - succ i) in
      let file = mk_file path in
      if Y.file_exists (F.concat base file) then
         scan_entry (is_script devel) base devel file 
      else E.missing path
   else E.unsupported protocol

let from_string base devel s =
   from_uri base devel (U.uri_of_string s)
