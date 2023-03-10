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

module F = Filename
module L = List
module P = Printf

module U  = NUri
module US = U.UriSet
module B  = Librarian
module H  = HExtlib

module M = MacLexer
module X = Error

let out_int i = P.printf "%u\n" i

let out_length uris = out_int (US.cardinal uris)

let out_uris uris =
  let map uri = P.printf "%S\n" (U.string_of_uri uri) in
  US.iter map uris

let is_registry str =
  F.check_suffix str ".conf.xml"

let get_uri str =
  let str = H.normalize_path str in
  let dir, file =
    if H.is_regular str && F.check_suffix str ".ma"
    then F.dirname str, F.chop_extension (F.basename str)
    else if H.is_dir str then str, ""
    else X.missing str
  in
  let rec aux bdir file = match B.find_roots_in_dir bdir with
  | [root] ->
    let buri = L.assoc "baseuri" (B.load_root_file root) in
    F.concat bdir file, F.concat buri file
  | roots  ->
    if bdir = F.current_dir_name || bdir = F.dir_sep then X.unrooted dir roots else
    aux (F.dirname bdir) (F.concat (F.basename bdir) file)
  in
  aux dir file

let mac fname =
  let ich = open_in fname in
  let lexbuf = Lexing.from_channel ich in
  M.token lexbuf; close_in ich
