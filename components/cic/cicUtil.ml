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

module C  = Cic

let xpointer_RE = Str.regexp "\\([^#]+\\)#xpointer(\\(.*\\))"
let slash_RE = Str.regexp "/"

let term_of_uri uri =
  let s = UriManager.string_of_uri uri in
  try
    (if UriManager.uri_is_con uri then
      C.Const (uri, [])
    else if UriManager.uri_is_var uri then
      C.Var (uri, [])
    else if not (Str.string_match xpointer_RE s 0) then
      raise (UriManager.IllFormedUri s)
    else
      let (baseuri,xpointer) = (Str.matched_group 1 s, Str.matched_group 2 s) in
      let baseuri = UriManager.uri_of_string baseuri in
      (match Str.split slash_RE xpointer with
      | [_; tyno] -> C.MutInd (baseuri, int_of_string tyno - 1, [])
      | [_; tyno; consno] ->
          C.MutConstruct
            (baseuri, int_of_string tyno - 1, int_of_string consno, [])
      | _ -> raise Exit))
  with
  | Exit
  | Failure _
  | Not_found -> raise (UriManager.IllFormedUri s)
