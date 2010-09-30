(* Copyright (C) 2000, HELM Team.
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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

(*
 * "cic:/a/b/c.con" => ("cic:/a/b/c.con", id )
 * "cic:/a/b/c.ind#xpointer(1/1)" => ("cic:/a/b/c.con#xpointer(1/1)", id)
 * "cic:/a/b/c.ind#xpointer(1/1/1)" => ("cic:/a/b/c.con#xpointer(1/1/1)", id)
 *)

let fresh_id =
 let id = ref 0 in
  function () ->
    incr id;
    !id

(* (uriwithxpointer, uniqueid) 
 * where uniqueid is used to build a set of uri *)
type uri = string * int;;

let eq uri1 uri2 =
  uri1 == uri2 
;;

let string_of_uri (uri,_) =
 uri

let name_of_uri (uri, _) = 
  let xpointer_offset = 
    try String.rindex uri '#' with Not_found -> String.length uri - 1
  in
  let index1 = String.rindex_from uri xpointer_offset '/' + 1 in
  let index2 = String.rindex uri '.' in
  String.sub uri index1 (index2 - index1)

let nameext_of_uri (uri, _) = 
  let xpointer_offset, mah = 
    try String.rindex uri '#', 0 with Not_found -> String.length uri - 1, 1
  in
  let index1 = String.rindex_from uri xpointer_offset '/' + 1 in
  String.sub uri index1 (xpointer_offset - index1 + mah)
  
let buri_of_uri (uri,_) = 
  let xpointer_offset = 
    try String.rindex uri '#' with Not_found -> String.length uri - 1
  in
  let index = String.rindex_from uri xpointer_offset '/' in
  String.sub uri 0 index

module OrderedStrings =
 struct
  type t = string
  let compare (s1 : t) (s2 : t) = compare s1 s2
 end
;;

module MapStringsToUri = Map.Make(OrderedStrings);;

(* Invariant: the map is the identity function,
 *  i.e. 
 *    let str' = (MapStringsToUri.find str !set_of_uri) in
 *    str' == (MapStringsToUri.find str' !set_of_uri)
 *)
let set_of_uri = ref MapStringsToUri.empty;;

exception IllFormedUri of string;;

let _dottypes = ".types"
let _types = "types",5
let _dotuniv = ".univ"
let _univ = "univ",4
let _dotann = ".ann"
let _ann = "ann",3
let _var = "var",3
let _dotbody = ".body"
let _con = "con",3
let _ind = "ind",3
let _xpointer = "#xpointer(1/"
let _con3 = "con"
let _var3 = "var"
let _ind3 = "ind"
let _ann3 = "ann"
let _univ4 = "univ"
let _types5 = "types"
let _xpointer8 = "xpointer"
let _cic5 = "cic:/"

let is_malformed suri =
  try 
    if String.sub suri 0 5 <> _cic5 then true
    else
      let len = String.length suri - 5 in
      let last5 = String.sub suri len 5 in
      let last4 = String.sub last5 1 4 in
      let last3 = String.sub last5 2 3 in
      if last3 = _con3 || last3 = _var3 || last3 = _ind3 || 
         last3 = _ann3 || last5 = _types5 || last5 = _dotbody ||
         last4 = _univ4 then 
           false
      else 
        try
          let index = String.rindex suri '#' + 1 in
          let xptr = String.sub suri index 8 in
          if xptr = _xpointer8 then
            false
          else
            true
        with Not_found -> true
  with Invalid_argument _ -> true
    
(* hash conses an uri *)
let uri_of_string suri =
  try
    MapStringsToUri.find suri !set_of_uri
  with Not_found -> 
    if is_malformed suri then
      raise (IllFormedUri suri) 
    else
      let new_uri = suri, fresh_id () in
      set_of_uri := MapStringsToUri.add suri new_uri !set_of_uri;
      new_uri


let strip_xpointer ((uri,_) as olduri) =
  try 
    let index = String.rindex uri '#' in
    let no_xpointer = String.sub uri 0 index in
    uri_of_string no_xpointer
  with
    Not_found -> olduri

let clear_suffix uri ?(pat2="",0) pat1 =
  try
    let index = String.rindex uri '.' in
    let index' = index + 1 in 
    let suffix = String.sub uri index' (String.length uri - index') in
    if fst pat1 = suffix || fst pat2 = suffix then
      String.sub uri 0 index
    else
      uri
  with
    Not_found -> assert false

let has_suffix uri (pat,n) =
  try
    let suffix = String.sub uri (String.length uri - n) n in
    pat = suffix 
  with
    Not_found -> assert false

 
let cicuri_of_uri (uri, _) = uri_of_string (clear_suffix uri ~pat2:_types _ann)

let annuri_of_uri (uri , _) = uri_of_string ((clear_suffix uri _ann) ^ _dotann)

let uri_is_annuri (uri, _) = has_suffix uri _ann

let uri_is_var (uri, _) = has_suffix uri _var

let uri_is_con (uri, _) = has_suffix uri _con

let uri_is_ind (uri, _) = has_suffix uri _ind

let bodyuri_of_uri (uri, _) =
  if has_suffix uri _con then
    Some (uri_of_string (uri ^ _dotbody))
  else
    None
;;

let ind_uri_split ((s, _) as uri) =
    let noxp = strip_xpointer uri in
    try 
      (let arg_index = String.rindex s '(' in
       try 
         (let ty_index = String.index_from s arg_index '/' in
          try 
            (let k_index = String.index_from s (ty_index+1) '/' in
             let tyno = int_of_string (String.sub s (ty_index + 1) (k_index - ty_index - 1)) in
             let kno = int_of_string (String.sub s (k_index + 1) (String.length s - k_index - 2)) in
             noxp, Some tyno, Some kno)
          with Not_found -> 
            let tyno = int_of_string (String.sub s (ty_index + 1) (String.length s - ty_index - 2)) in
            noxp, Some tyno, None)
       with Not_found -> noxp, None, None
      )
    with Not_found -> noxp, None, None
;;

(* these are bugged!
 * we should remove _types, _univ, _ann all toghether *)
let innertypesuri_of_uri (uri, _) =
  uri_of_string ((clear_suffix uri _types) ^ _dottypes)
;;
let univgraphuri_of_uri (uri,_) = 
  uri_of_string ((clear_suffix uri _univ) ^ _dotuniv)
;;
  

let uri_of_uriref (uri, _) typeno consno =
  let typeno = typeno + 1 in
  let suri =
    match consno with
    | None -> Printf.sprintf "%s%s%d)" uri _xpointer typeno
    | Some n -> Printf.sprintf "%s%s%d/%d)" uri _xpointer typeno n
  in
  uri_of_string suri

let compare (_,id1) (_,id2) = id1 - id2

module OrderedUri =
struct
  type t = uri
  let compare = compare (* the one above, not Pervasives.compare *)
end

module UriSet = Set.Make (OrderedUri)

(*
module OrderedUriPair =
struct
  type t = uri * uri
  let compare (u11, u12) (u21, u22) =
    match compare u11 u21 with
    | 0 -> compare u12 u22
    | x -> x
end

module UriPairSet = Set.Make (OrderedUriPair)
*)

module HashedUri =
struct
  type t = uri
  let equal = eq
  let hash = snd
end

module UriHashtbl = Hashtbl.Make (HashedUri)


