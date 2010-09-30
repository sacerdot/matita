(* Copyright (C) 2005, HELM Team.
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

(* fwd_simpl ****************************************************************)

let rec filter_map_n f n = function
   | []       -> []
   | hd :: tl -> 
      match f n hd with
         | None    -> filter_map_n f (succ n) tl
	 | Some hd -> hd :: filter_map_n f (succ n) tl

let get_uri t =
   let aux = function
      | Cic.Appl (hd :: tl) -> Some (CicUtil.uri_of_term hd, tl)
      | hd                  -> Some (CicUtil.uri_of_term hd, []) 
   in
   try aux t with
      | Invalid_argument "uri_of_term" -> None

let get_metadata t =
   let f n t =
      match get_uri t with
         | None          -> None 
	 | Some (uri, _) -> Some (n, uri)
   in
   match get_uri t with
      | None             -> None
      | Some (uri, args) -> Some (uri, filter_map_n f 1 args) 

let debug_metadata = function
   | None                 -> ()
   | Some (outer, inners) -> 
      let f (n, uri) = Printf.eprintf "%s: %i %s\n" "fwd" n (UriManager.string_of_uri uri) in
      Printf.eprintf "\n%s: %s\n" "fwd" (UriManager.string_of_uri outer);
      List.iter f inners; prerr_newline ()

let fwd_simpl ~dbd t =
   let map inners row = 
      match row.(0), row.(1), row.(2) with  
         | Some source, Some inner, Some index -> 
	    source,
             List.mem
              (int_of_string index, (UriManager.uri_of_string inner)) inners
	 | _                                   -> "", false
   in
   let rec rank ranks (source, ok) = 
      match ranks, ok with
         | [], false                               -> [source, 0]
	 | [], true                                -> [source, 1]
	 | (uri, i) :: tl, false when uri = source -> (uri, 0) :: tl
	 | (uri, 0) :: tl, true when uri = source  -> (uri, 0) :: tl
	 | (uri, i) :: tl, true when uri = source  -> (uri, succ i) :: tl
	 | hd :: tl, _ -> hd :: rank tl (source, ok)
   in
   let compare (_, x) (_, y) = compare x y in
   let filter n (uri, rank) =
      if rank > 0 then Some (UriManager.uri_of_string uri) else None
   in
   let metadata = get_metadata t in debug_metadata metadata;
   match metadata with
      | None                 -> []
      | Some (outer, inners) ->
         let select = "source, h_inner, h_index" in
	 let from = "genLemma" in
	 let where =
          Printf.sprintf "h_outer = \"%s\""
           (HSql.escape HSql.Library dbd (UriManager.string_of_uri outer)) in
         let query = Printf.sprintf "SELECT %s FROM %s WHERE %s" select from where in
	 let result = HSql.exec HSql.Library dbd query in
         let lemmas = HSql.map ~f:(map inners) result in
	 let ranked = List.fold_left rank [] lemmas in
	 let ordered = List.rev (List.fast_sort compare ranked) in
         filter_map_n filter 0 ordered

(* get_decomposables ********************************************************)

let decomposables ~dbd =
   let map row = match row.(0) with
      | None     -> None
      | Some str ->
         match CicUtil.term_of_uri (UriManager.uri_of_string str) with
            | Cic.MutInd (uri, typeno, _) -> Some (uri, Some typeno)
	    | Cic.Const (uri, _)          -> Some (uri, None)
	    | _                           -> 
	       raise (UriManager.IllFormedUri str)
   in
   let select, from = "source", "decomposables" in
   let query = Printf.sprintf "SELECT %s FROM %s" select from in
   let decomposables = HSql.map ~f:map (HSql.exec HSql.Library dbd query) in
   filter_map_n (fun _ x -> x) 0 decomposables   
