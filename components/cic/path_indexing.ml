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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

(* path indexing implementation *)

(* position of the subterm, subterm (Appl are not stored...) *)

module PathIndexing =
  functor(A:Set.S) -> 
    struct

type path_string_elem = Index of int | Term of Cic.term;;
type path_string = path_string_elem list;; 


let rec path_strings_of_term index =
  let module C = Cic in function
  | C.Meta _ -> [ [Index index; Term (C.Implicit None)] ]
  | C.Appl (hd::tl) ->
      let p = if index > 0 then [Index index; Term hd] else [Term hd] in
      let _, res = 
        List.fold_left
          (fun (i, r) t ->
             let rr = path_strings_of_term i t in
             (i+1, r @ (List.map (fun ps -> p @ ps) rr)))
          (1, []) tl
      in
      res
  | term -> [ [Index index; Term term] ]
;;

(*
let string_of_path_string ps =
  String.concat "."
    (List.map
       (fun e ->
          let s =
            match e with
            | Index i -> "Index " ^ (string_of_int i)
            | Term t -> "Term " ^ (CicPp.ppterm t)
          in
          "(" ^ s ^ ")")
       ps)
;;  
*)

module OrderedPathStringElement = struct
  type t = path_string_elem

  let compare t1 t2 =
    match t1, t2 with
    | Index i, Index j -> Pervasives.compare i j
    | Term t1, Term t2 -> if t1 = t2 then 0 else Pervasives.compare t1 t2
    | Index _, Term _ -> -1
    | Term _, Index _ -> 1
end

module PSMap = Map.Make(OrderedPathStringElement);;

module PSTrie = Trie.Make(PSMap);;

type t = A.t PSTrie.t
type key = Cic.term
let empty = PSTrie.empty
let arities = Hashtbl.create 0

let index trie term info =
  let ps = path_strings_of_term 0 term in
  List.fold_left 
  (fun trie ps ->
     let ps_set = try PSTrie.find ps trie with Not_found -> A.empty in
     let trie = PSTrie.add ps (A.add info ps_set) trie in
       trie) trie ps

let remove_index trie term info=
  let ps = path_strings_of_term 0 term in
  List.fold_left
    (fun trie ps ->
       try
        let ps_set = A.remove info (PSTrie.find ps trie) in
        if A.is_empty ps_set then
          PSTrie.remove ps trie
        else
          PSTrie.add ps ps_set trie
       with Not_found -> trie) trie ps
;;

let in_index trie term test =
  let ps = path_strings_of_term 0 term in
  let ok ps =
    try
      let set = PSTrie.find ps trie in
	A.exists test set
    with Not_found ->
      false
  in
  List.exists ok ps
;;


let head_of_term = function
  | Cic.Appl (hd::tl) -> hd
  | term -> term
;;


let subterm_at_pos index term =
  if index = 0 then
    term
  else
    match term with
    | Cic.Appl l ->
        (try List.nth l index with Failure _ -> raise Not_found)
    | _ -> raise Not_found
;;


let rec retrieve_generalizations trie term =
  match trie with
  | PSTrie.Node (value, map) ->
      let res = 
        match term with
        | Cic.Meta _ -> A.empty
        | term ->
            let hd_term = head_of_term term in
            try
              let n = PSMap.find (Term hd_term) map in
              match n with
              | PSTrie.Node (Some s, _) -> s
              | PSTrie.Node (None, m) ->
                  let l = 
                    PSMap.fold
                      (fun k v res ->
                         match k with
                         | Index i ->
                             let t = subterm_at_pos i term in
                             let s = retrieve_generalizations v t in
                             s::res
                         | _ -> res)
                      m []
                  in
                  match l with
                  | hd::tl ->
                      List.fold_left (fun r s -> A.inter r s) hd tl
                  | _ -> A.empty
            with Not_found ->
              A.empty
      in
      try
        let n = PSMap.find (Term (Cic.Implicit None)) map in
        match n with
        | PSTrie.Node (Some s, _) -> A.union res s
        | _ -> res
      with Not_found ->
        res
;;


let rec retrieve_unifiables trie term =
  match trie with
  | PSTrie.Node (value, map) ->
      let res = 
        match term with
        | Cic.Meta _ ->
            PSTrie.fold
              (fun ps v res -> A.union res v)
              (PSTrie.Node (None, map))
              A.empty
        | _ ->
            let hd_term = head_of_term term in
            try
              let n = PSMap.find (Term hd_term) map in
              match n with
              | PSTrie.Node (Some v, _) -> v
              | PSTrie.Node (None, m) ->
                  let l = 
                    PSMap.fold
                      (fun k v res ->
                         match k with
                         | Index i ->
                             let t = subterm_at_pos i term in
                             let s = retrieve_unifiables v t in
                             s::res
                         | _ -> res)
                      m []
                  in
                  match l with
                  | hd::tl ->
                      List.fold_left (fun r s -> A.inter r s) hd tl
                  | _ -> A.empty
            with Not_found ->
              A.empty
      in
      try
        let n = PSMap.find (Term (Cic.Implicit None)) map in
        match n with
        | PSTrie.Node (Some s, _) -> A.union res s
        | _ -> res
      with Not_found ->
        res
;;

end
