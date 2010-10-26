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

open Printf

module Ast = NotationPt

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

type interpretation_id = int

let idref id t = Ast.AttributedTerm (`IdRef id, t)

type cic_id = string

type term_info =
  { sort: (cic_id, Ast.sort_kind) Hashtbl.t;
    uri: (cic_id, UriManager.uri) Hashtbl.t;
  }

  (* persistent state *)

let initial_level2_patterns32 () = Hashtbl.create 211
let initial_interpretations () = Hashtbl.create 211

let level2_patterns32 = ref (initial_level2_patterns32 ())
(* symb -> id list ref *)
let interpretations = ref (initial_interpretations ())
let pattern32_matrix = ref []
let counter = ref ~-1 
let find_level2_patterns32 pid = Hashtbl.find !level2_patterns32 pid;;

let stack = ref []

let push () =
 stack := (!counter,!level2_patterns32,!interpretations,!pattern32_matrix)::!stack;
 counter := ~-1;
 level2_patterns32 := initial_level2_patterns32 ();
 interpretations := initial_interpretations ();
 pattern32_matrix := []
;;

let pop () =
 match !stack with
    [] -> assert false
  | (ocounter,olevel2_patterns32,ointerpretations,opattern32_matrix)::old ->
   stack := old;
   counter := ocounter;
   level2_patterns32 := olevel2_patterns32;
   interpretations := ointerpretations;
   pattern32_matrix := opattern32_matrix
;;

let add_idrefs =
  List.fold_right (fun idref t -> Ast.AttributedTerm (`IdRef idref, t))

let instantiate32 term_info idrefs env symbol args =
  let rec instantiate_arg = function
    | Ast.IdentArg (n, name) ->
        let t = 
          try List.assoc name env 
          with Not_found -> prerr_endline ("name not found in env: "^name);
                            assert false
        in
        let rec count_lambda = function
          | Ast.AttributedTerm (_, t) -> count_lambda t
          | Ast.Binder (`Lambda, _, body) -> 1 + count_lambda body
          | _ -> 0
        in
        let rec add_lambda t n =
          if n > 0 then
            let name = NotationUtil.fresh_name () in
            Ast.Binder (`Lambda, (Ast.Ident (name, None), None),
              Ast.Appl [add_lambda t (n - 1); Ast.Ident (name, None)])
          else
            t
        in
        add_lambda t (n - count_lambda t)
  in
  let head =
    let symbol = Ast.Symbol (symbol, 0) in
    add_idrefs idrefs symbol
  in
  if args = [] then head
  else Ast.Appl (head :: List.map instantiate_arg args)

let load_patterns32s = ref [];;

let add_load_patterns32 f = load_patterns32s := f :: !load_patterns32s;;
let fresh_id =
  fun () ->
    incr counter;
    !counter

let add_interpretation dsc (symbol, args) appl_pattern =
  let id = fresh_id () in
  Hashtbl.add !level2_patterns32 id (dsc, symbol, args, appl_pattern);
  pattern32_matrix := (true, appl_pattern, id) :: !pattern32_matrix;
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s;
  (try
    let ids = Hashtbl.find !interpretations symbol in
    ids := id :: !ids
  with Not_found -> Hashtbl.add !interpretations symbol (ref [id]));
  id

let get_all_interpretations () =
  List.map
    (function (_, _, id) ->
      let (dsc, _, _, _) =
        try
          Hashtbl.find !level2_patterns32 id
        with Not_found -> assert false
      in
      (id, dsc))
    !pattern32_matrix

let get_active_interpretations () =
  HExtlib.filter_map (function (true, _, id) -> Some id | _ -> None)
    !pattern32_matrix

let set_active_interpretations ids =
  let pattern32_matrix' =
    List.map
      (function 
        | (_, ap, id) when List.mem id ids -> (true, ap, id)
        | (_, ap, id) -> (false, ap, id))
      !pattern32_matrix
  in
  pattern32_matrix := pattern32_matrix';
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s

exception Interpretation_not_found

let lookup_interpretations ?(sorted=true) symbol =
  try
    let raw = 
      List.map (
        fun id ->
          let (dsc, _, args, appl_pattern) =
            try
              Hashtbl.find !level2_patterns32 id
            with Not_found -> assert false 
          in
          dsc, args, appl_pattern
      )
      !(Hashtbl.find !interpretations symbol)
    in
    if sorted then HExtlib.list_uniq (List.sort Pervasives.compare raw)
              else raw
  with Not_found -> raise Interpretation_not_found

let remove_interpretation id =
  (try
    let dsc, symbol, _, _ = Hashtbl.find !level2_patterns32 id in
    let ids = Hashtbl.find !interpretations symbol in
    ids := List.filter ((<>) id) !ids;
    Hashtbl.remove !level2_patterns32 id;
  with Not_found -> raise Interpretation_not_found);
  pattern32_matrix :=
    List.filter (fun (_, _, id') -> id <> id') !pattern32_matrix;
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s

let init () = List.iter (fun f -> f []) !load_patterns32s

let instantiate_appl_pattern 
  ~mk_appl ~mk_implicit ~term_of_uri ~term_of_nref env appl_pattern 
=
  let lookup name =
    try List.assoc name env
    with Not_found ->
      prerr_endline (sprintf "Name %s not found" name);
      assert false
  in
  let rec aux = function
    | Ast.UriPattern uri -> term_of_uri uri
    | Ast.NRefPattern nref -> term_of_nref nref
    | Ast.ImplicitPattern -> mk_implicit false
    | Ast.VarPattern name -> lookup name
    | Ast.ApplPattern terms -> mk_appl (List.map aux terms)
  in
  aux appl_pattern

