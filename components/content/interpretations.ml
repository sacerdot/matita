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

let load_patterns32 = ref (fun _ -> assert false);;
let set_load_patterns32 f = load_patterns32 := f;;

type interpretation_id = int

let idref id t = Ast.AttributedTerm (`IdRef id, t)

type cic_id = string

type term_info =
  { sort: (cic_id, Ast.sort_kind) Hashtbl.t;
    uri: (cic_id, NReference.reference) Hashtbl.t;
  }

module IntMap = Map.Make(struct type t = int let compare = compare end);;
module StringMap = Map.Make(String);;

type db = {
  counter: int;
  pattern32_matrix: (bool * NotationPt.cic_appl_pattern * interpretation_id) list;
  level2_patterns32:
   (string * string * NotationPt.argument_pattern list *
     NotationPt.cic_appl_pattern) IntMap.t;
  interpretations: interpretation_id list StringMap.t; (* symb -> id list *)
}

let initial_db = {
   counter = -1; 
   pattern32_matrix = [];
   level2_patterns32 = IntMap.empty;
   interpretations = StringMap.empty
}

class type g_status =
  object
    method interp_db: db
  end
 
class status =
 object
   val interp_db = initial_db  
   method interp_db = interp_db
   method set_interp_db v = {< interp_db = v >}
   method set_interp_status
    : 'status. #g_status as 'status -> 'self
    = fun o -> {< interp_db = o#interp_db >}
 end

let find_level2_patterns32 status pid =
 IntMap.find pid status#interp_db.level2_patterns32

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

let fresh_id status =
  let counter = status#interp_db.counter+1 in
   status#set_interp_db ({ status#interp_db with counter = counter  }), counter

let add_interpretation (status : #status) dsc (symbol, args) appl_pattern =
  let status,id = fresh_id status in
  let ids =
   try
    StringMap.find symbol status#interp_db.interpretations
   with Not_found -> [id] in
  let status =
   status#set_interp_db { status#interp_db with
    level2_patterns32 =
      IntMap.add id (dsc, symbol, args, appl_pattern)
       status#interp_db.level2_patterns32;
    pattern32_matrix = (true,appl_pattern,id)::status#interp_db.pattern32_matrix;
    interpretations = StringMap.add symbol ids status#interp_db.interpretations
   }
  in
   !load_patterns32 status#interp_db.pattern32_matrix;
   status,id

let toggle_active_interpretations status b =
  status#set_interp_db { status#interp_db with
   pattern32_matrix =
     List.map (fun (_,ap,id) -> b,ap,id) status#interp_db.pattern32_matrix }

exception Interpretation_not_found

let lookup_interpretations status ?(sorted=true) symbol =
  try
    let raw = 
      List.map (
        fun id ->
          let (dsc, _, args, appl_pattern) =
            try IntMap.find id status#interp_db.level2_patterns32
            with Not_found -> assert false 
          in
          dsc, args, appl_pattern
      ) (StringMap.find symbol status#interp_db.interpretations)
    in
    if sorted then HExtlib.list_uniq (List.sort Pervasives.compare raw)
              else raw
  with Not_found -> raise Interpretation_not_found

let instantiate_appl_pattern 
  ~mk_appl ~mk_implicit ~term_of_nref env appl_pattern 
=
  let lookup name =
    try List.assoc name env
    with Not_found ->
      prerr_endline (sprintf "Name %s not found" name);
      assert false
  in
  let rec aux = function
    | Ast.NRefPattern nref -> term_of_nref nref
    | Ast.ImplicitPattern -> mk_implicit false
    | Ast.VarPattern name -> lookup name
    | Ast.ApplPattern terms -> mk_appl (List.map aux terms)
  in
  aux appl_pattern
