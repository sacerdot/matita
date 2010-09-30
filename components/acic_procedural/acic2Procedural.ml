(* Copyright (C) 2003-2005, HELM Team.
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

module C  = Cic
module L  = Librarian
module G  = GrafiteAst

module H  = ProceduralHelpers
module T  = ProceduralTypes
module P1 = Procedural1
module P2 = Procedural2
module X  = ProceduralTeX

let tex_formatter = ref None

(* object costruction *******************************************************)

let th_flavours = [`Theorem; `Lemma; `Remark; `Fact]

let def_flavours = [`Definition; `Variant]

let get_flavour sorts params context v attrs =
   let rec aux = function
      | []               -> 
         if H.is_acic_proof sorts context v then List.hd th_flavours
	 else List.hd def_flavours
      | `Flavour fl :: _ -> fl
      | _ :: tl          -> aux tl
   in
   let flavour_map x y = match x, y with
      | None, G.IPAs flavour -> Some flavour
      | _                    -> x
   in   
   match List.fold_left flavour_map None params with
      | Some fl -> fl
      | None    -> aux attrs

let rec is_record = function
   | []                           -> None
   | `Class (`Record fields) :: _ -> Some fields
   | _ :: tl                      -> is_record tl

let proc_obj ?(info="") proc_proof sorts params context = function
   | C.AConstant (_, _, s, Some v, t, [], attrs)         ->
      begin match get_flavour sorts params context v attrs with
         | flavour when List.mem flavour th_flavours  ->
            let ast = proc_proof v in
            let steps, nodes = T.count_steps 0 ast, T.count_nodes 0 ast in
            let text =
	       if List.mem G.IPComments params then 
	          Printf.sprintf "%s\n%s%s: %u\n%s: %u\n%s"
	          "COMMENTS" info "Tactics" steps "Final nodes" nodes "END"
	       else
	          ""
	    in
            T.Statement (flavour, Some s, t, None, "") :: ast @ [T.Qed text]
         | flavour when List.mem flavour def_flavours ->
            [T.Statement (flavour, Some s, t, Some v, "")]
	 | _                                  ->
            failwith "not a theorem, definition, axiom or inductive type"
      end
   | C.AConstant (_, _, s, None, t, [], attrs)           ->
      [T.Statement (`Axiom, Some s, t, None, "")]
   | C.AInductiveDefinition (_, types, [], lpsno, attrs) ->
      begin match is_record attrs with
         | None    -> [T.Inductive (types, lpsno, "")]
	 | Some fs -> [T.Record (types, lpsno, fs, "")]
      end
   | _                                          ->
      failwith "not a theorem, definition, axiom or inductive type"

(* interface functions ******************************************************)

let get_proc_proof ~ids_to_inner_sorts ~ids_to_inner_types params context =
   let level_map x y = match x, y with
      | None, G.IPLevel level -> Some level
      | _                     -> x
   in   
   match List.fold_left level_map None params with
      | None
      | Some 2 ->   
         P2.proc_proof 
            (P2.init ~ids_to_inner_sorts ~ids_to_inner_types params context)
      | Some 1 ->
         P1.proc_proof 
            (P1.init ~ids_to_inner_sorts ~ids_to_inner_types params context)
      | Some n ->
         failwith (
	    "Procedural reconstruction level not supported: " ^ 
	    string_of_int n
	 )

let procedural_of_acic_object ~ids_to_inner_sorts ~ids_to_inner_types 
   ?info params anobj = 
   let proc_proof = 
      get_proc_proof ~ids_to_inner_sorts ~ids_to_inner_types params []
   in 
   L.time_stamp "P : LEVEL 2  ";
   HLog.debug "Procedural: level 2 transformation";
   let steps = proc_obj ?info proc_proof ids_to_inner_sorts params [] anobj in
   let _ = match !tex_formatter with
      | None     -> ()
      | Some frm -> X.tex_of_steps frm ids_to_inner_sorts steps
   in
   L.time_stamp "P : RENDERING";
   HLog.debug "Procedural: grafite rendering";
   let r = List.rev (T.render_steps [] steps) in
   L.time_stamp "P : DONE     "; r

let procedural_of_acic_term ~ids_to_inner_sorts ~ids_to_inner_types params
   context annterm = 
   let proc_proof =
      get_proc_proof ~ids_to_inner_sorts ~ids_to_inner_types params context
   in
   HLog.debug "Procedural: level 2 transformation";
   let steps = proc_proof annterm in
   let _ = match !tex_formatter with
      | None     -> ()
      | Some frm -> X.tex_of_steps frm ids_to_inner_sorts steps
   in
   HLog.debug "Procedural: grafite rendering";
   List.rev (T.render_steps [] steps)

let rec is_debug n = function
   | []                   -> false
   | G.IPDebug debug :: _ -> n <= debug
   | _ :: tl              -> is_debug n tl
