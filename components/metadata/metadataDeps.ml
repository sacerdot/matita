(* Copyright (C) 2006, HELM Team.
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

open Printf

open MetadataTypes

module Pp = GraphvizPp.Dot
module UriSet = UriManager.UriSet

let strip_prefix s =
  let prefix_len = String.length position_prefix in
  String.sub s prefix_len (String.length s - prefix_len)

let parse_pos =
  function
    | Some s, Some d ->
        (match strip_prefix s with
        | "MainConclusion" -> `MainConclusion (Some (Eq (int_of_string d)))
        | "MainHypothesis" -> `MainHypothesis (Some (Eq (int_of_string d)))
        | s ->
            prerr_endline ("Invalid main position: " ^ s);
            assert false)
    | Some s, None ->
        (match strip_prefix s with
        | "InConclusion" -> `InConclusion
        | "InHypothesis" -> `InHypothesis
        | "InBody" -> `InBody
        | s ->
            prerr_endline ("Invalid position: " ^ s);
            assert false)
    | _ -> assert false

let unbox_row = function `Obj (uri, pos) -> (uri, pos)

let direct_deps ~dbd uri =
  let obj_metadata_of_row =
    function
      | [| Some _; Some occurrence; pos; depth |] ->
          `Obj (UriManager.uri_of_string occurrence, parse_pos (pos, depth))
      | _ ->
          prerr_endline "invalid (direct) refObj metadata row";
          assert false 
  in
  let do_query (dbtype, tbl) =
    let res = 
      HSql.exec dbtype dbd (SqlStatements.direct_deps tbl uri dbtype dbd) 
    in
    let deps =
      HSql.map res (fun row -> unbox_row (obj_metadata_of_row row)) in
    deps
  in
  do_query (HSql.User, MetadataTypes.obj_tbl ())
    @ do_query (HSql.Library, MetadataTypes.library_obj_tbl)
    @ do_query (HSql.Legacy, MetadataTypes.library_obj_tbl)

let inverse_deps ~dbd uri =
  let inv_obj_metadata_of_row =
    function
      | [| Some src; Some _; pos; depth |] ->
          `Obj (UriManager.uri_of_string src, parse_pos (pos, depth))
      | _ ->
          prerr_endline "invalid (inverse) refObj metadata row";
          assert false 
  in
  let do_query (dbtype, tbl) =
    let res = 
      HSql.exec dbtype dbd (SqlStatements.inverse_deps tbl uri dbtype dbd)
    in
    let deps =
      HSql.map res (fun row -> unbox_row (inv_obj_metadata_of_row row)) in
    deps
  in
  do_query (HSql.User, MetadataTypes.obj_tbl ())
    @ do_query (HSql.Library, MetadataTypes.library_obj_tbl)
    @ do_query (HSql.Legacy, MetadataTypes.library_obj_tbl)

let topological_sort ~dbd uris =
 let module OrderedUri =
  struct
   type t = UriManager.uri
   let compare = UriManager.compare
  end in
 let module Topo = HTopoSort.Make(OrderedUri) in
  Topo.topological_sort uris
   (fun uri -> fst (List.split (direct_deps ~dbd uri)))

let sorted_uris_of_baseuri ~dbd baseuri =
   let sql_pat = 
     Pcre.replace ~pat:"([^\\\\])_" ~templ:"$1\\_" baseuri ^ "%"
   in
   let query dbtype tbl =
      Printf.sprintf
         ("SELECT source FROM %s WHERE source LIKE \"%s\" "
          ^^ HSql.escape_string_for_like dbtype dbd)
         tbl sql_pat
   in
   let map cols = match cols.(0) with
      | Some s -> UriManager.uri_of_string s
      | _ -> assert false
   in
   let uris =
     List.fold_left
       (fun acc (dbtype, table) ->
          let result = HSql.exec dbtype dbd (query dbtype table) in
            HSql.map result map @ acc)
       []
       [HSql.User, MetadataTypes.name_tbl ();
       HSql.Library, MetadataTypes.library_name_tbl;
       HSql.Legacy, MetadataTypes.library_name_tbl]
   in
   let sorted_uris = topological_sort ~dbd uris in
   let filter_map uri =
      let s =
         Pcre.replace ~rex:(Pcre.regexp "#xpointer\\(1/1\\)") ~templ:""
                      (UriManager.string_of_uri uri)
      in
      try ignore (Pcre.exec ~rex:(Pcre.regexp"#xpointer") s); None
      with Not_found -> Some (UriManager.uri_of_string s)
   in
   HExtlib.filter_map filter_map sorted_uris

module DepGraph =
struct
  module UriTbl = UriManager.UriHashtbl

  let fat_value = 20
  let fat_increment = fat_value
  let incomplete_attrs = ["style", "dashed"]
  let global_node_attrs = ["fontsize", "12"; "width", ".4"; "height", ".4"]

  let label_of_uri uri = UriManager.name_of_uri uri
  (*let label_of_uri uri = UriManager.string_of_uri uri*)

  type neighborhood =
    { adjacency: UriManager.uri list lazy_t;  (* all outgoing edges *)
      mutable shown: int                      (* amount of edges to show *)
    }

    (** <adjacency list of the dependency graph,
     *   root,
     *   generator function,
     *   invert edges on render?>
     * All dependency graph have a single root, it is kept here to have a
     * starting point for graph traversals *)
  type t =
    neighborhood UriTbl.t * UriManager.uri
      * (UriManager.uri -> UriManager.uri list) * bool

  let dummy =
    UriTbl.create 0, UriManager.uri_of_string "cic:/a.con",
      (fun _ -> []), false

  let render fmt (adjlist, root, _f, invert) =
    let is_complete uri =
      try
        let neighbs = UriTbl.find adjlist uri in
        Lazy.lazy_is_val neighbs.adjacency
          && neighbs.shown >= List.length (Lazy.force neighbs.adjacency)
      with Not_found ->
        (*eprintf "Node '%s' not found.\n" (UriManager.string_of_uri uri);*)
        assert false
    in
    Pp.header ~graph_type:"strict digraph" ~graph_attrs:["rankdir", "LR"] ~node_attrs:global_node_attrs fmt;
    let rec aux =
      function
        | [] -> ()
        | uri :: tl ->
            let nice = UriManager.strip_xpointer in
            let suri = UriManager.string_of_uri (nice uri) in
            Pp.node suri
              ~attrs:([ "href", UriManager.string_of_uri uri;
                        "label", label_of_uri uri
                ] @ (if is_complete uri then [] else incomplete_attrs))
              fmt;
            let new_nodes = ref [] in
            (try
              let neighbs = UriTbl.find adjlist uri in
              if Lazy.lazy_is_val neighbs.adjacency then begin
                let adjacency, _ =
                  HExtlib.split_nth neighbs.shown (Lazy.force neighbs.adjacency)
                in
                List.iter
                  (fun dest ->
                    let uri1, uri2 = if invert then dest, uri else uri, dest in
                    Pp.edge (UriManager.string_of_uri (nice uri1))
                      (UriManager.string_of_uri (nice uri2)) fmt)
                  adjacency;
                new_nodes := adjacency
              end;
            with Not_found -> ());
            aux (!new_nodes @ tl)
    in
    aux [root];
    Pp.trailer fmt

  let expand uri (adjlist, _root, f, _invert) =
    (*eprintf "expanding uri %s\n%!" (UriManager.string_of_uri uri);*)
    try
      let neighbs = UriTbl.find adjlist uri in
      if not (Lazy.lazy_is_val neighbs.adjacency) then
          (* node has never been expanded *)
        let adjacency = Lazy.force neighbs.adjacency in
        let weight = min (List.length adjacency) fat_value in
        List.iter
          (fun dest ->
            (* perform look ahead of 1 edge to avoid making as expandable nodes
             * which have no outgoing edges *)
            let next_level = f dest in
            let neighborhood =
              if List.length next_level = 0 then begin
                (* no further outgoing edges, "expand" the node right now *)
                let lazy_val = lazy next_level in
                ignore (Lazy.force lazy_val);
                { adjacency = lazy_val; shown = 0 }
              end else
                { adjacency = lazy next_level; shown = 0 }
            in
            (*UriTbl.add adjlist dest { adjacency = lazy (f dest); shown = 0 }*)
            UriTbl.add adjlist dest neighborhood)
          adjacency;
        neighbs.shown <- weight;
        fst (HExtlib.split_nth weight adjacency), weight
      else begin  (* nodes has been expanded at least once *)
        let adjacency = Lazy.force neighbs.adjacency in
        let total_nodes = List.length adjacency in
        if neighbs.shown < total_nodes then begin
          (* some more children to show ... *)
          let shown_before = neighbs.shown in
          neighbs.shown <- min (neighbs.shown + fat_increment) total_nodes;
          let new_shown = neighbs.shown - shown_before in
          (fst (HExtlib.split_nth new_shown (List.rev adjacency))), new_shown
        end else
          [], 0 (* all children are already shown *)
      end
    with Not_found ->
      (*eprintf "uri not found: %s\n%!" (UriManager.string_of_uri uri);*)
      [], 0

  let collapse uri (adjlist, _root, f, _invert) =
    try
      let neighbs = UriTbl.find adjlist uri in
      if Lazy.lazy_is_val neighbs.adjacency then
        (* do not collapse already collapsed nodes *)
        if Lazy.force neighbs.adjacency <> [] then
          (* do not collapse nodes with no outgoing edges *)
          UriTbl.replace adjlist uri { adjacency = lazy (f uri); shown = 0 }
    with Not_found ->
      (* do not add a collapsed node if it was not part of the graph *)
      ()

  let graph_of_fun ?(invert = false) f ~dbd uri =
    let f ~dbd uri =
      (*eprintf "invoking graph fun on %s...\n%!" (UriManager.string_of_uri uri);*)
      let uris = fst (List.split (f ~dbd uri)) in
      let uriset = List.fold_right UriSet.add uris UriSet.empty in
      let res = UriSet.elements uriset in
      (*eprintf "returned uris: %s\n%!"*)
        (*(String.concat " " (List.map UriManager.string_of_uri res));*)
      res
    in
    let adjlist = UriTbl.create 17 in
    let gen_f = f ~dbd in
    UriTbl.add adjlist uri { adjacency = lazy (gen_f uri); shown = 0 };
    let dep_graph = adjlist, uri, gen_f, invert in
    let rec rec_expand weight =
      function
        | [] -> ()
        | uri :: tl when weight >= fat_value -> ()
        | uri :: tl ->
            let new_nodes, increase = expand uri dep_graph in
            rec_expand (weight + increase) (new_nodes @ tl) in
    rec_expand 1 [uri];
    dep_graph

  let direct_deps = graph_of_fun direct_deps
  let inverse_deps = graph_of_fun ~invert:true inverse_deps

  let expand uri graph =
    try
      ignore (expand uri graph)
    with Not_found -> ()
end

