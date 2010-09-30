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


(*
  The strings contains an unreadable message
*)
exception UniverseInconsistency of string Lazy.t

(*
  Cic.Type of universe 
*)
type universe

(*
  Opaque data structure you will use to store constraints
*)
type universe_graph

(*
  returns a fresh universe
*)
val fresh: 
  ?uri:UriManager.uri ->
  ?id:int ->
  unit -> 
    universe

    (* names a universe if unnamed *)
val name_universe: universe -> UriManager.uri -> universe
    
(*
  really useful at the begin and in all the functions that don't care 
  of universes
*)
val empty_ugraph: universe_graph

(* an universe that does nothing: i.e. no constraints are kept, no merges.. *)
val oblivion_ugraph: universe_graph

(* one of the previous two, no set to empty_ugraph *)
val default_ugraph: universe_graph


(*
  These are the real functions to add eq/ge/gt constraints 
  to the passed graph, returning an updated graph or raising
  UniverseInconsistency
*)
val add_eq: 
  universe -> universe -> universe_graph -> universe_graph
val add_ge: 
  universe -> universe -> universe_graph -> universe_graph
val add_gt: 
  universe -> universe -> universe_graph -> universe_graph

val do_rank: universe_graph -> int list * universe list
val get_rank: universe -> int

(*
  debug function to print the graph to standard error
*)
val print_ugraph: 
  universe_graph -> unit

(*
  does what expected, but I don't remember why this was exported
*)
val string_of_universe: 
  universe -> string

(*
  given the list of visible universes (see universes_of_obj) returns a
  cleaned graph (cleaned from the not visible nodes) 
*)
val clean_ugraph: 
  universe_graph -> universe list -> universe_graph

(*
  Since fresh() can't add the right uri to each node, you
  must fill empty nodes with the uri before you serialize the graph to xml

  these empty nodes are also filled in the universe list
*)
val fill_empty_nodes_with_uri:
  universe_graph -> universe list -> UriManager.uri -> 
    universe_graph * universe list

(*
  makes a union.
  TODO:
  - remember already merged uri so that we completely skip already merged
    graphs, this may include a dependecy graph (not merge a subpart of an
    already merged graph)
*)
val merge_ugraphs:
  base_ugraph:universe_graph -> 
  increment:(universe_graph * UriManager.uri) -> universe_graph

(*
  ugraph to xml file and viceversa
*)
val write_xml_of_ugraph: 
  string -> universe_graph -> universe list -> unit

(*
  given a filename parses the xml and returns the data structure
*)
val ugraph_and_univlist_of_xml:
  string -> universe_graph * universe list
val restart_numbering:
  unit -> unit

(*
  returns the universe number (used to save it do xml) 
*) 
val univno: universe -> int 
val univuri: universe -> UriManager.uri

  (** re-hash-cons URIs contained in the given universe so that phisicaly
   * equality could be enforced. Mainly used by
   * CicEnvironment.restore_from_channel *)
val recons_graph: universe_graph -> universe_graph

  (** re-hash-cons a single universe *)
val recons_univ: universe -> universe

  (** consistency check that should be done before committin the graph to the
   * cache *)
val assert_univs_have_uri: universe_graph -> universe list-> unit

  (** asserts the universe is named *)
val assert_univ: universe -> unit

val compare: universe -> universe -> int
val eq: universe -> universe -> bool

val is_anon: universe -> bool
