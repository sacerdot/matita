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

module Trivial_disambiguate:
sig
  exception Ambiguous_term of string Lazy.t
  (** disambiguate an _unanmbiguous_ term using dummy callbacks which fail if a
    * choice from the user is needed to disambiguate the term
    * @raise Ambiguous_term for ambiguous term *)
  val disambiguate_string:
    dbd:HSql.dbd ->
    ?context:Cic.context ->
    ?metasenv:Cic.metasenv ->
    ?initial_ugraph:CicUniv.universe_graph -> 
    ?aliases:DisambiguateTypes.environment ->(* previous interpretation status*)
    string ->
    ((DisambiguateTypes.domain_item * DisambiguateTypes.codomain_item) list *
     Cic.metasenv *                 (* new metasenv *)
     Cic.term *
     CicUniv.universe_graph) list   (* disambiguated term *)
end
=
struct
  exception Ambiguous_term of string Lazy.t
  exception Exit
  module Callbacks =
  struct
    let non p x = not (p x)
    let interactive_user_uri_choice ~selection_mode ?ok
          ?(enable_button_for_non_vars = true) ~title ~msg ~id uris =
            List.filter (non UriManager.uri_is_var) uris
    let interactive_interpretation_choice interp = raise Exit
    let input_or_locate_uri ~(title:string) ?id = raise Exit
  end
  module Disambiguator = Disambiguate.Make (Callbacks)
  let disambiguate_string ~dbd ?(context = []) ?(metasenv = []) ?initial_ugraph
    ?(aliases = DisambiguateTypes.Environment.empty) term
  =
    let ast =
      CicNotationParser.parse_level2_ast (Ulexing.from_utf8_string term)
    in
    try
      fst (Disambiguator.disambiguate_term ~dbd ~context ~metasenv ("",0,ast)
        ?initial_ugraph ~aliases ~universe:None)
    with Exit -> raise (Ambiguous_term (lazy term))
end

let configuration_file = ref "../../../matita/matita.conf.xml";;

let core_notation_script = "../../../matita/core_notation.moo";;

let get_from_user ~(dbd:HSql.dbd) =
  let rec get () =
    match read_line () with
    | "" -> []
    | t -> t::(get ())
  in
  let term_string = String.concat "\n" (get ()) in
  let env, metasenv, term, ugraph =
    List.nth (Trivial_disambiguate.disambiguate_string dbd term_string) 0
  in
  term, metasenv, ugraph
;;

let full = ref false;;

let retrieve_only = ref false;;

let demod_equalities = ref false;;

let main () =
  let module S = Saturation in
  let set_ratio v = S.weight_age_ratio := v; S.weight_age_counter := v
  and set_sel v = S.symbols_ratio := v; S.symbols_counter := v;
  and set_conf f = configuration_file := f
  and set_ordering o =
    match o with
    | "lpo" -> Utils.compare_terms := Utils.lpo
    | "kbo" -> Utils.compare_terms := Utils.kbo
    | "nr-kbo" -> Utils.compare_terms := Utils.nonrec_kbo
    | "ao" -> Utils.compare_terms := Utils.ao
    | o -> raise (Arg.Bad ("Unknown term ordering: " ^ o))
  and set_fullred b = S.use_fullred := b
  and set_time_limit v = S.time_limit := float_of_int v
  and set_width w = S.maxwidth := w
  and set_depth d = S.maxdepth := d
  and set_full () = full := true
  and set_retrieve () = retrieve_only := true
  and set_demod_equalities () = demod_equalities := true
  in
  Arg.parse [
    "-full", Arg.Unit set_full, "Enable full mode";
    "-f", Arg.Bool set_fullred,
    "Enable/disable full-reduction strategy (default: enabled)";
    
    "-r", Arg.Int set_ratio, "Weight-Age equality selection ratio (default: 4)";

    "-s", Arg.Int set_sel,
    "symbols-based selection ratio (relative to the weight ratio, default: 0)";

    "-c", Arg.String set_conf, "Configuration file (for the db connection)";

    "-o", Arg.String set_ordering,
    "Term ordering. Possible values are:\n" ^
      "\tkbo: Knuth-Bendix ordering\n" ^
      "\tnr-kbo: Non-recursive variant of kbo (default)\n" ^
      "\tlpo: Lexicographic path ordering";

    "-l", Arg.Int set_time_limit, "Time limit in seconds (default: no limit)";
    
    "-w", Arg.Int set_width,
    Printf.sprintf "Maximal width (default: %d)" !Saturation.maxwidth;
    
    "-d", Arg.Int set_depth,
    Printf.sprintf "Maximal depth (default: %d)" !Saturation.maxdepth;

    "-retrieve", Arg.Unit set_retrieve, "retrieve only";
    "-demod-equalities", Arg.Unit set_demod_equalities, "demod equalities";
  ] (fun a -> ()) "Usage:";
  Helm_registry.load_from !configuration_file;
  ignore (CicNotation2.load_notation [] core_notation_script);
  ignore (CicNotation2.load_notation [] "../../../matita/library/legacy/coq.ma");
  let dbd = HSql.quick_connect
    ~host:(Helm_registry.get "db.host")
    ~user:(Helm_registry.get "db.user")
    ~database:(Helm_registry.get "db.database")
    ()
  in
  let term, metasenv, ugraph = get_from_user ~dbd in
  if !retrieve_only then
    Saturation.retrieve_and_print dbd term metasenv ugraph
  else if !demod_equalities then
    Saturation.main_demod_equalities dbd term metasenv ugraph
  else
    Saturation.main dbd !full term metasenv ugraph
;;

let _ =
  (*try*)
    main ()
  (*with exn -> prerr_endline (Printexc.to_string exn)*)

