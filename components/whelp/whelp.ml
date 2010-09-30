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

let nonvar uri = not (UriManager.uri_is_var uri)

  (** maps a shell like pattern (which uses '*' and '?') to a sql pattern for
  * the "like" operator (which uses '%' and '_'). Does not support escaping. *)
let sqlpat_of_shellglob =
  let star_RE, qmark_RE, percent_RE, uscore_RE =
    Pcre.regexp "\\*", Pcre.regexp "\\?", Pcre.regexp "%", Pcre.regexp "_"
  in
  fun shellglob ->
    Pcre.replace ~rex:star_RE ~templ:"%"
      (Pcre.replace ~rex:qmark_RE ~templ:"_"
        (Pcre.replace ~rex:percent_RE ~templ:"\\%"
          (Pcre.replace ~rex:uscore_RE ~templ:"\\_"
            shellglob)))

let locate ~(dbd:HSql.dbd) ?(vars = false) pat =
  let escape dbtype dbd s = HSql.escape dbtype dbd s in
  let sql_pat = sqlpat_of_shellglob pat in
  let query dbtype tbl =
        sprintf 
          ("SELECT source FROM %s WHERE value LIKE \"%s\" "
           ^^ HSql.escape_string_for_like dbtype dbd)
          tbl (escape dbtype dbd sql_pat)
  in
  let tbls = 
    [HSql.User, MetadataTypes.name_tbl ();
     HSql.Library, MetadataTypes.library_name_tbl;
     HSql.Legacy, MetadataTypes.library_name_tbl]
  in
  let map cols =
    match cols.(0) with 
    | Some s -> UriManager.uri_of_string s | _ -> assert false
  in
  let result = 
    List.fold_left
      (fun acc (dbtype,tbl) -> 
         acc @ HSql.map ~f:map (HSql.exec dbtype dbd (query dbtype tbl)))
      [] tbls
  in
  List.filter nonvar result

let match_term ~(dbd:HSql.dbd) ty =
(*   debug_print (lazy (CicPp.ppterm ty)); *)
  let metadata = MetadataExtractor.compute ~body:None ~ty in
  let constants_no =
    MetadataConstraints.UriManagerSet.cardinal (MetadataConstraints.constants_of ty)
  in
  let full_card, diff =
    if CicUtil.is_meta_closed ty then
      Some (MetadataConstraints.Eq constants_no), None
    else
      let diff_no =
        let (hyp_constants, concl_constants) =
          (* collect different constants in hypotheses and conclusions *)
          List.fold_left
            (fun ((hyp, concl) as acc) metadata ->
               match (metadata: MetadataTypes.metadata) with
               | `Sort _ | `Rel _ -> acc
               | `Obj (uri, `InConclusion) | `Obj (uri, `MainConclusion _)
                 when not (List.mem uri concl) -> (hyp, uri :: concl)
               | `Obj (uri, `InHypothesis) | `Obj (uri, `MainHypothesis _)
                 when not (List.mem uri hyp) -> (uri :: hyp, concl)
               | `Obj _ -> acc)
            ([], [])
            metadata
        in
        List.length hyp_constants - List.length concl_constants
      in
      let (concl_metas, hyp_metas) = MetadataExtractor.compute_metas ty in
      let diff =
        if MetadataExtractor.IntSet.equal concl_metas hyp_metas then
          Some (MetadataConstraints.Eq diff_no)
        else if MetadataExtractor.IntSet.subset concl_metas hyp_metas then
          Some (MetadataConstraints.Gt (diff_no - 1))
        else if MetadataExtractor.IntSet.subset hyp_metas concl_metas then
          Some (MetadataConstraints.Lt (diff_no + 1))
        else
          None
      in
      None, diff
  in
  let constraints = List.map MetadataTypes.constr_of_metadata metadata in
    MetadataConstraints.at_least ~dbd ?full_card ?diff constraints

let fill_with_dummy_constants t =
  let rec aux i types =
    function
	Cic.Lambda (n,s,t) -> 
	  let dummy_uri = 
	    UriManager.uri_of_string ("cic:/dummy_"^(string_of_int i)^".con") in
	    (aux (i+1) (s::types)
	       (CicSubstitution.subst (Cic.Const(dummy_uri,[])) t))
      | t -> t,types
  in 
  let t,types = aux 0 [] t in
  t, List.rev types
      
let instance ~dbd t =
  let t',types = fill_with_dummy_constants t in 
  let metadata = MetadataExtractor.compute ~body:None ~ty:t' in
(*   List.iter 
    (fun x -> 
       debug_print 
         (lazy (MetadataPp.pp_constr (MetadataTypes.constr_of_metadata x)))) 
    metadata; *)
  let no_concl = MetadataDb.count_distinct `Conclusion metadata in
  let no_hyp = MetadataDb.count_distinct `Hypothesis metadata in
  let no_full = MetadataDb.count_distinct `Statement metadata in
  let is_dummy = function
    | `Obj(s, _) -> (String.sub (UriManager.string_of_uri s) 0 10) <> "cic:/dummy" 
	  | _ -> true 
  in
  let rec look_for_dummy_main = function
	  | [] -> None
    | `Obj(s,`MainConclusion (Some (MetadataTypes.Eq d)))::_ 
      when (String.sub (UriManager.string_of_uri s) 0 10 = "cic:/dummy") -> 
      let s = UriManager.string_of_uri s in
      let len = String.length s in
            let dummy_index = int_of_string (String.sub s 11 (len-15)) in
      let dummy_type = List.nth types dummy_index in
      Some (d,dummy_type)
    | _::l -> look_for_dummy_main l 
  in
  match (look_for_dummy_main metadata) with
    | None->
(*         debug_print (lazy "Caso None"); *)
        (* no dummy in main position *)
        let metadata = List.filter is_dummy metadata in
        let constraints = List.map MetadataTypes.constr_of_metadata metadata in
        let concl_card = Some (MetadataConstraints.Eq no_concl) in
        let full_card = Some (MetadataConstraints.Eq no_full) in
        let diff = Some (MetadataConstraints.Eq (no_hyp - no_concl)) in
          MetadataConstraints.at_least ~dbd ?concl_card ?full_card ?diff
            constraints
    | Some (depth, dummy_type) ->
(*         debug_print 
          (lazy (sprintf "Caso Some %d %s" depth (CicPp.ppterm dummy_type))); *)
        (* a dummy in main position *)
        let metadata_for_dummy_type = 
          MetadataExtractor.compute ~body:None ~ty:dummy_type in
        (* Let us skip this for the moment 
           let main_of_dummy_type = 
           look_for_dummy_main metadata_for_dummy_type in *)
        let metadata = List.filter is_dummy metadata in
        let constraints = List.map MetadataTypes.constr_of_metadata metadata in
        let metadata_for_dummy_type = 
          List.filter is_dummy metadata_for_dummy_type in
        let metadata_for_dummy_type, depth' = 
          (* depth' = the depth of the A -> A -> Prop *)
          List.fold_left (fun (acc,dep) c ->
            match c with
            | `Sort (s,`MainConclusion (Some (MetadataTypes.Eq i))) -> 
                (`Sort (s,`MainConclusion (Some (MetadataTypes.Ge i))))::acc, i
            | `Obj  (s,`MainConclusion (Some (MetadataTypes.Eq i))) -> 
                (`Obj (s,`MainConclusion (Some (MetadataTypes.Ge i))))::acc, i
            | `Rel  (`MainConclusion (Some (MetadataTypes.Eq i))) -> 
                (`Rel (`MainConclusion (Some (MetadataTypes.Ge i))))::acc, i
            | _ -> (c::acc,dep)) ([],0) metadata_for_dummy_type
        in
        let constraints_for_dummy_type =
           List.map MetadataTypes.constr_of_metadata metadata_for_dummy_type in
        (* start with the dummy constant in main conlusion *)
        let from = ["refObj as table0"] in (* XXX table hardcoded *)
        let where = 
          [sprintf "table0.h_position = \"%s\"" MetadataTypes.mainconcl_pos;
                 sprintf "table0.h_depth >= %d" depth] in
        let (n,from,where) =
          List.fold_left 
            (MetadataConstraints.add_constraint ~start:2)
            (2,from,where) constraints in
        let concl_card = Some (MetadataConstraints.Eq no_concl) in
        let full_card = Some (MetadataConstraints.Eq no_full) in
        let diff = Some (MetadataConstraints.Eq (no_hyp - no_concl)) in
        let (n,from,where) = 
          MetadataConstraints.add_all_constr 
            (n,from,where) concl_card full_card diff in
              (* join with the constraints over the type of the constant *)
        let where = 
          (sprintf "table0.h_occurrence = table%d.source" n)::where in
        let where = 
          sprintf "table0.h_depth - table%d.h_depth = %d" 
            n (depth - depth')::where
        in
        (* XXX performed only in library and legacy not user *)
        let (m,from,where) =
          List.fold_left 
            (MetadataConstraints.add_constraint ~start:n)
            (n,from,where) constraints_for_dummy_type 
        in
        MetadataConstraints.exec HSql.Library ~dbd (m,from,where)
        @
        MetadataConstraints.exec HSql.Legacy ~dbd (m,from,where)

let elim ~dbd uri =
  let constraints =
    [`Rel [`MainConclusion None];
     `Sort (Cic.Prop,[`MainHypothesis (Some (MetadataTypes.Ge 1))]);
     `Obj (uri,[`MainHypothesis (Some (MetadataTypes.Eq 0))]);
     `Obj (uri,[`InHypothesis]);
    ]
  in
  MetadataConstraints.at_least ~rating:`Hits ~dbd constraints

