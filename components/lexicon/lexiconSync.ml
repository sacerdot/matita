(* Copyright (C) 2004-2005, HELM Team.
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

let alias_diff ~from status = 
  let module Map = DisambiguateTypes.Environment in
  Map.fold
    (fun domain_item codomain_item acc ->
      let description1 = LexiconAst.description_of_alias codomain_item in
      try
       let description2 = 
          LexiconAst.description_of_alias 
            (Map.find domain_item from#lstatus.LexiconEngine.aliases)
       in
        if description1 <> description2 then
         (domain_item,codomain_item)::acc
        else
          acc
      with
       Not_found ->
         (domain_item,codomain_item)::acc)
    status#lstatus.LexiconEngine.aliases []
;;

(** given a uri and a type list (the contructors types) builds a list of pairs
 *  (name,uri) that is used to generate automatic aliases **)
let extract_alias types uri = 
  fst(List.fold_left (
    fun (acc,i) (name, _, _, cl) -> 
      (name, UriManager.uri_of_uriref uri i None) ::
      (fst(List.fold_left (
        fun (acc,j) (name,_) ->
          (((name,UriManager.uri_of_uriref uri i
          (Some j)) :: acc) , j+1)
        ) (acc,1) cl)),i+1
  ) ([],0) types)

let build_aliases =
 List.map
  (fun (name,uri) ->
    DisambiguateTypes.Id name, LexiconAst.Ident_alias (name, 
     UriManager.string_of_uri uri))

let add_aliases_for_inductive_def status types uri = 
  let aliases = build_aliases (extract_alias types uri) in
   LexiconEngine.set_proof_aliases status aliases

let add_alias_for_constant status uri =
 let name = UriManager.name_of_uri uri in
 let new_env = build_aliases [(name,uri)] in
 LexiconEngine.set_proof_aliases status new_env

let add_aliases_for_objs status =
  function
   `Old _ -> assert false (* MATITA 1.0 *)
 | `New nrefs ->
     List.fold_left
      (fun status nref ->
        let references = NCicLibrary.aliases_of nref in
        let new_env =
         List.map
          (fun u ->
            let name = NCicPp.r2s true u in
             DisambiguateTypes.Id name,
              LexiconAst.Ident_alias (name,NReference.string_of_reference u)
          ) references
        in
         LexiconEngine.set_proof_aliases status new_env
      ) status nrefs
 
module OrderedId = 
struct
  type t = CicNotation.notation_id
  let compare =  CicNotation.compare_notation_id
end

module IdSet  = Set.Make (OrderedId)

  (** @return l2 \ l1 *)
let id_list_diff l2 l1 =
  let module S = IdSet in
  let s1 = List.fold_left (fun set uri -> S.add uri set) S.empty l1 in
  let s2 = List.fold_left (fun set uri -> S.add uri set) S.empty l2 in
  let diff = S.diff s2 s1 in
  S.fold (fun uri uris -> uri :: uris) diff []

let time_travel ~present ~past =
  let notation_to_remove =
    id_list_diff present#lstatus.LexiconEngine.notation_ids
     past#lstatus.LexiconEngine.notation_ids
  in
   List.iter CicNotation.remove_notation notation_to_remove

let push () = CicNotation.push ();;
let pop () = CicNotation.pop ();;