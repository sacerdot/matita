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

open Printf

let is_a_variant obj = 
  match obj with
    | Cic.Constant(_,_,_,_,attrs) ->
	List.exists (fun x -> x = `Flavour `Variant) attrs
    | _ -> false

let uris_for_inductive_type uri obj =
  match obj with 
    | Cic.InductiveDefinition(types,_,_,_) ->
	let suri = UriManager.string_of_uri uri in
	let uris,_ =
	  List.fold_left
	    (fun (acc,i) (_,_,_,constructors)->
	       let is = string_of_int i in	     
	       let newacc,_ =
		 List.fold_left
		   (fun (acc,j) _ ->
		      let js = string_of_int j in
			UriManager.uri_of_string
			  (suri^"#xpointer(1/"^is^"/"^js^")")::acc,j+1) 
		   (acc,1) constructors
	       in
	       newacc,i+1)
	    ([],1) types 
	in uris
    | _ -> [uri] 
;;

  (** @return l2 \ l1 *)
let uri_list_diff l2 l1 =
  let module S = UriManager.UriSet in
  let s1 = List.fold_left (fun set uri -> S.add uri set) S.empty l1 in
  let s2 = List.fold_left (fun set uri -> S.add uri set) S.empty l2 in
  let diff = S.diff s2 s1 in
  S.fold (fun uri uris -> uri :: uris) diff []

let initial_status lexicon_status baseuri =
 (new GrafiteTypes.status baseuri)#set_lstatus lexicon_status#lstatus
;;

let time_travel  ~present ?(past=initial_status present present#baseuri) () =
  NCicLibrary.time_travel past
;;

let init lexicon_status =
  initial_status lexicon_status
  ;;
let pop () =
  LibraryObjects.pop ()
;;

let push () =
  LibraryObjects.push ()
;;

