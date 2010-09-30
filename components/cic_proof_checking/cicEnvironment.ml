(* Copyright (C) 2000, HELM Team.
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

(*****************************************************************************)
(*                                                                           *)
(*                              PROJECT HELM                                 *)
(*                                                                           *)
(*               Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                24/01/2000                                 *)
(*                                                                           *)
(* This module implements a trival cache system (an hash-table) for cic      *)
(* objects. Uses the getter (getter.ml) and the parser (cicParser.ml)        *)
(*                                                                           *)
(*****************************************************************************)

(* $Id$ *)

(* ************************************************************************** *
                 CicEnvironment SETTINGS (trust and clean_tmp)
 * ************************************************************************** *)

let debug = false;;
let cleanup_tmp = true;;
let trust = ref  (fun _ -> true);;
let set_trust f = trust := f
let trust_obj uri = !trust uri
let debug_print = if debug then fun x -> prerr_endline (Lazy.force x) else ignore

(* ************************************************************************** *
                                   TYPES 
 * ************************************************************************** *)

type type_checked_obj =
 | CheckedObj of (Cic.obj * CicUniv.universe_graph)    
 | UncheckedObj of Cic.obj * (CicUniv.universe_graph * CicUniv.universe list) option

exception AlreadyCooked of string;;
exception CircularDependency of string Lazy.t;;
exception CouldNotFreeze of string;;
exception CouldNotUnfreeze of string;;
exception Object_not_found of UriManager.uri;;


(* ************************************************************************** *
                         HERE STARTS THE CACHE MODULE 
 * ************************************************************************** *)

(* I think this should be the right place to implement mecanisms and 
 * invasriants 
 *)

(* Cache that uses == instead of = for testing equality *)
(* Invariant: an object is always in at most one of the *)
(* following states: unchecked, frozen and cooked.      *)
module Cache :
  sig
   val find_or_add_to_unchecked :
     UriManager.uri -> 
     get_object_to_add:
       (UriManager.uri -> 
         Cic.obj * (CicUniv.universe_graph * CicUniv.universe list) option) -> 
     Cic.obj * (CicUniv.universe_graph * CicUniv.universe list) option
   val can_be_cooked:
     UriManager.uri -> bool
   val unchecked_to_frozen : 
     UriManager.uri -> unit
   val frozen_to_cooked :
     uri:UriManager.uri -> 
     Cic.obj -> CicUniv.universe_graph -> CicUniv.universe list -> unit
   val find_cooked : 
     key:UriManager.uri -> 
       Cic.obj * CicUniv.universe_graph * CicUniv.universe list
   val add_cooked : 
     key:UriManager.uri -> 
     (Cic.obj * CicUniv.universe_graph * CicUniv.universe list) -> unit
   val remove: UriManager.uri -> unit
   val dump_to_channel : ?callback:(string -> unit) -> out_channel -> unit
   val restore_from_channel : ?callback:(string -> unit) -> in_channel -> unit
   val empty : unit -> unit
   val is_in_frozen: UriManager.uri -> bool
   val is_in_unchecked: UriManager.uri -> bool
   val is_in_cooked: UriManager.uri -> bool
   val list_all_cooked_uris: unit -> UriManager.uri list
   val invalidate: unit -> unit
  end 
=
  struct
   (*************************************************************************
     TASSI: invariant
     The cacheOfCookedObjects will contain only objects with a valid universe
     graph. valid means that not None (used if there is no universe file
     in the universe generation phase).
   **************************************************************************)

    (* DATA: the data structure that implements the CACHE *)
    module HashedType =
    struct
     type t = UriManager.uri
     let equal = UriManager.eq
     let hash = Hashtbl.hash
    end
    ;;

    module HT = Hashtbl.Make(HashedType);;

    let cacheOfCookedObjects = HT.create 1009;;

    (* DATA: The parking lists 
     * the lists elements are (uri * (obj * universe_graph option))
     * ( u, ( o, None )) means that the object has no universes file, this
     *  should happen only in the universe generation phase. 
     *  FIXME: if the universe generation is integrated in the library
     *  exportation phase, the 'option' MUST be removed.
     * ( u, ( o, Some g)) means that the object has a universes file,
     *  the usual case.
     *)

    (* frozen is used to detect circular dependency. *)
    let frozen_list = ref [];;
    (* unchecked is used to store objects just fetched, nothing more. *)    
    let unchecked_list = ref [];;

    let invalidate _ =
      let l = HT.fold (fun k (o,g,gl) acc -> (k,(o,Some (g,gl)))::acc) cacheOfCookedObjects [] in
      unchecked_list := 
        HExtlib.list_uniq ~eq:(fun (x,_) (y,_) -> UriManager.eq x y)
        (List.sort (fun (x,_) (y,_) -> UriManager.compare x y) (l @ !unchecked_list));
      frozen_list := [];
      HT.clear cacheOfCookedObjects;
    ;;

    let empty () = 
      HT.clear cacheOfCookedObjects;
      unchecked_list := [] ;
      frozen_list := []
    ;;

    (* FIX: universe stuff?? *)
    let dump_to_channel ?(callback = ignore) oc =
     HT.iter (fun uri _ -> callback (UriManager.string_of_uri uri)) 
       cacheOfCookedObjects;
     Marshal.to_channel oc cacheOfCookedObjects [] 
    ;;

    (* FIX: universes stuff?? *)
    let restore_from_channel ?(callback = ignore) ic =
      let restored = Marshal.from_channel ic in
      (* FIXME: should this empty clean the frozen and unchecked?
       * if not, the only-one-empty-end-not-3 patch is wrong 
       *)
      empty (); 
      HT.iter
       (fun k (v,u,l) ->
         callback (UriManager.string_of_uri k);
         let reconsed_entry = 
           CicUtil.rehash_obj v,
           CicUniv.recons_graph u,
           List.map CicUniv.recons_univ l
         in
         HT.add cacheOfCookedObjects 
           (UriManager.uri_of_string (UriManager.string_of_uri k)) 
           reconsed_entry)
       restored
    ;;

         
    let is_in_frozen uri =
      List.mem_assoc uri !frozen_list
    ;;
    
    let is_in_unchecked uri =
      List.mem_assoc uri !unchecked_list
    ;;
    
    let is_in_cooked uri =
      HT.mem cacheOfCookedObjects uri
    ;;

       
    (*******************************************************************
      TASSI: invariant
      we need, in the universe generation phase, to traverse objects
      that are not yet committed, so we search them in the frozen list.
      Only uncommitted objects without a universe file (see the assertion) 
      can be searched with method
    *******************************************************************)

    let find_or_add_to_unchecked uri ~get_object_to_add =
     try
       List.assq uri !unchecked_list
     with
         Not_found ->
           if List.mem_assq uri !frozen_list then
             (* CIRCULAR DEPENDENCY DETECTED, print the error and raise *)
             begin
(*
               prerr_endline "\nCircularDependency!\nfrozen list: \n";
               List.iter (
                 fun (u,(_,o)) ->
                   let su = UriManager.string_of_uri u in
                   let univ = if o = None then "NO_UNIV" else "" in
                   prerr_endline (su^" "^univ)) 
                 !frozen_list;
*)
               raise (CircularDependency (lazy (UriManager.string_of_uri uri)))
             end
           else
             if HT.mem cacheOfCookedObjects uri then
               (* DOUBLE COOK DETECTED, raise the exception *)
               raise (AlreadyCooked (UriManager.string_of_uri uri))
             else
               (* OK, it is not already frozen nor cooked *)
               let obj,ugraph_and_univlist = get_object_to_add uri in
               unchecked_list := (uri,(obj,ugraph_and_univlist))::!unchecked_list;
               obj, ugraph_and_univlist
    ;;

    let unchecked_to_frozen uri =
      try
        let obj,ugraph_and_univlist = List.assq uri !unchecked_list in
        unchecked_list := List.remove_assq uri !unchecked_list ;
        frozen_list := (uri,(obj,ugraph_and_univlist))::!frozen_list
      with
        Not_found -> raise (CouldNotFreeze (UriManager.string_of_uri uri))
    ;;

   let frozen_to_cooked ~uri o ug ul =
     CicUniv.assert_univs_have_uri ug ul;
     frozen_list := List.remove_assq uri !frozen_list ;
     HT.add cacheOfCookedObjects uri (o,ug,ul) 
   ;;

   let can_be_cooked uri = List.mem_assq uri !frozen_list;;
   
   let find_cooked ~key:uri = HT.find cacheOfCookedObjects uri ;;
 
   let add_cooked ~key:uri (obj,ugraph,univlist) = 
     HT.add cacheOfCookedObjects uri (obj,ugraph,univlist) 
   ;;

   (* invariant
    *
    * an object can be romeved from the cache only if we are not typechecking 
    * something. this means check and frozen must be empty.
    *)
   let remove uri =
     if !frozen_list <> [] then
       failwith "CicEnvironment.remove while type checking"
     else
      begin
       HT.remove cacheOfCookedObjects uri;
       unchecked_list :=
        List.filter (fun (uri',_) -> not (UriManager.eq uri uri')) !unchecked_list
      end
   ;;
   
   let  list_all_cooked_uris () =
     HT.fold (fun u _ l -> u::l) cacheOfCookedObjects []
   ;;
   
  end
;;

(* ************************************************************************
                        HERE ENDS THE CACHE MODULE
 * ************************************************************************ *)

(* exported cache functions *)
let dump_to_channel = Cache.dump_to_channel;;
let restore_from_channel = Cache.restore_from_channel;;
let empty = Cache.empty;;

let total_parsing_time = ref 0.0

let get_object_to_add uri =
 try
  let filename = Http_getter.getxml' uri in
  let bodyfilename =
    match UriManager.bodyuri_of_uri uri with
       None -> None
    |  Some bodyuri ->
        if Http_getter.exists' ~local:false bodyuri then
          Some (Http_getter.getxml' bodyuri)
        else
          None
  in
  let obj = 
    try 
      let time = Unix.gettimeofday() in
      let rc = CicParser.obj_of_xml uri filename bodyfilename in
      total_parsing_time := 
        !total_parsing_time +. ((Unix.gettimeofday()) -. time );
      rc
    with exn -> 
      (match exn with
      | CicParser.Getter_failure ("key_not_found", uri) ->
          raise (Object_not_found (UriManager.uri_of_string uri))
      | _ -> raise exn)
  in
  let ugraph_and_univlist,filename_univ = 
    try 
      let filename_univ = 
        let univ_uri = UriManager.univgraphuri_of_uri uri in
        Http_getter.getxml' univ_uri
      in
        Some (CicUniv.ugraph_and_univlist_of_xml filename_univ),
        Some filename_univ
    with 
    | Http_getter_types.Key_not_found _ 
    | Http_getter_types.Unresolvable_URI _ ->
      debug_print (lazy (
        "WE HAVE NO UNIVERSE FILE FOR " ^ (UriManager.string_of_uri uri)));
      None, None
  in
  obj, ugraph_and_univlist
 with Http_getter_types.Key_not_found _ -> raise (Object_not_found uri)
;;
 
(* this is the function to fetch the object in the unchecked list and 
 * nothing more (except returning it)
 *)
let find_or_add_to_unchecked uri =
 Cache.find_or_add_to_unchecked uri ~get_object_to_add

(* set_type_checking_info uri                                   *)
(* must be called once the type-checking of uri is finished     *)
(* The object whose uri is uri is unfreezed                     *)
(*                                                              *)
(* the replacement ugraph must be the one returned by the       *)
(* typechecker, restricted with the CicUnivUtils.clean_and_fill *)
let set_type_checking_info uri (o,ug,ul) =
  if not (Cache.can_be_cooked uri) then assert false
  else 
    Cache.frozen_to_cooked ~uri o ug ul
;;

(* fetch, unfreeze and commit an uri to the cacheOfCookedObjects and
 * return the object,ugraph
 *)
let add_trusted_uri_to_cache uri = 
  let o,u_and_ul = find_or_add_to_unchecked uri in
  Cache.unchecked_to_frozen uri;
  let u,ul = 
    match u_and_ul with
    (* for backward compat with Coq *)
    | None -> CicUniv.empty_ugraph, []
    | Some (ug,ul) -> ug, ul
  in
  set_type_checking_info uri (o,u,ul);
  try Cache.find_cooked uri
  with Not_found -> assert false 
;;

(* get the uri, if we trust it will be added to the cacheOfCookedObjects *)
let get_cooked_obj_with_univlist ?(trust=true) base_ugraph uri =
  try
    (* the object should be in the cacheOfCookedObjects *)
    let o,u,l = Cache.find_cooked uri in
      o,(CicUniv.merge_ugraphs ~base_ugraph ~increment:(u,uri(*,l*))),l
  with Not_found ->
    (* this should be an error case, but if we trust the uri... *)
    if trust && trust_obj uri then
      (* trusting means that we will fetch cook it on the fly *)
      let o,u,l = add_trusted_uri_to_cache uri in
        o,(CicUniv.merge_ugraphs ~base_ugraph ~increment:(u,uri(*,l*))),l
    else
      (* we don't trust the uri, so we fail *)
      begin
        debug_print (lazy ("CACHE MISS: " ^ (UriManager.string_of_uri uri)));
        raise Not_found
      end

let get_cooked_obj ?trust base_ugraph uri = 
  let o,g,_ = get_cooked_obj_with_univlist ?trust base_ugraph uri in
  o,g
      
let is_type_checked ?(trust=true) base_ugraph uri =
  try 
    let o,u,l = Cache.find_cooked uri in
      CheckedObj (o,(CicUniv.merge_ugraphs ~base_ugraph ~increment:(u,uri(*,l*))))
  with Not_found ->
    (* this should return UncheckedObj *)
    if trust && trust_obj uri then
      (* trusting means that we will fetch cook it on the fly *)
      let o,u,l = add_trusted_uri_to_cache uri in
        CheckedObj ( o, CicUniv.merge_ugraphs ~base_ugraph ~increment:(u,uri(*,l*)))
    else
      let o,u_and_ul = find_or_add_to_unchecked uri in
      Cache.unchecked_to_frozen uri;
      UncheckedObj (o,u_and_ul)
;;

(* as the get cooked, but if not present the object is only fetched,
 * not unfreezed and committed 
 *)
let get_obj base_ugraph uri =
  try
    (* the object should be in the cacheOfCookedObjects *)
    let o,u,_ = Cache.find_cooked uri in
    o,CicUniv.merge_ugraphs ~base_ugraph ~increment:(u,uri)
  with Not_found ->
    (* this should be an error case, but if we trust the uri... *)
      let o,u_and_l = find_or_add_to_unchecked uri in
      match u_and_l with
      | None -> o, base_ugraph
      | Some (ug,_) -> o,CicUniv.merge_ugraphs ~base_ugraph ~increment:(ug,uri)
;; 

let in_cache uri =
  Cache.is_in_cooked uri || Cache.is_in_frozen uri || Cache.is_in_unchecked uri

let add_type_checked_obj uri (obj,ugraph,univlist) =
 Cache.add_cooked ~key:uri (obj,ugraph,univlist)

let in_library uri = in_cache uri || Http_getter.exists' ~local:false uri

let remove_obj = Cache.remove
  
let list_uri () = 
  Cache.list_all_cooked_uris ()
;;

let list_obj () =
  try 
    List.map (fun u -> 
      let o,ug = get_obj CicUniv.empty_ugraph u in
        (u,o,ug)) 
    (list_uri ())
  with
    Not_found -> 
      debug_print (lazy "Who has removed the uri in the meanwhile?");
      raise Not_found
;;

let invalidate _ = 
   Cache.invalidate ()
;;
