(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id$ *)

exception LibraryOutOfSync of string Lazy.t

type automation_cache = NDiscriminationTree.DiscriminationTree.t
type unit_eq_cache = NCicParamod.state

class type g_eq_status =
 object
   method eq_cache : unit_eq_cache 
 end

class eq_status :
 object('self)
  inherit g_eq_status
  method set_eq_cache: unit_eq_cache -> 'self
  method set_eq_status: #g_eq_status -> 'self
 end

class type g_auto_status =
 object
  method auto_cache : automation_cache
 end

class auto_status :
 object('self)
  inherit g_auto_status
  method set_auto_cache: automation_cache -> 'self
  method set_auto_status: #g_auto_status -> 'self
 end

type timestamp

class type g_status =
 object
  method timestamp: timestamp
  inherit NRstatus.g_status
 end

class status :
 object ('self)
  inherit g_status
  method set_timestamp: timestamp -> 'self
  method set_library_status: #g_status -> 'self
 end

(* it also checks it and add it to the environment *)
val add_obj: #status as 'status -> NCic.obj -> 'status
val add_constraint: 
  #status as 'status -> NCic.universe -> NCic.universe -> 'status
val aliases_of: NUri.uri -> NReference.reference list
val resolve: string -> NReference.reference list
(* warning: get_obj may raise (NCicEnvironment.ObjectNotFoud l) *)
val get_obj: NUri.uri -> NCic.obj (* changes the current timestamp *)

val clear_cache : unit -> unit

val time_travel: #status -> unit
val decompile: baseuri:NUri.uri -> unit

val init: unit -> unit

type obj

class type g_dumpable_status =
 object
  inherit g_status
  inherit g_auto_status
  inherit g_eq_status
  method dump: obj list
 end
  
class dumpable_status :
 object ('self)
  inherit status
  inherit auto_status
  inherit eq_status
  inherit g_dumpable_status
  method set_dump: obj list -> 'self
  method set_dumpable_status: #g_dumpable_status -> 'self
 end

type 'a register_type =
 < run: 'status.
    'a -> refresh_uri_in_universe:(NCic.universe ->
      NCic.universe) -> refresh_uri_in_term:(NCic.term -> NCic.term) ->
       (#dumpable_status as 'status) -> 'status >

module Serializer:
 sig
  val register: < run: 'a.  string -> 'a register_type -> ('a -> obj) >
  val serialize: baseuri:NUri.uri -> obj list -> unit
  val require: baseuri:NUri.uri -> (#dumpable_status as 'status) -> 'status
 end

(* CSC: only required during old-to-NG phase, to be deleted *)
val refresh_uri: NUri.uri -> NUri.uri

(* EOF *)
