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

type timestamp

class type g_status =
 object
  method timestamp: timestamp
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

module type SerializerType =
 sig
  type dumpable_status

  type 'a register_type =
   'a ->
    refresh_uri_in_universe:(NCic.universe -> NCic.universe) ->
    refresh_uri_in_term:(NCic.term -> NCic.term) ->
     dumpable_status -> dumpable_status

  val register: < run: 'a.  string -> 'a register_type -> ('a -> obj) >
  val serialize: baseuri:NUri.uri -> obj list -> unit
   (* the obj is the "include" command to be added to the dump list *)
  val require: baseuri:NUri.uri -> dumpable_status -> dumpable_status * obj
 end

module Serializer(D: sig type dumpable_status end) :
  SerializerType with type dumpable_status = D.dumpable_status

class dumpable_status :
 object ('self)
  method dump: obj list
  method set_dump: obj list -> 'self
 end

(* CSC: only required during old-to-NG phase, to be deleted *)
val refresh_uri: NUri.uri -> NUri.uri

(* EOF *)
