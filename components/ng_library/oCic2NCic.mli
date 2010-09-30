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

val nuri_of_ouri: UriManager.uri -> NUri.uri

val reference_of_ouri: UriManager.uri -> NReference.spec -> NReference.reference

val reference_of_oxuri: UriManager.uri -> NReference.reference

val convert_obj: UriManager.uri -> Cic.obj -> NCic.obj list
val convert_term: UriManager.uri -> Cic.term -> NCic.term * NCic.obj list

val clear: unit -> unit
