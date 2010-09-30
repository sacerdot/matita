(*
 * Copyright (C) 2003:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

open Hbugs_types;;

exception Client_already_in of client_id
exception Client_not_found of client_id
exception Musing_already_in of musing_id
exception Musing_not_found of musing_id
exception Tutor_already_in of tutor_id
exception Tutor_not_found of tutor_id

class type registry =
  object
    method dump: string
    method purge: unit
  end

class clients:
  object
      (** 'register client_id client_url' *)
    method register: client_id -> string -> unit
    method unregister: client_id -> unit
    method isAuthenticated: client_id -> bool
      (** subcribe a client to a set of tutor removing previous subcriptions *)
    method subscribe: client_id -> tutor_id list -> unit
    method getUrl: client_id -> string
    method getSubscription: client_id -> tutor_id list

    method dump: string
    method purge: unit
  end

class tutors:
  object
    method register: tutor_id -> string -> hint_type -> string -> unit
    method unregister: tutor_id -> unit
    method isAuthenticated: tutor_id -> bool
    method exists: tutor_id -> bool
    method getTutor: tutor_id -> string * hint_type * string
    method getUrl: tutor_id -> string
    method getHintType: tutor_id -> hint_type
    method getDescription: tutor_id -> string
    method index: tutor_dsc list

    method dump: string
    method purge: unit
  end

class musings:
  object
    method register: musing_id -> client_id -> tutor_id -> unit
    method unregister: musing_id -> unit
    method getByMusingId: musing_id -> client_id * tutor_id
    method getByClientId: client_id -> musing_id list
    method getByTutorId: tutor_id -> musing_id list
    method isActive: musing_id -> bool

    method dump: string
    method purge: unit
  end

