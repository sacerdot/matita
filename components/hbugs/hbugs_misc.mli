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

  (** helpers *)

  (** remove all bindings of a given key from an hash table *)
val hashtbl_remove_all: ('a, 'b) Hashtbl.t -> 'a -> unit

  (** follows cut and paste from zack's Http_client_smart module *)

  (** can't parse an HTTP url *)
exception Malformed_URL of string
  (** can't parse an HTTP response *)
exception Malformed_HTTP_response of string
 
  (** HTTP GET request for a given url, return http response's body *)
val http_get: string -> string
  (** HTTP POST request for a given url, return http response's body,
 body argument, if specified, is sent as body along with request *)
val http_post: ?body:string -> string -> string

  (** perform an HTTP GET request and apply a given function on each
  'slice' of HTTP response read from server *)
val http_get_iter_buf: callback:(string -> unit) -> string -> unit

