(* Copyright (C) 2006, HELM Team.
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

type 'a t = ('a, int ref) Hashtbl.t

let create () = Hashtbl.create 113

let incr ~create_cb counters item =
  try
    let counter = Hashtbl.find counters item in
    incr counter
  with Not_found ->
    Hashtbl.add counters item (ref 1);
    create_cb item

let decr ~delete_cb counters item =
  try
    let counter = Hashtbl.find counters item in
    decr counter;
    if !counter = 0 then begin
      Hashtbl.remove counters item;
      delete_cb item
    end
  with Not_found ->
    prerr_endline "RefCounter: attempt to decrease unexistent counter";
    assert false

