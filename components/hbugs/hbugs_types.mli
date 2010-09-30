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

type broker_id = string
type client_id = string
type musing_id = string
type tutor_id = string
type tutor_dsc = tutor_id * string  (* tutor id, tutor description *)

type state =  (* proof assitant's state: proof type, proof body, goal *)
  string * string * int

type hint =
    (* tactics usage related hints *)
  | Use_ring
  | Use_fourier
  | Use_reflexivity
  | Use_symmetry
  | Use_assumption
  | Use_contradiction
  | Use_exists
  | Use_split
  | Use_left
  | Use_right
  | Use_apply of string        (* use apply tactic on embedded term *)
    (* hints list *)
  | Hints of hint list

type hint_type = string              (* TODO tipo di consiglio per l'utente *)

type musing_result =
  | Eureka of hint            (* extra information, if any, parsed depending
                                on tutor's hint_type *)
  | Sorry

  (* for each message, first component is an ID that identify the sender *)
type message =

  (* general purpose *)
  | Help  (* help request *)
  | Usage of string (* help response *)       (* usage string *)
  | Exception of string * string              (* name, value *)

  (* client -> broker *)
  | Register_client of client_id * string     (* client id, client url *)
  | Unregister_client of client_id            (* client id *)
  | List_tutors of client_id                  (* client_id *)
  | Subscribe of client_id * tutor_id list    (* client id, tutor id list *)
  | State_change of client_id * state option  (* client_id, new state *)
  | Wow of client_id                          (* client_id *)

  (* tutor -> broker *)
  | Register_tutor of tutor_id * string * hint_type * string
                                              (* tutor id, tutor url, hint type,
                                              tutor description *)
  | Unregister_tutor of tutor_id              (* tutor id *)
  | Musing_started of tutor_id * musing_id    (* tutor id, musing id *)
  | Musing_aborted of tutor_id * musing_id    (* tutor id, musing id *)
  | Musing_completed of tutor_id * musing_id * musing_result
                                              (* tutor id, musing id, result *)

  (* broker -> client *)
  | Client_registered of broker_id            (* broker id *)
  | Client_unregistered of broker_id          (* broker id *)
  | Tutor_list of broker_id * tutor_dsc list  (* broker id, tutor list *)
  | Subscribed of broker_id * tutor_id list   (* broker id, tutor list *)
  | State_accepted of broker_id * musing_id list * musing_id list
                                              (* broker id, stopped musing ids,
                                              started musing ids *)
  | Hint of broker_id * hint                  (* broker id, hint *)

  (* broker -> tutor *)
  | Tutor_registered of broker_id             (* broker id *)
  | Tutor_unregistered of broker_id           (* broker id *)
  | Start_musing of broker_id * state         (* broker id, state *)
  | Abort_musing of broker_id * musing_id     (* broker id, musing id *)
  | Thanks of broker_id * musing_id           (* broker id, musing id *)
  | Too_late of broker_id * musing_id         (* broker id, musing id *)

