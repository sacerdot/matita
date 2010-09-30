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

(* $Id$ *)

open Hbugs_misc;;
open Hbugs_types;;
open Printf;;

exception Client_already_in of client_id;;
exception Client_not_found of client_id;;
exception Musing_already_in of musing_id;;
exception Musing_not_found of musing_id;;
exception Tutor_already_in of tutor_id;;
exception Tutor_not_found of tutor_id;;

class type registry =
  object
    method dump: string
    method purge: unit
  end

let expire_time = 1800. (* 30 minutes *)

class clients =
  object (self)

    inherit ThreadSafe.threadSafe
(*
    (* <DEBUGGING> *)
    method private doCritical: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doWriter: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doReader: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    (* </DEBUGGING> *)
*)

    val timetable: (client_id, float) Hashtbl.t = Hashtbl.create 17
    val urls: (client_id, string) Hashtbl.t = Hashtbl.create 17
    val subscriptions: (client_id, tutor_id list) Hashtbl.t = Hashtbl.create 17

      (** INVARIANT: each client registered has an entry in 'urls' hash table
      _and_ in 'subscriptions hash table even if it hasn't yet invoked
      'subscribe' method *)

    method register id url = self#doWriter (lazy (
      if Hashtbl.mem urls id then
        raise (Client_already_in id)
      else begin
        Hashtbl.add urls id url;
        Hashtbl.add subscriptions id [];
        Hashtbl.add timetable id (Unix.time ())
      end
    ))
    method private remove id =
      Hashtbl.remove urls id;
      Hashtbl.remove subscriptions id;
      Hashtbl.remove timetable id
    method unregister id = self#doWriter (lazy (
      if Hashtbl.mem urls id then
        self#remove id
      else
        raise (Client_not_found id)
    ))
    method isAuthenticated id = self#doReader (lazy (
      Hashtbl.mem urls id
    ))
    method subscribe client_id tutor_ids = self#doWriter (lazy (
      if Hashtbl.mem urls client_id then
        Hashtbl.replace subscriptions client_id tutor_ids
      else
        raise (Client_not_found client_id)
    ))
    method getUrl id = self#doReader (lazy (
      if Hashtbl.mem urls id then
        Hashtbl.find urls id
      else
        raise (Client_not_found id)
    ))
    method getSubscription id = self#doReader (lazy (
      if Hashtbl.mem urls id then
        Hashtbl.find subscriptions id
      else
        raise (Client_not_found id)
    ))

    method dump = self#doReader (lazy (
      "<clients>\n" ^
      (Hashtbl.fold
        (fun id url dump ->
          (dump ^
          (sprintf "<client id=\"%s\" url=\"%s\">\n" id url) ^
          "<subscriptions>\n" ^
          (String.concat "\n" (* id's subscriptions *)
            (List.map
              (fun tutor_id -> sprintf "<tutor id=\"%s\" />\n" tutor_id)
              (Hashtbl.find subscriptions id))) ^
          "</subscriptions>\n</client>\n"))
        urls "") ^
      "</clients>"
    ))
    method purge = self#doWriter (lazy (
      let now = Unix.time () in
      Hashtbl.iter
        (fun id birthday ->
          if now -. birthday > expire_time then
            self#remove id)
        timetable
    ))

  end

class tutors =
  object (self)

    inherit ThreadSafe.threadSafe
(*
    (* <DEBUGGING> *)
    method private doCritical: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doWriter: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doReader: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    (* </DEBUGGING> *)
*)

    val timetable: (tutor_id, float) Hashtbl.t = Hashtbl.create 17
    val tbl: (tutor_id, string * hint_type * string) Hashtbl.t =
      Hashtbl.create 17

    method register id url hint_type dsc = self#doWriter (lazy (
      if Hashtbl.mem tbl id then
        raise (Tutor_already_in id)
      else begin
        Hashtbl.add tbl id (url, hint_type, dsc);
        Hashtbl.add timetable id (Unix.time ())
      end
    ))
    method private remove id =
      Hashtbl.remove tbl id;
      Hashtbl.remove timetable id
    method unregister id = self#doWriter (lazy (
      if Hashtbl.mem tbl id then
        self#remove id
      else
        raise (Tutor_not_found id)
    ))
    method isAuthenticated id = self#doReader (lazy (
      Hashtbl.mem tbl id
    ))
    method exists id = self#doReader (lazy (
      Hashtbl.mem tbl id
    ))
    method getTutor id = self#doReader (lazy (
      if Hashtbl.mem tbl id then
        Hashtbl.find tbl id
      else
        raise (Tutor_not_found id)
    ))
    method getUrl id =
      let (url, _, _) = self#getTutor id in
      url
    method getHintType id =
      let (_, hint_type, _) = self#getTutor id in
      hint_type
    method getDescription id =
      let (_, _, dsc) = self#getTutor id in
      dsc
    method index = self#doReader (lazy (
      Hashtbl.fold
        (fun id (url, hint_type, dsc) idx -> (id, dsc) :: idx) tbl []
    ))

    method dump = self#doReader (lazy (
      "<tutors>\n" ^
      (Hashtbl.fold
        (fun id (url, hint_type, dsc) dump ->
          dump ^
          (sprintf
"<tutor id=\"%s\" url=\"%s\">\n<hint_type>%s</hint_type>\n<description>%s</description>\n</tutor>"
            id url hint_type dsc))
        tbl "") ^
      "</tutors>"
    ))
    method purge = self#doWriter (lazy (
      let now = Unix.time () in
      Hashtbl.iter
        (fun id birthday ->
          if now -. birthday > expire_time then
            self#remove id)
        timetable
    ))

  end

class musings =
  object (self)

    inherit ThreadSafe.threadSafe
(*
    (* <DEBUGGING> *)
    method private doCritical: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doWriter: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    method private doReader: 'a. 'a lazy_t -> 'a = fun act -> Lazy.force act
    (* </DEBUGGING> *)
*)

    val timetable: (musing_id, float) Hashtbl.t = Hashtbl.create 17
    val musings: (musing_id, client_id * tutor_id) Hashtbl.t = Hashtbl.create 17
    val clients: (client_id, musing_id list) Hashtbl.t = Hashtbl.create 17
    val tutors: (tutor_id, musing_id list) Hashtbl.t = Hashtbl.create 17

      (** INVARIANT: each registered musing <musing_id, client_id, tutor_id> has
      an entry in 'musings' table, an entry in 'clients' (i.e. one of the
      musings for client_id is musing_id) table, an entry in 'tutors' table
      (i.e. one of the musings for tutor_id is musing_id) and an entry in
      'timetable' table *)


    method register musing_id client_id tutor_id = self#doWriter (lazy (
      if Hashtbl.mem musings musing_id then
        raise (Musing_already_in musing_id)
      else begin
        Hashtbl.add musings musing_id (client_id, tutor_id);
          (* now add this musing as the first one of musings list for client and
          tutor *)
        Hashtbl.replace clients client_id
          (musing_id ::
            (try Hashtbl.find clients client_id with Not_found -> []));
        Hashtbl.replace tutors tutor_id
          (musing_id ::
            (try Hashtbl.find tutors tutor_id with Not_found -> []));
        Hashtbl.add timetable musing_id (Unix.time ())
      end
    ))
    method private remove id =
        (* ASSUMPTION: this method is invoked under a 'writer' lock *)
      let (client_id, tutor_id) = self#getByMusingId' id in
      Hashtbl.remove musings id;
        (* now remove this musing from the list of musings for client and tutor
        *)
      Hashtbl.replace clients client_id
        (List.filter ((<>) id)
          (try Hashtbl.find clients client_id with Not_found -> []));
      Hashtbl.replace tutors tutor_id
        (List.filter ((<>) id)
          (try Hashtbl.find tutors tutor_id with Not_found -> []));
      Hashtbl.remove timetable id
    method unregister id = self#doWriter (lazy (
      if Hashtbl.mem musings id then
        self#remove id
    ))
    method private getByMusingId' id =
      (* ASSUMPTION: this method is invoked under a 'reader' lock *)
      try
        Hashtbl.find musings id
      with Not_found -> raise (Musing_not_found id)
    method getByMusingId id = self#doReader (lazy (
      self#getByMusingId' id
    ))
    method getByClientId id = self#doReader (lazy (
      try
        Hashtbl.find clients id
      with Not_found -> []
    ))
    method getByTutorId id = self#doReader (lazy (
      try
        Hashtbl.find tutors id
      with Not_found -> []
    ))
    method isActive id = self#doReader (lazy (
      Hashtbl.mem musings id
    ))

    method dump = self#doReader (lazy (
      "<musings>\n" ^
      (Hashtbl.fold
        (fun mid (cid, tid) dump ->
          dump ^
          (sprintf "<musing id=\"%s\" client=\"%s\" tutor=\"%s\" />\n"
            mid cid tid))
        musings "") ^
      "</musings>"
    ))
    method purge = self#doWriter (lazy (
      let now = Unix.time () in
      Hashtbl.iter
        (fun id birthday ->
          if now -. birthday > expire_time then
            self#remove id)
        timetable
    ))

  end

