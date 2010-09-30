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

open Hbugs_types;;
open Printf;;

let debug = true ;;
let debug_print s = if debug then prerr_endline (Lazy.force s) ;;

let daemon_name = "H-Bugs Broker" ;;
let default_port = 49081 ;;
let port_env_var = "HELM_HBUGS_BROKER_PORT" ;;
let port =
  try
    int_of_string (Sys.getenv port_env_var)
  with
  | Not_found -> default_port
  | Failure "int_of_string" ->
      prerr_endline "Warning: invalid port, reverting to default";
      default_port
;;
let usage_string = "HBugs Broker: usage string not yet written :-(";;

exception Unexpected_msg of message;;

let return_xml_msg body outchan =
  Http_daemon.respond ~headers:["Content-Type", "text/xml"] ~body outchan
;;
let parse_musing_id = function
  | Musing_started (_, musing_id) ->
	prerr_endline ("#### Started musing ID: " ^ musing_id);
	musing_id
  | Musing_aborted (_, musing_id) -> musing_id
  | msg ->
      prerr_endline (sprintf "Assertion failed, received msg: %s"
        (Hbugs_messages.string_of_msg msg));
      assert false
;;

let do_critical =
  let mutex = Mutex.create () in
  fun action ->
    try
(*       debug_print (lazy "Acquiring lock ..."); *)
      Mutex.lock mutex;
(*       debug_print (lazy "Lock Acquired!"); *)
      let res = Lazy.force action in
(*       debug_print (lazy "Releaseing lock ..."); *)
      Mutex.unlock mutex;
(*       debug_print (lazy "Lock released!"); *)
      res
    with e -> Mutex.unlock mutex; raise e
;;

  (* registries *)
let clients = new Hbugs_broker_registry.clients in
let tutors = new Hbugs_broker_registry.tutors in
let musings = new Hbugs_broker_registry.musings in
let registries =
  [ (clients :> Hbugs_broker_registry.registry);
    (tutors :> Hbugs_broker_registry.registry);
    (musings :> Hbugs_broker_registry.registry) ]
in

let my_own_id = Hbugs_id_generator.new_broker_id () in

  (* debugging: dump broker internal status, used by '/dump' method *)
let dump_registries () =
  assert debug;
  String.concat "\n" (List.map (fun o -> o#dump) registries)
in

let handle_msg outchan msg =
  (* messages from clients *)
  (match msg with

  | Help ->
      Hbugs_messages.respond_msg (Usage usage_string) outchan
  | Register_client (client_id, client_url) -> do_critical (lazy (
      try
        clients#register client_id client_url;
        Hbugs_messages.respond_msg (Client_registered my_own_id) outchan
      with Hbugs_broker_registry.Client_already_in id ->
        Hbugs_messages.respond_exc "already_registered" id outchan
    ))
  | Unregister_client client_id -> do_critical (lazy (
      if clients#isAuthenticated client_id then begin
        clients#unregister client_id;
        Hbugs_messages.respond_msg (Client_unregistered my_own_id) outchan
      end else
        Hbugs_messages.respond_exc "forbidden" client_id outchan
    ))
  | List_tutors client_id -> do_critical (lazy (
      if clients#isAuthenticated client_id then begin
        Hbugs_messages.respond_msg
          (Tutor_list (my_own_id, tutors#index))
          outchan
      end else
        Hbugs_messages.respond_exc "forbidden" client_id outchan
    ))
  | Subscribe (client_id, tutor_ids) -> do_critical (lazy (
      if clients#isAuthenticated client_id then begin
        if List.length tutor_ids <> 0 then begin  (* at least one tutor id *)
          if List.for_all tutors#exists tutor_ids then begin
            clients#subscribe client_id tutor_ids;
            Hbugs_messages.respond_msg
              (Subscribed (my_own_id, tutor_ids)) outchan
          end else  (* required subscription to at least one unexistent tutor *)
            let missing_tutors =
              List.filter (fun id -> not (tutors#exists id)) tutor_ids
            in
            Hbugs_messages.respond_exc
              "tutor_not_found" (String.concat " " missing_tutors) outchan
        end else  (* no tutor id specified *)
          Hbugs_messages.respond_exc "no_tutor_specified" "" outchan
      end else
        Hbugs_messages.respond_exc "forbidden" client_id outchan
    ))
  | State_change (client_id, new_state) -> do_critical (lazy (
      if clients#isAuthenticated client_id then begin
        let active_musings = musings#getByClientId client_id in
        prerr_endline (sprintf "ACTIVE MUSINGS: %s" (String.concat ", " active_musings));
        if List.length active_musings = 0 then
          prerr_endline ("No active musings for client " ^ client_id);
        prerr_endline "CSC: State change!!!" ;
        let stop_answers =
          List.map  (* collect Abort_musing message's responses *)
            (fun id ->  (* musing id *)
              let tutor = snd (musings#getByMusingId id) in
              Hbugs_messages.submit_req
                ~url:(tutors#getUrl tutor) (Abort_musing (my_own_id, id)))
            active_musings
        in
				let stopped_musing_ids = List.map parse_musing_id stop_answers in
        List.iter musings#unregister active_musings;
				(match new_state with
				| Some new_state ->	(* need to start new musings *)
					let subscriptions = clients#getSubscription client_id in
					if List.length subscriptions = 0 then
						prerr_endline ("No subscriptions for client " ^ client_id);
					let started_musing_ids =
						List.map  (* register new musings and collect their ids *)
							(fun tutor_id ->
								let res =
									Hbugs_messages.submit_req
										~url:(tutors#getUrl tutor_id)
										(Start_musing (my_own_id, new_state))
								in
								let musing_id = parse_musing_id res in
								musings#register musing_id client_id tutor_id;
								musing_id)
							subscriptions
					in
					Hbugs_messages.respond_msg
						(State_accepted (my_own_id, stopped_musing_ids, started_musing_ids))
						outchan
				| None ->	(* no need to start new musings *)
						Hbugs_messages.respond_msg
							(State_accepted (my_own_id, stopped_musing_ids, []))
							outchan)
      end else
        Hbugs_messages.respond_exc "forbidden" client_id outchan
    ))

  (* messages from tutors *)

  | Register_tutor (tutor_id, tutor_url, hint_type, dsc) -> do_critical (lazy (
      try
        tutors#register tutor_id tutor_url hint_type dsc;
        Hbugs_messages.respond_msg (Tutor_registered my_own_id) outchan
      with Hbugs_broker_registry.Tutor_already_in id ->
        Hbugs_messages.respond_exc "already_registered" id outchan
    ))
  | Unregister_tutor tutor_id -> do_critical (lazy (
      if tutors#isAuthenticated tutor_id then begin
        tutors#unregister tutor_id;
        Hbugs_messages.respond_msg (Tutor_unregistered my_own_id) outchan
      end else
        Hbugs_messages.respond_exc "forbidden" tutor_id outchan
    ))

  | Musing_completed (tutor_id, musing_id, result) -> do_critical (lazy (
      if not (tutors#isAuthenticated tutor_id) then begin (* unauthorized *)
        Hbugs_messages.respond_exc "forbidden" tutor_id outchan;
      end else if not (musings#isActive musing_id) then begin (* too late *)
        Hbugs_messages.respond_msg (Too_late (my_own_id, musing_id)) outchan;
      end else begin  (* all is ok: autorhized and on time *)
        (match result with
        | Sorry -> ()
        | Eureka hint ->
            let client_url =
              clients#getUrl (fst (musings#getByMusingId musing_id))
            in
            let res =
              Hbugs_messages.submit_req ~url:client_url (Hint (my_own_id, hint))
            in
            (match res with
            | Wow _ -> () (* ok: client is happy with our hint *)
            | unexpected_msg ->
                prerr_endline
                  (sprintf
                    "Warning: unexpected msg from client: %s\nExpected was: Wow"
                    (Hbugs_messages.string_of_msg msg))));
        Hbugs_messages.respond_msg (Thanks (my_own_id, musing_id)) outchan;
        musings#unregister musing_id
      end
    ))

  | msg ->  (* unexpected message *)
      debug_print (lazy "Unknown message!");
      Hbugs_messages.respond_exc
        "unexpected_msg" (Hbugs_messages.string_of_msg msg) outchan)
in
(*  (* DEBUGGING wrapper around 'handle_msg' *)
let handle_msg outchan =
  if debug then
    (fun msg -> (* filter handle_msg through a function which dumps input
                messages *)
      debug_print (lazy (Hbugs_messages.string_of_msg msg));
      handle_msg outchan msg)
  else
    handle_msg outchan
in
*)

  (* thread action *)
let callback (req: Http_types.request) outchan =
  try
    debug_print (lazy ("Connection from " ^ req#clientAddr));
    debug_print (lazy ("Received request: " ^ req#path));
    (match req#path with
      (* TODO write help message *)
    | "/help" -> return_xml_msg "<help> not yet written </help>" outchan
    | "/act" ->
        let msg = Hbugs_messages.msg_of_string req#body in
        handle_msg outchan msg
    | "/dump" ->
        if debug then
          Http_daemon.respond ~body:(dump_registries ()) outchan
        else
          Http_daemon.respond_error ~code:400 outchan
    | _ -> Http_daemon.respond_error ~code:400 outchan);
    debug_print (lazy "Done!\n")
  with
  | Http_types.Param_not_found attr_name ->
      Hbugs_messages.respond_exc "missing_parameter" attr_name outchan
  | exc ->
      Hbugs_messages.respond_exc
        "uncaught_exception" (Printexc.to_string exc) outchan
in

  (* thread who cleans up ancient client/tutor/musing registrations *)
let ragman () =
  let delay = 3600.0 in (* 1 hour delay *)
  while true do
    Thread.delay delay;
    List.iter (fun o -> o#purge) registries
  done
in

  (* start daemon *)
printf "Listening on port %d ...\n" port;
flush stdout;
ignore (Thread.create ragman ());
Http_daemon.start' ~port ~mode:`Thread callback

