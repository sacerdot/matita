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

let broker_url = "localhost:49081/act";;
let dump_environment_on_exit = false;;

let init_tutor = Hbugs_id_generator.new_tutor_id;;

  (** register a tutor to broker *)
let register_to_broker id url hint_type dsc =
  try
    let res =
      Hbugs_messages.submit_req
        ~url:broker_url (Register_tutor (id, url, hint_type, dsc))
    in
    (match res with
    | Tutor_registered id ->
        prerr_endline (sprintf "Tutor registered, broker id: %s" id);
        id
    | unexpected_msg ->
        raise (Hbugs_messages.Unexpected_message unexpected_msg))
  with e ->
    failwith (sprintf "Can't register tutor to broker: uncaught exception: %s"
      (Printexc.to_string e))
;;
  (** unregister a tutor from the broker *)
let unregister_from_broker id =
  let res = Hbugs_messages.submit_req ~url:broker_url (Unregister_tutor id) in
  match res with
  | Tutor_unregistered _ -> prerr_endline "Tutor unregistered!"
  | unexpected_msg ->
      failwith
        (sprintf "Can't unregister from broker, received unexpected msg: %s"
          (Hbugs_messages.string_of_msg unexpected_msg))
;;

  (* typecheck a loaded proof *)
  (* TODO this is a cut and paste from gTopLevel.ml *)
let typecheck_loaded_proof metasenv bo ty =
 let module T = CicTypeChecker in
  ignore (
   List.fold_left
    (fun metasenv ((_,context,ty) as conj) ->
      ignore (T.type_of_aux' metasenv context ty) ;
      metasenv @ [conj]
    ) [] metasenv) ;
  ignore (T.type_of_aux' metasenv [] ty) ;
  ignore (T.type_of_aux' metasenv [] bo)
;;

type xml_kind = Body | Type;;
let mk_dtdname ~ask_dtd_to_the_getter dtd =
 if ask_dtd_to_the_getter then
  Helm_registry.get "getter.url" ^ "getdtd?uri=" ^ dtd
 else
  "http://mowgli.cs.unibo.it/dtd/" ^ dtd
;;  
  (** this function must be the inverse function of GTopLevel.strip_xml_headings
  *)
let add_xml_headings ~kind s =
  let dtdname = mk_dtdname ~ask_dtd_to_the_getter:true "cic.dtd" in
  let root =
    match kind with
    | Body -> "CurrentProof"
    | Type -> "ConstantType"
  in
  "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n\n" ^
  "<!DOCTYPE " ^ root ^ " SYSTEM \""^ dtdname ^ "\">\n\n" ^
  s
;;

let load_state (type_string, body_string, goal) =
  prerr_endline "a0";
  let ((tmp1, oc1), (tmp2, oc2)) =
    (Filename.open_temp_file "" "", Filename.open_temp_file "" "")
  in
  prerr_endline "a1";
  output_string oc1 (add_xml_headings ~kind:Type type_string);
  output_string oc2 (add_xml_headings ~kind:Body body_string);
  close_out oc1; close_out oc2;
  prerr_endline (sprintf "Proof Type available in %s" tmp1);
  prerr_endline (sprintf "Proof Body available in %s" tmp2);
  let (proof, goal) =
    prerr_endline "a2";
    (match CicParser.obj_of_xml tmp1 (Some tmp2) with
    | Cic.CurrentProof (_,metasenv,bo,ty,attrs) ->  (* TODO il primo argomento e' una URI valida o e' casuale? *)
        prerr_endline "a3";
        let uri = UriManager.uri_of_string "cic:/foo.con" in
        prerr_endline "a4";
        typecheck_loaded_proof metasenv bo ty;
        prerr_endline "a5";
        ((uri, metasenv, bo, ty, attrs), goal)
    | _ -> assert false)
  in
  prerr_endline "a6";
  Sys.remove tmp1; Sys.remove tmp2;
  (proof, goal)

(* tutors creation stuff from now on *)

module type HbugsTutor =
  sig
    val start: unit -> unit
  end

module type HbugsTutorDescription =
  sig
    val addr: string
    val port: int
    val tactic: ProofEngineTypes.tactic
    val hint: hint
    val hint_type: hint_type
    val description: string
    val environment_file: string
  end

module BuildTutor (Dsc: HbugsTutorDescription) : HbugsTutor =
  struct
    let broker_id = ref None
    let my_own_id = init_tutor ()
    let my_own_addr, my_own_port = Dsc.addr, Dsc.port
    let my_own_url = sprintf "%s:%d" my_own_addr my_own_port

    let is_authenticated id =
      match !broker_id with
      | None -> false
      | Some broker_id -> id = broker_id

      (* thread who do the dirty work *)
    let slave (state, musing_id) =
      prerr_endline (sprintf "Hi, I'm the slave for musing %s" musing_id);
      let (proof, goal) = load_state state in
      let success =
        try
          ignore (Dsc.tactic (proof, goal));
          true
        with e -> false
      in
      let answer = 
        Musing_completed
          (my_own_id, musing_id, (if success then Eureka Dsc.hint else Sorry))
      in
      ignore (Hbugs_messages.submit_req ~url:broker_url answer);
      prerr_endline
        (sprintf "Bye, I've completed my duties (success = %b)" success)

    let hbugs_callback =
        (* hashtbl mapping musings ids to PID of threads doing the related (dirty)
        work *)
      let slaves = Hashtbl.create 17 in
      let forbidden () =
        prerr_endline "ignoring request from unauthorized broker";
        Exception ("forbidden", "")
      in
      function  (* _the_ callback *)
      | Start_musing (broker_id, state) ->
          if is_authenticated broker_id then begin
            prerr_endline "received Start_musing";
            let new_musing_id = Hbugs_id_generator.new_musing_id () in
            prerr_endline
              (sprintf "starting a new musing (id = %s)" new_musing_id);
(*             let slave_thread = Thread.create slave (state, new_musing_id) in *)
            let slave_thread =
              ExtThread.create slave (state, new_musing_id)
            in
            Hashtbl.add slaves new_musing_id slave_thread;
            Musing_started (my_own_id, new_musing_id)
          end else  (* broker unauthorized *)
            forbidden ();
      | Abort_musing (broker_id, musing_id) ->
          if is_authenticated broker_id then begin
            (try  (* kill thread responsible for "musing_id" *)
              let slave_thread = Hashtbl.find slaves musing_id in
              ExtThread.kill slave_thread;
              Hashtbl.remove slaves musing_id
            with
            | ExtThread.Can_t_kill (_, reason) ->
                prerr_endline (sprintf "Unable to kill slave: %s" reason)
            | Not_found ->
                prerr_endline (sprintf
                  "Can't find slave corresponding to musing %s, can't kill it"
                  musing_id));
            Musing_aborted (my_own_id, musing_id)
          end else (* broker unauthorized *)
            forbidden ();
      | unexpected_msg ->
          Exception ("unexpected_msg",
            Hbugs_messages.string_of_msg unexpected_msg)

    let callback (req: Http_types.request) outchan =
      try
        let req_msg = Hbugs_messages.msg_of_string req#body in
        let answer = hbugs_callback req_msg in
        Http_daemon.respond ~body:(Hbugs_messages.string_of_msg answer) outchan
      with Hbugs_messages.Parse_error (subj, reason) ->
        Http_daemon.respond
          ~body:(Hbugs_messages.string_of_msg
            (Exception ("parse_error", reason)))
          outchan

    let restore_environment () =
      let ic = open_in Dsc.environment_file in
      prerr_endline "Restoring environment ...";
      CicEnvironment.restore_from_channel
        ~callback:(fun uri -> prerr_endline uri) ic;
      prerr_endline "... done!";
      close_in ic

    let dump_environment () =
      let oc = open_out Dsc.environment_file in
      prerr_endline "Dumping environment ...";
      CicEnvironment.dump_to_channel
        ~callback:(fun uri -> prerr_endline uri) oc;
      prerr_endline "... done!";
      close_out oc

    let main () =
      try
        Sys.catch_break true;
        at_exit (fun () ->
          if dump_environment_on_exit then
            dump_environment ();
          unregister_from_broker my_own_id);
        broker_id :=
          Some (register_to_broker
            my_own_id my_own_url Dsc.hint_type Dsc.description);
        if Sys.file_exists Dsc.environment_file then
          restore_environment ();
        Http_daemon.start'
          ~addr:my_own_addr ~port:my_own_port ~mode:`Thread callback
      with Sys.Break -> ()  (* exit nicely, invoking at_exit functions *)

    let start = main

  end

