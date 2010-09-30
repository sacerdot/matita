(* $Id$ *)

open Hbugs_types;;
open Printf;;

exception Empty_must;;

module MQI  = MQueryInterpreter
module MQIC = MQIConn

let broker_id = ref None
let my_own_id = Hbugs_tutors.init_tutor ()
let my_own_addr, my_own_port = "127.0.0.1", 50011
let my_own_url = sprintf "%s:%d" my_own_addr my_own_port
let environment_file = "search_pattern_apply.environment"
let dump_environment_on_exit = false

let is_authenticated id =
  match !broker_id with
  | None -> false
  | Some broker_id -> id = broker_id

  (* thread who do the dirty work *)
let slave mqi_handle (state, musing_id) =
 try
  prerr_endline (sprintf "Hi, I'm the slave for musing %s" musing_id);
  let (proof, goal) = Hbugs_tutors.load_state state in
  let hint =
    try
      let choose_must must only = (* euristic: use 2nd precision level
                                  1st is more precise but is more slow *)
        match must with
        | [] -> raise Empty_must
        | _::hd::tl -> hd
        | hd::tl -> hd
      in
      let uris =
        TacticChaser.matchConclusion mqi_handle
         ~output_html:prerr_endline ~choose_must () ~status:(proof, goal)
      in
      if uris = [] then
        Sorry
      else
        Eureka (Hints (List.map (fun uri -> Use_apply uri) uris))
    with Empty_must -> Sorry
  in
  let answer = Musing_completed (my_own_id, musing_id, hint) in
  ignore (Hbugs_messages.submit_req ~url:Hbugs_tutors.broker_url answer);
  prerr_endline
    (sprintf "Bye, I've completed my duties (success = %b)" (hint <> Sorry))
 with
  (Pxp_types.At _) as e ->
    let rec unbox_exception =
     function
         Pxp_types.At (_,e) -> unbox_exception e
      | e -> e
    in
     prerr_endline ("Uncaught PXP exception: " ^ Pxp_types.string_of_exn e) ;
     (* e could be the Thread.exit exception; otherwise we will release an  *)
     (* uncaught exception and the Pxp_types.At was already an uncaught     *)
     (* exception ==> no additional arm                                     *)
     raise (unbox_exception e)

let hbugs_callback mqi_handle =
  let ids = Hashtbl.create 17 in
  let forbidden () =
    prerr_endline "ignoring request from unauthorized broker";
    Exception ("forbidden", "")
  in
  function
  | Start_musing (broker_id, state) ->
      if is_authenticated broker_id then begin
        prerr_endline "received Start_musing";
        let new_musing_id = Hbugs_id_generator.new_musing_id () in
        let id = ExtThread.create (slave mqi_handle) (state, new_musing_id) in
        prerr_endline (sprintf "starting a new musing (id = %s)" new_musing_id);
        Hashtbl.add ids new_musing_id id;
        (*ignore (Thread.create slave (state, new_musing_id));*)
        Musing_started (my_own_id, new_musing_id)
      end else  (* broker unauthorized *)
        forbidden ();
  | Abort_musing (broker_id, musing_id) ->
      prerr_endline "CSC: Abort_musing received" ;
      if is_authenticated broker_id then begin
        (* prerr_endline "Ignoring 'Abort_musing' message ..."; *)
        (try
          ExtThread.kill (Hashtbl.find ids musing_id) ;
          Hashtbl.remove ids musing_id ;
         with
            Not_found
          | ExtThread.Can_t_kill _ ->
             prerr_endline ("Can not kill slave " ^ musing_id)) ;
        Musing_aborted (my_own_id, musing_id)
      end else (* broker unauthorized *)
        forbidden ();
  | unexpected_msg ->
      Exception ("unexpected_msg",
        Hbugs_messages.string_of_msg unexpected_msg)

let callback mqi_handle (req: Http_types.request) outchan =
  try
    let req_msg = Hbugs_messages.msg_of_string req#body in
    let answer = hbugs_callback mqi_handle req_msg in
    Http_daemon.respond ~body:(Hbugs_messages.string_of_msg answer) outchan
  with Hbugs_messages.Parse_error (subj, reason) ->
    Http_daemon.respond
      ~body:(Hbugs_messages.string_of_msg
        (Exception ("parse_error", reason)))
      outchan

let restore_environment () =
  let ic = open_in environment_file in
  prerr_endline "Restoring environment ...";
  CicEnvironment.restore_from_channel
    ~callback:(fun uri -> prerr_endline uri) ic;
  prerr_endline "... done!";
  close_in ic

let dump_environment () =
  let oc = open_out environment_file in
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
      Hbugs_tutors.unregister_from_broker my_own_id);
    broker_id :=
      Some (Hbugs_tutors.register_to_broker
        my_own_id my_own_url "FOO" "Search_pattern_apply tutor");
    let mqi_handle = MQIC.init ~log:prerr_string () in 
    if Sys.file_exists environment_file then
      restore_environment ();
    Http_daemon.start'
      ~addr:my_own_addr ~port:my_own_port ~mode:`Thread (callback mqi_handle);
    MQIC.close mqi_handle
  with Sys.Break -> ()  (* exit nicely, invoking at_exit functions *)
;;

main ()

