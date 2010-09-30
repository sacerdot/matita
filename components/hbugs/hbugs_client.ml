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

open Hbugs_common;;
open Hbugs_types;;
open Printf;;

exception Invalid_URL of string;;

let do_nothing _ = ();;

module SmartHbugs_client_gui =
 struct
  class ['a] oneColumnCList gtree_view ~column_type ~column_title
  =
   let obj =
    ((Gobject.unsafe_cast gtree_view#as_widget) : Gtk.tree_view Gtk.obj) in
   let columns = new GTree.column_list in
   let col = columns#add column_type in
   let vcol = GTree.view_column ~title:column_title ()
    ~renderer:(GTree.cell_renderer_text[], ["text",col]) in
   let store = GTree.list_store columns in
   object(self)
    inherit GTree.view obj
    method clear = store#clear
    method append (v : 'a) =
     let row = store#append () in
      store#set ~row ~column:col v;
    method column = col
    initializer
     self#set_model (Some (store :> GTree.model)) ;
     ignore (self#append_column vcol)
   end

  class ['a,'b] twoColumnsCList gtree_view ~column1_type ~column2_type
   ~column1_title ~column2_title
  =
   let obj =
    ((Gobject.unsafe_cast gtree_view#as_widget) : Gtk.tree_view Gtk.obj) in
   let columns = new GTree.column_list in
   let col1 = columns#add column1_type in
   let vcol1 = GTree.view_column ~title:column1_title ()
    ~renderer:(GTree.cell_renderer_text[], ["text",col1]) in
   let col2 = columns#add column2_type in
   let vcol2 = GTree.view_column ~title:column2_title ()
    ~renderer:(GTree.cell_renderer_text[], ["text",col2]) in
   let store = GTree.list_store columns in
   object(self)
    inherit GTree.view obj
    method clear = store#clear
    method append (v1 : 'a) (v2 : 'b) =
     let row = store#append () in
      store#set ~row ~column:col1 v1;
      store#set ~row ~column:col2 v2
    method column1 = col1
    method column2 = col2
    initializer
     self#set_model (Some (store :> GTree.model)) ;
     ignore (self#append_column vcol1) ;
     ignore (self#append_column vcol2) ;
   end

  class subscribeWindow () =
   object(self)
    inherit Hbugs_client_gui.subscribeWindow ()
    val mutable tutorsSmartCList = None
    method tutorsSmartCList =
     match tutorsSmartCList with
        None -> assert false
      | Some w -> w
    initializer
     tutorsSmartCList <-
      Some
       (new twoColumnsCList self#tutorsCList
         ~column1_type:Gobject.Data.string ~column2_type:Gobject.Data.string
         ~column1_title:"Id" ~column2_title:"Description")
   end

  class hbugsMainWindow () =
   object(self)
    inherit Hbugs_client_gui.hbugsMainWindow ()
    val mutable subscriptionSmartCList = None
    val mutable hintsSmartCList = None
    method subscriptionSmartCList =
     match subscriptionSmartCList with
        None -> assert false
      | Some w -> w
    method hintsSmartCList =
     match hintsSmartCList with
        None -> assert false
      | Some w -> w
    initializer
     subscriptionSmartCList <-
      Some
       (new oneColumnCList self#subscriptionCList
         ~column_type:Gobject.Data.string ~column_title:"Description")
    initializer
     hintsSmartCList <-
      Some
       (new oneColumnCList self#hintsCList
         ~column_type:Gobject.Data.string ~column_title:"Description")
   end

 end
;;

class hbugsClient
  ?(use_hint_callback: hint -> unit = do_nothing)
  ?(describe_hint_callback: hint -> unit = do_nothing)
  ?(destroy_callback: unit -> unit = do_nothing)
  ()
  =

  let http_url_RE = Pcre.regexp "^(http://)?(.*):(\\d+)" in
  let port_of_http_url url =
    try
      let subs = Pcre.extract ~rex:http_url_RE url in
      int_of_string subs.(3)
    with e -> raise (Invalid_URL url)
  in

  object (self)

    val mainWindow = new SmartHbugs_client_gui.hbugsMainWindow ()
    val subscribeWindow = new SmartHbugs_client_gui.subscribeWindow ()
    val messageDialog = new Hbugs_client_gui.messageDialog ()
    val myOwnId = Hbugs_id_generator.new_client_id ()
    val mutable use_hint_callback = use_hint_callback
    val mutable myOwnUrl = "localhost:49082"
    val mutable brokerUrl = "localhost:49081"
    val mutable brokerId: broker_id option = None
      (* all available tutors, saved last time a List_tutors message was sent to
      broker *)
    val mutable availableTutors: tutor_dsc list = []
    val mutable statusContext = None
    val mutable subscribeWindowStatusContext = None
    val mutable debug = false (* enable/disable debugging buttons *)
    val mutable hints = []  (* actually available hints *)

    initializer
      self#initGui;
      self#startLocalHttpDaemon ();
      self#testLocalHttpDaemon ();
      self#testBroker ();
      self#registerToBroker ();
      self#reconfigDebuggingButtons

    method show = mainWindow#hbugsMainWindow#show
    method hide = mainWindow#hbugsMainWindow#misc#hide

    method setUseHintCallback callback =
     use_hint_callback <- callback

    method private debugButtons =
      List.map
        (fun (b: GButton.button) -> new GObj.misc_ops b#as_widget)
        [ mainWindow#startLocalHttpDaemonButton;
        mainWindow#testLocalHttpDaemonButton; mainWindow#testBrokerButton ]

    method private initGui =

        (* GUI: main window *)

          (* ignore delete events so that hbugs window is closable only using
          menu; on destroy (e.g. while quitting gTopLevel) self#quit is invoked
          *)

      ignore (mainWindow#hbugsMainWindow#event#connect#delete (fun _ -> true));
      ignore (mainWindow#hbugsMainWindow#event#connect#destroy
        (fun _ -> self#quit (); false));

        (* GUI main window's menu *)
      mainWindow#toggleDebuggingMenuItem#set_active debug;
      ignore (mainWindow#toggleDebuggingMenuItem#connect#toggled
        self#toggleDebug);

        (* GUI: local HTTP daemon settings *)
      ignore (mainWindow#clientUrlEntry#connect#changed
        (fun _ -> myOwnUrl <- mainWindow#clientUrlEntry#text));
      mainWindow#clientUrlEntry#set_text myOwnUrl;
      ignore (mainWindow#startLocalHttpDaemonButton#connect#clicked
        self#startLocalHttpDaemon);
      ignore (mainWindow#testLocalHttpDaemonButton#connect#clicked
        self#testLocalHttpDaemon);

        (* GUI: broker choice *)
      ignore (mainWindow#brokerUrlEntry#connect#changed
        (fun _ -> brokerUrl <- mainWindow#brokerUrlEntry#text));
      mainWindow#brokerUrlEntry#set_text brokerUrl;
      ignore (mainWindow#testBrokerButton#connect#clicked self#testBroker);
      mainWindow#clientIdLabel#set_text myOwnId;

        (* GUI: client registration *)
      ignore (mainWindow#registerClientButton#connect#clicked
        self#registerToBroker);

        (* GUI: subscriptions *)
      ignore (mainWindow#showSubscriptionWindowButton#connect#clicked
        (fun () ->
          self#listTutors ();
          subscribeWindow#subscribeWindow#show ()));

      let get_selected_row_index () =
       match mainWindow#hintsCList#selection#get_selected_rows with
          [path] ->
            (match GTree.Path.get_indices path with
                [|n|] -> n
              | _ -> assert false)
        | _ -> assert false
      in
        (* GUI: hints list *)
      ignore (
       let event_ops = new GObj.event_ops mainWindow#hintsCList#as_widget in
        event_ops#connect#button_press
         (fun event ->
           if GdkEvent.get_type event = `TWO_BUTTON_PRESS then
            use_hint_callback (self#hint (get_selected_row_index ())) ;
           false));

      ignore (mainWindow#hintsCList#selection#connect#changed
       (fun () ->
         describe_hint_callback (self#hint (get_selected_row_index ())))) ;

        (* GUI: main status bar *)
      let ctxt = mainWindow#mainWindowStatusBar#new_context "0" in
      statusContext <- Some ctxt;
      ignore (ctxt#push "Ready");

        (* GUI: subscription window *)
      subscribeWindow#tutorsCList#selection#set_mode `MULTIPLE;
      ignore (subscribeWindow#subscribeWindow#event#connect#delete
        (fun _ -> subscribeWindow#subscribeWindow#misc#hide (); true));
      ignore (subscribeWindow#listTutorsButton#connect#clicked self#listTutors);
      ignore (subscribeWindow#subscribeButton#connect#clicked
        self#subscribeSelected);
      ignore (subscribeWindow#subscribeAllButton#connect#clicked
        self#subscribeAll);
      (subscribeWindow#tutorsCList#get_column 0)#set_visible false;
      let ctxt = subscribeWindow#subscribeWindowStatusBar#new_context "0" in
      subscribeWindowStatusContext <- Some ctxt;
      ignore (ctxt#push "Ready");

        (* GUI: message dialog *)
      ignore (messageDialog#messageDialog#event#connect#delete
        (fun _ -> messageDialog#messageDialog#misc#hide (); true));
      ignore (messageDialog#okDialogButton#connect#clicked
        (fun _ -> messageDialog#messageDialog#misc#hide ()))

    (* accessory methods *)

      (** pop up a (modal) dialog window showing msg to the user *)
    method private showDialog msg =
      messageDialog#dialogLabel#set_text msg;
      messageDialog#messageDialog#show ()
      (** use showDialog to display an hbugs message to the user *)
    method private showMsgInDialog msg =
      self#showDialog (Hbugs_messages.string_of_msg msg)

      (** create a new thread which sends msg to broker, wait for an answer and
      invoke callback passing response message as argument *)
    method private sendReq ?(wait = false) ~msg callback =
      let thread () =
        try
          callback (Hbugs_messages.submit_req ~url:(brokerUrl ^ "/act") msg)
        with 
        | (Hbugs_messages.Parse_error (subj, reason)) as e ->
            self#showDialog
              (sprintf
"Parse_error, unable to fullfill request. Details follow.
Request: %s
Error: %s"
                (Hbugs_messages.string_of_msg msg) (Printexc.to_string e));
        | (Unix.Unix_error _) as e ->
            self#showDialog
              (sprintf
"Can't connect to HBugs Broker
Url: %s
Error: %s"
                brokerUrl (Printexc.to_string e))
        | e ->
            self#showDialog
              (sprintf "hbugsClient#sendReq: Uncaught exception: %s"
                (Printexc.to_string e))
      in
      let th = Thread.create thread () in
      if wait then
        Thread.join th
      else ()

      (** check if a broker is authenticated using its broker_id
      [ Background: during client registration, client save broker_id of its
      broker, further messages from broker are accepted only if they carry the
      same broker id ] *)
    method private isAuthenticated id =
      match brokerId with
      | None -> false
      | Some broker_id -> (id = broker_id)

    (* actions *)

    method private startLocalHttpDaemon =
        (* flatten an hint tree to an hint list *)
      let rec flatten_hint = function
        | Hints hints -> List.concat (List.map flatten_hint hints)
        | hint -> [hint]
      in
      fun () ->
      let callback req outchan =
        try
          (match Hbugs_messages.msg_of_string req#body with
          | Help ->
              Hbugs_messages.respond_msg
                (Usage "Local Http Daemon up and running!") outchan
          | Hint (broker_id, hint) ->
              if self#isAuthenticated broker_id then begin
                let received_hints = flatten_hint hint in
                List.iter
                  (fun h ->
                    (match h with Hints _ -> assert false | _ -> ());
                    ignore(mainWindow#hintsSmartCList#append(string_of_hint h)))
                  received_hints;
                hints <- hints @ received_hints;
                Hbugs_messages.respond_msg (Wow myOwnId) outchan
              end else  (* msg from unauthorized broker *)
                Hbugs_messages.respond_exc "forbidden" broker_id outchan
          | msg ->
              Hbugs_messages.respond_exc
                "unexpected_msg" (Hbugs_messages.string_of_msg msg) outchan)
        with (Hbugs_messages.Parse_error _) as e ->
          Hbugs_messages.respond_exc
            "parse_error" (Printexc.to_string e) outchan
      in
      let addr = "0.0.0.0" in (* TODO actually user specified "My URL" is used
                              only as a value to be sent to broker, local HTTP
                              daemon will listen on "0.0.0.0", port is parsed
                              from My URL though *)
      let httpDaemonThread () =
        try
          Http_daemon.start'
            ~addr ~port:(port_of_http_url myOwnUrl) ~mode:`Single callback
        with
        | Invalid_URL url -> self#showDialog (sprintf "Invalid URL: \"%s\"" url)
        | e ->
            self#showDialog (sprintf "Can't start local HTTP daemon: %s"
              (Printexc.to_string e))
      in
      ignore (Thread.create httpDaemonThread ())

    method private testLocalHttpDaemon () =
      try
        let msg =
          Hbugs_misc.http_post ~body:(Hbugs_messages.string_of_msg Help)
            myOwnUrl
        in
        ignore msg
(*         self#showDialog msg *)
      with
      | Hbugs_misc.Malformed_URL url ->
          self#showDialog
            (sprintf
              "Handshake with local HTTP daemon failed, Invalid URL: \"%s\""
              url)
      | Hbugs_misc.Malformed_HTTP_response res ->
          self#showDialog
            (sprintf
    "Handshake with local HTTP daemon failed, can't parse HTTP response: \"%s\""
              res)
      | (Unix.Unix_error _) as e ->
          self#showDialog
            (sprintf
              "Handshake with local HTTP daemon failed, can't connect: \"%s\""
              (Printexc.to_string e))

    method private testBroker () =
      self#sendReq ~msg:Help
        (function
          | Usage _ -> ()
          | unexpected_msg ->
              self#showDialog
                (sprintf
                  "Handshake with HBugs Broker failed, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))

    method registerToBroker () =
      (match brokerId with  (* undo previous registration, if any *)
      | Some id -> self#unregisterFromBroker ()
      | _ -> ());
      self#sendReq ~msg:(Register_client (myOwnId, myOwnUrl))
        (function
          | Client_registered broker_id -> (brokerId <- Some broker_id)
          | unexpected_msg ->
              self#showDialog
                (sprintf "Client NOT registered, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))

    method unregisterFromBroker () =
      self#sendReq ~wait:true ~msg:(Unregister_client myOwnId)
        (function
          | Client_unregistered _ -> (brokerId <- None)
          | unexpected_msg -> ())
(*
              self#showDialog
                (sprintf "Client NOT unregistered, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))
*)

    method stateChange new_state =
      mainWindow#hintsSmartCList#clear ();
      hints <- [];
      self#sendReq
        ~msg:(State_change (myOwnId, new_state))
        (function
          | State_accepted _ -> ()
          | unexpected_msg ->
              self#showDialog
                (sprintf "State NOT accepted by Hbugs, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))

    method hint = List.nth hints

    method private listTutors () =
        (* wait is set to true just to make sure that after invoking listTutors
        "availableTutors" is correctly filled *)
      self#sendReq ~wait:true ~msg:(List_tutors myOwnId)
        (function
          | Tutor_list (_, descriptions) ->
              availableTutors <-  (* sort accordingly to tutor description *)
                List.sort (fun (a,b) (c,d) -> compare (b,a) (d,c)) descriptions;
              subscribeWindow#tutorsSmartCList#clear ();
              List.iter
                (fun (id, dsc) ->
                  ignore (subscribeWindow#tutorsSmartCList#append id dsc))
                availableTutors
          | unexpected_msg ->
              self#showDialog
                (sprintf "Can't list tutors, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))

      (* low level used by subscribeSelected and subscribeAll *)
    method private subscribe' tutors_id =
      self#sendReq ~msg:(Subscribe (myOwnId, tutors_id))
        (function
          | (Subscribed (_, subscribedTutors)) as msg ->
              let sort = List.sort compare in
              mainWindow#subscriptionSmartCList#clear ();
              List.iter
                (fun tutor_id ->
                  ignore
                    (mainWindow#subscriptionSmartCList#append
                      ( try
                          List.assoc tutor_id availableTutors
                        with Not_found -> assert false )))
                tutors_id;
              subscribeWindow#subscribeWindow#misc#hide ();
              if sort subscribedTutors <> sort tutors_id then
                self#showDialog
                  (sprintf "Subscription mismatch\n: %s"
                    (Hbugs_messages.string_of_msg msg))
          | unexpected_msg ->
              mainWindow#subscriptionSmartCList#clear ();
              self#showDialog
                (sprintf "Subscription FAILED, unexpected message:\n%s"
                  (Hbugs_messages.string_of_msg unexpected_msg)))

    method private subscribeSelected () =
     let tutorsSmartCList = subscribeWindow#tutorsSmartCList in
     let selectedTutors =
       List.map
        (fun p ->
          tutorsSmartCList#model#get
           ~row:(tutorsSmartCList#model#get_iter p)
           ~column:tutorsSmartCList#column1)
        tutorsSmartCList#selection#get_selected_rows
     in
      self#subscribe' selectedTutors

    method subscribeAll () =
      self#listTutors ();  (* this fills 'availableTutors' field *)
      self#subscribe' (List.map fst availableTutors)

    method private quit () =
      self#unregisterFromBroker ();
      destroy_callback ()

      (** enable/disable debugging *)
    method private setDebug value = debug <- value

    method private reconfigDebuggingButtons =
      List.iter (* debug value changed, reconfigure buttons *)
        (fun (b: GObj.misc_ops) -> if debug then b#show () else b#hide ())
        self#debugButtons;
    
    method private toggleDebug () =
      self#setDebug (not debug);
      self#reconfigDebuggingButtons

  end
;;

