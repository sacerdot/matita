(* Copyright (C) 2004-2005, HELM Team.
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

(* $Id$ *)

open Printf
open GrafiteTypes

module TA = GrafiteAst

let debug = false
let debug_print = if debug then prerr_endline else ignore

  (** raised when one of the script margins (top or bottom) is reached *)
exception Margin
exception NoUnfinishedProof
exception ActionCancelled of string

let safe_substring s i j =
  try String.sub s i j with Invalid_argument _ -> assert false

let heading_nl_RE = Pcre.regexp "^\\s*\n\\s*"
let heading_nl_RE' = Pcre.regexp "^(\\s*\n\\s*)"
let only_dust_RE = Pcre.regexp "^(\\s|\n|%%[^\n]*\n)*$"
let multiline_RE = Pcre.regexp "^\n[^\n]+$"
let newline_RE = Pcre.regexp "\n"
let comment_RE = Pcre.regexp "\\(\\*(.|\n)*\\*\\)\n?" ~flags:[`UNGREEDY]
 
let comment str =
  if Pcre.pmatch ~rex:multiline_RE str then
    "\n(** " ^ (Pcre.replace ~rex:newline_RE str) ^ " *)"
  else
    "\n(**\n" ^ str ^ "\n*)"

let strip_comments str =
  Pcre.qreplace ~templ:"\n" ~pat:"\n\n" (Pcre.qreplace ~rex:comment_RE str)
;;
                     
let first_line s =
  let s = Pcre.replace ~rex:heading_nl_RE s in
  try
    let nl_pos = String.index s '\n' in
    String.sub s 0 nl_pos
  with Not_found -> s

type guistuff = {
  urichooser: NReference.reference list -> NReference.reference list;
  ask_confirmation: title:string -> message:string -> [`YES | `NO | `CANCEL];
}

let eval_with_engine include_paths guistuff grafite_status user_goal
 skipped_txt nonskipped_txt st
=
  let parsed_text_length =
    String.length skipped_txt + String.length nonskipped_txt 
  in
  let text = skipped_txt ^ nonskipped_txt in
  let prefix_len = MatitaGtkMisc.utf8_string_length skipped_txt in
  let enriched_history_fragment =
   MatitaEngine.eval_ast ~include_paths ~do_heavy_checks:(Helm_registry.get_bool
     "matita.do_heavy_checks")
    grafite_status (text,prefix_len,st)
  in
  let enriched_history_fragment = List.rev enriched_history_fragment in
  (* really fragile *)
  let res,_ = 
    List.fold_left 
      (fun (acc, to_prepend) (status,alias) ->
       match alias with
       | None -> (status,to_prepend ^ nonskipped_txt)::acc,""
       | Some (k,value) ->
            let newtxt = GrafiteAstPp.pp_alias value in
            (status,to_prepend ^ newtxt ^ "\n")::acc, "")
      ([],skipped_txt) enriched_history_fragment
  in
  res,"",parsed_text_length
;;

let pp_eager_statement_ast = GrafiteAstPp.pp_statement 

let eval_nmacro include_paths (buffer : GText.buffer) guistuff grafite_status user_goal unparsed_text parsed_text script mac =
  let parsed_text_length = String.length parsed_text in
  match mac with
  | TA.Screenshot (_,name) -> 
       let status = script#grafite_status in
       let _,_,menv,subst,_ = status#obj in
       let name = Filename.dirname (script#filename) ^ "/" ^ name in
       let sequents = 
         let selected = Continuationals.Stack.head_goals status#stack in
         List.filter (fun x,_ -> List.mem x selected) menv         
       in
       CicMathView.screenshot status sequents menv subst name;
       [status, parsed_text], "", parsed_text_length
  | TA.NCheck (_,t) ->
      let status = script#grafite_status in
      let _,_,menv,subst,_ = status#obj in
      let ctx = 
       match Continuationals.Stack.head_goals status#stack with
          [] -> []
        | g::tl ->
           if tl <> [] then
            HLog.warn
             "Many goals focused. Using the context of the first one\n";
           let _, ctx, _ = NCicUtils.lookup_meta g menv in
            ctx in
      let m, s, status, t = 
        GrafiteDisambiguate.disambiguate_nterm 
          status None ctx menv subst (parsed_text,parsed_text_length,
            NotationPt.Cast (t,NotationPt.Implicit `JustOne))  
          (* XXX use the metasenv, if possible *)
      in
      MatitaMathView.show_entry (`NCic (t,ctx,m,s));
      [status, parsed_text], "", parsed_text_length
  | TA.NIntroGuess _loc ->
      let names_ref = ref [] in
      let s = 
        NTactics.intros_tac ~names_ref [] script#grafite_status 
      in
      let rex = Pcre.regexp ~flags:[`MULTILINE] "\\A([\\n\\t\\r ]*).*\\Z" in
      let nl = Pcre.replace ~rex ~templ:"$1" parsed_text in
      [s, nl ^ "#" ^ String.concat " " !names_ref ^ ";"], "", parsed_text_length
  | TA.NAutoInteractive (_loc, (None,a)) -> 
      let trace_ref = ref [] in
      let s = 
        NnAuto.auto_tac 
          ~params:(None,a) ~trace_ref script#grafite_status 
      in
      let depth = 
        try List.assoc "depth" a
        with Not_found -> ""
      in
      let trace = "/"^(if int_of_string depth > 1 then depth else "")^"/ by " in
      let thms = 
        match !trace_ref with
        | [] -> "{}"
        | thms -> 
           String.concat ", "  
             (HExtlib.filter_map (function 
               | NotationPt.NRef r -> Some (NCicPp.r2s true r) 
               | _ -> None) 
             thms)
      in
      let rex = Pcre.regexp ~flags:[`MULTILINE] "\\A([\\n\\t\\r ]*).*\\Z" in
      let nl = Pcre.replace ~rex ~templ:"$1" parsed_text in
      [s, nl ^ trace ^ thms ^ ";"], "", parsed_text_length
  | TA.NAutoInteractive (_, (Some _,_)) -> assert false

let rec eval_executable include_paths (buffer : GText.buffer) guistuff
grafite_status user_goal unparsed_text skipped_txt nonskipped_txt
script ex loc
=
  try
   ignore (buffer#move_mark (`NAME "beginning_of_statement")
    ~where:((buffer#get_iter_at_mark (`NAME "locked"))#forward_chars
       (Glib.Utf8.length skipped_txt))) ;
   eval_with_engine include_paths 
    guistuff grafite_status user_goal skipped_txt nonskipped_txt
     (TA.Executable (loc, ex))
  with
     MatitaTypes.Cancel -> [], "", 0
   | GrafiteEngine.NMacro (_loc,macro) ->
       eval_nmacro include_paths buffer guistuff grafite_status
        user_goal unparsed_text (skipped_txt ^ nonskipped_txt) script macro


and eval_statement include_paths (buffer : GText.buffer) guistuff 
 grafite_status user_goal script statement
=
  let st,unparsed_text =
    match statement with
    | `Raw text ->
        if Pcre.pmatch ~rex:only_dust_RE text then raise Margin;
        let strm =
         GrafiteParser.parsable_statement grafite_status
          (Ulexing.from_utf8_string text) in
        let ast = MatitaEngine.get_ast grafite_status include_paths strm in
         ast, text
    | `Ast (st, text) -> st, text
  in
  let text_of_loc floc = 
    let nonskipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let start, stop = HExtlib.loc_of_floc floc in 
    let floc = HExtlib.floc_of_loc (0, start) in
    let skipped_txt,_ = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    let floc = HExtlib.floc_of_loc (0, stop) in
    let txt,len = MatitaGtkMisc.utf8_parsed_text unparsed_text floc in
    txt,nonskipped_txt,skipped_txt,len
  in 
  match st with
  | GrafiteAst.Executable (loc, ex) ->
     let _, nonskipped, skipped, parsed_text_length = text_of_loc loc in
      eval_executable include_paths buffer guistuff 
       grafite_status user_goal unparsed_text skipped nonskipped script ex loc
  | GrafiteAst.Comment (loc, GrafiteAst.Code (_, ex))
    when Helm_registry.get_bool "matita.execcomments" ->
     let _, nonskipped, skipped, parsed_text_length = text_of_loc loc in
      eval_executable include_paths buffer guistuff 
       grafite_status user_goal unparsed_text skipped nonskipped script ex loc
  | GrafiteAst.Comment (loc, _) -> 
      let parsed_text, _, _, parsed_text_length = text_of_loc loc in
      let remain_len = String.length unparsed_text - parsed_text_length in
      let s = String.sub unparsed_text parsed_text_length remain_len in
      let s,text,len = 
       try
        eval_statement include_paths buffer guistuff 
         grafite_status user_goal script (`Raw s)
       with
          HExtlib.Localized (floc, exn) ->
           HExtlib.raise_localized_exception 
             ~offset:(MatitaGtkMisc.utf8_string_length parsed_text) floc exn
        | MultiPassDisambiguator.DisambiguationError (offset,errorll) ->
           raise
            (MultiPassDisambiguator.DisambiguationError
              (offset+parsed_text_length, errorll))
      in
      assert (text=""); (* no macros inside comments, please! *)
      (match s with
      | (statuses,text)::tl ->
         (statuses,parsed_text ^ text)::tl,"",parsed_text_length + len
      | [] -> [], "", 0)
  
let fresh_script_id =
  let i = ref 0 in
  fun () -> incr i; !i

class script  ~(source_view: GSourceView2.source_view)
              ~ask_confirmation
              ~urichooser 
              () =
let buffer = source_view#buffer in
let source_buffer = source_view#source_buffer in
let initial_statuses current baseuri =
 let empty_lstatus = new GrafiteDisambiguate.status in
 (match current with
     Some current ->
      NCicLibrary.time_travel
       ((new GrafiteTypes.status current#baseuri)#set_disambiguate_db current#disambiguate_db);
      (* CSC: there is a known bug in invalidation; temporary fix here *)
      NCicEnvironment.invalidate ()
   | None -> ());
 let lexicon_status = empty_lstatus in
 let grafite_status = (new GrafiteTypes.status baseuri)#set_disambiguate_db lexicon_status#disambiguate_db in
  grafite_status
in
let read_include_paths file =
 try 
   let root, _buri, _fname, _tgt = 
     Librarian.baseuri_of_script ~include_paths:[] file 
   in 
   let rc = 
    Str.split (Str.regexp " ") 
     (List.assoc "include_paths" (Librarian.load_root_file (root^"/root")))
   in
   List.iter (HLog.debug) rc; rc
 with Librarian.NoRootFor _ | Not_found -> []
in
let default_buri = "cic:/matita/tests" in
let default_fname = ".unnamed.ma" in
object (self)
  val mutable include_paths_ = []

  val scriptId = fresh_script_id ()

  val guistuff = {
    urichooser = urichooser;
    ask_confirmation = ask_confirmation;
  }

  val mutable filename_ = (None : string option)

  method has_name = filename_ <> None
  
  method include_paths =
    include_paths_ @ 
    Helm_registry.get_list Helm_registry.string "matita.includes"

  method private curdir =
    try
     let root, _buri, _fname, _tgt = 
       Librarian.baseuri_of_script ~include_paths:self#include_paths
       self#filename 
     in 
     root
    with Librarian.NoRootFor _ -> Sys.getcwd ()

  method buri_of_current_file =
    match filename_ with
    | None -> default_buri 
    | Some f ->
        try 
          let _root, buri, _fname, _tgt = 
            Librarian.baseuri_of_script ~include_paths:self#include_paths f 
          in 
          buri
        with Librarian.NoRootFor _ -> default_buri

  method filename = match filename_ with None -> default_fname | Some f -> f

  initializer 
    ignore (GMain.Timeout.add ~ms:300000 
       ~callback:(fun _ -> self#_saveToBackupFile ();true));
    ignore (buffer#connect#modified_changed 
      (fun _ -> self#set_star buffer#modified))

  val mutable statements = []    (** executed statements *)

  val mutable history = [ initial_statuses None default_buri ]
    (** list of states before having executed statements. Head element of this
      * list is the current state, last element is the state at the beginning of
      * the script.
      * Invariant: this list length is 1 + length of statements *)

  (** goal as seen by the user (i.e. metano corresponding to current tab) *)
  val mutable userGoal = (None : int option)

  (** text mark and tag representing locked part of a script *)
  val locked_mark =
    buffer#create_mark ~name:"locked" ~left_gravity:true buffer#start_iter
  val beginning_of_statement_mark =
    buffer#create_mark ~name:"beginning_of_statement"
     ~left_gravity:true buffer#start_iter
  val locked_tag = buffer#create_tag [`BACKGROUND "lightblue"; `EDITABLE false]
  val error_tag = buffer#create_tag [`UNDERLINE `SINGLE; `FOREGROUND "red"]

  method locked_mark = locked_mark
  method locked_tag = locked_tag
  method error_tag = error_tag

    (* history can't be empty, the invariant above grant that it contains at
     * least the init grafite_status *)
  method grafite_status = match history with s::_ -> s | _ -> assert false

  method private _advance ?statement () =
   let s = match statement with Some s -> s | None -> self#getFuture in
   if self#bos then LibraryClean.clean_baseuris [self#buri_of_current_file];
   HLog.debug ("evaluating: " ^ first_line s ^ " ...");
   let time1 = Unix.gettimeofday () in
   let entries, newtext, parsed_len = 
    try
     eval_statement self#include_paths buffer guistuff
      self#grafite_status userGoal self (`Raw s)
    with End_of_file -> raise Margin
   in
   let time2 = Unix.gettimeofday () in
   HLog.debug ("... done in " ^ string_of_float (time2 -. time1) ^ "s");
   let new_statuses, new_statements =
     let statuses, texts = List.split entries in
     statuses, texts
   in
   history <- new_statuses @ history;
   statements <- new_statements @ statements;
   let start = buffer#get_iter_at_mark (`MARK locked_mark) in
   let new_text = String.concat "" (List.rev new_statements) in
   if statement <> None then
     buffer#insert ~iter:start new_text
   else begin
     let parsed_text = String.sub s 0 parsed_len in
     if new_text <> parsed_text then begin
       let stop = start#copy#forward_chars (Glib.Utf8.length parsed_text) in
       buffer#delete ~start ~stop;
       buffer#insert ~iter:start new_text;
     end;
   end;
   self#moveMark (Glib.Utf8.length new_text);
   buffer#insert ~iter:(buffer#get_iter_at_mark (`MARK locked_mark)) newtext;
   (* here we need to set the Goal in case we are going to cursor (or to
      bottom) and we will face a macro *)
    userGoal <- None

  method private _retract offset grafite_status new_statements new_history =
    NCicLibrary.time_travel grafite_status;
    statements <- new_statements;
    history <- new_history;
    self#moveMark (- offset)

  method advance ?statement () =
    try
      self#_advance ?statement ();
      self#notify
    with 
    | Margin -> self#notify
    | Not_found -> assert false
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method retract () =
    try
      let cmp,new_statements,new_history,grafite_status =
       match statements,history with
          stat::statements, _::(status::_ as history) ->
           assert (Glib.Utf8.validate stat);
           Glib.Utf8.length stat, statements, history, status
       | [],[_] -> raise Margin
       | _,_ -> assert false
      in
       self#_retract cmp grafite_status new_statements
        new_history;
       self#notify
    with 
    | Margin -> self#notify
    | Invalid_argument "Array.make" -> HLog.error "The script is too big!\n"
    | exc -> self#notify; raise exc

  method private getFuture =
    let lock = buffer#get_iter_at_mark (`MARK locked_mark) in
    let text = buffer#get_text ~start:lock ~stop:buffer#end_iter () in
    text

  method expandAllVirtuals =
    let lock = buffer#get_iter_at_mark (`MARK locked_mark) in
    let text = buffer#get_text ~start:lock ~stop:buffer#end_iter () in
    buffer#delete ~start:lock ~stop:buffer#end_iter;
    let text = Pcre.replace ~pat:":=" ~templ:"\\def" text in
    let text = Pcre.replace ~pat:"->" ~templ:"\\to" text in
    let text = Pcre.replace ~pat:"=>" ~templ:"\\Rightarrow" text in
    let text = 
      Pcre.substitute_substrings 
        ~subst:(fun str -> 
           let pristine = Pcre.get_substring str 0 in
           let input = 
             if pristine.[0] = ' ' then
               String.sub pristine 1 (String.length pristine -1) 
             else pristine 
           in
           let input = 
             if input.[String.length input-1] = ' ' then
               String.sub input 0 (String.length input -1) 
             else input
           in
           let before, after =  
             if input = "\\forall" || 
                input = "\\lambda" || 
                input = "\\exists" then "","" else " ", " " 
           in
           try 
             before ^ Glib.Utf8.from_unichar 
               (snd (Virtuals.symbol_of_virtual input)) ^ after
           with Virtuals.Not_a_virtual -> pristine) 
        ~pat:" ?\\\\[a-zA-Z]+ ?" text
    in
    buffer#insert ~iter:lock text
      
  (** @param rel_offset relative offset from current position of locked_mark *)
  method private moveMark rel_offset =
    let mark = `MARK locked_mark in
    let old_insert = buffer#get_iter_at_mark `INSERT in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    let current_mark_pos = buffer#get_iter_at_mark mark in
    let new_mark_pos =
      match rel_offset with
      | 0 -> current_mark_pos
      | n when n > 0 -> current_mark_pos#forward_chars n
      | n (* when n < 0 *) -> current_mark_pos#backward_chars (abs n)
    in
    buffer#move_mark mark ~where:new_mark_pos;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:new_mark_pos;
    buffer#move_mark `INSERT old_insert;
    let mark_position = buffer#get_iter_at_mark mark in
    if source_view#move_mark_onscreen mark then
     begin
      buffer#move_mark mark mark_position;
      source_view#scroll_to_mark ~use_align:true ~xalign:1.0 ~yalign:0.1 mark;
     end;
    while Glib.Main.pending () do ignore(Glib.Main.iteration false); done

  method clean_dirty_lock =
    let lock_mark_iter = buffer#get_iter_at_mark (`MARK locked_mark) in
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#apply_tag locked_tag ~start:buffer#start_iter ~stop:lock_mark_iter

  val mutable observers = []

  method addObserver (o: GrafiteTypes.status -> unit) =
    observers <- o :: observers

  method private notify =
    let grafite_status = self#grafite_status in
    List.iter (fun o -> o grafite_status) observers

  method loadFromString s =
    buffer#set_text s;
    self#reset_buffer;
    buffer#set_modified true

  method loadFromFile f =
    buffer#set_text (HExtlib.input_file f);
    self#reset_buffer;
    buffer#set_modified false

  method assignFileName file =
   match file with
      None ->
       (MatitaMisc.get_gui ())#main#scriptLabel#set_text default_fname;
       filename_ <- None;
       include_paths_ <- [];
       self#reset_buffer
    | Some file ->
       let f = Librarian.absolutize file in
        (MatitaMisc.get_gui ())#main#scriptLabel#set_text (Filename.basename f);
        filename_ <- Some f;
        include_paths_ <- read_include_paths f;
        self#reset_buffer;
        Sys.chdir self#curdir;
        HLog.debug ("Moving to " ^ Sys.getcwd ())

  method set_star b =
   let label = (MatitaMisc.get_gui ())#main#scriptLabel in
   label#set_text ((if b then "*" else "") ^ Filename.basename self#filename);
   label#misc#set_tooltip_text
    ("URI: " ^ self#buri_of_current_file ^ "\nPATH: " ^ self#filename)
    
  method saveToFile () =
    if self#has_name then
      let oc = open_out self#filename in
      output_string oc (buffer#get_text ~start:buffer#start_iter
                        ~stop:buffer#end_iter ());
      close_out oc;
      self#set_star false;
      buffer#set_modified false
    else
      HLog.error "Can't save, no filename selected"
  
  method private _saveToBackupFile () =
    if buffer#modified then
      begin
        let f = self#filename in
        let oc = open_out f in
        output_string oc (buffer#get_text ~start:buffer#start_iter
                            ~stop:buffer#end_iter ());
        close_out oc;
        HLog.debug ("backup " ^ f ^ " saved")                    
      end
  
  method private reset_buffer = 
    statements <- [];
    history <- [ initial_statuses (Some self#grafite_status) self#buri_of_current_file ];
    userGoal <- None;
    self#notify;
    buffer#remove_tag locked_tag ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#move_mark (`MARK locked_mark) ~where:buffer#start_iter

  method reset () =
    self#reset_buffer;
    source_buffer#begin_not_undoable_action ();
    buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter;
    source_buffer#end_not_undoable_action ();
    buffer#set_modified false;
  
  method template () =
    let template = HExtlib.input_file BuildTimeConf.script_template in 
    buffer#insert ~iter:(buffer#get_iter `START) template;
    buffer#set_modified false;
    self#set_star false

  method goto (pos: [`Top | `Bottom | `Cursor]) () =
  try  
    let old_locked_mark =
     `MARK
       (buffer#create_mark ~name:"old_locked_mark"
         ~left_gravity:true (buffer#get_iter_at_mark (`MARK locked_mark))) in
    let getpos _ = buffer#get_iter_at_mark (`MARK locked_mark) in 
    let getoldpos _ = buffer#get_iter_at_mark old_locked_mark in 
    let dispose_old_locked_mark () = buffer#delete_mark old_locked_mark in
    match pos with
    | `Top -> 
        dispose_old_locked_mark (); 
        self#reset_buffer;
        self#notify
    | `Bottom ->
        (try 
          let rec dowhile () =
            self#_advance ();
            let newpos = getpos () in
            if (getoldpos ())#compare newpos < 0 then
              begin
                buffer#move_mark old_locked_mark newpos;
                dowhile ()
              end
          in
          dowhile ();
          dispose_old_locked_mark ();
          self#notify 
        with 
        | Margin -> dispose_old_locked_mark (); self#notify
        | exc -> dispose_old_locked_mark (); self#notify; raise exc)
    | `Cursor ->
        let locked_iter () = buffer#get_iter_at_mark (`NAME "locked") in
        let cursor_iter () = buffer#get_iter_at_mark `INSERT in
        let remember =
         `MARK
           (buffer#create_mark ~name:"initial_insert"
             ~left_gravity:true (cursor_iter ())) in
        let dispose_remember () = buffer#delete_mark remember in
        let remember_iter () =
         buffer#get_iter_at_mark (`NAME "initial_insert") in
        let cmp () = (locked_iter ())#offset - (remember_iter ())#offset in
        let icmp = cmp () in
        let forward_until_cursor () = (* go forward until locked > cursor *)
          let rec aux () =
            self#_advance ();
            if cmp () < 0 && (getoldpos ())#compare (getpos ()) < 0 
            then
             begin
              buffer#move_mark old_locked_mark (getpos ());
              aux ()
             end
          in
          aux ()
        in
        let rec back_until_cursor len = (* go backward until locked < cursor *)
         function
            statements, ((grafite_status)::_ as history)
            when len <= 0 ->
             self#_retract (icmp - len) grafite_status statements
              history
          | statement::tl1, _::tl2 ->
             back_until_cursor (len - MatitaGtkMisc.utf8_string_length statement) (tl1,tl2)
          | _,_ -> assert false
        in
        (try
          begin
           if icmp < 0 then       (* locked < cursor *)
             (forward_until_cursor (); self#notify)
           else if icmp > 0 then  (* locked > cursor *)
             (back_until_cursor icmp (statements,history); self#notify)
           else                  (* cursor = locked *)
               ()
          end ;
          dispose_remember ();
          dispose_old_locked_mark ();
        with 
        | Margin -> dispose_remember (); dispose_old_locked_mark (); self#notify
        | exc -> dispose_remember (); dispose_old_locked_mark ();
                 self#notify; raise exc)
  with Invalid_argument "Array.make" ->
     HLog.error "The script is too big!\n"
  
  method stack = (assert false : Continuationals.Stack.t) (* MATITA 1.0 GrafiteTypes.get_stack
  self#grafite_status *)
  method setGoal n = userGoal <- n
  method goal = userGoal

  method bos = 
    match history with
    | _::[] -> true
    | _ -> false

  method eos = 
    let rec is_there_only_comments lexicon_status s = 
      if Pcre.pmatch ~rex:only_dust_RE s then raise Margin;
      let strm =
       GrafiteParser.parsable_statement lexicon_status
        (Ulexing.from_utf8_string s)in
      match GrafiteParser.parse_statement lexicon_status strm with
      | GrafiteAst.Comment (loc,_) -> 
          let _,parsed_text_length = MatitaGtkMisc.utf8_parsed_text s loc in
          (* CSC: why +1 in the following lines ???? *)
          let parsed_text_length = parsed_text_length + 1 in
          let remain_len = String.length s - parsed_text_length in
          let next = String.sub s parsed_text_length remain_len in
          is_there_only_comments lexicon_status next
      | GrafiteAst.Executable _ -> false
    in
    try is_there_only_comments self#grafite_status self#getFuture
    with 
    | NCicLibrary.IncludedFileNotCompiled _
    | HExtlib.Localized _
    | CicNotationParser.Parse_error _ -> false
    | Margin | End_of_file -> true
    | Invalid_argument "Array.make" -> false

  (* debug *)
  method dump () =
    HLog.debug "script status:";
    HLog.debug ("history size: " ^ string_of_int (List.length history));
    HLog.debug (sprintf "%d statements:" (List.length statements));
    List.iter HLog.debug statements;
    HLog.debug ("Current file name: " ^ self#filename);
end

let _script = ref None

let script ~source_view ~urichooser ~ask_confirmation ()
=
  let s = new script ~source_view ~ask_confirmation ~urichooser () in
  _script := Some s;
  s

let current () = match !_script with None -> assert false | Some s -> s

let _ =
 CicMathView.register_matita_script_current (current :> unit -> < advance: ?statement:string -> unit -> unit; grafite_status: GrafiteTypes.status; setGoal: int option -> unit >)
;;
