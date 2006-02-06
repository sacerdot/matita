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
exception ActionCancelled

let safe_substring s i j =
  try String.sub s i j with Invalid_argument _ -> assert false

let heading_nl_RE = Pcre.regexp "^\\s*\n\\s*"
let heading_nl_RE' = Pcre.regexp "^(\\s*\n\\s*)"
let only_dust_RE = Pcre.regexp "^(\\s|\n|%%[^\n]*\n)*$"
let multiline_RE = Pcre.regexp "^\n[^\n]+$"
let newline_RE = Pcre.regexp "\n"
 
let comment str =
  if Pcre.pmatch ~rex:multiline_RE str then
    "\n(** " ^ (Pcre.replace ~rex:newline_RE str) ^ " *)"
  else
    "\n(**\n" ^ str ^ "\n*)"
                     
let first_line s =
  let s = Pcre.replace ~rex:heading_nl_RE s in
  try
    let nl_pos = String.index s '\n' in
    String.sub s 0 nl_pos
  with Not_found -> s

  (** creates a statement AST for the Goal tactic, e.g. "goal 7" *)
let goal_ast n =
  let module A = GrafiteAst in
  let loc = HExtlib.dummy_floc in
  A.Executable (loc, A.Tactical (loc,
    A.Tactic (loc, A.Goal (loc, n)),
    Some (A.Dot loc)))

type guistuff = {
  mathviewer:MatitaTypes.mathViewer;
  urichooser: UriManager.uri list -> UriManager.uri list;
  ask_confirmation: title:string -> message:string -> [`YES | `NO | `CANCEL];
  develcreator: containing:string option -> unit;
  mutable filenamedata: string option * MatitamakeLib.development option
}

let eval_with_engine guistuff lexicon_status grafite_status user_goal
 parsed_text st
=
  let module TAPp = GrafiteAstPp in
  let parsed_text_length = String.length parsed_text in
  let initial_space,parsed_text =
   try
    let pieces = Pcre.extract ~rex:heading_nl_RE' parsed_text in
    let p1 = pieces.(1) in
    let p1_len = String.length p1 in
    let rest = String.sub parsed_text p1_len (parsed_text_length - p1_len) in
     p1, rest
   with
    Not_found -> "", parsed_text in
  let inital_space,new_grafite_status,new_lexicon_status,new_status_and_text_list' =
   (* the code commented out adds the "select" command if needed *)
   initial_space,grafite_status,lexicon_status,[] in
(* let loc, ex = 
    match st with TA.Executable (loc,ex) -> loc, ex | _ -> assert false in
    match grafite_status.proof_status with
     | Incomplete_proof { stack = stack }
      when not (List.mem user_goal (Continuationals.head_goals stack)) ->
        let grafite_status =
          MatitaEngine.eval_ast
            ~do_heavy_checks:true grafite_status (goal_ast user_goal)
        in
        let initial_space = if initial_space = "" then "\n" else initial_space
        in
        "\n", grafite_status,
        [ grafite_status,
          initial_space ^ TAPp.pp_tactical (TA.Select (loc, [user_goal])) ]
      | _ -> initial_space,grafite_status,[] in *)
  let enriched_history_fragment =
   MatitaEngine.eval_ast ~do_heavy_checks:true
    new_lexicon_status new_grafite_status st
  in
  let _,new_text_list_rev = 
    let module DTE = DisambiguateTypes.Environment in
    let module UM = UriManager in
    List.fold_right (
      fun (_,alias) (initial_space,acc) ->
       match alias with
          None -> initial_space,initial_space::acc
        | Some (k,((v,_) as value)) ->
           let new_text =
            let initial_space =
             if initial_space = "" then "\n" else initial_space
            in
             initial_space ^
              DisambiguatePp.pp_environment
               (DisambiguateTypes.Environment.add k value
                 DisambiguateTypes.Environment.empty)
           in
            "\n",new_text::acc
    ) enriched_history_fragment (initial_space,[]) in
  let new_text_list_rev =
   match enriched_history_fragment,new_text_list_rev with
      (_,None)::_, initial_space::tl -> (initial_space ^ parsed_text)::tl
    | _,_ -> assert false
  in
   let res =
    try
     List.combine (fst (List.split enriched_history_fragment)) new_text_list_rev
    with
     Invalid_argument _ -> assert false
   in
    res,parsed_text_length

let wrap_with_developments guistuff f arg = 
  try 
    f arg
  with
  | DependenciesParser.UnableToInclude what 
  | LexiconEngine.IncludedFileNotCompiled what 
  | GrafiteEngine.IncludedFileNotCompiled what as exc ->
      let compile_needed_and_go_on d =
        let target = Pcre.replace ~pat:"lexicon$" ~templ:"moo" what in
        let refresh_cb () = 
          while Glib.Main.pending () do ignore(Glib.Main.iteration false); done
        in
        if not(MatitamakeLib.build_development_in_bg ~target refresh_cb d) then
          raise exc
        else
          f arg
      in
      let do_nothing () = raise ActionCancelled in
      let handle_with_devel d =
        let name = MatitamakeLib.name_for_development d in
        let title = "Unable to include " ^ what in
        let message = 
          what ^ " is handled by development <b>" ^ name ^ "</b>.\n\n" ^
          "<i>Should I compile it and Its dependencies?</i>"
        in
        (match guistuff.ask_confirmation ~title ~message with
        | `YES -> compile_needed_and_go_on d
        | `NO -> raise exc
        | `CANCEL -> do_nothing ())
      in
      let handle_without_devel filename =
        let title = "Unable to include " ^ what in
        let message = 
         what ^ " is <b>not</b> handled by a development.\n" ^
         "All dependencies are automatically solved for a development.\n\n" ^
         "<i>Do you want to set up a development?</i>"
        in
        (match guistuff.ask_confirmation ~title ~message with
        | `YES -> 
            (match filename with
            | Some f -> 
                guistuff.develcreator ~containing:(Some (Filename.dirname f))
            | None -> guistuff.develcreator ~containing:None);
            do_nothing ()
        | `NO -> raise exc
        | `CANCEL -> do_nothing())
      in
      match guistuff.filenamedata with
      | None,None -> handle_without_devel None
      | None,Some d -> handle_with_devel d
      | Some f,_ ->
          match MatitamakeLib.development_for_dir (Filename.dirname f) with
          | None -> handle_without_devel (Some f)
          | Some d -> handle_with_devel d
;;
    
let eval_with_engine
     guistuff lexicon_status grafite_status user_goal parsed_text st
=
  wrap_with_developments guistuff
    (eval_with_engine 
      guistuff lexicon_status grafite_status user_goal parsed_text) st
;;

let pp_eager_statement_ast =
  GrafiteAstPp.pp_statement ~term_pp:CicNotationPp.pp_term
    ~lazy_term_pp:(fun _ -> assert false) ~obj_pp:(fun _ -> assert false)
 
let rec eval_macro include_paths (buffer : GText.buffer) guistuff lexicon_status grafite_status user_goal unparsed_text parsed_text script mac =
  let module TAPp = GrafiteAstPp in
  let module MQ = MetadataQuery in
  let module MDB = LibraryDb in
  let module CTC = CicTypeChecker in
  let module CU = CicUniv in
  (* no idea why ocaml wants this *)
  let parsed_text_length = String.length parsed_text in
  let dbd = LibraryDb.instance () in
  (* XXX use a real CIC -> string pretty printer *)
  let pp_macro = TAPp.pp_macro ~term_pp:CicPp.ppterm in
  match mac with
  (* WHELP's stuff *)
  | TA.WMatch (loc, term) -> 
     let l =  Whelp.match_term ~dbd term in
     let query_url =
       MatitaMisc.strip_suffix ~suffix:"."
         (HExtlib.trim_blanks unparsed_text)
     in
     let entry = `Whelp (query_url, l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], parsed_text_length
  | TA.WInstance (loc, term) ->
     let l = Whelp.instance ~dbd term in
     let entry = `Whelp (pp_macro (TA.WInstance (loc, term)), l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], parsed_text_length
  | TA.WLocate (loc, s) -> 
     let l = Whelp.locate ~dbd s in
     let entry = `Whelp (pp_macro (TA.WLocate (loc, s)), l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], parsed_text_length
  | TA.WElim (loc, term) ->
     let uri =
       match term with
       | Cic.MutInd (uri,n,_) -> UriManager.uri_of_uriref uri n None 
       | _ -> failwith "Not a MutInd"
     in
     let l = Whelp.elim ~dbd uri in
     let entry = `Whelp (pp_macro (TA.WElim (loc, term)), l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], parsed_text_length
  | TA.WHint (loc, term) ->
     let s = ((None,[0,[],term], Cic.Meta (0,[]) ,term),0) in
     let l = List.map fst (MQ.experimental_hint ~dbd s) in
     let entry = `Whelp (pp_macro (TA.WHint (loc, term)), l) in
     guistuff.mathviewer#show_uri_list ~reuse:true ~entry l;
     [], parsed_text_length
  (* REAL macro *)
  | TA.Hint loc -> 
      let user_goal' =
       match user_goal with
          Some n -> n
        | None -> raise NoUnfinishedProof
      in
      let proof = GrafiteTypes.get_current_proof grafite_status in
      let proof_status = proof,user_goal' in
      let l = List.map fst (MQ.experimental_hint ~dbd proof_status) in
      let selected = guistuff.urichooser l in
      (match selected with
      | [] -> [], parsed_text_length
      | [uri] -> 
          let suri = UriManager.string_of_uri uri in
          let ast loc =
            TA.Executable (loc, (TA.Tactical (loc,
              TA.Tactic (loc,
                TA.Apply (loc, CicNotationPt.Uri (suri, None))),
                Some (TA.Dot loc)))) in
          let text =
           comment parsed_text ^ "\n" ^
            pp_eager_statement_ast (ast HExtlib.dummy_floc) in
          let text_len = String.length text in
          let loc = HExtlib.floc_of_loc (0,text_len) in
          let statement = `Ast (GrafiteParser.LSome (ast loc),text) in
          let res,_parsed_text_len =
           eval_statement include_paths buffer guistuff lexicon_status
            grafite_status user_goal script statement
          in
           (* we need to replace all the parsed_text *)
           res,String.length parsed_text
      | _ -> 
          HLog.error 
            "The result of the urichooser should be only 1 uri, not:\n";
          List.iter (
            fun u -> HLog.error (UriManager.string_of_uri u ^ "\n")
          ) selected;
          assert false)
  | TA.Check (_,term) ->
      let metasenv = GrafiteTypes.get_proof_metasenv grafite_status in
      let context =
       match user_goal with
          None -> []
        | Some n -> GrafiteTypes.get_proof_context grafite_status n in
      let ty,_ = CTC.type_of_aux' metasenv context term CicUniv.empty_ugraph in
      let t_and_ty = Cic.Cast (term,ty) in
      guistuff.mathviewer#show_entry (`Cic (t_and_ty,metasenv));
      [], parsed_text_length
  (* TODO *)
  | TA.Quit _ -> failwith "not implemented"
  | TA.Print (_,kind) -> failwith "not implemented"
  | TA.Search_pat (_, search_kind, str) -> failwith "not implemented"
  | TA.Search_term (_, search_kind, term) -> failwith "not implemented"
                                
and eval_executable include_paths (buffer : GText.buffer) guistuff lexicon_status grafite_status user_goal unparsed_text parsed_text script loc ex
=
 let module TAPp = GrafiteAstPp in
 let module MD = GrafiteDisambiguator in
 let module ML = MatitaMisc in
  try
   begin
    match ex with
     | TA.Command (_,TA.Set (_,"baseuri",u)) ->
        if not (GrafiteMisc.is_empty u) then
         (match 
            guistuff.ask_confirmation 
              ~title:"Baseuri redefinition" 
              ~message:(
                "Baseuri " ^ u ^ " already exists.\n" ^
                "Do you want to redefine the corresponding "^
                "part of the library?")
          with
           | `YES ->
               let basedir = Helm_registry.get "matita.basedir" in
                LibraryClean.clean_baseuris ~basedir [u]
           | `NO -> ()
           | `CANCEL -> raise MatitaTypes.Cancel)
     | _ -> ()
   end;
   eval_with_engine
    guistuff lexicon_status grafite_status user_goal parsed_text
     (TA.Executable (loc, ex))
  with
     MatitaTypes.Cancel -> [], 0
   | GrafiteEngine.Macro (_loc,lazy_macro) ->
      let context =
       match user_goal with
          None -> []
        | Some n -> GrafiteTypes.get_proof_context grafite_status n in
      let grafite_status,macro = lazy_macro context in
       eval_macro include_paths buffer guistuff lexicon_status grafite_status
        user_goal unparsed_text parsed_text script macro

and eval_statement include_paths (buffer : GText.buffer) guistuff lexicon_status
 grafite_status user_goal script statement
=
  let (lexicon_status,st), unparsed_text =
    match statement with
    | `Raw text ->
        if Pcre.pmatch ~rex:only_dust_RE text then raise Margin;
        let ast = 
          wrap_with_developments guistuff
            (GrafiteParser.parse_statement 
              (Ulexing.from_utf8_string text) ~include_paths) lexicon_status 
        in
          ast, text
    | `Ast (st, text) -> (lexicon_status, st), text
  in
  let text_of_loc loc =
    let parsed_text_length = snd (HExtlib.loc_of_floc loc) in
    let parsed_text = safe_substring unparsed_text 0 parsed_text_length in
    parsed_text, parsed_text_length
  in
  match st with
  | GrafiteParser.LNone loc ->
      let parsed_text, parsed_text_length = text_of_loc loc in
       [(grafite_status,lexicon_status),parsed_text],
        parsed_text_length
  | GrafiteParser.LSome (GrafiteAst.Comment (loc, _)) -> 
      let parsed_text, parsed_text_length = text_of_loc loc in
      let remain_len = String.length unparsed_text - parsed_text_length in
      let s = String.sub unparsed_text parsed_text_length remain_len in
      let s,len = 
       try
        eval_statement include_paths buffer guistuff lexicon_status
         grafite_status user_goal script (`Raw s)
       with
          HExtlib.Localized (floc, exn) ->
           HExtlib.raise_localized_exception ~offset:parsed_text_length floc exn
        | GrafiteDisambiguator.DisambiguationError (offset,errorll) ->
           raise
            (GrafiteDisambiguator.DisambiguationError
              (offset+parsed_text_length, errorll))
      in
      (match s with
      | (statuses,text)::tl ->
         (statuses,parsed_text ^ text)::tl,parsed_text_length + len
      | [] -> [], 0)
  | GrafiteParser.LSome (GrafiteAst.Executable (loc, ex)) ->
     let parsed_text, parsed_text_length = text_of_loc loc in
      eval_executable include_paths buffer guistuff lexicon_status
       grafite_status user_goal unparsed_text parsed_text script loc ex
  
let fresh_script_id =
  let i = ref 0 in
  fun () -> incr i; !i

class script  ~(source_view: GSourceView.source_view)
              ~(mathviewer: MatitaTypes.mathViewer) 
              ~set_star
              ~ask_confirmation
              ~urichooser 
              ~develcreator 
              () =
let buffer = source_view#buffer in
let source_buffer = source_view#source_buffer in
let initial_statuses =
 (* these include_paths are used only to load the initial notation *)
 let include_paths =
  Helm_registry.get_list Helm_registry.string "matita.includes" in
 let lexicon_status =
  CicNotation2.load_notation ~include_paths
   BuildTimeConf.core_notation_script in
 let grafite_status = GrafiteSync.init () in
  grafite_status,lexicon_status
in
object (self)
  val mutable include_paths =
   Helm_registry.get_list Helm_registry.string "matita.includes"

  val scriptId = fresh_script_id ()
  
  val guistuff = {
    mathviewer = mathviewer;
    urichooser = urichooser;
    ask_confirmation = ask_confirmation;
    develcreator = develcreator;
    filenamedata = (None, None)} 
  
  method private getFilename =
    match guistuff.filenamedata with Some f,_ -> f | _ -> assert false

  method filename = self#getFilename
    
  method private ppFilename =
    match guistuff.filenamedata with 
    | Some f,_ -> f 
    | None,_ -> sprintf ".unnamed%d.ma" scriptId
  
  initializer 
    ignore (GMain.Timeout.add ~ms:300000 
       ~callback:(fun _ -> self#_saveToBackupFile ();true));
    ignore (buffer#connect#modified_changed 
      (fun _ -> set_star (Filename.basename self#ppFilename) buffer#modified))

  val mutable statements = []    (** executed statements *)

  val mutable history = [ initial_statuses ]
    (** list of states before having executed statements. Head element of this
      * list is the current state, last element is the state at the beginning of
      * the script.
      * Invariant: this list length is 1 + length of statements *)

  (** goal as seen by the user (i.e. metano corresponding to current tab) *)
  val mutable userGoal = None

  (** text mark and tag representing locked part of a script *)
  val locked_mark =
    buffer#create_mark ~name:"locked" ~left_gravity:true buffer#start_iter
  val locked_tag = buffer#create_tag [`BACKGROUND "lightblue"; `EDITABLE false]
  val error_tag = buffer#create_tag [`UNDERLINE `SINGLE; `FOREGROUND "red"]

  method locked_mark = locked_mark
  method locked_tag = locked_tag
  method error_tag = error_tag

    (* history can't be empty, the invariant above grant that it contains at
     * least the init grafite_status *)
  method grafite_status = match history with (s,_)::_ -> s | _ -> assert false
  method lexicon_status = match history with (_,ss)::_ -> ss | _ -> assert false

  method private _advance ?statement () =
   let s = match statement with Some s -> s | None -> self#getFuture in
   HLog.debug ("evaluating: " ^ first_line s ^ " ...");
   let (entries, parsed_len) = 
    try
     eval_statement include_paths buffer guistuff self#lexicon_status
      self#grafite_status userGoal self (`Raw s)
    with End_of_file -> raise Margin
   in
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
     if new_text <> String.sub s 0 parsed_len then begin
       buffer#delete ~start ~stop:(start#copy#forward_chars parsed_len);
       buffer#insert ~iter:start new_text;
     end;
   end;
   self#moveMark (String.length new_text);
   (* here we need to set the Goal in case we are going to cursor (or to
      bottom) and we will face a macro *)
   match self#grafite_status.proof_status with
      Incomplete_proof p ->
       userGoal <-
         (try Some (Continuationals.Stack.find_goal p.stack)
         with Failure _ -> None)
    | _ -> userGoal <- None

  method private _retract offset lexicon_status grafite_status new_statements
   new_history
  =
   let cur_grafite_status,cur_lexicon_status =
    match history with s::_ -> s | [] -> assert false
   in
    LexiconSync.time_travel ~present:cur_lexicon_status ~past:lexicon_status;
    GrafiteSync.time_travel ~present:cur_grafite_status ~past:grafite_status;
    statements <- new_statements;
    history <- new_history;
    self#moveMark (- offset)

  method advance ?statement () =
    try
      self#_advance ?statement ();
      self#notify
    with 
    | Margin -> self#notify
    | exc -> self#notify; raise exc

  method retract () =
    try
      let cmp,new_statements,new_history,(grafite_status,lexicon_status) =
       match statements,history with
          stat::statements, _::(status::_ as history) ->
           String.length stat, statements, history, status
       | [],[_] -> raise Margin
       | _,_ -> assert false
      in
       self#_retract cmp lexicon_status grafite_status new_statements
        new_history;
       self#notify
    with 
    | Margin -> self#notify
    | exc -> self#notify; raise exc

  method private getFuture =
    buffer#get_text ~start:(buffer#get_iter_at_mark (`MARK locked_mark))
      ~stop:buffer#end_iter ()

      
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

  method addObserver (o: LexiconEngine.status -> GrafiteTypes.status -> unit) =
    observers <- o :: observers

  method private notify =
    let lexicon_status = self#lexicon_status in
    let grafite_status = self#grafite_status in
    List.iter (fun o -> o lexicon_status grafite_status) observers

  method loadFromFile f =
    buffer#set_text (HExtlib.input_file f);
    self#reset_buffer;
    buffer#set_modified false
    
  method assignFileName file =
    let abspath = MatitaMisc.absolute_path file in
    let dirname = Filename.dirname abspath in
    let devel = MatitamakeLib.development_for_dir dirname in
    guistuff.filenamedata <- Some abspath, devel;
    let include_ = 
     match MatitamakeLib.development_for_dir dirname with
        None -> []
      | Some devel -> [MatitamakeLib.root_for_development devel] in
    let include_ =
     include_ @ (Helm_registry.get_list Helm_registry.string "matita.includes")
    in
     include_paths <- include_
    
  method saveToFile () =
    let oc = open_out self#getFilename in
    output_string oc (buffer#get_text ~start:buffer#start_iter
                        ~stop:buffer#end_iter ());
    close_out oc;
    buffer#set_modified false
  
  method private _saveToBackupFile () =
    if buffer#modified then
      begin
        let f = self#ppFilename ^ "~" in
        let oc = open_out f in
        output_string oc (buffer#get_text ~start:buffer#start_iter
                            ~stop:buffer#end_iter ());
        close_out oc;
        HLog.debug ("backup " ^ f ^ " saved")                    
      end
  
  method private goto_top =
    let grafite_status,lexicon_status = 
      let rec last x = function 
      | [] -> x
      | hd::tl -> last hd tl
      in
      last (self#grafite_status,self#lexicon_status) history
    in
    (* FIXME: this is not correct since there is no undo for 
     * library_objects.set_default... *)
    GrafiteSync.time_travel ~present:self#grafite_status ~past:grafite_status;
    LexiconSync.time_travel ~present:self#lexicon_status ~past:lexicon_status

  method private reset_buffer = 
    statements <- [];
    history <- [ initial_statuses ];
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
    let development = MatitamakeLib.development_for_dir (Unix.getcwd ()) in
    guistuff.filenamedata <- (None,development);
    let include_ = 
     match development with
        None -> []
      | Some devel -> [MatitamakeLib.root_for_development devel ]
    in
    let include_ =
     include_ @ (Helm_registry.get_list Helm_registry.string "matita.includes")
    in
     include_paths <- include_ ;
     buffer#set_modified false;
     set_star (Filename.basename self#ppFilename) false

  method goto (pos: [`Top | `Bottom | `Cursor]) () =
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
        self#goto_top; 
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
            statements, ((grafite_status,lexicon_status)::_ as history)
            when len <= 0 ->
             self#_retract (icmp - len) lexicon_status grafite_status statements
              history
          | statement::tl1, _::tl2 ->
             back_until_cursor (len - String.length statement) (tl1,tl2)
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
              
  method onGoingProof () =
    match self#grafite_status.proof_status with
    | No_proof | Proof _ -> false
    | Incomplete_proof _ -> true
    | Intermediate _ -> assert false

(*   method proofStatus = MatitaTypes.get_proof_status self#status *)
  method proofMetasenv = GrafiteTypes.get_proof_metasenv self#grafite_status

  method proofContext =
   match userGoal with
      None -> []
    | Some n -> GrafiteTypes.get_proof_context self#grafite_status n

  method proofConclusion =
   match userGoal with
      None -> assert false
    | Some n ->
       GrafiteTypes.get_proof_conclusion self#grafite_status n

  method stack = GrafiteTypes.get_stack self#grafite_status
  method setGoal n = userGoal <- n
  method goal = userGoal

  method eos = 
    let s = self#getFuture in
    let rec is_there_only_comments lexicon_status s = 
      if Pcre.pmatch ~rex:only_dust_RE s then raise Margin;
      let lexicon_status,st =
       GrafiteParser.parse_statement (Ulexing.from_utf8_string s)
        ~include_paths lexicon_status
      in
      match st with
      | GrafiteParser.LSome (GrafiteAst.Comment (loc,_)) -> 
          let parsed_text_length = snd (HExtlib.loc_of_floc loc) in
          let remain_len = String.length s - parsed_text_length in
          let next = String.sub s parsed_text_length remain_len in
          is_there_only_comments lexicon_status next
      | GrafiteParser.LNone _
      | GrafiteParser.LSome (GrafiteAst.Executable _) -> false
    in
    try
      is_there_only_comments self#lexicon_status s
    with 
    | CicNotationParser.Parse_error _ -> false
    | Margin | End_of_file -> true

  (* debug *)
  method dump () =
    HLog.debug "script status:";
    HLog.debug ("history size: " ^ string_of_int (List.length history));
    HLog.debug (sprintf "%d statements:" (List.length statements));
    List.iter HLog.debug statements;
    HLog.debug ("Current file name: " ^
      (match guistuff.filenamedata with 
      |None,_ -> "[ no name ]" 
      | Some f,_ -> f));

end

let _script = ref None

let script ~source_view ~mathviewer ~urichooser ~develcreator ~ask_confirmation ~set_star ()
=
  let s = new script 
    ~source_view ~mathviewer ~ask_confirmation ~urichooser ~develcreator ~set_star () 
  in
  _script := Some s;
  s

let current () = match !_script with None -> assert false | Some s -> s

