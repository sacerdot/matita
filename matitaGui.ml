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

open MatitaGeneratedGui
open MatitaGtkMisc
open MatitaMisc

exception Found of int

let gui_instance = ref None

class type browserWin =
  (* this class exists only because GEdit.combo_box_entry is not supported by
   * lablgladecc :-(((( *)
object
  inherit MatitaGeneratedGui.browserWin
  method browserUri: GEdit.combo_box_entry
end

class console ~(buffer: GText.buffer) () =
  object (self)
    val error_tag   = buffer#create_tag [ `FOREGROUND "red" ]
    val warning_tag = buffer#create_tag [ `FOREGROUND "orange" ]
    val message_tag = buffer#create_tag []
    val debug_tag   = buffer#create_tag [ `FOREGROUND "#888888" ]
    method message s = buffer#insert ~iter:buffer#end_iter ~tags:[message_tag] s
    method error s   = buffer#insert ~iter:buffer#end_iter ~tags:[error_tag] s
    method warning s = buffer#insert ~iter:buffer#end_iter ~tags:[warning_tag] s
    method debug s   = buffer#insert ~iter:buffer#end_iter ~tags:[debug_tag] s
    method clear () =
      buffer#delete ~start:buffer#start_iter ~stop:buffer#end_iter
    method log_callback (tag: HLog.log_tag) s =
      match tag with
      | `Debug -> self#debug (s ^ "\n")
      | `Error -> self#error (s ^ "\n")
      | `Message -> self#message (s ^ "\n")
      | `Warning -> self#warning (s ^ "\n")
  end
        
let clean_current_baseuri grafite_status = 
    try  
      let baseuri = GrafiteTypes.get_string_option grafite_status "baseuri" in
      LibraryClean.clean_baseuris [baseuri]
    with GrafiteTypes.Option_error _ -> ()

let ask_and_save_moo_if_needed parent fname lexicon_status grafite_status = 
  let baseuri =
   try Some (GrafiteTypes.get_string_option grafite_status "baseuri")
   with GrafiteTypes.Option_error _ -> None
  in
  if (MatitaScript.current ())#eos &&
     grafite_status.GrafiteTypes.proof_status = GrafiteTypes.No_proof &&
     baseuri <> None
  then
   begin
    let baseuri = match baseuri with Some b -> b | None -> assert false in
    let moo_fname = 
     LibraryMisc.obj_file_of_baseuri ~must_exist:false ~baseuri
      ~writable:true in
    let save () =
      let lexicon_fname =
       LibraryMisc.lexicon_file_of_baseuri 
         ~must_exist:false ~baseuri ~writable:true
      in
       GrafiteMarshal.save_moo moo_fname
        grafite_status.GrafiteTypes.moo_content_rev;
       LexiconMarshal.save_lexicon lexicon_fname
        lexicon_status.LexiconEngine.lexicon_content_rev
    in
     begin
       let rc = 
         MatitaGtkMisc.ask_confirmation
         ~title:"A .moo can be generated"
         ~message:(Printf.sprintf 
           "%s can be generated for %s.\n<i>Should I generate it?</i>"
           (Filename.basename moo_fname) (Filename.basename fname))
         ~parent ()
       in
       let b = 
         match rc with 
         | `YES -> true 
         | `NO -> false 
         | `CANCEL -> raise MatitaTypes.Cancel 
       in
       if b then
           save ()
       else
         clean_current_baseuri grafite_status
     end
   end
  else
    clean_current_baseuri grafite_status 
    
let ask_unsaved parent =
  MatitaGtkMisc.ask_confirmation 
    ~parent ~title:"Unsaved work!" 
    ~message:("Your work is <b>unsaved</b>!\n\n"^
         "<i>Do you want to save the script before continuing?</i>")
    ()

class interpErrorModel =
  let cols = new GTree.column_list in
  let id_col = cols#add Gobject.Data.string in
  let dsc_col = cols#add Gobject.Data.string in
  let interp_no_col = cols#add Gobject.Data.caml in
  let tree_store = GTree.tree_store cols in
  let id_renderer = GTree.cell_renderer_text [], ["text", id_col] in
  let dsc_renderer = GTree.cell_renderer_text [], ["text", dsc_col] in
  let id_view_col = GTree.view_column ~renderer:id_renderer () in
  let dsc_view_col = GTree.view_column ~renderer:dsc_renderer () in
  fun (tree_view: GTree.view) choices ->
    object
      initializer
        tree_view#set_model (Some (tree_store :> GTree.model));
        ignore (tree_view#append_column id_view_col);
        ignore (tree_view#append_column dsc_view_col);
        tree_store#clear ();
        let idx1 = ref ~-1 in
        List.iter
          (fun _,lll ->
            incr idx1;
            let loc_row =
             if List.length choices = 1 then
              None
             else
              (let loc_row = tree_store#append () in
                begin
                 match lll with
                    [passes,envs_and_diffs,_,_] ->
                      tree_store#set ~row:loc_row ~column:id_col
                       ("Error location " ^ string_of_int (!idx1+1) ^
                        ", error message " ^ string_of_int (!idx1+1) ^ ".1" ^
                        " (in passes " ^
                        String.concat " " (List.map string_of_int passes) ^
                        ")");
                      tree_store#set ~row:loc_row ~column:interp_no_col
                       (!idx1,Some 0,None);
                  | _ ->
                    tree_store#set ~row:loc_row ~column:id_col
                     ("Error location " ^ string_of_int (!idx1+1));
                    tree_store#set ~row:loc_row ~column:interp_no_col
                     (!idx1,None,None);
                end ;
                Some loc_row) in
            let idx2 = ref ~-1 in
             List.iter
              (fun passes,envs_and_diffs,_,_ ->
                incr idx2;
                let msg_row =
                 if List.length lll = 1 then
                  loc_row
                 else
                  let msg_row = tree_store#append ?parent:loc_row () in
                   (tree_store#set ~row:msg_row ~column:id_col
                     ("Error message " ^ string_of_int (!idx1+1) ^ "." ^
                      string_of_int (!idx2+1) ^
                      " (in passes " ^
                      String.concat " " (List.map string_of_int passes) ^
                      ")");
                    tree_store#set ~row:msg_row ~column:interp_no_col
                     (!idx1,Some !idx2,None);
                    Some msg_row) in
                let idx3 = ref ~-1 in
                List.iter
                 (fun (passes,env,_) ->
                   incr idx3;
                   let interp_row =
                    match envs_and_diffs with
                       _::_::_ ->
                        let interp_row = tree_store#append ?parent:msg_row () in
                        tree_store#set ~row:interp_row ~column:id_col
                          ("Interpretation " ^ string_of_int (!idx3+1) ^
                           " (in passes " ^
                           String.concat " " (List.map string_of_int passes) ^
                           ")");
                        tree_store#set ~row:interp_row ~column:interp_no_col
                         (!idx1,Some !idx2,Some !idx3);
                        Some interp_row
                     | [_] -> msg_row
                     | [] -> assert false
                   in
                    List.iter
                     (fun (_, id, dsc) ->
                       let row = tree_store#append ?parent:interp_row () in
                       tree_store#set ~row ~column:id_col id;
                       tree_store#set ~row ~column:dsc_col dsc;
                       tree_store#set ~row ~column:interp_no_col
                        (!idx1,Some !idx2,Some !idx3)
                     ) env
                 ) envs_and_diffs
              ) lll ;
             if List.length lll > 1 then
              HExtlib.iter_option
               (fun p -> tree_view#expand_row (tree_store#get_path p))
               loc_row
          ) choices

      method get_interp_no tree_path =
        let iter = tree_store#get_iter tree_path in
        tree_store#get ~row:iter ~column:interp_no_col
    end


let rec interactive_error_interp ?(all_passes=false) (source_buffer:GSourceView.source_buffer) notify_exn offset errorll
= 
  assert (List.flatten errorll <> []);
  let errorll' =
   let remove_non_significant =
     List.filter (fun (_env,_diff,_loc,_msg,significant) -> significant) in
   if all_passes then errorll else
     let safe_list_nth l n = try List.nth l n with Failure _ -> [] in
    (* We remove passes 1,2 and 5,6 *)
     let res =
      []::[]
      ::(remove_non_significant (safe_list_nth errorll 2))
      ::(remove_non_significant (safe_list_nth errorll 3))
      ::[]::[]
     in
      if List.flatten res <> [] then res
      else
       (* all errors (if any) are not significant: we keep them *)
       let res =
        []::[]
        ::(safe_list_nth errorll 2)
        ::(safe_list_nth errorll 3)
        ::[]::[]
       in
        if List.flatten res <> [] then
	 begin
          HLog.warn
	   "All disambiguation errors are not significant. Showing them anyway." ;
	  res
	 end
	else
         begin
          HLog.warn
	   "No errors in phases 2 and 3. Showing all errors in all phases" ;
          errorll
         end
   in
  let choices =
   let pass = ref 0 in
   List.flatten
    (List.map
      (fun l ->
        incr pass;
        List.map
         (fun (env,diff,offset,msg,significant) ->
           offset, [[!pass], [[!pass], env, diff], msg, significant]) l
      ) errorll') in
  (* Here we are doing a stable sort and list_uniq returns the latter
     "equal" element. I.e. we are showing the error corresponding to the
     most advanced disambiguation pass *)
  let choices =
   let choices_compare (o1,_) (o2,_) = compare o1 o2 in
   let choices_compare_by_passes (p1,_,_,_) (p2,_,_,_) =
    compare p1 p2 in
   let rec uniq =
    function
       [] -> []
     | h::[] -> [h]
     | (o1,res1)::(o2,res2)::tl when o1 = o2 ->
        let merge_by_name errors =
         let merge_by_env errors =
          let choices_compare_by_env (_,e1,_) (_,e2,_) = compare e1 e2 in
          let choices_compare_by_passes (p1,_,_) (p2,_,_) =
           compare p1 p2 in
          let rec uniq_by_env =
           function
              [] -> []
            | h::[] -> [h]
            | (p1,e1,_)::(p2,e2,d2)::tl when e1 = e2 ->
                uniq_by_env ((p1@p2,e2,d2) :: tl) 
            | h1::tl -> h1 :: uniq_by_env tl
          in
           List.sort choices_compare_by_passes
            (uniq_by_env (List.stable_sort choices_compare_by_env errors))
         in
         let choices_compare_by_msg (_,_,m1,_) (_,_,m2,_) =
          compare (Lazy.force m1) (Lazy.force m2) in
         let rec uniq_by_msg =
          function
             [] -> []
           | h::[] -> [h]
           | (p1,i1,m1,s1)::(p2,i2,m2,s2)::tl
             when Lazy.force m1 = Lazy.force m2 && s1 = s2 ->
               uniq_by_msg ((p1@p2,merge_by_env (i1@i2),m2,s2) :: tl)
           | h1::tl -> h1 :: uniq_by_msg tl
         in
          List.sort choices_compare_by_msg
           (uniq_by_msg (List.stable_sort choices_compare_by_msg errors))
        in
         let res = merge_by_name (res1@res2) in
          uniq ((o1,res) :: tl)
     | h1::tl -> h1 :: uniq tl
   in
   (* Errors in phase 3 that are not also in phase 4 are filtered out *)
   let filter_phase_3 choices =
    if all_passes then choices
    else
     let filter =
      HExtlib.filter_map
       (function
           (loffset,messages) ->
              let filtered_messages =
               HExtlib.filter_map
                (function
                    [3],_,_,_ -> None
                  | item -> Some item
                ) messages
              in
               if filtered_messages = [] then
                None
               else
                Some (loffset,filtered_messages))
     in
      filter choices
   in
    filter_phase_3
     (List.map (fun o,l -> o,List.sort choices_compare_by_passes l)
       (uniq (List.stable_sort choices_compare choices)))
  in
   match choices with
      [] -> assert false
    | [loffset,[_,envs_and_diffs,msg,significant]] ->
        let _,env,diff = List.hd envs_and_diffs in
         notify_exn
          (GrafiteDisambiguator.DisambiguationError
            (offset,[[env,diff,loffset,msg,significant]]));
    | _::_ ->
       let dialog = new disambiguationErrors () in
       dialog#check_widgets ();
       if all_passes then
        dialog#disambiguationErrorsMoreErrors#misc#set_sensitive false;
       let model = new interpErrorModel dialog#treeview choices in
       dialog#disambiguationErrors#set_title "Disambiguation error";
       dialog#disambiguationErrorsLabel#set_label
        "Click on an error to see the corresponding message:";
       ignore (dialog#treeview#connect#cursor_changed
        (fun _ ->
          let tree_path =
           match fst (dialog#treeview#get_cursor ()) with
              None -> assert false
           | Some tp -> tp in
          let idx1,idx2,idx3 = model#get_interp_no tree_path in
          let loffset,lll = List.nth choices idx1 in
          let _,envs_and_diffs,msg,significant =
           match idx2 with
              Some idx2 -> List.nth lll idx2
            | None ->
                [],[],lazy "Multiple error messages. Please select one.",true
          in
          let _,env,diff =
           match idx3 with
              Some idx3 -> List.nth envs_and_diffs idx3
            | None -> [],[],[] (* dymmy value, used *) in
          let script = MatitaScript.current () in
          let error_tag = script#error_tag in
           source_buffer#remove_tag error_tag
             ~start:source_buffer#start_iter
             ~stop:source_buffer#end_iter;
           notify_exn
            (GrafiteDisambiguator.DisambiguationError
              (offset,[[env,diff,loffset,msg,significant]]))
           ));
       let return _ =
         dialog#disambiguationErrors#destroy ();
         GMain.Main.quit ()
       in
       let fail _ = return () in
       ignore(dialog#disambiguationErrors#event#connect#delete (fun _ -> true));
       connect_button dialog#disambiguationErrorsOkButton
        (fun _ ->
          let tree_path =
           match fst (dialog#treeview#get_cursor ()) with
              None -> assert false
           | Some tp -> tp in
          let idx1,idx2,idx3 = model#get_interp_no tree_path in
          let diff =
           match idx2,idx3 with
              Some idx2, Some idx3 ->
               let _,lll = List.nth choices idx1 in
               let _,envs_and_diffs,_,_ = List.nth lll idx2 in
               let _,_,diff = List.nth envs_and_diffs idx3 in
                diff
            | _,_ -> assert false
          in
           let newtxt =
            String.concat "\n"
             ("" ::
               List.map
                (fun k,value ->
                  DisambiguatePp.pp_environment
                   (DisambiguateTypes.Environment.add k value
                     DisambiguateTypes.Environment.empty))
                diff) ^ "\n"
           in
            source_buffer#insert
             ~iter:
               (source_buffer#get_iter_at_mark
                (`NAME "beginning_of_statement")) newtxt ;
            return ()
        );
       connect_button dialog#disambiguationErrorsMoreErrors
        (fun _ -> return () ;
          interactive_error_interp ~all_passes:true source_buffer notify_exn offset
           errorll);
       connect_button dialog#disambiguationErrorsCancelButton fail;
       dialog#disambiguationErrors#show ();
       GtkThread.main ()


(** Selection handling
 * Two clipboards are used: "clipboard" and "primary".
 * "primary" is used by X, when you hit the middle button mouse is content is
 *    pasted between applications. In Matita this selection always contain the
 *    textual version of the selected term.
 * "clipboard" is used inside Matita only and support ATM two different targets:
 *    "TERM" and "PATTERN", in the future other targets like "MATHMLCONTENT" may
 *    be added
 *)

class gui () =
    (* creation order _is_ relevant for windows placement *)
  let main = new mainWin () in
  let fileSel = new fileSelectionWin () in
  let findRepl = new findReplWin () in
  let develList = new develListWin () in
  let newDevel = new newDevelWin () in
  let keyBindingBoxes = (* event boxes which should receive global key events *)
    [ main#mainWinEventBox ]
  in
  let console = new console ~buffer:main#logTextView#buffer () in
  let (source_view: GSourceView.source_view) =
    GSourceView.source_view
      ~auto_indent:true
      ~insert_spaces_instead_of_tabs:true ~tabs_width:2
      ~margin:80 ~show_margin:true
      ~smart_home_end:true
      ~packing:main#scriptScrolledWin#add
      ()
  in
  let default_font_size =
    Helm_registry.get_opt_default Helm_registry.int
      ~default:BuildTimeConf.default_font_size "matita.font_size"
  in
  let source_buffer = source_view#source_buffer in
  object (self)
    val mutable chosen_file = None
    val mutable _ok_not_exists = false
    val mutable _only_directory = false
    val mutable script_fname = None
    val mutable font_size = default_font_size
    val mutable next_devel_must_contain = None
    val mutable next_ligatures = []
    val clipboard = GData.clipboard Gdk.Atom.clipboard
    val primary = GData.clipboard Gdk.Atom.primary
   
    initializer
        (* glade's check widgets *)
      List.iter (fun w -> w#check_widgets ())
        (let c w = (w :> <check_widgets: unit -> unit>) in
        [ c fileSel; c main; c findRepl]);
        (* key bindings *)
      List.iter (* global key bindings *)
        (fun (key, callback) -> self#addKeyBinding key callback)
(*
        [ GdkKeysyms._F3,
            toggle_win ~check:main#showProofMenuItem proof#proofWin;
          GdkKeysyms._F4,
            toggle_win ~check:main#showCheckMenuItem check#checkWin;
*)
        [ ];
        (* about win *)
      let parse_txt_file file =
       let ch = open_in (BuildTimeConf.runtime_base_dir ^ "/" ^ file) in
       let l_rev = ref [] in
       try
        while true do
         l_rev := input_line ch :: !l_rev;
        done;
        assert false
       with
        End_of_file ->
         close_in ch;
         List.rev !l_rev in 
      let about_dialog =
       GWindow.about_dialog
        ~authors:(parse_txt_file "AUTHORS")
        (*~comments:"comments"*)
        ~copyright:"Copyright (C) 2005, the HELM team"
        ~license:(String.concat "\n" (parse_txt_file "LICENSE"))
        ~logo:(GdkPixbuf.from_file (MatitaMisc.image_path "/matita_medium.png"))
        ~name:"Matita"
        ~version:BuildTimeConf.version
        ~website:"http://helm.cs.unibo.it"
        ()
      in
      connect_menu_item main#contentsMenuItem (fun () ->
        let cmd =
          sprintf "gnome-help ghelp://%s/C/matita.xml &" BuildTimeConf.help_dir
        in
        ignore (Sys.command cmd));
      connect_menu_item main#aboutMenuItem about_dialog#present;
        (* findRepl win *)
      let show_find_Repl () = 
        findRepl#toplevel#misc#show ();
        findRepl#toplevel#misc#grab_focus ()
      in
      let hide_find_Repl () = findRepl#toplevel#misc#hide () in
      let find_forward _ = 
          let highlight start end_ =
            source_buffer#move_mark `INSERT ~where:start;
            source_buffer#move_mark `SEL_BOUND ~where:end_;
            source_view#scroll_mark_onscreen `INSERT
          in
          let text = findRepl#findEntry#text in
          let iter = source_buffer#get_iter `SEL_BOUND in
          match iter#forward_search text with
          | None -> 
              (match source_buffer#start_iter#forward_search text with
              | None -> ()
              | Some (start,end_) -> highlight start end_)
          | Some (start,end_) -> highlight start end_ 
      in
      let replace _ =
        let text = findRepl#replaceEntry#text in
        let ins = source_buffer#get_iter `INSERT in
        let sel = source_buffer#get_iter `SEL_BOUND in
        if ins#compare sel < 0 then 
          begin
            ignore(source_buffer#delete_selection ());
            source_buffer#insert text
          end
      in
      connect_button findRepl#findButton find_forward;
      connect_button findRepl#findReplButton replace;
      connect_button findRepl#cancelButton (fun _ -> hide_find_Repl ());
      ignore(findRepl#toplevel#event#connect#delete 
        ~callback:(fun _ -> hide_find_Repl ();true));
      let safe_undo =
       fun () ->
        (* phase 1: we save the actual status of the marks and we undo *)
        let locked_mark = `MARK ((MatitaScript.current ())#locked_mark) in
        let locked_iter = source_view#buffer#get_iter_at_mark locked_mark in
        let locked_iter_offset = locked_iter#offset in
        let mark2 =
         `MARK
           (source_view#buffer#create_mark ~name:"lock_point"
             ~left_gravity:true locked_iter) in
        source_view#source_buffer#undo ();
        (* phase 2: we save the cursor position and we redo, restoring
           the previous status of all the marks *)
        let cursor_iter = source_view#buffer#get_iter_at_mark `INSERT in
        let mark =
         `MARK
           (source_view#buffer#create_mark ~name:"undo_point"
             ~left_gravity:true cursor_iter)
        in
         source_view#source_buffer#redo ();
         let mark_iter = source_view#buffer#get_iter_at_mark mark in
         let mark2_iter = source_view#buffer#get_iter_at_mark mark2 in
         let mark2_iter = mark2_iter#set_offset locked_iter_offset in
          source_view#buffer#move_mark locked_mark ~where:mark2_iter;
          source_view#buffer#delete_mark mark;
          source_view#buffer#delete_mark mark2;
          (* phase 3: if after the undo the cursor was in the locked area,
             then we move it there again and we perform a goto *)
          if mark_iter#offset < locked_iter_offset then
           begin
            source_view#buffer#move_mark `INSERT ~where:mark_iter;
            (MatitaScript.current ())#goto `Cursor ();
           end;
          (* phase 4: we perform again the undo. This time we are sure that
             the text to undo is not locked *)
          source_view#source_buffer#undo ();
          source_view#misc#grab_focus () in
      let safe_redo =
       fun () ->
        (* phase 1: we save the actual status of the marks, we redo and
           we undo *)
        let locked_mark = `MARK ((MatitaScript.current ())#locked_mark) in
        let locked_iter = source_view#buffer#get_iter_at_mark locked_mark in
        let locked_iter_offset = locked_iter#offset in
        let mark2 =
         `MARK
           (source_view#buffer#create_mark ~name:"lock_point"
             ~left_gravity:true locked_iter) in
        source_view#source_buffer#redo ();
        source_view#source_buffer#undo ();
        (* phase 2: we save the cursor position and we restore
           the previous status of all the marks *)
        let cursor_iter = source_view#buffer#get_iter_at_mark `INSERT in
        let mark =
         `MARK
           (source_view#buffer#create_mark ~name:"undo_point"
             ~left_gravity:true cursor_iter)
        in
         let mark_iter = source_view#buffer#get_iter_at_mark mark in
         let mark2_iter = source_view#buffer#get_iter_at_mark mark2 in
         let mark2_iter = mark2_iter#set_offset locked_iter_offset in
          source_view#buffer#move_mark locked_mark ~where:mark2_iter;
          source_view#buffer#delete_mark mark;
          source_view#buffer#delete_mark mark2;
          (* phase 3: if after the undo the cursor is in the locked area,
             then we move it there again and we perform a goto *)
          if mark_iter#offset < locked_iter_offset then
           begin
            source_view#buffer#move_mark `INSERT ~where:mark_iter;
            (MatitaScript.current ())#goto `Cursor ();
           end;
          (* phase 4: we perform again the redo. This time we are sure that
             the text to redo is not locked *)
          source_view#source_buffer#redo ();
          source_view#misc#grab_focus ()
      in
      connect_menu_item main#undoMenuItem safe_undo;
      ignore(source_view#source_buffer#connect#can_undo
        ~callback:main#undoMenuItem#misc#set_sensitive);
      connect_menu_item main#redoMenuItem safe_redo;
      ignore(source_view#source_buffer#connect#can_redo
        ~callback:main#redoMenuItem#misc#set_sensitive);
      ignore(source_view#connect#after#populate_popup
       ~callback:(fun pre_menu ->
         let menu = new GMenu.menu pre_menu in
         let menuItems = menu#children in
         let undoMenuItem, redoMenuItem =
          match menuItems with
             [undo;redo;sep1;cut;copy;paste;delete;sep2;
              selectall;sep3;inputmethod;insertunicodecharacter] ->
                List.iter menu#remove [ copy; cut; delete; paste ];
                undo,redo
           | _ -> assert false in
         let add_menu_item =
           let i = ref 2 in (* last occupied position *)
           fun ?label ?stock () ->
             incr i;
             GMenu.image_menu_item ?label ?stock ~packing:(menu#insert ~pos:!i)
              ()
         in
         let copy = add_menu_item ~stock:`COPY () in
         let cut = add_menu_item ~stock:`CUT () in
         let delete = add_menu_item ~stock:`DELETE () in
         let paste = add_menu_item ~stock:`PASTE () in
         let paste_pattern = add_menu_item ~label:"Paste as pattern" () in
         copy#misc#set_sensitive self#canCopy;
         cut#misc#set_sensitive self#canCut;
         delete#misc#set_sensitive self#canDelete;
         paste#misc#set_sensitive self#canPaste;
         paste_pattern#misc#set_sensitive self#canPastePattern;
         connect_menu_item copy self#copy;
         connect_menu_item cut self#cut;
         connect_menu_item delete self#delete;
         connect_menu_item paste self#paste;
         connect_menu_item paste_pattern self#pastePattern;
         let new_undoMenuItem =
          GMenu.image_menu_item
           ~image:(GMisc.image ~stock:`UNDO ())
           ~use_mnemonic:true
           ~label:"_Undo"
           ~packing:(menu#insert ~pos:0) () in
         new_undoMenuItem#misc#set_sensitive
          (undoMenuItem#misc#get_flag `SENSITIVE);
         menu#remove (undoMenuItem :> GMenu.menu_item);
         connect_menu_item new_undoMenuItem safe_undo;
         let new_redoMenuItem =
          GMenu.image_menu_item
           ~image:(GMisc.image ~stock:`REDO ())
           ~use_mnemonic:true
           ~label:"_Redo"
           ~packing:(menu#insert ~pos:1) () in
         new_redoMenuItem#misc#set_sensitive
          (redoMenuItem#misc#get_flag `SENSITIVE);
          menu#remove (redoMenuItem :> GMenu.menu_item);
          connect_menu_item new_redoMenuItem safe_redo));

      connect_menu_item main#editMenu (fun () ->
        main#copyMenuItem#misc#set_sensitive self#canCopy;
        main#cutMenuItem#misc#set_sensitive self#canCut;
        main#deleteMenuItem#misc#set_sensitive self#canDelete;
        main#pasteMenuItem#misc#set_sensitive self#canPaste;
        main#pastePatternMenuItem#misc#set_sensitive self#canPastePattern);
      connect_menu_item main#copyMenuItem self#copy;
      connect_menu_item main#cutMenuItem self#cut;
      connect_menu_item main#deleteMenuItem self#delete;
      connect_menu_item main#pasteMenuItem self#paste;
      connect_menu_item main#pastePatternMenuItem self#pastePattern;
      connect_menu_item main#selectAllMenuItem (fun () ->
        source_buffer#move_mark `INSERT source_buffer#start_iter;
        source_buffer#move_mark `SEL_BOUND source_buffer#end_iter);
      connect_menu_item main#findReplMenuItem show_find_Repl;
      connect_menu_item main#externalEditorMenuItem self#externalEditor;
      connect_menu_item main#ligatureButton self#nextLigature;
      ignore (findRepl#findEntry#connect#activate find_forward);
        (* interface lockers *)
      let lock_world _ =
        main#buttonsToolbar#misc#set_sensitive false;
        develList#buttonsHbox#misc#set_sensitive false;
        main#scriptMenu#misc#set_sensitive false;
        source_view#set_editable false
      in
      let unlock_world _ =
        main#buttonsToolbar#misc#set_sensitive true;
        develList#buttonsHbox#misc#set_sensitive true;
        main#scriptMenu#misc#set_sensitive true;
        source_view#set_editable true;
        (*The next line seems sufficient to avoid some unknown race condition *)
        GtkThread.sync (fun () -> ()) ()
      in
      let worker_thread = ref None in
      let notify_exn exn =
       let floc, msg = MatitaExcPp.to_string exn in
        begin
         match floc with
            None -> ()
          | Some floc ->
             let (x, y) = HExtlib.loc_of_floc floc in
             let script = MatitaScript.current () in
             let locked_mark = script#locked_mark in
             let error_tag = script#error_tag in
             let baseoffset =
              (source_buffer#get_iter_at_mark (`MARK locked_mark))#offset in
             let x' = baseoffset + x in
             let y' = baseoffset + y in
             let x_iter = source_buffer#get_iter (`OFFSET x') in
             let y_iter = source_buffer#get_iter (`OFFSET y') in
             source_buffer#apply_tag error_tag ~start:x_iter ~stop:y_iter;
             let id = ref None in
             id := Some (source_buffer#connect#changed ~callback:(fun () ->
               source_buffer#remove_tag error_tag
                 ~start:source_buffer#start_iter
                 ~stop:source_buffer#end_iter;
               match !id with
               | None -> assert false (* a race condition occurred *)
               | Some id ->
                   (new GObj.gobject_ops source_buffer#as_buffer)#disconnect id));
             source_buffer#place_cursor
              (source_buffer#get_iter (`OFFSET x'));
        end;
        HLog.error msg in
      let locker f () =
       let thread_main =
        fun () -> 
          lock_world ();
          try
           f ();
           unlock_world ()
          with
           | GrafiteDisambiguator.DisambiguationError (offset,errorll) ->
              (try
                interactive_error_interp source_buffer notify_exn offset
                 errorll
               with
                exc -> notify_exn exc);
              unlock_world ()
           | exc ->
              notify_exn exc;
              unlock_world ()
       in
        worker_thread := Some (Thread.create thread_main ()) in
      let kill_worker =
       (* the following lines are from Xavier Leroy: http://alan.petitepomme.net/cwn/2005.11.08.html *)
       let interrupt = ref None in
       let old_callback = ref (function _ -> ()) in
       let force_interrupt n =
         (* This function is called just before the thread's timeslice ends *)
         !old_callback n;
         if Some(Thread.id(Thread.self())) = !interrupt then
          (interrupt := None; raise Sys.Break) in
       let _ =
        match Sys.signal Sys.sigvtalrm (Sys.Signal_handle force_interrupt) with
           Sys.Signal_handle f -> old_callback := f
         | Sys.Signal_ignore
         | Sys.Signal_default -> assert false
       in
        fun () ->
         match !worker_thread with
            None -> assert false
          | Some t -> interrupt := Some (Thread.id t) in
      let keep_focus f =
        fun () ->
         try
          f (); source_view#misc#grab_focus ()
         with
          exc -> source_view#misc#grab_focus (); raise exc in
        (* developments win *)
      let model = 
        new MatitaGtkMisc.multiStringListModel 
          ~cols:2 develList#developmentsTreeview
      in
      let refresh_devels_win () =
        model#list_store#clear ();
        List.iter 
          (fun (name, root) -> model#easy_mappend [name;root]) 
          (MatitamakeLib.list_known_developments ())
      in
      let get_devel_selected () = 
        match model#easy_mselection () with
        | [[name;_]] -> MatitamakeLib.development_for_name name
        | _ -> None
      in
      let refresh () = 
        while Glib.Main.pending () do 
          ignore(Glib.Main.iteration false); 
        done
      in
      connect_button develList#newButton
        (fun () -> 
          next_devel_must_contain <- None;
          newDevel#toplevel#misc#show());
      connect_button develList#deleteButton
        (locker (fun () -> 
          (match get_devel_selected () with
          | None -> ()
          | Some d -> MatitamakeLib.destroy_development_in_bg refresh d);
          refresh_devels_win ()));
      connect_button develList#buildButton 
        (locker (fun () -> 
          match get_devel_selected () with
          | None -> ()
          | Some d -> 
              let build = locker 
                (fun () -> MatitamakeLib.build_development_in_bg refresh d)
              in
              ignore(build ())));
      connect_button develList#cleanButton 
        (locker (fun () -> 
          match get_devel_selected () with
          | None -> ()
          | Some d -> 
              let clean = locker 
                (fun () -> MatitamakeLib.clean_development_in_bg refresh d)
              in
              ignore(clean ())));
      connect_button develList#publishButton 
        (locker (fun () -> 
          match get_devel_selected () with
          | None -> ()
          | Some d -> 
              let publish = locker (fun () ->
                MatitamakeLib.publish_development_in_bg refresh d) in
              ignore(publish ())));
      connect_button develList#graphButton (fun () -> 
        match get_devel_selected () with
        | None -> ()
        | Some d ->
            (match MatitamakeLib.dot_for_development d with
            | None -> ()
            | Some _ ->
                let browser = MatitaMathView.cicBrowser () in
                browser#load (`Development
                  (MatitamakeLib.name_for_development d))));
      connect_button develList#closeButton 
        (fun () -> develList#toplevel#misc#hide());
      ignore(develList#toplevel#event#connect#delete 
        (fun _ -> develList#toplevel#misc#hide();true));
      connect_menu_item main#developmentsMenuItem
        (fun () -> refresh_devels_win ();develList#toplevel#misc#show ());
      
        (* add development win *)
      let check_if_root_contains root =
        match next_devel_must_contain with
        | None -> true
        | Some path -> 
            let is_prefix_of d1 d2 =
              let len1 = String.length d1 in
              let len2 = String.length d2 in
              if len2 < len1 then 
                false
              else
                let pref = String.sub d2 0 len1 in
                pref = d1
            in
            is_prefix_of root path
      in
      connect_button newDevel#addButton 
       (fun () -> 
          let name = newDevel#nameEntry#text in
          let root = newDevel#rootEntry#text in
          if check_if_root_contains root then
            begin
              ignore (MatitamakeLib.initialize_development name root);
              refresh_devels_win ();
              newDevel#nameEntry#set_text "";
              newDevel#rootEntry#set_text "";
              newDevel#toplevel#misc#hide()
            end
          else
            HLog.error ("The selected root does not contain " ^ 
              match next_devel_must_contain with 
              | Some x -> x 
              | _ -> assert false));
      connect_button newDevel#chooseRootButton 
       (fun () ->
         let path = self#chooseDir () in
         match path with
         | Some path -> newDevel#rootEntry#set_text path
         | None -> ());
      connect_button newDevel#cancelButton 
       (fun () -> newDevel#toplevel#misc#hide ());
      ignore(newDevel#toplevel#event#connect#delete 
        (fun _ -> newDevel#toplevel#misc#hide();true));
      
        (* file selection win *)
      ignore (fileSel#fileSelectionWin#event#connect#delete (fun _ -> true));
      ignore (fileSel#fileSelectionWin#connect#response (fun event ->
        let return r =
          chosen_file <- r;
          fileSel#fileSelectionWin#misc#hide ();
          GMain.Main.quit ()
        in
        match event with
        | `OK ->
            let fname = fileSel#fileSelectionWin#filename in
            if Sys.file_exists fname then
              begin
                if HExtlib.is_regular fname && not (_only_directory) then 
                  return (Some fname) 
                else if _only_directory && HExtlib.is_dir fname then 
                  return (Some fname)
              end
            else
              begin
                if _ok_not_exists then 
                  return (Some fname)
              end
        | `CANCEL -> return None
        | `HELP -> ()
        | `DELETE_EVENT -> return None));
        (* menus *)
      List.iter (fun w -> w#misc#set_sensitive false) [ main#saveMenuItem ];
        (* console *)
      let adj = main#logScrolledWin#vadjustment in
        ignore (adj#connect#changed
                (fun _ -> adj#set_value (adj#upper -. adj#page_size)));
      console#message (sprintf "\tMatita version %s\n" BuildTimeConf.version);
        (* toolbar *)
      let module A = GrafiteAst in
      let hole = CicNotationPt.UserInput in
      let loc = HExtlib.dummy_floc in
      let tac ast _ =
        if (MatitaScript.current ())#onGoingProof () then
          (MatitaScript.current ())#advance
            ~statement:("\n"
              ^ GrafiteAstPp.pp_tactic ~term_pp:CicNotationPp.pp_term
                ~lazy_term_pp:CicNotationPp.pp_term ast)
            ()
      in
      let tac_w_term ast _ =
        if (MatitaScript.current ())#onGoingProof () then
          let buf = source_buffer in
          buf#insert ~iter:(buf#get_iter_at_mark (`NAME "locked"))
            ("\n"
            ^ GrafiteAstPp.pp_tactic ~term_pp:CicNotationPp.pp_term
              ~lazy_term_pp:CicNotationPp.pp_term ast)
      in
      let tbar = main in
      connect_button tbar#introsButton (tac (A.Intros (loc, (None, []))));
      connect_button tbar#applyButton (tac_w_term (A.Apply (loc, hole)));
      connect_button tbar#exactButton (tac_w_term (A.Exact (loc, hole)));
      connect_button tbar#elimButton (tac_w_term
        (let pattern = None, [], Some CicNotationPt.UserInput in
	A.Elim (loc, hole, None, pattern, (None, []))));
      connect_button tbar#elimTypeButton (tac_w_term
        (A.ElimType (loc, hole, None, (None, []))));
      connect_button tbar#splitButton (tac (A.Split loc));
      connect_button tbar#leftButton (tac (A.Left loc));
      connect_button tbar#rightButton (tac (A.Right loc));
      connect_button tbar#existsButton (tac (A.Exists loc));
      connect_button tbar#reflexivityButton (tac (A.Reflexivity loc));
      connect_button tbar#symmetryButton (tac (A.Symmetry loc));
      connect_button tbar#transitivityButton
        (tac_w_term (A.Transitivity (loc, hole)));
      connect_button tbar#assumptionButton (tac (A.Assumption loc));
      connect_button tbar#cutButton (tac_w_term (A.Cut (loc, None, hole)));
      connect_button tbar#autoButton (tac (A.AutoBatch (loc,[])));
      MatitaGtkMisc.toggle_widget_visibility
       ~widget:(main#tacticsButtonsHandlebox :> GObj.widget)
       ~check:main#tacticsBarMenuItem;
      let module Hr = Helm_registry in
      if
        not (Hr.get_opt_default Hr.bool ~default:false "matita.tactics_bar")
      then 
        main#tacticsBarMenuItem#set_active false;
      MatitaGtkMisc.toggle_callback ~check:main#fullscreenMenuItem
        ~callback:(function 
          | true -> main#toplevel#fullscreen () 
          | false -> main#toplevel#unfullscreen ());
      main#fullscreenMenuItem#set_active false;
      MatitaGtkMisc.toggle_callback ~check:main#ppNotationMenuItem
        ~callback:(function
          | true ->
              CicNotation.set_active_notations
                (List.map fst (CicNotation.get_all_notations ()))
          | false ->
              CicNotation.set_active_notations []);
      MatitaGtkMisc.toggle_callback ~check:main#hideCoercionsMenuItem
        ~callback:(fun enabled -> Acic2content.hide_coercions := enabled);
      MatitaGtkMisc.toggle_callback ~check:main#unicodeAsTexMenuItem
        ~callback:(fun enabled ->
          Helm_registry.set_bool "matita.paste_unicode_as_tex" enabled);
      if not (Helm_registry.has "matita.paste_unicode_as_tex") then
        Helm_registry.set_bool "matita.paste_unicode_as_tex" true;
      main#unicodeAsTexMenuItem#set_active
        (Helm_registry.get_bool "matita.paste_unicode_as_tex");
        (* log *)
      HLog.set_log_callback self#console#log_callback;
      GtkSignal.user_handler :=
        (function 
        | MatitaScript.ActionCancelled s -> HLog.error s
        | exn ->
          if not (Helm_registry.get_bool "matita.debug") then
           notify_exn exn
          else raise exn);
        (* script *)
      ignore (source_buffer#connect#mark_set (fun _ _ -> next_ligatures <- []));
      let _ =
        match GSourceView.source_language_from_file BuildTimeConf.lang_file with
        | None ->
            HLog.warn (sprintf "can't load language file %s"
              BuildTimeConf.lang_file)
        | Some matita_lang ->
            source_buffer#set_language matita_lang;
            source_buffer#set_highlight true
      in
      let s () = MatitaScript.current () in
      let disableSave () =
        script_fname <- None;
        main#saveMenuItem#misc#set_sensitive false
      in
      let saveAsScript () =
        let script = s () in
        match self#chooseFile ~ok_not_exists:true () with
        | Some f -> 
              script#assignFileName f;
              script#saveToFile (); 
              console#message ("'"^f^"' saved.\n");
              self#_enableSaveTo f
        | None -> ()
      in
      let saveScript () =
        match script_fname with
        | None -> saveAsScript ()
        | Some f -> 
              (s ())#assignFileName f;
              (s ())#saveToFile ();
              console#message ("'"^f^"' saved.\n");
      in
      let abandon_script () =
        let lexicon_status = (s ())#lexicon_status in
        let grafite_status = (s ())#grafite_status in
        if source_view#buffer#modified then
          (match ask_unsaved main#toplevel with
          | `YES -> saveScript ()
          | `NO -> ()
          | `CANCEL -> raise MatitaTypes.Cancel);
        (match script_fname with
        | None -> ()
        | Some fname ->
           ask_and_save_moo_if_needed main#toplevel fname
            lexicon_status grafite_status);
      in
      let loadScript () =
        let script = s () in 
        try 
          match self#chooseFile () with
          | Some f -> 
              abandon_script ();
              script#reset (); 
              script#assignFileName f;
              source_view#source_buffer#begin_not_undoable_action ();
              script#loadFromFile f; 
              source_view#source_buffer#end_not_undoable_action ();
              console#message ("'"^f^"' loaded.\n");
              self#_enableSaveTo f
          | None -> ()
        with MatitaTypes.Cancel -> ()
      in
      let newScript () = 
        abandon_script ();
        source_view#source_buffer#begin_not_undoable_action ();
        (s ())#reset (); 
        (s ())#template (); 
        source_view#source_buffer#end_not_undoable_action ();
        disableSave ();
        script_fname <- None
      in
      let cursor () =
        source_buffer#place_cursor
          (source_buffer#get_iter_at_mark (`NAME "locked")) in
      let advance _ = (MatitaScript.current ())#advance (); cursor () in
      let retract _ = (MatitaScript.current ())#retract (); cursor () in
      let top _ = (MatitaScript.current ())#goto `Top (); cursor () in
      let bottom _ = (MatitaScript.current ())#goto `Bottom (); cursor () in
      let jump _ = (MatitaScript.current ())#goto `Cursor (); cursor () in
      let advance = locker (keep_focus advance) in
      let retract = locker (keep_focus retract) in
      let top = locker (keep_focus top) in
      let bottom = locker (keep_focus bottom) in
      let jump = locker (keep_focus jump) in
        (* quit *)
      self#setQuitCallback (fun () -> 
        let lexicon_status = (MatitaScript.current ())#lexicon_status in
        let grafite_status = (MatitaScript.current ())#grafite_status in
        if source_view#buffer#modified then
          begin
            let rc = ask_unsaved main#toplevel in 
            try
              match rc with
              | `YES -> saveScript ();
                        if not source_view#buffer#modified then
                          begin
                            (match script_fname with
                            | None -> ()
                            | Some fname -> 
                               ask_and_save_moo_if_needed main#toplevel
                                fname lexicon_status grafite_status);
                          GMain.Main.quit ()
                          end
              | `NO -> GMain.Main.quit ()
              | `CANCEL -> raise MatitaTypes.Cancel
            with MatitaTypes.Cancel -> ()
          end 
        else 
          begin  
            (match script_fname with
            | None -> clean_current_baseuri grafite_status; GMain.Main.quit ()
            | Some fname ->
                try
                  ask_and_save_moo_if_needed main#toplevel fname lexicon_status
                   grafite_status;
                  GMain.Main.quit ()
                with MatitaTypes.Cancel -> ())
          end);
      connect_button main#scriptAdvanceButton advance;
      connect_button main#scriptRetractButton retract;
      connect_button main#scriptTopButton top;
      connect_button main#scriptBottomButton bottom;
      connect_button main#scriptJumpButton jump;
      connect_button main#scriptAbortButton kill_worker;
      connect_menu_item main#scriptAdvanceMenuItem advance;
      connect_menu_item main#scriptRetractMenuItem retract;
      connect_menu_item main#scriptTopMenuItem top;
      connect_menu_item main#scriptBottomMenuItem bottom;
      connect_menu_item main#scriptJumpMenuItem jump;
      connect_menu_item main#openMenuItem   loadScript;
      connect_menu_item main#saveMenuItem   saveScript;
      connect_menu_item main#saveAsMenuItem saveAsScript;
      connect_menu_item main#newMenuItem    newScript;
         (* script monospace font stuff *)  
      self#updateFontSize ();
        (* debug menu *)
      main#debugMenu#misc#hide ();
        (* status bar *)
      main#hintLowImage#set_file (image_path "matita-bulb-low.png");
      main#hintMediumImage#set_file (image_path "matita-bulb-medium.png");
      main#hintHighImage#set_file (image_path "matita-bulb-high.png");
        (* focus *)
      self#sourceView#misc#grab_focus ();
        (* main win dimension *)
      let width = Gdk.Screen.width () in
      let height = Gdk.Screen.height () in
      let main_w = width * 90 / 100 in 
      let main_h = height * 80 / 100 in
      let script_w = main_w * 6 / 10 in
      main#toplevel#resize ~width:main_w ~height:main_h;
      main#hpaneScriptSequent#set_position script_w;
        (* source_view *)
      ignore(source_view#connect#after#paste_clipboard 
        ~callback:(fun () -> (MatitaScript.current ())#clean_dirty_lock));
      (* clean_locked is set to true only "during" a PRIMARY paste
         operation (i.e. by clicking with the second mouse button) *)
      let clean_locked = ref false in
      ignore(source_view#event#connect#button_press
        ~callback:
          (fun button ->
            if GdkEvent.Button.button button = 2 then
             clean_locked := true;
            false
          ));
      ignore(source_view#event#connect#button_release
        ~callback:(fun button -> clean_locked := false; false));
      ignore(source_view#buffer#connect#after#apply_tag
       ~callback:(
         fun tag ~start:_ ~stop:_ ->
          if !clean_locked &&
             tag#get_oid = (MatitaScript.current ())#locked_tag#get_oid
          then
           begin
            clean_locked := false;
            (MatitaScript.current ())#clean_dirty_lock;
            clean_locked := true
           end));
      (* math view handling *)
      connect_menu_item main#newCicBrowserMenuItem (fun () ->
        ignore (MatitaMathView.cicBrowser ()));
      connect_menu_item main#increaseFontSizeMenuItem (fun () ->
        self#increaseFontSize ();
        MatitaMathView.increase_font_size ();
        MatitaMathView.update_font_sizes ());
      connect_menu_item main#decreaseFontSizeMenuItem (fun () ->
        self#decreaseFontSize ();
        MatitaMathView.decrease_font_size ();
        MatitaMathView.update_font_sizes ());
      connect_menu_item main#normalFontSizeMenuItem (fun () ->
        self#resetFontSize ();
        MatitaMathView.reset_font_size ();
        MatitaMathView.update_font_sizes ());
      MatitaMathView.reset_font_size ();

      (** selections / clipboards handling *)

    method markupSelected = MatitaMathView.has_selection ()
    method private textSelected =
      (source_buffer#get_iter_at_mark `INSERT)#compare
        (source_buffer#get_iter_at_mark `SEL_BOUND) <> 0
    method private somethingSelected = self#markupSelected || self#textSelected
    method private markupStored = MatitaMathView.has_clipboard ()
    method private textStored = clipboard#text <> None
    method private somethingStored = self#markupStored || self#textStored

    method canCopy = self#somethingSelected
    method canCut = self#textSelected
    method canDelete = self#textSelected
    method canPaste = self#somethingStored
    method canPastePattern = self#markupStored

    method copy () =
      if self#textSelected
      then begin
        MatitaMathView.empty_clipboard ();
        source_view#buffer#copy_clipboard clipboard;
      end else
        MatitaMathView.copy_selection ()
    method cut () =
      source_view#buffer#cut_clipboard clipboard;
      MatitaMathView.empty_clipboard ()
    method delete () = ignore (source_view#buffer#delete_selection ())
    method paste () =
      if MatitaMathView.has_clipboard ()
      then source_view#buffer#insert (MatitaMathView.paste_clipboard `Term)
      else source_view#buffer#paste_clipboard clipboard;
      (MatitaScript.current ())#clean_dirty_lock
    method pastePattern () =
      source_view#buffer#insert (MatitaMathView.paste_clipboard `Pattern)
    
    method private nextLigature () =
      let iter = source_buffer#get_iter_at_mark `INSERT in
      let write_ligature len s =
        assert(Glib.Utf8.validate s);
        source_buffer#delete ~start:iter ~stop:(iter#copy#backward_chars len);
        source_buffer#insert ~iter:(source_buffer#get_iter_at_mark `INSERT) s
      in
      let get_ligature word =
        let len = String.length word in
        let aux_tex () =
          try
            for i = len - 1 downto 0 do
              if HExtlib.is_alpha word.[i] then ()
              else
                (if word.[i] = '\\' then raise (Found i) else raise (Found ~-1))
            done;
            None
          with Found i ->
            if i = ~-1 then None else Some (String.sub word i (len - i))
        in
        let aux_ligature () =
          try
            for i = len - 1 downto 0 do
              if CicNotationLexer.is_ligature_char word.[i] then ()
              else raise (Found (i+1))
            done;
            raise (Found 0)
          with
          | Found i ->
              (try
                Some (String.sub word i (len - i))
              with Invalid_argument _ -> None)
        in
        match aux_tex () with
        | Some macro -> macro
        | None -> (match aux_ligature () with Some l -> l | None -> word)
      in
      (match next_ligatures with
      | [] -> (* find ligatures and fill next_ligatures, then try again *)
          let last_word =
            iter#get_slice
              ~stop:(iter#copy#backward_find_char Glib.Unichar.isspace)
          in
          let ligature = get_ligature last_word in
          (match CicNotationLexer.lookup_ligatures ligature with
          | [] -> ()
          | hd :: tl ->
              write_ligature (MatitaGtkMisc.utf8_string_length ligature) hd;
              next_ligatures <- tl @ [ hd ])
      | hd :: tl ->
          write_ligature 1 hd;
          next_ligatures <- tl @ [ hd ])

    method private externalEditor () =
      let cmd = Helm_registry.get "matita.external_editor" in
(* ZACK uncomment to enable interactive ask of external editor command *)
(*      let cmd =
         let msg =
          "External editor command:
%f  will be substitute for the script name,
%p  for the cursor position in bytes,
%l  for the execution point in bytes."
        in
        ask_text ~gui:self ~title:"External editor" ~msg ~multiline:false
          ~default:(Helm_registry.get "matita.external_editor") ()
      in *)
      let fname = (MatitaScript.current ())#filename in
      let slice mark =
        source_buffer#start_iter#get_slice
          ~stop:(source_buffer#get_iter_at_mark mark)
      in
      let script = MatitaScript.current () in
      let locked = `MARK script#locked_mark in
      let string_pos mark = string_of_int (String.length (slice mark)) in
      let cursor_pos = string_pos `INSERT in
      let locked_pos = string_pos locked in
      let cmd =
        Pcre.replace ~pat:"%f" ~templ:fname
          (Pcre.replace ~pat:"%p" ~templ:cursor_pos
            (Pcre.replace ~pat:"%l" ~templ:locked_pos
              cmd))
      in
      let locked_before = slice locked in
      let locked_offset = (source_buffer#get_iter_at_mark locked)#offset in
      ignore (Unix.system cmd);
      source_buffer#set_text (HExtlib.input_file fname);
      let locked_iter = source_buffer#get_iter (`OFFSET locked_offset) in
      source_buffer#move_mark locked locked_iter;
      source_buffer#apply_tag script#locked_tag
        ~start:source_buffer#start_iter ~stop:locked_iter;
      let locked_after = slice locked in
      let line = ref 0 in
      let col = ref 0 in
      try
        for i = 0 to String.length locked_before - 1 do
          if locked_before.[i] <> locked_after.[i] then begin
            source_buffer#place_cursor
              ~where:(source_buffer#get_iter (`LINEBYTE (!line, !col)));
            script#goto `Cursor ();
            raise Exit
          end else if locked_before.[i] = '\n' then begin
            incr line;
            col := 0
          end
        done
      with
      | Exit -> ()
      | Invalid_argument _ -> script#goto `Bottom ()

    method loadScript file =       
      let script = MatitaScript.current () in
      script#reset (); 
      if Pcre.pmatch ~pat:"\\.p$" file then
        begin
          let tptppath = 
            Helm_registry.get_opt_default Helm_registry.string ~default:"./"
              "matita.tptppath"
          in
          let data = Matitaprover.p_to_ma ~filename:file ~tptppath () in
          let filename = Pcre.replace ~pat:"\\.p$" ~templ:".ma" file in
          script#assignFileName filename;
          source_view#source_buffer#begin_not_undoable_action ();
          script#loadFromString data;
          source_view#source_buffer#end_not_undoable_action ();
          console#message ("'"^filename^"' loaded.");
          self#_enableSaveTo filename
        end
      else
        begin
          script#assignFileName file;
          let content =
           if Sys.file_exists file then file
           else BuildTimeConf.script_template
          in
           source_view#source_buffer#begin_not_undoable_action ();
           script#loadFromFile content;
           source_view#source_buffer#end_not_undoable_action ();
           console#message ("'"^file^"' loaded.");
           self#_enableSaveTo file
        end
      
    method setStar name b =
      let l = main#scriptLabel in
      if b then
        l#set_text (name ^  " *")
      else
        l#set_text (name)
        
    method private _enableSaveTo file =
      script_fname <- Some file;
      self#main#saveMenuItem#misc#set_sensitive true
        
    method console = console
    method sourceView: GSourceView.source_view =
      (source_view: GSourceView.source_view)
    method fileSel = fileSel
    method findRepl = findRepl
    method main = main
    method develList = develList
    method newDevel = newDevel

    method newBrowserWin () =
      object (self)
        inherit browserWin ()
        val combo = GEdit.combo_box_entry ()
        initializer
          self#check_widgets ();
          let combo_widget = combo#coerce in
          uriHBox#pack ~from:`END ~fill:true ~expand:true combo_widget;
          combo#entry#misc#grab_focus ()
        method browserUri = combo
      end

    method newUriDialog () =
      let dialog = new uriChoiceDialog () in
      dialog#check_widgets ();
      dialog

    method newConfirmationDialog () =
      let dialog = new confirmationDialog () in
      dialog#check_widgets ();
      dialog

    method newEmptyDialog () =
      let dialog = new emptyDialog () in
      dialog#check_widgets ();
      dialog

    method private addKeyBinding key callback =
      List.iter (fun evbox -> add_key_binding key callback evbox)
        keyBindingBoxes

    method setQuitCallback callback =
      connect_menu_item main#quitMenuItem callback;
      ignore (main#toplevel#event#connect#delete 
        (fun _ -> callback ();true));
      self#addKeyBinding GdkKeysyms._q callback

    method chooseFile ?(ok_not_exists = false) () =
      _ok_not_exists <- ok_not_exists;
      _only_directory <- false;
      fileSel#fileSelectionWin#show ();
      GtkThread.main ();
      chosen_file

    method private chooseDir ?(ok_not_exists = false) () =
      _ok_not_exists <- ok_not_exists;
      _only_directory <- true;
      fileSel#fileSelectionWin#show ();
      GtkThread.main ();
      (* we should check that this is a directory *)
      chosen_file
  
    method createDevelopment ~containing =
      next_devel_must_contain <- containing;
      newDevel#toplevel#misc#show()

    method askText ?(title = "") ?(msg = "") () =
      let dialog = new textDialog () in
      dialog#textDialog#set_title title;
      dialog#textDialogLabel#set_label msg;
      let text = ref None in
      let return v =
        text := v;
        dialog#textDialog#destroy ();
        GMain.Main.quit ()
      in
      ignore (dialog#textDialog#event#connect#delete (fun _ -> true));
      connect_button dialog#textDialogCancelButton (fun _ -> return None);
      connect_button dialog#textDialogOkButton (fun _ ->
        let text = dialog#textDialogTextView#buffer#get_text () in
        return (Some text));
      dialog#textDialog#show ();
      GtkThread.main ();
      !text

    method private updateFontSize () =
      self#sourceView#misc#modify_font_by_name
        (sprintf "%s %d" BuildTimeConf.script_font font_size)

    method increaseFontSize () =
      font_size <- font_size + 1;
      self#updateFontSize ()

    method decreaseFontSize () =
      font_size <- font_size - 1;
      self#updateFontSize ()

    method resetFontSize () =
      font_size <- default_font_size;
      self#updateFontSize ()

  end

let gui () = 
  let g = new gui () in
  gui_instance := Some g;
  MatitaMathView.set_gui g;
  g
  
let instance = singleton gui

let non p x = not (p x)

(* this is a shit and should be changed :-{ *)
let interactive_uri_choice
  ?(selection_mode:[`SINGLE|`MULTIPLE] = `MULTIPLE) ?(title = "")
  ?(msg = "") ?(nonvars_button = false) ?(hide_uri_entry=false) 
  ?(hide_try=false) ?(ok_label="_Auto") ?(ok_action:[`SELECT|`AUTO] = `AUTO) 
  ?copy_cb ()
  ~id uris
=
  let gui = instance () in
  let nonvars_uris = lazy (List.filter (non UriManager.uri_is_var) uris) in
  if (selection_mode <> `SINGLE) &&
    (Helm_registry.get_opt_default Helm_registry.get_bool ~default:true "matita.auto_disambiguation")
  then
    Lazy.force nonvars_uris
  else begin
    let dialog = gui#newUriDialog () in
    if hide_uri_entry then
      dialog#uriEntryHBox#misc#hide ();
    if hide_try then
      begin
      dialog#uriChoiceSelectedButton#misc#hide ();
      dialog#uriChoiceConstantsButton#misc#hide ();
      end;
    dialog#okLabel#set_label ok_label;  
    dialog#uriChoiceTreeView#selection#set_mode
      (selection_mode :> Gtk.Tags.selection_mode);
    let model = new stringListModel dialog#uriChoiceTreeView in
    let choices = ref None in
    (match copy_cb with
    | None -> ()
    | Some cb ->
        dialog#copyButton#misc#show ();
        connect_button dialog#copyButton 
        (fun _ ->
          match model#easy_selection () with
          | [u] -> (cb u)
          | _ -> ()));
    dialog#uriChoiceDialog#set_title title;
    dialog#uriChoiceLabel#set_text msg;
    List.iter model#easy_append (List.map UriManager.string_of_uri uris);
    dialog#uriChoiceConstantsButton#misc#set_sensitive nonvars_button;
    let return v =
      choices := v;
      dialog#uriChoiceDialog#destroy ();
      GMain.Main.quit ()
    in
    ignore (dialog#uriChoiceDialog#event#connect#delete (fun _ -> true));
    connect_button dialog#uriChoiceConstantsButton (fun _ ->
      return (Some (Lazy.force nonvars_uris)));
    if ok_action = `AUTO then
      connect_button dialog#uriChoiceAutoButton (fun _ ->
        Helm_registry.set_bool "matita.auto_disambiguation" true;
        return (Some (Lazy.force nonvars_uris)))
    else
      connect_button dialog#uriChoiceAutoButton (fun _ ->
        match model#easy_selection () with
        | [] -> ()
        | uris -> return (Some (List.map UriManager.uri_of_string uris)));
    connect_button dialog#uriChoiceSelectedButton (fun _ ->
      match model#easy_selection () with
      | [] -> ()
      | uris -> return (Some (List.map UriManager.uri_of_string uris)));
    connect_button dialog#uriChoiceAbortButton (fun _ -> return None);
    dialog#uriChoiceDialog#show ();
    GtkThread.main ();
    (match !choices with 
    | None -> raise MatitaTypes.Cancel
    | Some uris -> uris)
  end

class interpModel =
  let cols = new GTree.column_list in
  let id_col = cols#add Gobject.Data.string in
  let dsc_col = cols#add Gobject.Data.string in
  let interp_no_col = cols#add Gobject.Data.int in
  let tree_store = GTree.tree_store cols in
  let id_renderer = GTree.cell_renderer_text [], ["text", id_col] in
  let dsc_renderer = GTree.cell_renderer_text [], ["text", dsc_col] in
  let id_view_col = GTree.view_column ~renderer:id_renderer () in
  let dsc_view_col = GTree.view_column ~renderer:dsc_renderer () in
  fun tree_view choices ->
    object
      initializer
        tree_view#set_model (Some (tree_store :> GTree.model));
        ignore (tree_view#append_column id_view_col);
        ignore (tree_view#append_column dsc_view_col);
        let name_of_interp =
          (* try to find a reasonable name for an interpretation *)
          let idx = ref 0 in
          fun interp ->
            try
              List.assoc "0" interp
            with Not_found ->
              incr idx; string_of_int !idx
        in
        tree_store#clear ();
        let idx = ref ~-1 in
        List.iter
          (fun interp ->
            incr idx;
            let interp_row = tree_store#append () in
            tree_store#set ~row:interp_row ~column:id_col
              (name_of_interp interp);
            tree_store#set ~row:interp_row ~column:interp_no_col !idx;
            List.iter
              (fun (id, dsc) ->
                let row = tree_store#append ~parent:interp_row () in
                tree_store#set ~row ~column:id_col id;
                tree_store#set ~row ~column:dsc_col dsc;
                tree_store#set ~row ~column:interp_no_col !idx)
              interp)
          choices

      method get_interp_no tree_path =
        let iter = tree_store#get_iter tree_path in
        tree_store#get ~row:iter ~column:interp_no_col
    end

let interactive_string_choice 
  text prefix_len ?(title = "") ?(msg = "") () ~id locs uris 
=
  let gui = instance () in
    let dialog = gui#newUriDialog () in
    dialog#uriEntryHBox#misc#hide ();
    dialog#uriChoiceSelectedButton#misc#hide ();
    dialog#uriChoiceAutoButton#misc#hide ();
    dialog#uriChoiceConstantsButton#misc#hide ();
    dialog#uriChoiceTreeView#selection#set_mode
      (`SINGLE :> Gtk.Tags.selection_mode);
    let model = new stringListModel dialog#uriChoiceTreeView in
    let choices = ref None in
    dialog#uriChoiceDialog#set_title title; 
    let hack_len = MatitaGtkMisc.utf8_string_length text in
    let rec colorize acc_len = function
      | [] -> 
          let floc = HExtlib.floc_of_loc (acc_len,hack_len) in
          fst(MatitaGtkMisc.utf8_parsed_text text floc)
      | he::tl -> 
          let start, stop =  HExtlib.loc_of_floc he in
          let floc1 = HExtlib.floc_of_loc (acc_len,start) in
          let str1,_=MatitaGtkMisc.utf8_parsed_text text floc1 in
          let str2,_ = MatitaGtkMisc.utf8_parsed_text text he in
          str1 ^ "<b>" ^ str2 ^ "</b>" ^ colorize stop tl
    in
(*     List.iter (fun l -> let start, stop = HExtlib.loc_of_floc l in
                Printf.eprintf "(%d,%d)" start stop) locs; *)
    let locs = 
      List.sort 
        (fun loc1 loc2 -> 
          fst (HExtlib.loc_of_floc loc1) - fst (HExtlib.loc_of_floc loc2)) 
        locs 
    in
(*     prerr_endline "XXXXXXXXXXXXXXXXXXXX";
    List.iter (fun l -> let start, stop = HExtlib.loc_of_floc l in
                Printf.eprintf "(%d,%d)" start stop) locs;
    prerr_endline "XXXXXXXXXXXXXXXXXXXX2"; *)
    dialog#uriChoiceLabel#set_use_markup true;
    let txt = colorize 0 locs in
    let txt,_ = MatitaGtkMisc.utf8_parsed_text txt
      (HExtlib.floc_of_loc (prefix_len,MatitaGtkMisc.utf8_string_length txt))
    in
    dialog#uriChoiceLabel#set_label txt;
    List.iter model#easy_append uris;
    let return v =
      choices := v;
      dialog#uriChoiceDialog#destroy ();
      GMain.Main.quit ()
    in
    ignore (dialog#uriChoiceDialog#event#connect#delete (fun _ -> true));
    connect_button dialog#uriChoiceForwardButton (fun _ ->
      match model#easy_selection () with
      | [] -> ()
      | uris -> return (Some uris));
    connect_button dialog#uriChoiceAbortButton (fun _ -> return None);
    dialog#uriChoiceDialog#show ();
    GtkThread.main ();
    (match !choices with 
    | None -> raise MatitaTypes.Cancel
    | Some uris -> uris)

let interactive_interp_choice () text prefix_len choices =
(*List.iter (fun l -> prerr_endline "==="; List.iter (fun (_,id,dsc) -> prerr_endline (id ^ " = " ^ dsc)) l) choices;*)
 let filter_choices filter =
  let rec is_compatible filter =
   function
      [] -> true
    | ([],_,_)::tl -> is_compatible filter tl
    | (loc::tlloc,id,dsc)::tl ->
       try
        if List.assoc (loc,id) filter = dsc then
         is_compatible filter ((tlloc,id,dsc)::tl)
        else
         false
       with
        Not_found -> true
  in
   List.filter (fun (_,interp) -> is_compatible filter interp)
 in
 let rec get_choices loc id =
  function
     [] -> []
   | (_,he)::tl ->
      let _,_,dsc =
       List.find (fun (locs,id',_) -> id = id' && List.mem loc locs) he
      in
       dsc :: (List.filter (fun dsc' -> dsc <> dsc') (get_choices loc id tl))
 in
 let example_interp =
  match choices with
     [] -> assert false
   | he::_ -> he in
 let ask_user id locs choices =
  interactive_string_choice
   text prefix_len
   ~title:"Ambiguous input"
   ~msg:("Choose an interpretation for " ^ id) () ~id locs choices
 in
 let rec classify ids filter partial_interpretations =
  match ids with
     [] -> List.map fst partial_interpretations
   | ([],_,_)::tl -> classify tl filter partial_interpretations
   | (loc::tlloc,id,dsc)::tl ->
      let choices = get_choices loc id partial_interpretations in
      let chosen_dsc =
       match choices with
          [] -> prerr_endline ("NO CHOICES FOR " ^ id); assert false
        | [dsc] -> dsc
        | _ ->
          match ask_user id [loc] choices with
             [x] -> x
           | _ -> assert false
      in
       let filter = ((loc,id),chosen_dsc)::filter in
       let compatible_interps = filter_choices filter partial_interpretations in
        classify ((tlloc,id,dsc)::tl) filter compatible_interps
 in
 let enumerated_choices =
  let idx = ref ~-1 in
  List.map (fun interp -> incr idx; !idx,interp) choices
 in
  classify example_interp [] enumerated_choices

let _ =
  (* disambiguator callbacks *)
  GrafiteDisambiguator.set_choose_uris_callback (interactive_uri_choice ());
  GrafiteDisambiguator.set_choose_interp_callback (interactive_interp_choice ());
  (* gtk initialization *)
  GtkMain.Rc.add_default_file BuildTimeConf.gtkrc_file; (* loads gtk rc *)
  GMathView.add_configuration_path BuildTimeConf.gtkmathview_conf;
  ignore (GMain.Main.init ())

