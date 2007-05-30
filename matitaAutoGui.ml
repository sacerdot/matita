(* Copyright (C) 2003, HELM Team.
 * 
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
 * http://cs.unibo.it/helm/.
 *)

type status = 
  Cic.context * (int * Cic.term * bool * int * (int * Cic.term) list) list * 
  (int * Cic.term * int) list *
  Cic.term list
let fake_goal = Cic.Implicit None;;
let fake_candidates = [];;

let start = ref 0;;
let len = ref 10;;

let pp c t =
  (*
  let t = 
    ProofEngineReduction.replace 
      ~equality:(fun a b -> match b with Cic.Meta _ -> true | _ -> false) 
      ~what:[Cic.Rel 1] ~with_what:[Cic.Implicit None] ~where:t
  in
    ApplyTransformation.txt_of_cic_term ~map_unicode_to_tex:false
      max_int [] c t
  *)
  let names = List.map (function None -> None | Some (x,_) -> Some x) c in
  let txt_t = CicPp.pp t names in
  Pcre.replace ~pat:"\\?(\\d+)\\[[^]]*\\]" ~templ:"?<sub>$1</sub>" txt_t
;;
let pp_goal context x = 
  if x == fake_goal then "" else pp context x
;;
let pp_candidate context x = pp context x

let sublist start len l = 
  let rec aux pos len = function
    | [] when pos < start -> aux (pos+1) len []
    | [] when len > 0 -> 
          (0,fake_goal, false, 0, fake_candidates) :: aux (pos+1) (len-1) [] 
    | [] (* when len <= 0 *) -> []
    | he::tl when pos < start -> aux (pos+1) len tl
    | he::tl when pos >= start && len > 0 -> he::aux (pos+1) (len-1) tl
    | he::tl (* when pos >= start && len <= 0 *) -> []
  in
  aux 0 len l
;;

let cell_of_candidate height context ?(active=false) g id c = 
  let tooltip = GData.tooltips () in (* should be only one isn't it? *)
  let button = 
    GButton.button 
      ~label:(pp_candidate context c(* ^ " - " ^ string_of_int id*))
      () 
  in
  button#misc#set_size_request ~height ();
  if active then
    button#misc#set_sensitive false;
  let text = 
    "Follow computation of "^pp_candidate context c^" on "^pp_goal context g
  in
  tooltip#set_tip ~text (button :> GObj.widget);
  ignore(button#connect#clicked 
    (fun _ -> 
      let menu = GMenu.menu () in
      let follow = GMenu.menu_item ~label:"Follow" () in
      let prune = GMenu.menu_item ~label:"Prune" () in
      ignore (follow#connect#activate 
        (fun _ -> HLog.warn (string_of_int id); Auto.give_hint id));
      ignore (prune#connect#activate 
        (fun _ -> HLog.warn (string_of_int id); Auto.give_prune_hint id));
      menu#append follow;
      menu#append prune;
      menu#popup 0 (GtkMain.Main.get_current_event_time ())));
  button
;;
let cell_of_goal height win_width context goal = 
  GMisc.label 
    ~markup:(pp_goal context goal) ~xalign:0.0 
    ~width:(min (win_width * 60 / 100) 500) 
    ~line_wrap:false
    ~ellipsize:`END
    ~height
    ()
;;
let cell_of_row_header height n k id = 
  GMisc.label
    ~markup:("<span stretch=\"ultracondensed\">" ^ string_of_int n ^ "<sub>(" ^
             string_of_int id ^ "|" ^ string_of_int k ^ ")</sub></span>") 
    ~line_wrap:true ~justify:`LEFT ~height ~width:80 ()
;;
let cell_of_candidates height grey context goal cads = 
  let hbox = GPack.hbox () in
  match cads with
  | [] -> hbox
  | (id,c)::tl ->
      hbox#pack 
        (cell_of_candidate height ~active:grey 
          context goal id c :> GObj.widget);
      List.iter
        (fun (id,c) -> 
        hbox#pack (cell_of_candidate height context goal id c :> GObj.widget)) tl;
        hbox
;;

let elems_to_rows height context win_width (table : GPack.table) (or_list) =
  let height = height / ((List.length or_list) + 1) in
  let _ = 
   List.fold_left 
    (fun position (goal_id, goal, grey, depth, candidates) ->
      table#attach ~left:0 ~top:position 
        (cell_of_row_header height (position + !start) 
          depth goal_id :> GObj.widget);
      table#attach ~left:1 ~top:position ~fill:`BOTH
        (cell_of_goal height win_width context goal :> GObj.widget);
      table#attach ~left:2 ~top:position 
        (cell_of_candidates height grey context goal candidates :> GObj.widget);
      position+1)
    0 or_list
  in 
  ()
;;

let old_displayed_status = ref [];;
let old_size = ref 0;;

let fill_win (win : MatitaGeneratedGui.autoWin) cb =
  let init = Unix.gettimeofday () in
    try 
      let (status : status) = cb () in
      let win_size = win#toplevel#misc#allocation.Gtk.width in
      let ctx, or_list, and_list, last_moves = status in
      let displayed_status = 
        sublist !start !len 
          (or_list @ (List.map (fun (id,x,d) -> id,x,false,d,[]) and_list)) 
      in
      if displayed_status <> !old_displayed_status || !old_size <> win_size then
        begin
          old_displayed_status := displayed_status;
          old_size := win_size;
          win#labelLAST#set_text 
            (String.concat ";" (List.map (pp_candidate ctx) last_moves));
          List.iter win#table#remove win#table#children;
          let height = win#viewportAREA#misc#allocation.Gtk.height in
          elems_to_rows height ctx win_size win#table displayed_status;
          Printf.eprintf 
            "REDRAW COST: %2.1f\n%!" (Unix.gettimeofday () -.  init);
        end
    with exn -> prerr_endline (Printexc.to_string exn); ()
;;

let auto_dialog elems =
  let win = new MatitaGeneratedGui.autoWin () in
  let width = Gdk.Screen.width () in
  let height = Gdk.Screen.height () in
  let main_w = width * 70 / 100 in 
  let main_h = height * 60 / 100 in
  win#toplevel#resize ~width:main_w ~height:main_h;
  win#check_widgets ();
  win#table#set_columns 3;
  win#table#set_col_spacings 6;
  win#table#set_row_spacings 4;
  ignore(win#buttonUP#connect#clicked 
    (fun _ -> start := max 0 (!start -1); fill_win win elems));
  ignore(win#buttonDOWN#connect#clicked 
    (fun _ -> incr start; fill_win win elems));
  ignore(win#buttonCLOSE#connect#clicked 
    (fun _ -> 
      Auto.pause false;
      Auto.step ();
      win#toplevel#destroy ();
      GMain.Main.quit ()));
  ignore(win#toplevel#event#connect#delete
    (fun _ -> 
      Auto.pause false;
      Auto.step ();
      win#toplevel#destroy ();
      GMain.Main.quit ();true));
  let redraw_callback _ = fill_win win elems;true in
  let redraw = GMain.Timeout.add ~ms:400 ~callback:redraw_callback in
  ignore(win#buttonPAUSE#connect#clicked 
    (fun _ -> 
      Auto.pause true;
      win#buttonPLAY#misc#set_sensitive true;
      win#buttonPAUSE#misc#set_sensitive false;));
  ignore(win#buttonPLAY#connect#clicked 
    (fun _ -> 
      Auto.pause false;
      Auto.step ();
      win#buttonPLAY#misc#set_sensitive false;
      win#buttonPAUSE#misc#set_sensitive true;));
  ignore(win#buttonNEXT#connect#clicked 
    (fun _ -> Auto.step ()));
  Auto.pause true;
  win#buttonPLAY#misc#set_sensitive true;
  win#buttonPAUSE#misc#set_sensitive false;  
  fill_win win elems;
  win#toplevel#show ();
  GtkThread.main ();
  GMain.Timeout.remove redraw;
;;

