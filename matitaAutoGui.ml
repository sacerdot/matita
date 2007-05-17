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
  Cic.context * (Cic.term * (int * Cic.term) list) list * Cic.term list *
  Cic.term list
let fake_goal = Cic.Implicit None;;
let fake_candidates = [];;

let start = ref 0;;
let len = ref 10;;

let pp c t =
  let names = List.map (function None -> None | Some (n,_) -> Some n) c in
  let t = 
    ProofEngineReduction.replace 
      ~equality:(fun a b -> match b with Cic.Meta _ -> true | _ -> false) 
      ~what:[Cic.Rel 1] ~with_what:[Cic.Implicit None] ~where:t
  in
  CicPp.pp t names
;;
let pp_goal context x = 
  if x == fake_goal then "" else pp context x
;;
let pp_candidate context x = pp context x

let sublist start len l = 
  let rec aux pos len = function
    | [] when pos < start -> aux (pos+1) len []
    | [] when len > 0 -> (fake_goal, fake_candidates) :: aux (pos+1) (len-1) [] 
    | [] (* when len <= 0 *) -> []
    | he::tl when pos < start -> aux (pos+1) len tl
    | he::tl when pos >= start && len > 0 -> he::aux (pos+1) (len-1) tl
    | he::tl (* when pos >= start && len <= 0 *) -> []
  in
  aux 0 len l
;;

let cell_of_candidate context ?(active=false) g id c = 
  let tooltip = GData.tooltips () in (* should be only one isn't it? *)
  let button = 
    GButton.button 
      ~label:(pp_candidate context c(* ^ " - " ^ string_of_int id*)) () 
  in
  if active then
    button#misc#set_sensitive false;
  let text = 
    "Follow computation of "^pp_candidate context c^" on "^pp_goal context g
  in
  tooltip#set_tip ~text (button :> GObj.widget);
  ignore(button#connect#clicked 
    (fun _ -> HLog.warn (string_of_int id); Auto.give_hint id));
  button
;;
let cell_of_goal win_width context goal = 
  GMisc.label ~text:(pp_goal context goal) ~xalign:0.0 ()
;;
let cell_of_int n = 
  GMisc.label ~text:(string_of_int n) 
    ~line_wrap:true ~justify:`RIGHT ()
;;
let cell_of_candidates context goal cads = 
  let hbox = GPack.hbox () in
  match cads with
  | [] -> hbox
  | (id,c)::tl ->
      hbox#pack 
        (cell_of_candidate ~active:true context goal id c :> GObj.widget);
      List.iter
        (fun (id,c) -> 
        hbox#pack (cell_of_candidate context goal id c :> GObj.widget)) tl;
        hbox
;;

let elems_to_rows context win_width (table : GPack.table) (or_list) =
  let _ = 
   List.fold_left 
    (fun position (goal, candidates) ->
      table#attach ~left:0 ~top:position 
        (cell_of_int (position + !start) :> GObj.widget);
      table#attach ~left:1 ~top:position ~expand:`BOTH ~fill:`BOTH
        (cell_of_goal win_width context goal :> GObj.widget);
      table#attach ~left:2 ~top:position 
        (cell_of_candidates context goal candidates :> GObj.widget);
      position+1)
    0 or_list
  in 
  ()
;;

let old_displayed_status = ref ([]);;
let old_size = ref 0;;

let fill_win (win : MatitaGeneratedGui.autoWin) cb =
  let init = Unix.gettimeofday () in
    try 
      let (status : status) = cb () in
      let win_size = win#toplevel#misc#allocation.Gtk.width in
      let ctx, or_list, and_list, last_moves = status in
      let displayed_status = 
        sublist !start !len (or_list @ (List.map (fun x -> x,[]) and_list)) 
      in
      if displayed_status <> !old_displayed_status || !old_size <> win_size then
        begin
          old_displayed_status := displayed_status;
          old_size := win_size;
          win#labelLAST#set_text 
            (String.concat ";" (List.map (pp_candidate ctx) last_moves));
          List.iter win#table#remove win#table#children;
          elems_to_rows ctx win_size win#table displayed_status;
          Printf.eprintf 
            "REDRAW COST: %2.1f\n%!" (Unix.gettimeofday () -.  init);
        end
    with exn -> prerr_endline (Printexc.to_string exn); ()
;;

let auto_dialog elems =
  let win = new MatitaGeneratedGui.autoWin () in
  win#check_widgets ();
  win#table#set_columns 3;
  win#table#set_col_spacings 6;
  win#table#set_row_spacings 4;
  ignore(win#buttonUP#connect#clicked 
    (fun _ -> start := max 0 (!start -1); fill_win win elems));
  ignore(win#buttonDOWN#connect#clicked 
    (fun _ -> incr start; fill_win win elems));
  ignore(win#buttonCLOSE#connect#clicked 
    (fun _ -> win#toplevel#destroy ();GMain.Main.quit ()));
  let redraw_callback _ = fill_win win elems;true in
  let redraw = GMain.Timeout.add ~ms:400 ~callback:redraw_callback in
  ignore(win#buttonPAUSE#connect#clicked 
    (fun _ -> Auto.pause true));
  ignore(win#buttonPLAY#connect#clicked 
    (fun _ -> Auto.pause false;Auto.step ()));
  ignore(win#buttonNEXT#connect#clicked 
    (fun _ -> Auto.step ()));
  fill_win win elems;
  win#toplevel#show ();
  GtkThread.main ();
  GMain.Timeout.remove redraw;
;;

