(* Copyright (C) 2005, HELM Team.
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

module Pres = Mpresentation

(** {2 Pretty printing from BoxML to strings} *)

let string_space = " "
let string_space_len = String.length string_space
let string_indent = (* string_space *) ""
let string_indent_len = String.length string_indent
let string_ink = "---------------------------"
let string_ink_len = String.length string_ink

let contains_attrs contained container =
  List.for_all (fun attr -> List.mem attr container) contained

let want_indent = contains_attrs (RenderingAttrs.indent_attributes `BoxML)
let want_spacing = contains_attrs (RenderingAttrs.spacing_attributes `BoxML)

let indent_string s = string_indent ^ s
let indent_children (size, children) =
  let children' = List.map indent_string children in
  size + string_space_len, children'

let choose_rendering size (best, other) =
  let best_size, _ = best in
  if size >= best_size then best else other

let merge_columns sep cols =
  let sep_len = String.length sep in
  let indent = ref 0 in
  let res_rows = ref [] in
  let add_row ~continue row =
    match !res_rows with
    | last :: prev when continue ->
        res_rows := (String.concat sep [last; row]) :: prev;
        indent := !indent + String.length last + sep_len
    | _ -> res_rows := (String.make !indent ' ' ^ row) :: !res_rows;
  in
  List.iter
    (fun rows ->
      match rows with
      | hd :: tl ->
          add_row ~continue:true hd;
          List.iter (add_row ~continue:false) tl
      | [] -> ())
    cols;
  List.rev !res_rows
    
let max_len =
  List.fold_left (fun max_size s -> max (String.length s) max_size) 0

let render_row available_space spacing children =
  let spacing_bonus = if spacing then string_space_len else 0 in
  let rem_space = ref available_space in
  let renderings = ref [] in
  List.iter
    (fun f ->
      let occupied_space, rendering = f !rem_space in
      renderings := rendering :: !renderings;
      rem_space := !rem_space - (occupied_space + spacing_bonus))
    children;
  let sep = if spacing then string_space else "" in
  let rendering = merge_columns sep (List.rev !renderings) in
  max_len rendering, rendering

let fixed_rendering s =
  let s_len = String.length s in
  (fun _ -> s_len, [s])

let render_to_strings ~map_unicode_to_tex choose_action size markup =
  let max_size = max_int in
  let rec aux_box =
    function
    | Box.Text (_, t) -> fixed_rendering t
    | Box.Space _ -> fixed_rendering string_space
    | Box.Ink _ -> fixed_rendering string_ink
    | Box.Action (_, []) -> assert false
    | Box.Action (_, l) -> aux_box (choose_action l)
    | Box.Object (_, o) -> aux_mpres o
    | Box.H (attrs, children) ->
        let spacing = want_spacing attrs in
        let children' = List.map aux_box children in
        (fun size -> render_row size spacing children')
    | Box.HV (attrs, children) ->
        let spacing = want_spacing attrs in
        let children' = List.map aux_box children in
        (fun size ->
          let (size', renderings) as res =
            render_row max_size spacing children'
          in
          if size' <= size then (* children fit in a row *)
            res
          else  (* break needed, re-render using a Box.V *)
            aux_box (Box.V (attrs, children)) size)
    | Box.V (attrs, []) -> assert false
    | Box.V (attrs, [child]) -> aux_box child
    | Box.V (attrs, hd :: tl) ->
        let indent = want_indent attrs in
        let hd_f = aux_box hd in
        let tl_fs = List.map aux_box tl in
        (fun size ->
          let _, hd_rendering = hd_f size in
          let children_size =
            max 0 (if indent then size - string_indent_len else size)
          in
          let tl_renderings =
            List.map
              (fun f ->
(*                 let indent_header = if indent then string_indent else "" in *)
                snd (indent_children (f children_size)))
              tl_fs
          in
          let rows = hd_rendering @ List.concat tl_renderings in
          max_len rows, rows)
    | Box.HOV (attrs, []) -> assert false
    | Box.HOV (attrs, [child]) -> aux_box child
    | Box.HOV (attrs, children) ->
        let spacing = want_spacing attrs in
        let indent = want_indent attrs in
        let spacing_bonus = if spacing then string_space_len else 0 in
        let indent_bonus = if indent then string_indent_len else 0 in
        let sep = if spacing then string_space else "" in
        let fs = List.map aux_box children in
        (fun size ->
          let rows = ref [] in
          let renderings = ref [] in
          let rem_space = ref size in
          let first_row = ref true in
          let use_rendering (space, rendering) =
            let use_indent = !renderings = [] && not !first_row in
            let rendering' =
              if use_indent then List.map indent_string rendering
              else rendering
            in
            renderings := rendering' :: !renderings;
            let bonus = if use_indent then indent_bonus else spacing_bonus in
            rem_space := !rem_space - (space + bonus)
          in
          let end_cluster () =
            let new_rows = merge_columns sep (List.rev !renderings) in
            rows := List.rev_append new_rows !rows;
            rem_space := size - indent_bonus;
            renderings := [];
            first_row := false
          in
          List.iter
            (fun f ->
              let (best_space, _) as best = f max_size in
              if best_space <= !rem_space then
                use_rendering best
              else begin
                end_cluster ();
                if best_space <= !rem_space then use_rendering best
                else use_rendering (f size)
              end)
            fs;
          if !renderings <> [] then end_cluster ();
          max_len !rows, List.rev !rows)
  and aux_mpres =
    let text s = Pres.Mtext ([], s) in
    let mrow c = Pres.Mrow ([], c) in
    let parentesize s = s in
    function
    | Pres.Mi (_, s)
    | Pres.Mn (_, s)
    | Pres.Mtext (_, s)
    | Pres.Ms (_, s)
    | Pres.Mgliph (_, s) -> fixed_rendering s
    | Pres.Mo (_, s) ->
        let s =
          if map_unicode_to_tex then begin
            if String.length s = 1 && Char.code s.[0] < 128 then
              s
            else
              match Utf8Macro.tex_of_unicode s with
              | s::_ -> s ^ " "
              | [] -> " " ^ s ^ " "
          end else
            s
        in
        fixed_rendering s
    | Pres.Mspace _ -> fixed_rendering string_space
    | Pres.Mrow (attrs, children) ->
        let children' = List.map aux_mpres children in
        (fun size -> render_row size false children')
    | Pres.Mfrac (_, m, n) ->
       aux_mpres (mrow [ text " \\frac "; parentesize m ; text " "; parentesize n; text " " ])
    | Pres.Msqrt (_, m) -> aux_mpres (mrow [ text " \\sqrt "; parentesize m; text " "])
    | Pres.Mroot (_, r, i) ->
        aux_mpres (mrow [
          text " \\root "; parentesize i; text " \\of "; parentesize r; text " " ])
    | Pres.Mstyle (_, m)
    | Pres.Merror (_, m)
    | Pres.Mpadded (_, m)
    | Pres.Mphantom (_, m)
    | Pres.Menclose (_, m) -> aux_mpres m
    | Pres.Mfenced (_, children) -> aux_mpres (mrow children)
    | Pres.Maction (_, []) -> assert false
    | Pres.Msub (_, m, n) ->
        aux_mpres (mrow [ text " "; parentesize m; text " \\sub "; parentesize n; text " " ])
    | Pres.Msup (_, m, n) ->
        aux_mpres (mrow [ text " "; parentesize m; text " \\sup "; parentesize n; text " " ])
    | Pres.Munder (_, m, n) ->
        aux_mpres (mrow [ text " "; parentesize m; text " \\below "; parentesize n; text " " ])
    | Pres.Mover (_, m, n) ->
        aux_mpres (mrow [ text " "; parentesize m; text " \\above "; parentesize n; text " " ])
    | Pres.Msubsup _
    | Pres.Munderover _
    | Pres.Mtable _ ->
        prerr_endline
          "MathML presentation element not yet available in concrete syntax";
        assert false
    | Pres.Maction (_, hd :: _) -> aux_mpres hd
    | Pres.Mobject (_, o) -> aux_box (o: CicNotationPres.boxml_markup)
  in
  snd (aux_mpres markup size)

let render_to_string ~map_unicode_to_tex choose_action size markup =
  String.concat "\n"
    (render_to_strings ~map_unicode_to_tex choose_action size markup)

