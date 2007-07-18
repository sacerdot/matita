(* Copyright (C) 2006, HELM Team.
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

type attribute = string * string  (* <key, value> pair *)

let png_flags = "-Tpng"
let map_flags = "-Tcmapx"

let tempfile () = Filename.temp_file "matita_" ""

class type graphviz_widget =
  object
    method load_graph_from_file: ?gviz_cmd:string -> string -> unit
    method connect_href:
      (GdkEvent.Button.t -> (string * string) list -> unit) -> unit
    method center_on_href: string -> unit
    method as_image: GMisc.image
    method as_viewport: GBin.viewport
  end

class graphviz_impl ?packing () =
  let viewport = GBin.viewport ?packing () in
  let mk_gviz_cmd gviz_cmd flags src_fname dest_fname =
    sprintf "cat %s | %s %s > %s" src_fname gviz_cmd flags
      dest_fname in
  let image =
    GMisc.image ~packing:viewport#add ~xalign:0. ~yalign:0. ~xpad:0 ~ypad:0 ()
  in
  let parse_coords s =
    match List.map float_of_string (HExtlib.split ~sep:',' s) with
    | [x1; y1; x2; y2 ] -> x1, y1, x2, y2
    | _ -> assert false in
  object (self)
    val mutable href_cb = fun _ _ -> ()
    val mutable map = []  (* list of associative list attr name -> attr value *)

    initializer
      ignore (viewport#event#connect#button_press (fun button ->
        (*eprintf "x: %f; y: %f;\n%!" (GdkEvent.Button.x button +. viewport#hadjustment#value) (GdkEvent.Button.y button +. viewport#vadjustment#value);*)
        (* compute coordinates relative to image origin *)
        let x = GdkEvent.Button.x button +. viewport#hadjustment#value in
        let y = GdkEvent.Button.y button +. viewport#vadjustment#value in
        (try href_cb button (self#find_href x y) with Not_found -> ());
        false))

    method load_graph_from_file ?(gviz_cmd = "dot") fname =
      let tmp_png = tempfile () in
      let rc = Sys.command (mk_gviz_cmd gviz_cmd png_flags fname tmp_png) in
      if rc <> 0 then
        eprintf
          ("Graphviz command failed (exit code: %d) on the following graph:\n"
           ^^ "%s\n%!")
          rc (HExtlib.input_file fname);
      image#set_file tmp_png;
      HExtlib.safe_remove tmp_png;
      let tmp_map = tempfile () in
      ignore (Sys.command (mk_gviz_cmd gviz_cmd map_flags fname tmp_map));
      self#load_map tmp_map;
      HExtlib.safe_remove tmp_map

    method private load_map fname =
      let areas = ref [] in
      let is_rect l = 
        try List.assoc "shape" l = "rect" with Not_found -> false
      in
      let p =
        XmlPushParser.create_parser
          { XmlPushParser.default_callbacks with
            XmlPushParser.start_element =
              Some (fun elt attrs ->
                match elt with
                | "area" when is_rect attrs -> areas := attrs :: !areas
                | _ -> ()) } in
      XmlPushParser.parse p (`File fname);
      map <- !areas

    method private find_href x y =
      List.find
        (fun attrs ->
          let x1, y1, x2, y2 = parse_coords (List.assoc "coords" attrs) in
          x1 <= x && x <= x2 && y1 <= y && y <= y2)
        map

    method connect_href
      (cb: GdkEvent.Button.t -> (string * string) list -> unit)
    =
      href_cb <- cb

    method center_on_href href =
      (*eprintf "Centering viewport on uri %s\n%!" href;*)
      let attrs = 
        List.find
          (fun attrs ->
            try List.assoc "href" attrs = href with Not_found -> false)
          map in
      try
        let x1, y1, x2, y2 = parse_coords (List.assoc "coords" attrs) in
        viewport#hadjustment#clamp_page ~lower:x1 ~upper:x2;
        viewport#vadjustment#clamp_page ~lower:y1 ~upper:y2;
      with Not_found -> ()

    method as_image = image
    method as_viewport = viewport

  end

let graphviz ?packing () =
  (new graphviz_impl ?packing () :> graphviz_widget)

