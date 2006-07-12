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

let png_flags = "-Tpng"
let map_flags = "-Tcmapx"

let tempfile () = Filename.temp_file "matita_" ""

class type graphviz_widget =
  object
    method load_graph_from_file: string -> unit
    method connect_href:
      (GdkEvent.Button.t -> (string * string) list -> unit) -> unit
    method as_image: GMisc.image
    method as_viewport: GBin.viewport
  end

class graphviz_impl ?packing gviz_cmd =
  let viewport = GBin.viewport ?packing () in
  let image =
    GMisc.image ~packing:viewport#add ~xalign:0. ~yalign:0. ~xpad:0 ~ypad:0 ()
  in
  object (self)
    val mutable href_cb = fun _ _ -> ()
    val mutable map = []

    initializer
      ignore (viewport#event#connect#button_press (fun button ->
        (*eprintf "x: %f; y: %f;\n%!" (GdkEvent.Button.x button +. viewport#hadjustment#value) (GdkEvent.Button.y button +. viewport#vadjustment#value);*)
        (* compute coordinates relative to image origin *)
        let x = GdkEvent.Button.x button +. viewport#hadjustment#value in
        let y = GdkEvent.Button.y button +. viewport#vadjustment#value in
        (try
          href_cb button (self#find_href x y)
        with Not_found -> ());
        false))

    method load_graph_from_file fname =
      let tmp_png = tempfile () in
      ignore (Sys.command (sprintf "%s %s %s > %s"
        gviz_cmd png_flags fname tmp_png));
      image#set_file tmp_png;
      HExtlib.safe_remove tmp_png;
      let tmp_map = tempfile () in
      ignore (Sys.command (sprintf "%s %s %s > %s"
        gviz_cmd map_flags fname tmp_map));
      self#load_map tmp_map;
      HExtlib.safe_remove tmp_map

    method private load_map fname =
      let areas = ref [] in
      let p =
        XmlPushParser.create_parser
          { XmlPushParser.default_callbacks with
            XmlPushParser.start_element =
              Some (fun elt attrs ->
                match elt with
                | "area" -> areas := attrs :: !areas
                | _ -> ()) } in
      XmlPushParser.parse p (`File fname);
      map <- !areas

    method private find_href x y =
      let parse_coords s =
        match List.map float_of_string (HExtlib.split ~sep:',' s) with
        | [x1; y1; x2; y2 ] -> x1, y1, x2, y2
        | _ -> assert false in
      List.find
        (fun attrs ->
          let x1, y1, x2, y2 = parse_coords (List.assoc "coords" attrs) in
          x1 <= x && x <= x2 && y1 <= y && y <= y2)
        map

    method connect_href
      (cb: GdkEvent.Button.t -> (string * string) list -> unit)
    =
      href_cb <- cb

    method as_image = image
    method as_viewport = viewport

  end

let factory cmd ?packing () =
  (new graphviz_impl ?packing cmd :> graphviz_widget)

let gDot = factory "dot"
let gNeato = factory "neato"
let gTwopi = factory "twopi"
let gCirco = factory "circo"
let gFdp = factory "fdp"

