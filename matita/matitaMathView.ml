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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

open Printf

open GrafiteTypes
open MatitaGtkMisc
open MatitaGuiTypes

module Stack = Continuationals.Stack

(** inherit from this class if you want to access current script *)
class scriptAccessor =
object (self)
  method private script = MatitaScript.current ()
end

let cicBrowsers = ref []
let gui_instance = ref None
let set_gui gui = gui_instance := Some gui
let get_gui () =
  match !gui_instance with
  | None -> assert false
  | Some gui -> gui

let default_font_size () =
  Helm_registry.get_opt_default Helm_registry.int
    ~default:BuildTimeConf.default_font_size "matita.font_size"
let current_font_size = ref ~-1
let increase_font_size () = incr current_font_size
let decrease_font_size () = decr current_font_size
let reset_font_size () = current_font_size := default_font_size ()

  (* is there any lablgtk2 constant corresponding to the various mouse
   * buttons??? *)
let left_button = 1
let middle_button = 2
let right_button = 3

let near (x1, y1) (x2, y2) =
  let distance = sqrt (((x2 -. x1) ** 2.) +. ((y2 -. y1) ** 2.)) in
  (distance < 4.)

(*
let mathml_ns = Gdome.domString "http://www.w3.org/1998/Math/MathML"
let xlink_ns = Gdome.domString "http://www.w3.org/1999/xlink"
let helm_ns = Gdome.domString "http://www.cs.unibo.it/helm"
let href_ds = Gdome.domString "href"
let maction_ds = Gdome.domString "maction"
let xref_ds = Gdome.domString "xref"

let domImpl = Gdome.domImplementation ()

  (** Gdome.element of a MathML document whose rendering should be blank. Used
  * by cicBrowser to render "about:blank" document *)
let empty_mathml = lazy (
  domImpl#createDocument ~namespaceURI:(Some DomMisc.mathml_ns)
    ~qualifiedName:(Gdome.domString "math") ~doctype:None)

let empty_boxml = lazy (
  domImpl#createDocument ~namespaceURI:(Some DomMisc.boxml_ns) 
    ~qualifiedName:(Gdome.domString "box") ~doctype:None)
    *)

  (** shown for goals closed by side effects *)
let closed_goal_mathml = lazy "chiuso per side effect..."

(*
(* ids_to_terms should not be passed here, is just for debugging *)
let find_root_id annobj id ids_to_father_ids ids_to_terms ids_to_inner_types =
  assert false (* MATITA 1.0
  let find_parent id ids =
    let rec aux id =
(*       (prerr_endline (sprintf "id %s = %s" id
        (try
          CicPp.ppterm (Hashtbl.find ids_to_terms id)
        with Not_found -> "NONE"))); *)
      if List.mem id ids then Some id
      else
        (match
          (try Hashtbl.find ids_to_father_ids id with Not_found -> None)
        with
        | None -> None
        | Some id' -> aux id')
    in
    aux id
  in
  let return_father id ids =
    match find_parent id ids with
    | None -> assert false
    | Some parent_id -> parent_id
  in
  let mk_ids terms = List.map CicUtil.id_of_annterm terms in
  let inner_types =
   Hashtbl.fold
    (fun _ types acc ->
      match types.Cic2acic.annexpected with
         None -> types.Cic2acic.annsynthesized :: acc
       | Some ty -> ty :: types.Cic2acic.annsynthesized :: acc
    ) ids_to_inner_types [] in
  match annobj with
  | Cic.AConstant (_, _, _, Some bo, ty, _, _)
  | Cic.AVariable (_, _, Some bo, ty, _, _)
  | Cic.ACurrentProof (_, _, _, _, bo, ty, _, _) ->
      return_father id (mk_ids (ty :: bo :: inner_types))
  | Cic.AConstant (_, _, _, None, ty, _, _)
  | Cic.AVariable (_, _, None, ty, _, _) ->
      return_father id (mk_ids (ty::inner_types))
  | Cic.AInductiveDefinition _ ->
      assert false  (* TODO *)
      *)

  (** @return string content of a dom node having a single text child node, e.g.
   * <m:mi xlink:href="...">bool</m:mi> *)
let string_of_dom_node node =
  match node#get_firstChild with
  | None -> ""
  | Some node ->
      (try
        let text = new Gdome.text_of_node node in
        text#get_data#to_string
      with GdomeInit.DOMCastException _ -> "")

let name_of_hypothesis = function
  | Some (Cic.Name s, _) -> s
  | _ -> assert false

let id_of_node (node: Gdome.element) =
  let xref_attr =
    node#getAttributeNS ~namespaceURI:helm_ns ~localName:xref_ds in
  try
    List.hd (HExtlib.split ~sep:' ' xref_attr#to_string)
  with Failure _ -> assert false

type selected_term =
  | SelTerm of Cic.term * string option (* term, parent hypothesis (if any) *)
  | SelHyp of string * Cic.context (* hypothesis, context *)

let hrefs_of_elt elt =
  let localName = href_ds in
  if elt#hasAttributeNS ~namespaceURI:xlink_ns ~localName then
    let text =
      (elt#getAttributeNS ~namespaceURI:xlink_ns ~localName)#to_string in
    Some (HExtlib.split text)
  else
    None

let rec has_maction (elt :Gdome.element) = 
  (* fix this comparison *)
  if elt#get_tagName#to_string = "m:maction" ||
   elt#get_tagName#to_string = "b:action" then
    true
  else 
    match elt#get_parentNode with
    | Some node when node#get_nodeType = GdomeNodeTypeT.ELEMENT_NODE -> 
        has_maction (new Gdome.element_of_node node)
    | _ -> false
;;
*)

class clickableMathView obj =
let text_width = 80 in
object (self)
  inherit GSourceView2.source_view obj

  method has_selection = (assert false : bool)
  method strings_of_selection = (assert false : (paste_kind * string) list)
  method update_font_size =
   self#misc#modify_font_by_name
     (sprintf "%s %d" BuildTimeConf.script_font !current_font_size)
  method set_href_callback = (function _ -> () : (string -> unit) option -> unit)
  method private set_cic_info = (function _ -> () : unit (*(Cic.conjecture option * (Cic.id, Cic.term) Hashtbl.t *
         (Cic.id, Cic.hypothesis) Hashtbl.t *
         (Cic.id, Cic.id option) Hashtbl.t * ('a, 'b) Hashtbl.t * 'c option)*) option -> unit)
  (* dal widget di Luca *)
  method load_root ~root =
    self#buffer#delete ~start:(self#buffer#get_iter `START)
    ~stop:(self#buffer#get_iter `END);
    self#buffer#insert root
  method remove_selections = (() : unit)
  method set_selection = (fun _ -> () : unit option -> unit)
  method get_selections = (assert false : unit list)
  method set_font_size font_size =
   self#misc#modify_font_by_name
     (sprintf "%s %d" BuildTimeConf.script_font font_size)

  initializer
    self#set_font_size !current_font_size;
    self#source_buffer#set_language (Some MatitaGtkMisc.matita_lang);
    self#source_buffer#set_highlight_syntax true;
    self#set_editable false

(* MATITA1.0
  inherit GMathViewAux.multi_selection_math_view obj

  val mutable href_callback: (string -> unit) option = None
  method set_href_callback f = href_callback <- f

  val mutable _cic_info = None
  method private set_cic_info info = _cic_info <- info
  method private cic_info = _cic_info

  val normal_cursor = Gdk.Cursor.create `LEFT_PTR
  val href_cursor = Gdk.Cursor.create `HAND2
  val maction_cursor = Gdk.Cursor.create `QUESTION_ARROW

  initializer
    self#set_font_size !current_font_size;
    ignore (self#connect#selection_changed self#choose_selection_cb);
    ignore (self#event#connect#button_press self#button_press_cb);
    ignore (self#event#connect#button_release self#button_release_cb);
    ignore (self#event#connect#selection_clear self#selection_clear_cb);
    ignore (self#connect#element_over self#element_over_cb);
    ignore (self#coerce#misc#connect#selection_get self#selection_get_cb)

  val mutable button_press_x = -1.
  val mutable button_press_y = -1.
  val mutable selection_changed = false
  val mutable href_statusbar_msg:
    (GMisc.statusbar_context * Gtk.statusbar_message) option = None
    (* <statusbar ctxt, statusbar msg> *)

  method private selection_get_cb ctxt ~info ~time =
    let text =
      match ctxt#target with
      | "PATTERN" -> self#text_of_selection `Pattern
      | "TERM" | _ -> self#text_of_selection `Term
    in
    match text with
    | None -> ()
    | Some s -> ctxt#return s

  method private text_of_selection fmt =
    match self#get_selections with
    | [] -> None
    | node :: _ -> Some (self#string_of_node ~paste_kind:fmt node)

  method private selection_clear_cb sel_event =
    self#remove_selections;
    (GData.clipboard Gdk.Atom.clipboard)#clear ();
    false

  method private button_press_cb gdk_button =
    let button = GdkEvent.Button.button gdk_button in
    if  button = left_button then begin
      button_press_x <- GdkEvent.Button.x gdk_button;
      button_press_y <- GdkEvent.Button.y gdk_button;
      selection_changed <- false
    end else if button = right_button then
      self#popup_contextual_menu 
        (self#get_element_at 
          (int_of_float (GdkEvent.Button.x gdk_button)) 
          (int_of_float (GdkEvent.Button.y gdk_button)))  
        (GdkEvent.Button.time gdk_button);
    false

  method private element_over_cb (elt_opt, _, _, _) =
    let win () = self#misc#window in
    let leave_href () =
      Gdk.Window.set_cursor (win ()) normal_cursor;
      HExtlib.iter_option (fun (ctxt, msg) -> ctxt#remove msg)
        href_statusbar_msg
    in
    match elt_opt with
    | Some elt ->
        if has_maction elt then
          Gdk.Window.set_cursor (win ()) maction_cursor
        else
        (match hrefs_of_elt elt with
        | Some ((_ :: _) as hrefs) ->
            Gdk.Window.set_cursor (win ()) href_cursor;
            let msg_text = (* now create statusbar msg and store it *)
              match hrefs with
              | [ href ] -> sprintf "Hyperlink to %s" href
              | _ -> sprintf "Hyperlinks to: %s" (String.concat ", " hrefs) in
            let ctxt = (get_gui ())#main#statusBar#new_context ~name:"href" in
            let msg = ctxt#push msg_text in
            href_statusbar_msg <- Some (ctxt, msg)
        | _ -> leave_href ())
    | None -> leave_href ()

  method private tactic_text_pattern_of_node node =
   let id = id_of_node node in
   let cic_info, unsh_sequent = self#get_cic_info id in
   match self#get_term_by_id cic_info id with
   | SelTerm (t, father_hyp) ->
       let sequent = self#sequent_of_id ~paste_kind:`Pattern id in
       let text = self#string_of_cic_sequent ~output_type:`Pattern sequent in
       (match father_hyp with
       | None -> None, [], Some text
       | Some hyp_name -> None, [ hyp_name, text ], None)
   | SelHyp (hyp_name, _ctxt) -> None, [ hyp_name, "%" ], None

  method private tactic_text_of_node node =
   let id = id_of_node node in
   let cic_info, unsh_sequent = self#get_cic_info id in
   match self#get_term_by_id cic_info id with
   | SelTerm (t, father_hyp) ->
       let sequent = self#sequent_of_id ~paste_kind:`Term id in
       let text = self#string_of_cic_sequent ~output_type:`Term sequent in
       text
   | SelHyp (hyp_name, _ctxt) -> hyp_name

    (** @return a pattern structure which contains pretty printed terms *)
  method private tactic_text_pattern_of_selection =
    match self#get_selections with
    | [] -> assert false (* this method is invoked only if there's a sel. *)
    | node :: _ -> self#tactic_text_pattern_of_node node

  method private popup_contextual_menu element time =
    let menu = GMenu.menu () in
    let add_menu_item ?(menu = menu) ?stock ?label () =
      GMenu.image_menu_item ?stock ?label ~packing:menu#append () in
    let check = add_menu_item ~label:"Check" () in
    let reductions_menu_item = GMenu.menu_item ~label:"βδιζ-reduce" () in
    let tactics_menu_item = GMenu.menu_item ~label:"Apply tactic" () in
    let hyperlinks_menu_item = GMenu.menu_item ~label:"Hyperlinks" () in
    menu#append reductions_menu_item;
    menu#append tactics_menu_item;
    menu#append hyperlinks_menu_item;
    let reductions = GMenu.menu () in
    let tactics = GMenu.menu () in
    let hyperlinks = GMenu.menu () in
    reductions_menu_item#set_submenu reductions;
    tactics_menu_item#set_submenu tactics;
    hyperlinks_menu_item#set_submenu hyperlinks;
    let normalize = add_menu_item ~menu:reductions ~label:"Normalize" () in
    let simplify = add_menu_item ~menu:reductions ~label:"Simplify" () in
    let whd = add_menu_item ~menu:reductions ~label:"Weak head" () in
    (match element with 
    | None -> hyperlinks_menu_item#misc#set_sensitive false
    | Some elt -> 
        match hrefs_of_elt elt, href_callback with
        | Some l, Some f ->
            List.iter 
              (fun h ->
                let item = add_menu_item ~menu:hyperlinks ~label:h () in
                connect_menu_item item (fun () -> f h)) l
        | _ -> hyperlinks_menu_item#misc#set_sensitive false);
    menu#append (GMenu.separator_item ());
    let copy = add_menu_item ~stock:`COPY () in
    let gui = get_gui () in
    List.iter (fun item -> item#misc#set_sensitive gui#canCopy)
      [ copy; check; normalize; simplify; whd ];
    let reduction_action kind () =
      let pat = self#tactic_text_pattern_of_selection in
      let statement =
        let loc = HExtlib.dummy_floc in
        "\n" ^
        GrafiteAstPp.pp_executable ~term_pp:(fun s -> s)
          ~lazy_term_pp:(fun _ -> assert false) ~obj_pp:(fun _ -> assert false)
          ~map_unicode_to_tex:(Helm_registry.get_bool
            "matita.paste_unicode_as_tex")
          (GrafiteAst.Tactic (loc,
            Some (GrafiteAst.Reduce (loc, kind, pat)),
            GrafiteAst.Semicolon loc)) in
      (MatitaScript.current ())#advance ~statement () in
    connect_menu_item copy gui#copy;
    connect_menu_item normalize (reduction_action `Normalize);
    connect_menu_item simplify (reduction_action `Simpl);
    connect_menu_item whd (reduction_action `Whd);
    menu#popup ~button:right_button ~time

  method private button_release_cb gdk_button =
    if GdkEvent.Button.button gdk_button = left_button then begin
      let button_release_x = GdkEvent.Button.x gdk_button in
      let button_release_y = GdkEvent.Button.y gdk_button in
      if selection_changed then
        ()
      else  (* selection _not_ changed *)
        if near (button_press_x, button_press_y)
          (button_release_x, button_release_y)
        then
          let x = int_of_float button_press_x in
          let y = int_of_float button_press_y in
          (match self#get_element_at x y with
          | None -> ()
          | Some elt ->
              if has_maction elt then ignore(self#action_toggle elt) else
              (match hrefs_of_elt elt with
              | Some hrefs -> self#invoke_href_callback hrefs gdk_button
              | None -> ()))
    end;
    false

  method private invoke_href_callback hrefs gdk_button =
    let button = GdkEvent.Button.button gdk_button in
    if button = left_button then
      let time = GdkEvent.Button.time gdk_button in
      match href_callback with
      | None -> ()
      | Some f ->
          (match hrefs with
          | [ uri ] ->  f uri
          | uris ->
              let menu = GMenu.menu () in
              List.iter
                (fun uri ->
                  let menu_item =
                    GMenu.menu_item ~label:uri ~packing:menu#append () in
                  connect_menu_item menu_item 
                  (fun () -> try f uri with Not_found -> assert false))
                uris;
              menu#popup ~button ~time)

  method private choose_selection_cb gdome_elt =
    let set_selection elt =
      let misc = self#coerce#misc in
      self#set_selection (Some elt);
      misc#add_selection_target ~target:"STRING" Gdk.Atom.primary;
      ignore (misc#grab_selection Gdk.Atom.primary);
    in
    let rec aux elt =
      if (elt#getAttributeNS ~namespaceURI:helm_ns
            ~localName:xref_ds)#to_string <> ""
      then
        set_selection elt
      else
        try
          (match elt#get_parentNode with
          | None -> assert false
          | Some p -> aux (new Gdome.element_of_node p))
        with GdomeInit.DOMCastException _ -> ()
    in
    (match gdome_elt with
    | Some elt when (elt#getAttributeNS ~namespaceURI:xlink_ns
        ~localName:href_ds)#to_string <> "" ->
          set_selection elt
    | Some elt -> aux elt
    | None -> self#set_selection None);
    selection_changed <- true

  method update_font_size = self#set_font_size !current_font_size

    (** find a term by id from stored CIC infos @return either `Hyp if the id
     * correspond to an hypothesis or `Term (cic, hyp) if the id correspond to a
     * term. In the latter case hyp is either None (if the term is a subterm of
     * the sequent conclusion) or Some hyp_name if the term belongs to an
     * hypothesis *)
  method private get_term_by_id cic_info id =
    let unsh_item, ids_to_terms, ids_to_hypotheses, ids_to_father_ids, _, _ =
      cic_info in
    let rec find_father_hyp id =
      if Hashtbl.mem ids_to_hypotheses id
      then Some (name_of_hypothesis (Hashtbl.find ids_to_hypotheses id))
      else
        let father_id =
          try Hashtbl.find ids_to_father_ids id
          with Not_found -> assert false in
        match father_id with
        | Some id -> find_father_hyp id
        | None -> None
    in
    try
      let term = Hashtbl.find ids_to_terms id in
      let father_hyp = find_father_hyp id in
      SelTerm (term, father_hyp)
    with Not_found ->
      try
        let hyp = Hashtbl.find ids_to_hypotheses id in
        let _, context, _ =
          match unsh_item with Some seq -> seq | None -> assert false in
        let context' = MatitaMisc.list_tl_at hyp context in
        SelHyp (name_of_hypothesis hyp, context')
      with Not_found -> assert false
    
  method private find_obj_conclusion id =
    match self#cic_info with
    | None
    | Some (_, _, _, _, _, None) -> assert false
    | Some (_, ids_to_terms, _, ids_to_father_ids, ids_to_inner_types, Some annobj) ->
        let id =
         find_root_id annobj id ids_to_father_ids ids_to_terms ids_to_inner_types
        in
         (try Hashtbl.find ids_to_terms id with Not_found -> assert false)

  method private string_of_node ~(paste_kind:paste_kind) node =
    if node#hasAttributeNS ~namespaceURI:helm_ns ~localName:xref_ds
    then
      match paste_kind with
      | `Pattern ->
          let tactic_text_pattern =  self#tactic_text_pattern_of_node node in
          GrafiteAstPp.pp_tactic_pattern
            ~term_pp:(fun s -> s) ~lazy_term_pp:(fun _ -> assert false)
            ~map_unicode_to_tex:(Helm_registry.get_bool
              "matita.paste_unicode_as_tex")
            tactic_text_pattern
      | `Term -> self#tactic_text_of_node node
    else string_of_dom_node node

  method private string_of_cic_sequent ~output_type cic_sequent =
    let script = MatitaScript.current () in
    let metasenv =
      if script#onGoingProof () then script#proofMetasenv else [] in
    let map_unicode_to_tex =
      Helm_registry.get_bool "matita.paste_unicode_as_tex" in
    ApplyTransformation.txt_of_cic_sequent_conclusion ~map_unicode_to_tex
     ~output_type text_width metasenv cic_sequent

  method private pattern_of term father_hyp unsh_sequent =
    let _, unsh_context, conclusion = unsh_sequent in
    let where =
     match father_hyp with
        None -> conclusion
      | Some name ->
         let rec aux =
          function
             [] -> assert false
           | Some (Cic.Name name', Cic.Decl ty)::_ when name' = name -> ty
           | Some (Cic.Name name', Cic.Def (bo,_))::_ when name' = name-> bo
           | _::tl -> aux tl
         in
          aux unsh_context
    in
     ProofEngineHelpers.pattern_of ~term:where [term]

  method private get_cic_info id =
    match self#cic_info with
    | Some ((Some unsh_sequent, _, _, _, _, _) as info) -> info, unsh_sequent
    | Some ((None, _, _, _, _, _) as info) ->
        let t = self#find_obj_conclusion id in
        info, (~-1, [], t) (* dummy sequent for obj *)
    | None -> assert false

  method private sequent_of_id ~(paste_kind:paste_kind) id =
    let cic_info, unsh_sequent = self#get_cic_info id in
    let cic_sequent =
      match self#get_term_by_id cic_info id with
      | SelTerm (t, father_hyp) ->
(*
IDIOTA: PRIMA SI FA LA LOCATE, POI LA PATTERN_OF. MEGLIO UN'UNICA pattern_of CHE PRENDA IN INPUT UN TERMINE E UN SEQUENTE. PER IL MOMENTO RISOLVO USANDO LA father_hyp PER RITROVARE L'IPOTESI PERDUTA
*)
          let occurrences =
            ProofEngineHelpers.locate_in_conjecture t unsh_sequent in
          (match occurrences with
          | [ context, _t ] ->
              (match paste_kind with
              | `Term -> ~-1, context, t
              | `Pattern -> ~-1, [], self#pattern_of t father_hyp unsh_sequent)
          | _ ->
              HLog.error (sprintf "found %d occurrences while 1 was expected"
                (List.length occurrences));
              assert false) (* since it uses physical equality *)
      | SelHyp (_name, context) -> ~-1, context, Cic.Rel 1 in
    cic_sequent

  method private string_of_selection ~(paste_kind:paste_kind) =
    match self#get_selections with
    | [] -> None
    | node :: _ -> Some (self#string_of_node ~paste_kind node)

  method has_selection = self#get_selections <> []

    (** @return an associative list format -> string with all possible selection
     * formats. Rationale: in order to convert the selection to TERM or PATTERN
     * format we need the sequent, the metasenv, ... keeping all of them in a
     * closure would be more expensive than keeping their already converted
     * forms *)
  method strings_of_selection =
    try
      let misc = self#coerce#misc in
      List.iter
        (fun target -> misc#add_selection_target ~target Gdk.Atom.clipboard)
        [ "TERM"; "PATTERN"; "STRING" ];
      ignore (misc#grab_selection Gdk.Atom.clipboard);
      List.map
        (fun paste_kind ->
          paste_kind, HExtlib.unopt (self#string_of_selection ~paste_kind))
        [ `Term; `Pattern ]
    with Failure _ -> failwith "no selection"
*)
end

open GtkSourceView2

let clickableMathView ?hadjustment ?vadjustment ?font_size ?log_verbosity =
  SourceView.make_params [] ~cont:(
    GtkText.View.make_params ~cont:(
      GContainer.pack_container ~create:(fun pl ->
        let obj = SourceView.new_ () in
        Gobject.set_params (Gobject.try_cast obj "GtkSourceView") pl;
        new clickableMathView obj)))
  (* MATITA1.0
  GtkBase.Widget.size_params
    ~cont:(OgtkSourceView2Props.pack_return (fun p ->
      OgtkSourceView2Props.set_params
        (new clickableMathView (GtkSourceView2Props.MathView_GMetaDOM.create p))
        ~font_size:None ~log_verbosity:None))
    []
    *)

class cicMathView obj =
object (self)
  inherit clickableMathView obj

  val mutable current_mathml = None

  method nload_sequent:
   'status. #ApplyTransformation.status as 'status -> NCic.metasenv ->
     NCic.substitution -> int -> unit
   = fun status metasenv subst metano ->
    let sequent = List.assoc metano metasenv in
    let txt =
     ApplyTransformation.ntxt_of_cic_sequent
      ~map_unicode_to_tex:false 80 status metasenv subst (metano,sequent)
    in
    (* MATITA 1.0 if BuildTimeConf.debug then begin
      let name =
       "/tmp/sequent_viewer_" ^ string_of_int (Unix.getuid ()) ^ ".xml" in
      HLog.debug ("load_sequent: dumping MathML to ./" ^ name);
      ignore (domImpl#saveDocumentToFile ~name ~doc:mathml ())
    end;*)
    self#load_root ~root:txt

  method load_nobject :
   'status. #ApplyTransformation.status as 'status -> NCic.obj -> unit
   = fun status obj ->
    let txt = ApplyTransformation.ntxt_of_cic_object ~map_unicode_to_tex:false
    80 status obj in
(*
    self#set_cic_info
      (Some (None, ids_to_terms, ids_to_hypotheses, ids_to_father_ids, ids_to_inner_types, Some annobj));
    (match current_mathml with
    | Some current_mathml when use_diff ->
        self#freeze;
        XmlDiff.update_dom ~from:current_mathml mathml;
        self#thaw
    |  _ ->
*)
        (* MATITA1.0 if BuildTimeConf.debug then begin
          let name =
           "/tmp/cic_browser_" ^ string_of_int (Unix.getuid ()) ^ ".xml" in
          HLog.debug ("cic_browser: dumping MathML to ./" ^ name);
          ignore (domImpl#saveDocumentToFile ~name ~doc:mathml ())
        end;*)
        self#load_root ~root:txt;
        (*current_mathml <- Some mathml*)(*)*);
end

let tab_label meta_markup =
  let rec aux =
    function
    | `Closed m -> sprintf "<s>%s</s>" (aux m)
    | `Current m -> sprintf "<b>%s</b>" (aux m)
    | `Shift (pos, m) -> sprintf "|<sub>%d</sub>: %s" pos (aux m)
    | `Meta n -> sprintf "?%d" n
  in
  let markup = aux meta_markup in
  (GMisc.label ~markup ~show:true ())#coerce

let goal_of_switch = function Stack.Open g | Stack.Closed g -> g

class sequentsViewer ~(notebook:GPack.notebook) ~(cicMathView:cicMathView) () =
  object (self)
    inherit scriptAccessor

    method cicMathView = cicMathView  (** clickableMathView accessor *)

    val mutable pages = 0
    val mutable switch_page_callback = None
    val mutable page2goal = []  (* associative list: page no -> goal no *)
    val mutable goal2page = []  (* the other way round *)
    val mutable goal2win = []   (* associative list: goal no -> scrolled win *)
    val mutable _metasenv = `Old []
    val mutable scrolledWin: GBin.scrolled_window option = None
      (* scrolled window to which the sequentViewer is currently attached *)
    val logo = (GMisc.image
      ~file:(MatitaMisc.image_path "matita_medium.png") ()
      :> GObj.widget)
            
    val logo_with_qed = (GMisc.image
      ~file:(MatitaMisc.image_path "matita_small.png") ()
      :> GObj.widget)

    method load_logo =
     notebook#set_show_tabs false;
     ignore(notebook#append_page logo)

    method load_logo_with_qed =
     notebook#set_show_tabs false;
     ignore(notebook#append_page logo_with_qed)

    method reset =
      cicMathView#remove_selections;
      (match scrolledWin with
      | Some w ->
          (* removing page from the notebook will destroy all contained widget,
          * we do not want the cicMathView to be destroyed as well *)
          w#remove cicMathView#coerce;
          scrolledWin <- None
      | None -> ());
      (match switch_page_callback with
      | Some id ->
          GtkSignal.disconnect notebook#as_widget id;
          switch_page_callback <- None
      | None -> ());
      for i = 0 to pages do notebook#remove_page 0 done; 
      notebook#set_show_tabs true;
      pages <- 0;
      page2goal <- [];
      goal2page <- [];
      goal2win <- [];
      _metasenv <- `Old []; 
      self#script#setGoal None

    method nload_sequents : 'status. #GrafiteTypes.status as 'status -> unit
    = fun (status : #GrafiteTypes.status) ->
     let _,_,metasenv,subst,_ = status#obj in
      _metasenv <- `New (metasenv,subst);
      pages <- 0;
      let win goal_switch =
        let w =
          GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`ALWAYS
            ~shadow_type:`IN ~show:true ()
        in
        let reparent () =
          scrolledWin <- Some w;
          match cicMathView#misc#parent with
          | None -> w#add cicMathView#coerce
          | Some parent ->
             let parent =
              match cicMathView#misc#parent with
                 None -> assert false
               | Some p -> GContainer.cast_container p
             in
              parent#remove cicMathView#coerce;
              w#add cicMathView#coerce
        in
        goal2win <- (goal_switch, reparent) :: goal2win;
        w#coerce
      in
      assert (
        let stack_goals = Stack.open_goals status#stack in
        let proof_goals = List.map fst metasenv in
        if
          HExtlib.list_uniq (List.sort Pervasives.compare stack_goals)
          <> List.sort Pervasives.compare proof_goals
        then begin
          prerr_endline ("STACK GOALS = " ^ String.concat " " (List.map string_of_int stack_goals));
          prerr_endline ("PROOF GOALS = " ^ String.concat " " (List.map string_of_int proof_goals));
          false
        end
        else true
      );
      let render_switch =
        function Stack.Open i ->`Meta i | Stack.Closed i ->`Closed (`Meta i)
      in
      let page = ref 0 in
      let added_goals = ref [] in
        (* goals can be duplicated on the tack due to focus, but we should avoid
         * multiple labels in the user interface *)
      let add_tab markup goal_switch =
        let goal = Stack.goal_of_switch goal_switch in
        if not (List.mem goal !added_goals) then begin
          ignore(notebook#append_page 
            ~tab_label:(tab_label markup) (win goal_switch));
          page2goal <- (!page, goal_switch) :: page2goal;
          goal2page <- (goal_switch, !page) :: goal2page;
          incr page;
          pages <- pages + 1;
          added_goals := goal :: !added_goals
        end
      in
      let add_switch _ _ (_, sw) = add_tab (render_switch sw) sw in
      Stack.iter  (** populate notebook with tabs *)
        ~env:(fun depth tag (pos, sw) ->
          let markup =
            match depth, pos with
            | 0, 0 -> `Current (render_switch sw)
            | 0, _ -> `Shift (pos, `Current (render_switch sw))
            | 1, pos when Stack.head_tag status#stack = `BranchTag ->
                `Shift (pos, render_switch sw)
            | _ -> render_switch sw
          in
          add_tab markup sw)
        ~cont:add_switch ~todo:add_switch
        status#stack;
      switch_page_callback <-
        Some (notebook#connect#switch_page ~callback:(fun page ->
          let goal_switch =
            try List.assoc page page2goal with Not_found -> assert false
          in
          self#script#setGoal (Some (goal_of_switch goal_switch));
          self#render_page status ~page ~goal_switch))

    method private render_page:
     'status. #ApplyTransformation.status as 'status -> page:int ->
       goal_switch:Stack.switch -> unit
     = fun status ~page ~goal_switch ->
      (match goal_switch with
      | Stack.Open goal ->
         (match _metasenv with
             `Old menv -> assert false (* MATITA 1.0 *)
           | `New (menv,subst) ->
               cicMathView#nload_sequent status menv subst goal)
      | Stack.Closed goal ->
          let doc = Lazy.force closed_goal_mathml in
          cicMathView#load_root ~root:doc);
      (try
        cicMathView#set_selection None;
        List.assoc goal_switch goal2win ()
      with Not_found -> assert false)

    method goto_sequent: 'status. #ApplyTransformation.status as 'status -> int -> unit
     = fun status goal ->
      let goal_switch, page =
        try
          List.find
            (function Stack.Open g, _ | Stack.Closed g, _ -> g = goal)
            goal2page
        with Not_found -> assert false
      in
      notebook#goto_page page;
      self#render_page status ~page ~goal_switch

  end

 (** constructors *)
type 'widget constructor =
 ?hadjustment:GData.adjustment ->
 ?vadjustment:GData.adjustment ->
 ?font_size:int ->
 ?log_verbosity:int ->
 ?auto_indent:bool ->
 ?highlight_current_line:bool ->
 ?indent_on_tab:bool ->
 ?indent_width:int ->
 ?insert_spaces_instead_of_tabs:bool ->
 ?right_margin_position:int ->
 ?show_line_marks:bool ->
 ?show_line_numbers:bool ->
 ?show_right_margin:bool ->
 ?smart_home_end:SourceView2Enums.source_smart_home_end_type ->
 ?tab_width:int ->
 ?editable:bool ->
 ?cursor_visible:bool ->
 ?justification:GtkEnums.justification ->
 ?wrap_mode:GtkEnums.wrap_mode ->
 ?accepts_tab:bool ->
 ?border_width:int ->
 ?width:int ->
 ?height:int ->
 ?packing:(GObj.widget -> unit) ->
 ?show:bool -> unit ->
  'widget

let cicMathView ?hadjustment ?vadjustment ?font_size ?log_verbosity =
  SourceView.make_params [] ~cont:(
    GtkText.View.make_params ~cont:(
      GContainer.pack_container ~create:(fun pl ->
        let obj = SourceView.new_ () in
        Gobject.set_params (Gobject.try_cast obj "GtkSourceView") pl;
        new cicMathView obj)))
(* MATITA 1.0
  GtkBase.Widget.size_params
    ~cont:(OgtkMathViewProps.pack_return (fun p ->
      OgtkMathViewProps.set_params
        (new cicMathView (GtkMathViewProps.MathView_GMetaDOM.create p))
        ~font_size ~log_verbosity))
    []
*)

let blank_uri = BuildTimeConf.blank_uri
let current_proof_uri = BuildTimeConf.current_proof_uri

type term_source =
  [ `Ast of NotationPt.term
  | `NCic of NCic.term * NCic.context * NCic.metasenv * NCic.substitution
  | `String of string
  ]

class cicBrowser_impl ~(history:MatitaTypes.mathViewer_entry MatitaMisc.history)
  ()
=
  let uri_RE =
    Pcre.regexp
      "^cic:/([^/]+/)*[^/]+\\.(con|ind|var)(#xpointer\\(\\d+(/\\d+)+\\))?$"
  in
  let dir_RE = Pcre.regexp "^cic:((/([^/]+/)*[^/]+(/)?)|/|)$" in
  let is_uri txt = Pcre.pmatch ~rex:uri_RE txt in
  let is_dir txt = Pcre.pmatch ~rex:dir_RE txt in
  let gui = get_gui () in
  let (win: MatitaGuiTypes.browserWin) = gui#newBrowserWin () in
  let gviz = LablGraphviz.graphviz ~packing:win#graphScrolledWin#add () in
  let searchText = 
    GSourceView2.source_view ~auto_indent:false ~editable:false ()
  in
  let _ =
     win#scrolledwinContent#add (searchText :> GObj.widget);
     let callback () = 
       let text = win#entrySearch#text in
       let highlight start end_ =
         searchText#source_buffer#move_mark `INSERT ~where:start;
         searchText#source_buffer#move_mark `SEL_BOUND ~where:end_;
         searchText#scroll_mark_onscreen `INSERT
       in
       let iter = searchText#source_buffer#get_iter `SEL_BOUND in
       match iter#forward_search text with
       | None -> 
           (match searchText#source_buffer#start_iter#forward_search text with
           | None -> ()
           | Some (start,end_) -> highlight start end_)
       | Some (start,end_) -> highlight start end_
     in
     ignore(win#entrySearch#connect#activate ~callback);
     ignore(win#buttonSearch#connect#clicked ~callback);
  in
  let toplevel = win#toplevel in
  let mathView = cicMathView ~packing:win#scrolledBrowser#add () in
  let fail message = 
    MatitaGtkMisc.report_error ~title:"Cic browser" ~message 
      ~parent:toplevel ()  
  in
  let tags =
    [ "dir", GdkPixbuf.from_file (MatitaMisc.image_path "matita-folder.png");
      "obj", GdkPixbuf.from_file (MatitaMisc.image_path "matita-object.png") ]
  in
  let b = (not (Helm_registry.get_bool "matita.debug")) in
  let handle_error f =
    try
      f ()
    with exn ->
      if b then
        fail (snd (MatitaExcPp.to_string exn))
      else raise exn
  in
  let handle_error' f = (fun () -> handle_error (fun () -> f ())) in
  let load_easter_egg = lazy (
    win#browserImage#set_file (MatitaMisc.image_path "meegg.png"))
  in
  let load_hints () =
      let module Pp = GraphvizPp.Dot in
      let filename, oc = Filename.open_temp_file "matita" ".dot" in
      let fmt = Format.formatter_of_out_channel oc in
      let status = (MatitaScript.current ())#grafite_status in
      Pp.header 
        ~name:"Hints"
        ~graph_type:"graph"
        ~graph_attrs:["overlap", "false"]
        ~node_attrs:["fontsize", "9"; "width", ".4"; 
            "height", ".4"; "shape", "box"]
        ~edge_attrs:["fontsize", "10"; "len", "2"] fmt;
      NCicUnifHint.generate_dot_file status fmt;
      Pp.trailer fmt;
      Pp.raw "@." fmt;
      close_out oc;
      gviz#load_graph_from_file ~gviz_cmd:"neato -Tpng" filename;
      (*HExtlib.safe_remove filename*)
  in
  let load_coerchgraph tred () = 
      let module Pp = GraphvizPp.Dot in
      let filename, oc = Filename.open_temp_file "matita" ".dot" in
      let fmt = Format.formatter_of_out_channel oc in
      Pp.header 
        ~name:"Coercions"
        ~node_attrs:["fontsize", "9"; "width", ".4"; "height", ".4"]
        ~edge_attrs:["fontsize", "10"] fmt;
      let status = (MatitaScript.current ())#grafite_status in
      NCicCoercion.generate_dot_file status fmt;
      Pp.trailer fmt;
      Pp.raw "@." fmt;
      close_out oc;
      if tred then
        gviz#load_graph_from_file 
          ~gviz_cmd:"dot -Txdot | tred |gvpack -gv | dot" filename
      else
        gviz#load_graph_from_file 
          ~gviz_cmd:"dot -Txdot | gvpack -gv | dot" filename;
      HExtlib.safe_remove filename
  in
  object (self)
    inherit scriptAccessor
    
    val mutable gviz_uri = NReference.reference_of_string "cic:/dummy.dec";

    val dep_contextual_menu = GMenu.menu ()

    initializer
      win#mathOrListNotebook#set_show_tabs false;
      win#browserForwardButton#misc#set_sensitive false;
      win#browserBackButton#misc#set_sensitive false;
      ignore (win#browserUri#connect#activate (handle_error' (fun () ->
        self#loadInput win#browserUri#text)));
      ignore (win#browserHomeButton#connect#clicked (handle_error' (fun () ->
        self#load (`About `Current_proof))));
      ignore (win#browserRefreshButton#connect#clicked
        (handle_error' (self#refresh ~force:true)));
      ignore (win#browserBackButton#connect#clicked (handle_error' self#back));
      ignore (win#browserForwardButton#connect#clicked
        (handle_error' self#forward));
      ignore (win#toplevel#event#connect#delete (fun _ ->
        let my_id = Oo.id self in
        cicBrowsers := List.filter (fun b -> Oo.id b <> my_id) !cicBrowsers;
        false));
      ignore(win#whelpResultTreeview#connect#row_activated 
        ~callback:(fun _ _ ->
          handle_error (fun () -> self#loadInput (self#_getSelectedUri ()))));
      mathView#set_href_callback (Some (fun uri ->
        handle_error (fun () ->
         let uri = `NRef (NReference.reference_of_string uri) in
          self#load uri)));
      gviz#connect_href (fun button_ev attrs ->
        let time = GdkEvent.Button.time button_ev in
        let uri = List.assoc "href" attrs in
        gviz_uri <- NReference.reference_of_string uri;
        match GdkEvent.Button.button button_ev with
        | button when button = left_button -> self#load (`NRef gviz_uri)
        | button when button = right_button ->
            dep_contextual_menu#popup ~button ~time
        | _ -> ());
      connect_menu_item win#browserCloseMenuItem (fun () ->
        let my_id = Oo.id self in
        cicBrowsers := List.filter (fun b -> Oo.id b <> my_id) !cicBrowsers;
        win#toplevel#misc#hide(); win#toplevel#destroy ());
      connect_menu_item win#browserUrlMenuItem (fun () ->
        win#browserUri#misc#grab_focus ());

      self#_load (`About `Blank);
      toplevel#show ()

    val mutable current_entry = `About `Blank 

      (** @return None if no object uri can be built from the current entry *)
    method private currentCicUri =
      match current_entry with
      | `NRef uri -> Some uri
      | _ -> None

    val model =
      new MatitaGtkMisc.taggedStringListModel tags win#whelpResultTreeview
    val model_univs =
      new MatitaGtkMisc.multiStringListModel ~cols:2 win#universesTreeview

    val mutable lastDir = ""  (* last loaded "directory" *)

    method mathView = (mathView :> MatitaGuiTypes.clickableMathView)

    method private _getSelectedUri () =
      match model#easy_selection () with
      | [sel] when is_uri sel -> sel  (* absolute URI selected *)
(*       | [sel] -> win#browserUri#entry#text ^ sel  |+ relative URI selected +| *)
      | [sel] -> lastDir ^ sel
      | _ -> assert false

    (** history RATIONALE 
     *
     * All operations about history are done using _historyFoo.
     * Only toplevel functions (ATM load and loadInput) call _historyAdd.
     *)
          
    method private _historyAdd item = 
      history#add item;
      win#browserBackButton#misc#set_sensitive true;
      win#browserForwardButton#misc#set_sensitive false

    method private _historyPrev () =
      let item = history#previous in
      if history#is_begin then win#browserBackButton#misc#set_sensitive false;
      win#browserForwardButton#misc#set_sensitive true;
      item
    
    method private _historyNext () =
      let item = history#next in
      if history#is_end then win#browserForwardButton#misc#set_sensitive false;
      win#browserBackButton#misc#set_sensitive true;
      item

    (** notebook RATIONALE 
     * 
     * Use only these functions to switch between the tabs
     *)
    method private _showMath = win#mathOrListNotebook#goto_page  0
    method private _showList = win#mathOrListNotebook#goto_page  1
    method private _showList2 = win#mathOrListNotebook#goto_page 5
    method private _showSearch = win#mathOrListNotebook#goto_page 6
    method private _showGviz = win#mathOrListNotebook#goto_page  3

    method private back () =
      try
        self#_load (self#_historyPrev ())
      with MatitaMisc.History_failure -> ()

    method private forward () =
      try
        self#_load (self#_historyNext ())
      with MatitaMisc.History_failure -> ()

      (* loads a uri which can be a cic uri or an about:* uri
      * @param uri string *)
    method private _load ?(force=false) entry =
      handle_error (fun () ->
       if entry <> current_entry || entry = `About `Current_proof || entry =
         `About `Coercions || entry = `About `CoercionsFull || force then
        begin
          (match entry with
          | `About `Current_proof -> self#home ()
          | `About `Blank -> self#blank ()
          | `About `Us -> self#egg ()
          | `About `CoercionsFull -> self#coerchgraph false ()
          | `About `Coercions -> self#coerchgraph true ()
          | `About `Hints -> self#hints ()
          | `About `TeX -> self#tex ()
          | `About `Grammar -> self#grammar () 
          | `Check term -> self#_loadCheck term
          | `NCic (term, ctx, metasenv, subst) -> 
               self#_loadTermNCic term metasenv subst ctx
          | `Dir dir -> self#_loadDir dir
          | `NRef nref -> self#_loadNReference nref);
          self#setEntry entry
        end)

    method private blank () =
      self#_showMath;
      mathView#load_root ""

    method private _loadCheck term =
      failwith "not implemented _loadCheck";
(*       self#_showMath *)

    method private egg () =
      win#mathOrListNotebook#goto_page 2;
      Lazy.force load_easter_egg

    method private redraw_gviz ?center_on () =
      if Sys.command "which dot" = 0 then
       let tmpfile, oc = Filename.open_temp_file "matita" ".dot" in
       let fmt = Format.formatter_of_out_channel oc in
       (* MATITA 1.0 MetadataDeps.DepGraph.render fmt gviz_graph;*)
       close_out oc;
       gviz#load_graph_from_file ~gviz_cmd:"tred | dot" tmpfile;
       (match center_on with
       | None -> ()
       | Some uri -> gviz#center_on_href (NReference.string_of_reference uri));
       HExtlib.safe_remove tmpfile
      else
       MatitaGtkMisc.report_error ~title:"graphviz error"
        ~message:("Graphviz is not installed but is necessary to render "^
         "the graph of dependencies amoung objects. Please install it.")
        ~parent:win#toplevel ()

    method private dependencies direction uri () =
      assert false (* MATITA 1.0
      let dbd = LibraryDb.instance () in
      let graph =
        match direction with
        | `Fwd -> MetadataDeps.DepGraph.direct_deps ~dbd uri
        | `Back -> MetadataDeps.DepGraph.inverse_deps ~dbd uri in
      gviz_graph <- graph;  (** XXX check this for memory consuption *)
      self#redraw_gviz ~center_on:uri ();
      self#_showGviz *)

    method private coerchgraph tred () =
      load_coerchgraph tred ();
      self#_showGviz

    method private hints () =
      load_hints ();
      self#_showGviz

    method private tex () =
      let b = Buffer.create 1000 in
      Printf.bprintf b "UTF-8 equivalence classes (rotate with ALT-L):\n\n";
      List.iter 
        (fun l ->
           List.iter (fun sym ->
             Printf.bprintf b "  %s" (Glib.Utf8.from_unichar sym) 
           ) l;
           Printf.bprintf b "\n";
        )
        (List.sort 
          (fun l1 l2 -> compare (List.hd l1) (List.hd l2))
          (Virtuals.get_all_eqclass ()));
      Printf.bprintf b "\n\nVirtual keys (trigger with ALT-L):\n\n";
      List.iter 
        (fun tag, items -> 
           Printf.bprintf b "  %s:\n" tag;
           List.iter 
             (fun names, symbol ->
                Printf.bprintf b "  \t%s\t%s\n" 
                  (Glib.Utf8.from_unichar symbol)
                  (String.concat ", " names))
             (List.sort 
               (fun (_,a) (_,b) -> compare a b)
               items);
           Printf.bprintf b "\n")
        (List.sort 
          (fun (a,_) (b,_) -> compare a b)
          (Virtuals.get_all_virtuals ()));
      self#_loadText (Buffer.contents b)

    method private _loadText text =
      searchText#source_buffer#set_text text;
      win#entrySearch#misc#grab_focus ();
      self#_showSearch

    method private grammar () =
      self#_loadText (Print_grammar.ebnf_of_term self#script#grafite_status);

    method private home () =
      self#_showMath;
      match self#script#grafite_status#ng_mode with
         `ProofMode ->
           self#_loadNObj self#script#grafite_status
           self#script#grafite_status#obj
       | _ -> self#blank ()

    method private _loadNReference (NReference.Ref (uri,_)) =
      let obj = NCicEnvironment.get_checked_obj uri in
      self#_loadNObj self#script#grafite_status obj

    method private _loadDir dir = 
      let content = Http_getter.ls ~local:false dir in
      let l =
        List.fast_sort
          Pervasives.compare
          (List.map
            (function 
              | Http_getter_types.Ls_section s -> "dir", s
              | Http_getter_types.Ls_object o -> "obj", o.Http_getter_types.uri)
            content)
      in
      lastDir <- dir;
      self#_loadList l

    method private setEntry entry =
      win#browserUri#set_text (MatitaTypes.string_of_entry entry);
      current_entry <- entry

    method private _loadNObj status obj =
      (* showMath must be done _before_ loading the document, since if the
       * widget is not mapped (hidden by the notebook) the document is not
       * rendered *)
      self#_showMath;
      mathView#load_nobject status obj

    method private _loadTermNCic term m s c =
      let d = 0 in
      let m = (0,([],c,term))::m in
      let status = (MatitaScript.current ())#grafite_status in
      mathView#nload_sequent status m s d;
      self#_showMath

    method private _loadList l =
      model#list_store#clear ();
      List.iter (fun (tag, s) -> model#easy_append ~tag s) l;
      self#_showList

    method private _loadList2 l =
      model_univs#list_store#clear ();
      List.iter model_univs#easy_mappend l;
      self#_showList2
    
    (** { public methods, all must call _load!! } *)
      
    method load entry =
      handle_error (fun () -> self#_load entry; self#_historyAdd entry)

    (**  this is what the browser does when you enter a string an hit enter *)
    method loadInput txt =
      let txt = HExtlib.trim_blanks txt in
      (* (* ZACK: what the heck? *)
      let fix_uri txt =
        UriManager.string_of_uri
          (UriManager.strip_xpointer (UriManager.uri_of_string txt))
      in
      *)
        let entry =
          match txt with
          | txt when is_uri txt ->
              `NRef (NReference.reference_of_string ((*fix_uri*) txt))
          | txt when is_dir txt -> `Dir (MatitaMisc.normalize_dir txt)
          | txt ->
             (try
               MatitaTypes.entry_of_string txt
              with Invalid_argument _ ->
               raise
                (GrafiteTypes.Command_error(sprintf "unsupported uri: %s" txt)))
        in
        self#_load entry;
        self#_historyAdd entry

      (** {2 methods accessing underlying GtkMathView} *)

    method updateFontSize = mathView#set_font_size !current_font_size

      (** {2 methods used by constructor only} *)

    method win = win
    method history = history
    method currentEntry = current_entry
    method refresh ~force () = self#_load ~force current_entry

  end
  
let sequentsViewer ~(notebook:GPack.notebook) ~(cicMathView:cicMathView) ():
  MatitaGuiTypes.sequentsViewer
=
  new sequentsViewer ~notebook ~cicMathView ()

let cicBrowser () =
  let size = BuildTimeConf.browser_history_size in
  let rec aux history =
    let browser = new cicBrowser_impl ~history () in
    let win = browser#win in
    ignore (win#browserNewButton#connect#clicked (fun () ->
      let history =
        new MatitaMisc.browser_history ~memento:history#save size
          (`About `Blank)
      in
      let newBrowser = aux history in
      newBrowser#load browser#currentEntry));
(*
      (* attempt (failed) to close windows on CTRL-W ... *)
    MatitaGtkMisc.connect_key win#browserWinEventBox#event ~modifiers:[`CONTROL]
      GdkKeysyms._W (fun () -> win#toplevel#destroy ());
*)
    cicBrowsers := browser :: !cicBrowsers;
    (browser :> MatitaGuiTypes.cicBrowser)
  in
  let history = new MatitaMisc.browser_history size (`About `Blank) in
  aux history

let default_cicMathView () = cicMathView ~show:true ()
let cicMathView_instance = MatitaMisc.singleton default_cicMathView

let default_sequentsViewer () =
  let gui = get_gui () in
  let cicMathView = cicMathView_instance () in
  sequentsViewer ~notebook:gui#main#sequentsNotebook ~cicMathView ()
let sequentsViewer_instance = MatitaMisc.singleton default_sequentsViewer

let mathViewer () = 
  object(self)
    method private get_browser reuse = 
      if reuse then
        (match !cicBrowsers with
        | [] -> cicBrowser ()
        | b :: _ -> (b :> MatitaGuiTypes.cicBrowser))
      else
        (cicBrowser ())
          
    method show_entry ?(reuse=false) t = (self#get_browser reuse)#load t
      
    method show_uri_list ?(reuse=false) ~entry l =
      (self#get_browser reuse)#load entry

    method screenshot status sequents metasenv subst (filename as ofn) =
      () (*MATITA 1.0
       let w = GWindow.window ~title:"screenshot" () in
       let width = 500 in
       let height = 2000 in
       let m = GMathView.math_view 
          ~font_size:!current_font_size ~width ~height
          ~packing:w#add
          ~show:true ()
       in
       w#show ();
       let filenames = 
        HExtlib.list_mapi
         (fun (mno,_ as sequent) i ->
            let mathml = 
              ApplyTransformation.nmml_of_cic_sequent 
                status metasenv subst sequent
            in
            m#load_root ~root:mathml#get_documentElement;
            let pixmap = m#get_buffer in
            let pixbuf = GdkPixbuf.create ~width ~height () in
            GdkPixbuf.get_from_drawable ~dest:pixbuf pixmap;
            let filename = 
              filename ^ "-raw" ^ string_of_int i ^ ".png" 
            in
            GdkPixbuf.save ~filename ~typ:"png" pixbuf;
            filename,mno)
         sequents
       in
       let items = 
         List.map (fun (x,mno) -> 
           ignore(Sys.command
             (Printf.sprintf
              ("convert "^^
              " '(' -gravity west -bordercolor grey -border 1 label:%d ')' "^^
              " '(' -trim -bordercolor white -border 5 "^^
                " -bordercolor grey -border 1 %s ')' -append %s ")
              mno
              (Filename.quote x)
              (Filename.quote (x ^ ".label.png"))));
             x ^ ".label.png")
         filenames
       in
       let rec div2 = function 
         | [] -> []
         | [x] -> [[x]]
         | x::y::tl -> [x;y] :: div2 tl
       in
       let items = div2 items in
       ignore(Sys.command (Printf.sprintf 
         "convert %s -append  %s" 
          (String.concat ""
            (List.map (fun items ->
              Printf.sprintf " '(' %s +append ')' "
                (String.concat 
                   (" '(' -gravity center -size 10x10 xc: ')' ") items)) items))
         (Filename.quote (ofn ^ ".png")))); 
       List.iter (fun x,_ -> Sys.remove x) filenames;
       List.iter Sys.remove (List.flatten items);
       w#destroy ();
    *)
  end

let refresh_all_browsers () =
  List.iter (fun b -> b#refresh ~force:false ()) !cicBrowsers

let update_font_sizes () =
  List.iter (fun b -> b#updateFontSize) !cicBrowsers;
  (cicMathView_instance ())#update_font_size

let get_math_views () =
  ((cicMathView_instance ()) :> MatitaGuiTypes.clickableMathView)
  :: (List.map (fun b -> b#mathView) !cicBrowsers)

let find_selection_owner () =
  let rec aux =
    function
    | [] -> raise Not_found
    | mv :: tl ->
        (match mv#get_selections with
        | [] -> aux tl
        | sel :: _ -> mv)
  in
  aux (get_math_views ())

let has_selection () =
  try ignore (find_selection_owner ()); true
  with Not_found -> false

let math_view_clipboard = ref None (* associative list target -> string *)
let has_clipboard () = !math_view_clipboard <> None
let empty_clipboard () = math_view_clipboard := None

let copy_selection () =
  try
    math_view_clipboard :=
      Some ((find_selection_owner ())#strings_of_selection)
  with Not_found -> failwith "no selection"

let paste_clipboard paste_kind =
  match !math_view_clipboard with
  | None -> failwith "empty clipboard"
  | Some cb ->
      (try List.assoc paste_kind cb with Not_found -> assert false)

