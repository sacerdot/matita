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

open LexiconAst

type notation_id =
  | RuleId of CicNotationParser.rule_id
  | InterpretationId of TermAcicContent.interpretation_id
  | PrettyPrinterId of TermContentPres.pretty_printer_id

let compare_notation_id x y = 
  match x,y with
  | RuleId i1, RuleId i2 -> CicNotationParser.compare_rule_id i1 i2
  | RuleId _, _ -> ~-1
  | _, RuleId _ -> 1
  | x,y -> Pervasives.compare x y

let initial_parser_ref_counter () = RefCounter.create ()
let initial_rule_ids_to_items ()= Hashtbl.create 113

let parser_ref_counter = ref (initial_parser_ref_counter ());;
let rule_ids_to_items = ref (initial_rule_ids_to_items ());;

let process_notation st =
  match st with
  | Notation (loc, dir, l1, associativity, precedence, l2) ->
      let l1 = 
        CicNotationParser.check_l1_pattern
         l1 (dir = Some `RightToLeft) precedence associativity
      in
      let item = (l1, precedence, associativity, l2) in
      let rule_id = ref [] in
      let _ =
        if dir <> Some `RightToLeft then
          let create_cb (l1, precedence, associativity, l2) =
            let id =
              CicNotationParser.extend l1 
                (fun env loc ->
                  CicNotationPt.AttributedTerm
                   (`Loc loc,TermContentPres.instantiate_level2 env l2)) in
            rule_id := [ RuleId id ];
            Hashtbl.add !rule_ids_to_items id item
          in
          RefCounter.incr ~create_cb !parser_ref_counter item
      in
      let pp_id =
        if dir <> Some `LeftToRight then
          [ PrettyPrinterId
              (TermContentPres.add_pretty_printer 
                l2 l1) ]
        else
          []
      in
      !rule_id @ pp_id
  | Interpretation (loc, dsc, l2, l3) ->
      let interp_id = TermAcicContent.add_interpretation dsc l2 l3 in
       [InterpretationId interp_id]
  | st -> []

let remove_notation = function
  | RuleId id ->
      let item =
        try
          Hashtbl.find !rule_ids_to_items id
        with Not_found -> assert false in
      RefCounter.decr ~delete_cb:(fun _ -> CicNotationParser.delete id)
        !parser_ref_counter item
  | PrettyPrinterId id -> TermContentPres.remove_pretty_printer id
  | InterpretationId id -> TermAcicContent.remove_interpretation id

let get_all_notations () =
  List.map
    (fun (interp_id, dsc) ->
      InterpretationId interp_id, "interpretation: " ^ dsc)
    (TermAcicContent.get_all_interpretations ())

let get_active_notations () =
  List.map (fun id -> InterpretationId id)
    (TermAcicContent.get_active_interpretations ())

let set_active_notations ids =
  let interp_ids =
    HExtlib.filter_map
      (function InterpretationId interp_id -> Some interp_id | _ -> None)
      ids
  in
  TermAcicContent.set_active_interpretations interp_ids

let history = ref [];;

let push () =
 history := (!parser_ref_counter,!rule_ids_to_items) :: !history;
 parser_ref_counter := initial_parser_ref_counter ();
 rule_ids_to_items := initial_rule_ids_to_items ();
 TermContentPres.push ();
 TermAcicContent.push ();
 CicNotationParser.push ()
;;

let pop () =
 TermContentPres.pop ();
 TermAcicContent.pop ();
 CicNotationParser.pop ();
 match !history with
 | [] -> assert false
 | (prc,riti) :: tail ->
     parser_ref_counter := prc;
     rule_ids_to_items := riti;
     history := tail;
;;
