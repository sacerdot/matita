(* Copyright (C) 2004, HELM Team.
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

module C   = Cic
module Obj = LibraryObjects
module DT  = DisambiguateTypes

let error msg =
   raise (DT.Invalid_choice (lazy (Stdpp.dummy_loc, msg)))

let build_nat o s str =
   let n = int_of_string str in
   if n < 0 then error (str ^ " is not a valid natural number number") else
   let rec aux n = if n = 0 then o () else s (aux (pred n)) in
   aux n

let interp_natural_number num =
   let nat_URI = match Obj.nat_URI () with
      | Some uri -> uri
      | None     -> error "no default natural numbers"
   in
   let o () = C.MutConstruct (nat_URI,0,1,[]) in
   let s t = C.Appl [C.MutConstruct (nat_URI,0,2,[]); t] in
   build_nat o s num

let _ =
  DisambiguateChoices.add_num_choice
    ("natural number", `Num_interp interp_natural_number);
  DisambiguateChoices.add_num_choice
    ("Coq natural number",
      `Num_interp (fun num -> HelmLibraryObjects.build_nat (int_of_string num)));
  DisambiguateChoices.add_num_choice
    ("real number",
      `Num_interp (fun num -> HelmLibraryObjects.build_real (int_of_string num)));
  DisambiguateChoices.add_num_choice
    ("binary positive number",
      `Num_interp (fun num ->
        let num = int_of_string num in
        if num = 0 then 
          error "0 is not a valid positive number"
        else
          HelmLibraryObjects.build_bin_pos num));
  DisambiguateChoices.add_num_choice
    ("binary integer number",
      `Num_interp (fun num ->
        let num = int_of_string num in
        if num = 0 then
          HelmLibraryObjects.BinInt.z0
        else if num > 0 then
          Cic.Appl [
            HelmLibraryObjects.BinInt.zpos;
            HelmLibraryObjects.build_bin_pos num ]
        else
          assert false))
