(*
 * Copyright (C) 2003:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id$ *)

let _ = Random.self_init ()

let id_length = 32
let min_ascii = 33
let max_ascii = 126
  (* characters forbidden inside an XML attribute value. Well, '>' and '''
  aren't really forbidden, but are listed here ... just to be sure *)
let forbidden_chars = (* i.e. [ '"'; '&'; '\''; '<'; '>' ] *)
  [ 34; 38; 39; 60; 62 ]  (* assumption: is sorted! *)
let chars_range = max_ascii - min_ascii + 1 - (List.length forbidden_chars)

  (* return a random id char c such that 
      (min_ascii <= Char.code c) &&
      (Char.code c <= max_ascii) &&
      (not (List.mem (Char.code c) forbidden_chars))
  *)
let random_id_char () =
  let rec nth_char ascii shifts = function
    | [] -> Char.chr (ascii + shifts)
    | hd::tl when ascii + shifts < hd -> Char.chr (ascii + shifts)
    | hd::tl (* when ascii + shifts >= hd *) -> nth_char ascii (shifts + 1) tl
  in
  nth_char (Random.int chars_range + min_ascii) 0 forbidden_chars

  (* return a random id string which have length id_length *)
let new_id () =
  let str = String.create id_length in
  for i = 0 to id_length - 1 do
    String.set str i (random_id_char ())
  done;
  str

let new_broker_id = new_id
let new_client_id = new_id
let new_musing_id = new_id
let new_tutor_id = new_id

