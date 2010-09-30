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

exception History_failure

class ['a] history size =
  let unsome = function Some x -> x | None -> assert false in
  object (self)

    val history_data = Array.create (size + 1) None

    val mutable history_hd = 0  (* rightmost index *)
    val mutable history_cur = 0 (* current index *)
    val mutable history_tl = 0  (* leftmost index *)

    method private is_empty = history_data.(history_cur) = None

    method push (status: 'a) =
      if self#is_empty then
        history_data.(history_cur) <- Some status
      else begin
        history_cur <- (history_cur + 1) mod size;
        history_data.(history_cur) <- Some status;
        history_hd <- history_cur;  (* throw away fake future line *)
        if history_hd = history_tl then (* tail overwritten *)
          history_tl <- (history_tl + 1) mod size
      end

    method undo = function
      | 0 -> unsome history_data.(history_cur)
      | steps when steps > 0 ->
          let max_undo_steps =
            if history_cur >= history_tl then
              history_cur - history_tl
            else
              history_cur + (size - history_tl)
          in
          if steps > max_undo_steps then
            raise History_failure;
          history_cur <- history_cur - steps;
          if history_cur < 0 then (* fix underflow *)
            history_cur <- size + history_cur;
          unsome history_data.(history_cur)
      | steps (* when steps > 0 *) -> self#redo ~-steps

    method redo = function
      | 0 -> unsome history_data.(history_cur)
      | steps when steps > 0 ->
          let max_redo_steps =
            if history_hd >= history_cur then
              history_hd - history_cur
            else
              history_hd + (size - history_cur)
          in
          if steps > max_redo_steps then
            raise History_failure;
          history_cur <- (history_cur + steps) mod size;
          unsome history_data.(history_cur)
      | steps (* when steps > 0 *) -> self#undo ~-steps

  end

