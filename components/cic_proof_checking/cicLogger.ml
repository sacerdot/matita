(* Copyright (C) 2000, HELM Team.
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

type msg =
 [ `Start_type_checking of UriManager.uri
 | `Type_checking_completed of UriManager.uri
 | `Trusting of UriManager.uri
 ]

let log ?(level = 1) =
 let module U = UriManager in
    function
     | `Start_type_checking uri ->
         HelmLogger.log (`Msg (`DIV (level, None, `T
          ("Type-Checking of " ^ (U.string_of_uri uri) ^ " started"))))
     | `Type_checking_completed uri ->
         HelmLogger.log (`Msg (`DIV (level, Some "green", `T
          ("Type-Checking of " ^ (U.string_of_uri uri) ^ " completed"))))
     | `Trusting uri ->
         HelmLogger.log (`Msg (`DIV (level, Some "blue", `T
          ((U.string_of_uri uri) ^ " is trusted."))))

class logger =
  object
    val mutable level = 0 (* indentation level *)
    method log (msg: msg) =
      match msg with
      | `Start_type_checking _ ->
          level <- level + 1;
          log ~level msg
      | `Type_checking_completed _ ->
          log ~level msg;
          level <- level - 1;
      | _ -> log ~level msg
  end

let log msg = log ~level:1 msg

