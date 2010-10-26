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
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

exception Option_error of string * string
exception Statement_error of string
exception Command_error of string

val command_error: string -> 'a   (** @raise Command_error *)

class status :
 string ->
  object ('self)
   method moo_content_rev: GrafiteMarshal.moo
   method set_moo_content_rev: GrafiteMarshal.moo -> 'self
   method baseuri: string
   method set_baseuri: string -> 'self
   method ng_mode: [`ProofMode | `CommandMode]
   method set_ng_mode: [`ProofMode | `CommandMode] -> 'self
   (* Warning: #stack and #obj are meaningful iff #ng_mode is `ProofMode *)
   inherit NTacStatus.tac_status
  end

  (** list is not reversed, head command will be the first emitted *)
val add_moo_content: GrafiteMarshal.ast_command list -> status -> status