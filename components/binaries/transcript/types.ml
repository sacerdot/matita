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

type local = bool

type inline_kind = Con | Ind | Var

type input_kind = Gallina8 | Grafite of string

type output_kind = Declarative | Procedural

type source = string

type prefix = string

type flavour = Cic.object_flavour option

type params = GrafiteAst.inline_param list

type item = Heading of (string * int)
          | Line of string
	  | Comment of string
          | Unexport of string
	  | Include of (bool * string)
          | Coercion of (local * string)
	  | Notation of (local * string)
	  | Section of (local * string * string)
	  | Inline of (local * inline_kind * source * prefix * flavour * params)
          | Verbatim of string
	  | Discard of string

type items = item list
