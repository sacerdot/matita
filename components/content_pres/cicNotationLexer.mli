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

  (** begin of error offset (counted in unicode codepoint)
   * end of error offset (counted as above)
   * error message *)
exception Error of int * int * string

  (** XXX ZACK DEFCON 4 BEGIN: never use the tok_func field of the glexers below
   * passing values of type char Stream.t, they should be in fact Ulexing.lexbuf
   * casted with Obj.magic :-/ Read the comment in the .ml for the rationale *)

val level1_pattern_lexer: unit -> (string * string) Token.glexer
val level2_ast_lexer: unit -> (string * string) Token.glexer
val level2_meta_lexer: unit -> (string * string) Token.glexer

  (** XXX ZACK DEFCON 4 END *)

val add_level2_ast_keyword: string -> unit    (** non idempotent *)
val remove_level2_ast_keyword: string -> unit (** non idempotent *)

(** {2 Ligatures} *)

val push: unit -> unit
val pop: unit -> unit
