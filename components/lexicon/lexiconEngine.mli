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

exception IncludedFileNotCompiled of string * string

type lexicon_status = {
  aliases: LexiconAst.alias_spec DisambiguateTypes.Environment.t;
  multi_aliases: LexiconAst.alias_spec list DisambiguateTypes.Environment.t;
  lexicon_content_rev: LexiconMarshal.lexicon;
}

class type g_status =
 object
  inherit CicNotation.g_status
  method lstatus: lexicon_status
 end

class status :
 object ('self)
  inherit g_status
  inherit CicNotation.status
  method set_lstatus: lexicon_status -> 'self
  method set_lexicon_engine_status: #g_status -> 'self
 end

val eval_command : #status as 'status -> LexiconAst.command -> 'status

val set_proof_aliases:
 #status as 'status ->
  (DisambiguateTypes.domain_item * LexiconAst.alias_spec) list -> 'status

(* args: print function, message (may be empty), status *) 
val dump_aliases: (string -> unit) -> string -> #status -> unit
