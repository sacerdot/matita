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

type lexicon_status = {
  aliases: GrafiteAst.alias_spec DisambiguateTypes.Environment.t;
  multi_aliases: GrafiteAst.alias_spec list DisambiguateTypes.Environment.t;
  new_aliases: (DisambiguateTypes.domain_item * GrafiteAst.alias_spec) list
}

let initial_status = {
  aliases = DisambiguateTypes.Environment.empty;
  multi_aliases = DisambiguateTypes.Environment.empty;
  new_aliases = []
}

class type g_status =
 object
  inherit Interpretations.g_status
  inherit TermContentPres.g_status
  inherit CicNotationParser.g_status
  method lstatus: lexicon_status
 end

class status =
 object(self)
  inherit Interpretations.status
  inherit TermContentPres.status
  inherit CicNotationParser.status ~keywords:[]
  val lstatus = initial_status
  method lstatus = lstatus
  method set_lstatus v = {< lstatus = v >}
  method set_lexicon_engine_status : 'status. #g_status as 'status -> 'self
   = fun o -> (((self#set_lstatus o#lstatus)#set_interp_status o)#set_content_pres_status o)#set_notation_parser_status o
 end
