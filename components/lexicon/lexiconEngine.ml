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

let dump_aliases out msg status =
   out (if msg = "" then "aliases dump:" else msg ^ ": aliases dump:");
   DisambiguateTypes.Environment.iter
      (fun _ x -> out (GrafiteAstPp.pp_alias x))
      status#lstatus.LexiconTypes.aliases
   
let set_proof_aliases status mode new_aliases =
 if mode = GrafiteAst.WithoutPreferences then
   status
 else
   (* MATITA 1.0
   let new_commands =
     List.map
      (fun _,alias -> GrafiteAst.Alias (HExtlib.dummy_floc, alias)) new_aliases
   in *)
   let aliases =
    List.fold_left (fun acc (d,c) -> DisambiguateTypes.Environment.add d c acc)
     status#lstatus.LexiconTypes.aliases new_aliases in
   let multi_aliases =
    List.fold_left (fun acc (d,c) -> 
      DisambiguateTypes.Environment.cons GrafiteAst.description_of_alias 
         d c acc)
     status#lstatus.LexiconTypes.multi_aliases new_aliases
   in
   let new_status =
    {LexiconTypes.multi_aliases = multi_aliases ; aliases = aliases}
   in
    status#set_lstatus new_status
