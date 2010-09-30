(* Copyright (C) 2003-2005, HELM Team.
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

module C   = Cic
module PEH = ProofEngineHelpers

module Cl = ProceduralClassify

let is_eliminator = function
   | _ :: (_, C.MutInd _) :: _               -> true
   | _ :: (_, C.Appl (C.MutInd _ :: _)) :: _ -> true
   | _                                       -> false

let is_const = function
   | C.Sort _
   | C.Const _ 
   | C.Var _ 
   | C.MutInd _
   | C.MutConstruct _ -> true 
   | _                -> false 

let rec is_appl b = function
   | C.Appl (hd :: tl) -> List.fold_left is_appl (is_const hd) tl
   | t when is_const t -> b
   | C.Rel _           -> b   
   | _                 -> false 

let bkd c t =
   let classes, rc = Cl.classify c t in
   let premises, _ = PEH.split_with_whd (c, t) in
   match rc with
      | Some (i, j, _, _) when i > 1 && i <= List.length classes && is_eliminator premises -> true
      | _ ->
         let _, conclusion = List.hd premises in
         is_appl true conclusion
