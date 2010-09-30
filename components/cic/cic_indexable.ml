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
 * http://cs.unibo.it/helm/.
 *)

(* $Id: discrimination_tree.ml 8991 2008-09-19 12:47:23Z tassi $ *)

module CicIndexable : Discrimination_tree.Indexable 
with type input = Cic.term and type constant_name = UriManager.uri 
= struct

        type input = Cic.term
        type constant_name = UriManager.uri
        open Discrimination_tree
        
        let ppelem = function
          | Constant (uri,arity) -> 
              "("^UriManager.name_of_uri uri ^ "," ^ string_of_int arity^")"
          | Bound (i,arity) -> 
              "("^string_of_int i ^ "," ^ string_of_int arity^")"
          | Variable -> "?"
          | Proposition -> "Prop"
          | Datatype -> "Type"
          | Dead -> "Dead"
        ;;

        let path_string_of =
          let rec aux arity = function
            | Cic.Appl ((Cic.Meta _|Cic.Implicit _)::_) -> [Variable]
            | Cic.Appl (Cic.Lambda _ :: _) -> 
                [Variable] (* maybe we should b-reduce *)
            | Cic.Appl [] -> assert false
            | Cic.Appl (hd::tl) ->
                aux (List.length tl) hd @ List.flatten (List.map (aux 0) tl) 
            | Cic.Cast (t,_) -> aux arity t
            | Cic.Lambda (_,s,t) | Cic.Prod (_,s,t) -> [Variable]
                (* I think we should CicSubstitution.subst Implicit t *)
            | Cic.LetIn (_,s,_,t) -> [Variable] (* z-reduce? *)
            | Cic.Meta _ | Cic.Implicit _ -> assert (arity = 0); [Variable]
            | Cic.Rel i -> [Bound (i, arity)]
            | Cic.Sort (Cic.Prop) -> assert (arity=0); [Proposition]
            | Cic.Sort _ -> assert (arity=0); [Datatype]
            | Cic.Const _ | Cic.Var _ 
            | Cic.MutInd _ | Cic.MutConstruct _ as t ->
                [Constant (CicUtil.uri_of_term t, arity)]
            | Cic.MutCase _ | Cic.Fix _ | Cic.CoFix _ -> [Dead]
          in 
            aux 0
        ;;

        let compare e1 e2 =
          match e1,e2 with
          | Constant (u1,a1),Constant (u2,a2) -> 
               let x = UriManager.compare u1 u2 in
               if x = 0 then Pervasives.compare a1 a2 else x
          | e1,e2 -> Pervasives.compare e1 e2
        ;;
        
        let string_of_path l = String.concat "." (List.map ppelem l) ;;
end 

