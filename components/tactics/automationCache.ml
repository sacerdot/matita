(* Copyright (C) 2002, HELM Team.
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

type tables = 
  Saturation.active_table * Saturation.passive_table * Equality.equality_bag

type cache = {
        univ : Universe.universe;
        tables : Saturation.active_table * 
                 Saturation.passive_table *
                 Equality.equality_bag;
}

let empty_tables () =
  Saturation.make_active [], 
  Saturation.make_passive [],
  Equality.mk_equality_bag ()
;;

let empty () = { 
        univ = Universe.empty; 
        tables = empty_tables ();
}

let pump cache steps = 
  let active, passive, bag = cache.tables in
  let active, passive, bag = 
    Saturation.pump_actives 
      [] bag active passive steps infinity
  in
  let tables = active, passive, bag in 
  { cache with tables = tables }
;;

let add_term_to_active cache metasenv subst context t ty_opt =
  let actives, passives, bag = cache.tables in
  let bag, metasenv, head, t, args, mes, ugraph =
    match ty_opt with
    | Some ty -> 
        bag, metasenv, ty, t, [], (CicUtil.metas_of_term (Cic.Appl [t;ty])),
        CicUniv.oblivion_ugraph
    | None -> 
        let ty, ugraph = 
          CicTypeChecker.type_of_aux' 
            ~subst metasenv context t CicUniv.oblivion_ugraph
        in
        let bag, head, metasenv, args =
          Equality.saturate_term bag metasenv subst context ty
        in
        let mes = CicUtil.metas_of_term (Cic.Appl (head::t::args)) in
        let t = if args = [] then t else Cic.Appl (t:: args) in
        bag, metasenv, head, t, args, mes, ugraph
  in
  if List.exists 
      (function 
      | Cic.Meta(i,_) -> 
          (try 
            let _,mc, mt = CicUtil.lookup_meta i metasenv in
            let sort, u = 
               CicTypeChecker.type_of_aux' metasenv mc mt ugraph
            in
            fst (CicReduction.are_convertible mc sort (Cic.Sort Cic.Prop) u)
          with
          | CicUtil.Meta_not_found _ -> false)
      | _ -> assert false)
     args 
  then
    cache
  else
    let env = metasenv, context, CicUniv.oblivion_ugraph in 
    let newmetas = 
      List.filter (fun (i,_,_) -> List.mem_assoc i mes) metasenv
    in
    let tables = 
      Saturation.add_to_active bag actives passives env head t newmetas
    in
    { cache with tables = tables }
;;

let pp_cache cache =
  prerr_endline "Automation cache";
  prerr_endline "----------------------------------------------";
  prerr_endline "universe:";      
  Universe.iter cache.univ (fun _ ts ->
    prerr_endline (" "^
      String.concat "\n " (List.map CicPp.ppterm ts)));
  prerr_endline "tables/actives:";      
  let active, passive, _ = cache.tables in
  List.iter 
    (fun e -> prerr_endline (" " ^ Equality.string_of_equality e)) 
    (Saturation.list_of_active active);
  prerr_endline "tables/passives:";      
  List.iter 
    (fun e -> prerr_endline (" " ^ Equality.string_of_equality e)) 
    (Saturation.list_of_passive passive);
  prerr_endline "----------------------------------------------";
;;
