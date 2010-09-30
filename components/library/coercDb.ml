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

(* $Id$ *)

let debug = false
let debug_print =
  if debug then fun x -> prerr_endline (Lazy.force x)
  else ignore
;;

type coerc_carr = 
  | Uri of UriManager.uri 
  | Sort of Cic.sort 
  | Fun of int 
  | Dead
;;

type saturations = int
type coerced_pos = int
type coercion_entry = 
  coerc_carr * coerc_carr * UriManager.uri * saturations * coerced_pos

type coerc_db = (* coercion_entry grouped by carrier with molteplicity *)
 (coerc_carr * coerc_carr * 
   (UriManager.uri * int * saturations * coerced_pos) list) list

let db =  ref ([] : coerc_db)
let dump () = !db 
let restore coerc_db = db := coerc_db
let empty_coerc_db = []

let rec coerc_carr_of_term t a =
 try
  match t, a with
   | Cic.Sort s, 0 -> Sort s
   | Cic.Appl (t::_), 0 -> coerc_carr_of_term t a
   | t, 0 -> Uri (CicUtil.uri_of_term t)
   | _, n -> Fun n
 with Invalid_argument _ -> Dead
;;

let string_of_carr = function
  | Uri u -> UriManager.name_of_uri u
  | Sort s -> CicPp.ppsort s
  | Fun i -> "FunClass_" ^ string_of_int i   
  | Dead -> "UnsupportedCarrier"
;;

let eq_carr ?(exact=false) src tgt =
  match src, tgt with
  | Uri src, Uri tgt -> 
      let coarse_eq = UriManager.eq src tgt in
      let t = CicUtil.term_of_uri src in
      let ty,_ = CicTypeChecker.type_of_aux' [] [] t CicUniv.oblivion_ugraph in
      (match ty, exact with
      | Cic.Prod _, true -> false
      | Cic.Prod _, false -> coarse_eq
      | _ -> coarse_eq) 
  | Sort _, Sort _ -> true
  | Fun _,Fun _ when not exact -> true (* only one Funclass *)
  | Fun i,Fun j when i = j -> true (* only one Funclass *)
  | _, _ -> false
;;

let to_list db =
  List.map (fun (s,t,l) -> s,t,List.map (fun a,_,b,c -> a,b,c) l) db
;;

let rec myfilter p = function
  | [] -> []
  | (s,t,l)::tl ->
      let l = 
        HExtlib.filter_map 
          (fun (u,n,saturations,cpos) as e -> 
            if p (s,t,u,saturations,cpos) then
              if n = 1 then None
              else Some (u,n-1,saturations,cpos)
            else Some e) 
          l 
      in
      if l = [] then myfilter p tl else (s,t,l)::myfilter p tl
;;
  
let remove_coercion p = db := myfilter p !db;;

let find_coercion f =
  List.map
   (fun (uri,_,saturations,_) -> uri,saturations)
   (List.flatten
    (HExtlib.filter_map (fun (s,t,l) -> if f (s,t) then Some l else None) !db))
;;

let is_a_coercion t = 
  try
   let uri = CicUtil.uri_of_term t in
   match 
     HExtlib.filter_map
      (fun (src,tgt,xl) -> 
         let xl = List.filter (fun (x,_,_,_) -> UriManager.eq uri x) xl in
         if xl = [] then None else Some (src,tgt,xl))
      !db
   with
   | [] -> None
   | (_,_,[])::_ -> assert false
   | [src,tgt,[u,_,s,p]] -> Some (src,tgt,u,s,p)
   | (src,tgt,(u,_,s,p)::_)::_ -> 
       debug_print 
         (lazy "coercion has multiple entries, returning the first one");
       Some (src,tgt,u,s,p)
  with Invalid_argument _ -> 
    debug_print (lazy "this term is not a constant");      
    None
;;

let add_coercion (src,tgt,u,saturations,cpos) =
  let f s t = eq_carr s src && eq_carr t tgt in
  let where = List.filter (fun (s,t,_) -> f s t) !db in
  let rest = List.filter (fun (s,t,_) -> not (f s t)) !db in
  match where with
  | [] -> db := (src,tgt,[u,1,saturations,cpos]) :: !db
  | (src,tgt,l)::tl ->
      assert (tl = []); (* not sure, this may be a feature *)
      if List.exists (fun (x,_,_,_) -> UriManager.eq u x) l then
        let l = 
          let l = 
            (* this code reorders the list so that adding an already declared 
             * coercion moves it to the begging of the list *)
            let item = List.find (fun (x,_,_,_) -> UriManager.eq u x) l in
            let rest=List.filter (fun (x,_,_,_) -> not (UriManager.eq u x)) l in
            item :: rest
          in
          List.map
          (fun (x,n,x_saturations,x_cpos) as e ->
            if UriManager.eq u x then
             (* not sure, this may be a feature *)
             (assert (x_saturations = saturations && x_cpos = cpos);       
             (x,n+1,saturations,cpos))
            else e)
          l
        in
        db := (src,tgt,l)::tl @ rest
      else
        db := (src,tgt,(u,1,saturations,cpos)::l)::tl @ rest
;;

let prefer u = 
  let prefer (s,t,l) =
    let lb,la = List.partition (fun (uri,_,_,_) -> UriManager.eq uri u) l in
    s,t,lb@la
  in
  db := List.map prefer !db;
;;
