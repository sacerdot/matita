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

(**** TABLES ****)

let default_eq_URIs = []
let default_true_URIs = []
let default_false_URIs = []
let default_absurd_URIs = []
let default_nat_URIs = []

(* eq, sym_eq, trans_eq, eq_ind, eq_ind_R *)
let eq_URIs_ref = ref default_eq_URIs;;

let true_URIs_ref = ref default_true_URIs
let false_URIs_ref = ref default_false_URIs
let absurd_URIs_ref = ref default_absurd_URIs
let nat_URIs_ref = ref default_nat_URIs


(**** SET_DEFAULT ****)

exception NotRecognized of string;;

(* insert an element in front of the list, removing from the list all the
   previous elements with the same key associated *)
let insert_unique e extract l =
 let uri = extract e in
 let l' =
  List.filter (fun x -> let uri' = extract x in not (UriManager.eq uri uri')) l
 in
  e :: l'

let set_default what l =
  match what,l with
  "equality",[eq_URI;sym_eq_URI;trans_eq_URI;eq_ind_URI;
              eq_ind_r_URI;eq_rec_URI;eq_rec_r_URI;eq_rect_URI;
              eq_rect_r_URI;eq_f_URI;eq_f_sym_URI] ->
      eq_URIs_ref :=
       insert_unique
         (eq_URI,sym_eq_URI,trans_eq_URI,eq_ind_URI,
          eq_ind_r_URI,eq_rec_URI,eq_rec_r_URI,eq_rect_URI,
          eq_rect_r_URI,eq_f_URI,eq_f_sym_URI)
        (fun x,_,_,_,_,_,_,_,_,_,_ -> x) !eq_URIs_ref
  | "true",[true_URI] ->
      true_URIs_ref := insert_unique true_URI (fun x -> x) !true_URIs_ref
  | "false",[false_URI] ->
      false_URIs_ref := insert_unique false_URI (fun x -> x) !false_URIs_ref
  | "absurd",[absurd_URI] ->
      absurd_URIs_ref := insert_unique absurd_URI (fun x -> x) !absurd_URIs_ref
  | "natural numbers",[nat_URI] ->
      nat_URIs_ref := insert_unique nat_URI (fun x -> x) !nat_URIs_ref
  | _,l -> 
      raise 
        (NotRecognized (what^" with "^string_of_int(List.length l)^" params"))
;;

let reset_defaults () =
  eq_URIs_ref := default_eq_URIs;
  true_URIs_ref := default_true_URIs;
  false_URIs_ref := default_false_URIs;
  absurd_URIs_ref := default_absurd_URIs;
  nat_URIs_ref := default_nat_URIs
;;

let stack = ref [];;

let push () =
  stack := (!eq_URIs_ref, !true_URIs_ref, !false_URIs_ref, !absurd_URIs_ref,
            !nat_URIs_ref
	   )::!stack;
  reset_defaults ()
;;

let pop () =
  match !stack with
  | [] -> raise (Failure "Unable to POP in libraryObjects.ml")
  | (eq,t,f,a,n)::tl ->
      stack := tl;
      eq_URIs_ref := eq;
      true_URIs_ref := t;
      false_URIs_ref := f;
      absurd_URIs_ref := a;
      nat_URIs_ref := n
;;

(**** LOOKUP FUNCTIONS ****)
let eq_URI () =
 try let eq,_,_,_,_,_,_,_,_,_,_ = List.hd !eq_URIs_ref in Some eq
 with Failure "hd" -> None

let is_eq_URI uri =
 List.exists (fun (eq,_,_,_,_,_,_,_,_,_,_) -> UriManager.eq eq uri) !eq_URIs_ref

let is_eq_refl_URI uri =
  let urieq = UriManager.strip_xpointer uri in
  is_eq_URI urieq &&
  not (UriManager.eq urieq uri)
;;

let is_eq_ind_URI uri =
 List.exists (fun (_,_,_,eq_ind,_,_,_,_,_,_,_) -> UriManager.eq eq_ind uri) !eq_URIs_ref
let is_eq_ind_r_URI uri =
 List.exists (fun (_,_,_,_,eq_ind_r,_,_,_,_,_,_) -> UriManager.eq eq_ind_r uri) !eq_URIs_ref
let is_eq_rec_URI uri =
 List.exists (fun (_,_,_,_,_,eq_rec,_,_,_,_,_) -> UriManager.eq eq_rec uri) !eq_URIs_ref
let is_eq_rec_r_URI uri =
 List.exists (fun (_,_,_,_,_,_,eq_rec_r,_,_,_,_) -> UriManager.eq eq_rec_r uri) !eq_URIs_ref
let is_eq_rect_URI uri =
 List.exists (fun (_,_,_,_,_,_,_,eq_rect,_,_,_) -> UriManager.eq eq_rect uri) !eq_URIs_ref
let is_eq_rect_r_URI uri =
 List.exists (fun (_,_,_,_,_,_,_,_,eq_rect_r,_,_) -> UriManager.eq eq_rect_r uri) !eq_URIs_ref
let is_trans_eq_URI uri = 
 List.exists (fun (_,_,trans_eq,_,_,_,_,_,_,_,_) -> UriManager.eq trans_eq uri) !eq_URIs_ref
let is_sym_eq_URI uri =
 List.exists (fun (_,sym_eq,_,_,_,_,_,_,_,_,_) -> UriManager.eq sym_eq uri) !eq_URIs_ref
let is_eq_f_URI uri =
 List.exists (fun (_,_,_,_,_,_,_,_,_,eq_f,_) -> UriManager.eq eq_f uri) !eq_URIs_ref
let is_eq_f_sym_URI uri =
 List.exists (fun (_,_,_,_,_,_,_,_,_,_,eq_f1) -> UriManager.eq eq_f1 uri) !eq_URIs_ref

let in_eq_URIs uri =  
  is_eq_URI uri || is_eq_refl_URI uri || is_eq_ind_URI uri || 
  is_eq_ind_r_URI uri || is_eq_rec_URI uri || is_eq_rec_r_URI uri ||
  is_eq_rect_URI uri || is_eq_rect_r_URI uri ||
  is_trans_eq_URI uri || is_sym_eq_URI uri || is_eq_f_URI uri ||
  is_eq_f_sym_URI uri


 
let eq_refl_URI ~eq:uri =
  let uri = UriManager.strip_xpointer uri in
  UriManager.uri_of_string (UriManager.string_of_uri uri ^ "#xpointer(1/1/1)")
 
let sym_eq_URI ~eq:uri =
 try
  let _,x,_,_,_,_,_,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let trans_eq_URI ~eq:uri =
 try
  let _,_,x,_,_,_,_,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_ind_URI ~eq:uri =
 try
  let _,_,_,x,_,_,_,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_ind_r_URI ~eq:uri =
 try
  let _,_,_,_,x,_,_,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_rec_URI ~eq:uri =
 try
  let _,_,_,_,_,x,_,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_rec_r_URI ~eq:uri =
 try
  let _,_,_,_,_,_,x,_,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_rect_URI ~eq:uri =
 try
  let _,_,_,_,_,_,_,x,_,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_rect_r_URI ~eq:uri =
 try
  let _,_,_,_,_,_,_,_,x,_,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_f_URI ~eq:uri =
 try
  let _,_,_,_,_,_,_,_,_,x,_ = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))

let eq_f_sym_URI ~eq:uri =
 try
  let _,_,_,_,_,_,_,_,_,_,x = List.find (fun eq,_,_,_,_,_,_,_,_,_,_ -> UriManager.eq eq uri) !eq_URIs_ref in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri uri))


let eq_URI_of_eq_f_URI eq_f_URI = 
  try
  let x,_,_,_,_,_,_,_,_,_,_ = 
    List.find (fun _,_,_,_,_,_,_,_,_,u,_ -> UriManager.eq eq_f_URI u) !eq_URIs_ref 
  in x
 with Not_found -> raise (NotRecognized (UriManager.string_of_uri eq_f_URI))
 
let true_URI () =
 try Some (List.hd !true_URIs_ref) with Failure "hd" -> None
let false_URI () =
 try Some (List.hd !false_URIs_ref) with Failure "hd" -> None
let absurd_URI () =
 try Some (List.hd !absurd_URIs_ref) with Failure "hd" -> None

let nat_URI () =
 try Some (List.hd !nat_URIs_ref) with Failure "hd" -> None
let is_nat_URI uri =
 List.exists (fun nat -> UriManager.eq nat uri) !nat_URIs_ref
