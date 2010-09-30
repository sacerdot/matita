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

(* $Id$ *)


(******************** THE FOURIER TACTIC ***********************)

(* La tactique Fourier ne fonctionne de manière sûre que si les coefficients 
des inéquations et équations sont entiers. En attendant la tactique Field.
*)

open Fourier
open ProofEngineTypes


let debug x = print_string ("____ "^x) ; flush stdout;;

let debug_pcontext x = 
 let str = ref "" in
 List.iter (fun y -> match y with Some(Cic.Name(a),_) -> str := !str ^ 
  a ^ " " | _ ->()) x ;
 debug ("contesto : "^ (!str) ^ "\n")
;;

(******************************************************************************
Operations on linear combinations.

Opérations sur les combinaisons linéaires affines.
La partie homogène d'une combinaison linéaire est en fait une table de hash 
qui donne le coefficient d'un terme du calcul des constructions, 
qui est zéro si le terme n'y est pas. 
*)



(**
        The type for linear combinations
*)
type flin = {fhom:(Cic.term , rational)Hashtbl.t;fcste:rational}             
;;

(**
        @return an empty flin
*)
let flin_zero () = {fhom = Hashtbl.create 50;fcste=r0}
;;

(**
        @param f a flin
        @param x a Cic.term
        @return the rational associated with x (coefficient)
*)
let flin_coef f x = 
        try
                (Hashtbl.find f.fhom x)
        with
                _ -> r0
;;
                        
(**
        Adds c to the coefficient of x
        @param f a flin
        @param x a Cic.term
        @param c a rational
        @return the new flin
*)
let flin_add f x c = 
    match x with
    Cic.Rel(n) ->(
      let cx = flin_coef f x in
      Hashtbl.remove f.fhom x;
      Hashtbl.add f.fhom x (rplus cx c);
      f)
    |_->debug ("Internal error in Fourier! this is not a Rel "^CicPp.ppterm x^"\n");
      let cx = flin_coef f x in
      Hashtbl.remove f.fhom x;
      Hashtbl.add f.fhom x (rplus cx c);
      f
;;
(**
        Adds c to f.fcste
        @param f a flin
        @param c a rational
        @return the new flin
*)
let flin_add_cste f c =              
    {fhom=f.fhom;
     fcste=rplus f.fcste c}
;;

(**
        @return a empty flin with r1 in fcste
*)
let flin_one () = flin_add_cste (flin_zero()) r1;;

(**
        Adds two flin
*)
let flin_plus f1 f2 = 
    let f3 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f1.fhom;
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f2.fhom;
    flin_add_cste (flin_add_cste f3 f1.fcste) f2.fcste;
;;

(**
        Substracts two flin
*)
let flin_minus f1 f2 = 
    let f3 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f1.fhom;
    Hashtbl.iter (fun x c -> let _=flin_add f3 x (rop c) in ()) f2.fhom;
    flin_add_cste (flin_add_cste f3 f1.fcste) (rop f2.fcste);
;;

(**
        @return a times f
*)
let flin_emult a f =
    let f2 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f2 x (rmult a c) in ()) f.fhom;
    flin_add_cste f2 (rmult a f.fcste);
;;

   
(*****************************************************************************)


(**
        @param t a term
        @raise Failure if conversion is impossible
        @return rational proiection of t
*)
let rec rational_of_term t =
  (* fun to apply f to the first and second rational-term of l *)
  let rat_of_binop f l =
          let a = List.hd l and
            b = List.hd(List.tl l) in
        f (rational_of_term a) (rational_of_term b)
  in
  (* as before, but f is unary *)
  let rat_of_unop f l =
          f (rational_of_term (List.hd l))
  in
  match t with
  | Cic.Cast (t1,t2) -> (rational_of_term t1)
  | Cic.Appl (t1::next) ->
        (match t1 with
           Cic.Const (u,boh) ->
            if UriManager.eq u HelmLibraryObjects.Reals.ropp_URI then
                      rat_of_unop rop next 
            else if UriManager.eq u HelmLibraryObjects.Reals.rinv_URI then
                      rat_of_unop rinv next 
            else if UriManager.eq u HelmLibraryObjects.Reals.rmult_URI then
                      rat_of_binop rmult next
            else if UriManager.eq u HelmLibraryObjects.Reals.rdiv_URI then
                      rat_of_binop rdiv next
            else if UriManager.eq u HelmLibraryObjects.Reals.rplus_URI then
                      rat_of_binop rplus next
            else if UriManager.eq u HelmLibraryObjects.Reals.rminus_URI then
                      rat_of_binop rminus next
            else failwith "not a rational"
          | _ -> failwith "not a rational")
  | Cic.Const (u,boh) ->
        if UriManager.eq u HelmLibraryObjects.Reals.r1_URI then r1
        else if UriManager.eq u HelmLibraryObjects.Reals.r0_URI then r0
        else failwith "not a rational"
  |  _ -> failwith "not a rational"
;;

(* coq wrapper
let rational_of_const = rational_of_term;;
*)
let fails f a =
 try
  ignore (f a);
  false
 with 
   _-> true
 ;;

let rec flin_of_term t =
        let fl_of_binop f l =
                let a = List.hd l and
                    b = List.hd(List.tl l) in
                f (flin_of_term a)  (flin_of_term b)
        in
  try(
    match t with
  | Cic.Cast (t1,t2) -> (flin_of_term t1)
  | Cic.Appl (t1::next) ->
        begin
        match t1 with
        Cic.Const (u,boh) ->
            begin
             if UriManager.eq u HelmLibraryObjects.Reals.ropp_URI then
                  flin_emult (rop r1) (flin_of_term (List.hd next))
             else if UriManager.eq u HelmLibraryObjects.Reals.rplus_URI then
                  fl_of_binop flin_plus next 
             else if UriManager.eq u HelmLibraryObjects.Reals.rminus_URI then
                  fl_of_binop flin_minus next
             else if UriManager.eq u HelmLibraryObjects.Reals.rmult_URI then
                     begin
                let arg1 = (List.hd next) and
                    arg2 = (List.hd(List.tl next)) 
                in
                if fails rational_of_term arg1 
                   then
                   if fails rational_of_term arg2
                      then
                      ( (* prodotto tra 2 incognite ????? impossibile*)
                      failwith "Sistemi lineari!!!!\n" 
                      )
                      else
                      (
                      match arg1 with
                      Cic.Rel(n) -> (*trasformo al volo*)
                                    (flin_add (flin_zero()) arg1 (rational_of_term arg2))
                       |_-> (* test this *)
                           let tmp = flin_of_term arg1 in
                           flin_emult  (rational_of_term arg2) (tmp)
                      )
                   else
                   if fails rational_of_term arg2
                      then
                      (
                      match arg2 with
                      Cic.Rel(n) -> (*trasformo al volo*)
                                    (flin_add (flin_zero()) arg2 (rational_of_term arg1))
                       |_-> (* test this *)
                           let tmp = flin_of_term arg2 in
                           flin_emult (rational_of_term arg1) (tmp)

                      )
                      else
                      (  (*prodotto tra razionali*)
                      (flin_add_cste (flin_zero()) (rmult (rational_of_term arg1) (rational_of_term arg2)))  
                      )
                          (*try
                        begin
                        (*let a = rational_of_term arg1 in
                        debug("ho fatto rational of term di "^CicPp.ppterm arg1^
                         " e ho ottenuto "^string_of_int a.num^"/"^string_of_int a.den^"\n");*)
                        let a = flin_of_term arg1  
                           try 
                                begin
                                let b = (rational_of_term arg2) in
                                debug("ho fatto rational of term di "^CicPp.ppterm arg2^
                                 " e ho ottenuto "^string_of_int b.num^"/"^string_of_int b.den^"\n");
                                    (flin_add_cste (flin_zero()) (rmult a b))
                                end
                           with 
                                _ -> debug ("ho fallito2 su "^CicPp.ppterm arg2^"\n");
                                     (flin_add (flin_zero()) arg2 a)
                        end
                      with 
                        _-> debug ("ho fallito1 su "^CicPp.ppterm arg1^"\n");
                            (flin_add(flin_zero()) arg1 (rational_of_term arg2))
                            *)
                end
            else if UriManager.eq u HelmLibraryObjects.Reals.rinv_URI then
               let a=(rational_of_term (List.hd next)) in
               flin_add_cste (flin_zero()) (rinv a)
            else if UriManager.eq u HelmLibraryObjects.Reals.rdiv_URI then
                    begin
                      let b=(rational_of_term (List.hd(List.tl next))) in
                       try 
                        begin
                        let a = (rational_of_term (List.hd next)) in
                        (flin_add_cste (flin_zero()) (rdiv a b))
                        end
                       with 
                        _-> (flin_add (flin_zero()) (List.hd next) (rinv b))
                end
            else assert false
            end
        |_ -> assert false
        end
  | Cic.Const (u,boh) ->
        begin
         if UriManager.eq u HelmLibraryObjects.Reals.r1_URI then flin_one ()
         else if UriManager.eq u HelmLibraryObjects.Reals.r0_URI then flin_zero ()
         else assert false
        end
  |_-> assert false)
  with _ -> debug("eccezione = "^CicPp.ppterm t^"\n");flin_add (flin_zero()) t r1
;;

(* coq wrapper
let flin_of_constr = flin_of_term;;
*)

(**
        Translates a flin to (c,x) list
        @param f a flin
        @return something like (c1,x1)::(c2,x2)::...::(cn,xn)
*)
let flin_to_alist f =
    let res=ref [] in
    Hashtbl.iter (fun x c -> res:=(c,x)::(!res)) f;
    !res
;;

(* Représentation des hypothèses qui sont des inéquations ou des équations.
*)

(**
        The structure for ineq
*)
type hineq={hname:Cic.term; (* le nom de l'hypothèse *)
            htype:string; (* Rlt, Rgt, Rle, Rge, eqTLR ou eqTRL *)
            hleft:Cic.term;
            hright:Cic.term;
            hflin:flin;
            hstrict:bool}
;;

(* Transforme une hypothese h:t en inéquation flin<0 ou flin<=0
*)

let ineq1_of_term (h,t) =
    match t with (* match t *)
       Cic.Appl (t1::next) ->
         let arg1= List.hd next in
         let arg2= List.hd(List.tl next) in
         (match t1 with (* match t1 *)
           Cic.Const (u,boh) ->
             if UriManager.eq u HelmLibraryObjects.Reals.rlt_URI then
                            [{hname=h;
                           htype="Rlt";
                           hleft=arg1;
                           hright=arg2;
                           hflin= flin_minus (flin_of_term arg1)
                                             (flin_of_term arg2);
                           hstrict=true}]
             else if UriManager.eq u HelmLibraryObjects.Reals.rgt_URI then
                           [{hname=h;
                           htype="Rgt";
                           hleft=arg2;
                           hright=arg1;
                           hflin= flin_minus (flin_of_term arg2)
                                             (flin_of_term arg1);
                           hstrict=true}]
             else if UriManager.eq u HelmLibraryObjects.Reals.rle_URI then
                           [{hname=h;
                           htype="Rle";
                           hleft=arg1;
                           hright=arg2;
                           hflin= flin_minus (flin_of_term arg1)
                                             (flin_of_term arg2);
                           hstrict=false}]
             else if UriManager.eq u HelmLibraryObjects.Reals.rge_URI then
                           [{hname=h;
                           htype="Rge";
                           hleft=arg2;
                           hright=arg1;
                           hflin= flin_minus (flin_of_term arg2)
                                             (flin_of_term arg1);
                           hstrict=false}]
             else assert false
          | Cic.MutInd (u,i,o) ->
             if UriManager.eq u HelmLibraryObjects.Logic.eq_URI then
                            let t0= arg1 in
                           let arg1= arg2 in
                           let arg2= List.hd(List.tl (List.tl next)) in
                    (match t0 with
                         Cic.Const (u,boh) ->
                           if UriManager.eq u HelmLibraryObjects.Reals.r_URI then
                         [{hname=h;
                           htype="eqTLR";
                           hleft=arg1;
                           hright=arg2;
                           hflin= flin_minus (flin_of_term arg1)
                                             (flin_of_term arg2);
                           hstrict=false};
                          {hname=h;
                           htype="eqTRL";
                           hleft=arg2;
                           hright=arg1;
                           hflin= flin_minus (flin_of_term arg2)
                                             (flin_of_term arg1);
                           hstrict=false}]
                          else assert false
                        |_-> assert false)
                  else assert false
          |_-> assert false)(* match t1 *)
        |_-> assert false (* match t *)
;;
(* coq wrapper 
let ineq1_of_constr = ineq1_of_term;;
*)

(* Applique la méthode de Fourier à une liste d'hypothèses (type hineq)
*)

let rec print_rl l =
 match l with
 []-> ()
 | a::next -> Fourier.print_rational a ; print_string " " ; print_rl next
;;

let rec print_sys l =
 match l with
 [] -> ()
 | (a,b)::next -> (print_rl a;
                 print_string (if b=true then "strict\n"else"\n");
                print_sys next)
 ;;

(*let print_hash h =
        Hashtbl.iter (fun x y -> print_string ("("^"-"^","^"-"^")")) h
;;*)

let fourier_lineq lineq1 = 
   let nvar=ref (-1) in
   let hvar=Hashtbl.create 50 in (* la table des variables des inéquations *)
   List.iter (fun f ->
               Hashtbl.iter (fun x c ->
                                 try ignore(Hashtbl.find hvar x)
                                 with Not_found -> nvar:=(!nvar)+1;
                                             Hashtbl.add hvar x (!nvar);
                                          debug("aggiungo una var "^
                                           string_of_int !nvar^" per "^
                                            CicPp.ppterm x^"\n"))
                            f.hflin.fhom)
             lineq1;
   (*print_hash hvar;*)
   debug("Il numero di incognite e' "^string_of_int (!nvar+1)^"\n");
   let sys= List.map (fun h->
               let v=Array.create ((!nvar)+1) r0 in
               Hashtbl.iter (fun x c -> v.(Hashtbl.find hvar x) <- c) 
                  h.hflin.fhom;
               ((Array.to_list v)@[rop h.hflin.fcste],h.hstrict))
             lineq1 in
   debug ("chiamo unsolvable sul sistema di "^ 
    string_of_int (List.length sys) ^"\n");
   print_sys sys;
   unsolvable sys
;;

(*****************************************************************************
Construction de la preuve en cas de succès de la méthode de Fourier,
i.e. on obtient une contradiction.
*)


let _eqT = Cic.MutInd(HelmLibraryObjects.Logic.eq_URI, 0, []) ;;
let _False = Cic.MutInd (HelmLibraryObjects.Logic.false_URI, 0, []) ;;
let _not = Cic.Const (HelmLibraryObjects.Logic.not_URI,[]);;
let _R0 = Cic.Const (HelmLibraryObjects.Reals.r0_URI,[]);;
let _R1 = Cic.Const (HelmLibraryObjects.Reals.r1_URI,[]);;
let _R = Cic.Const (HelmLibraryObjects.Reals.r_URI,[]);;
let _Rfourier_eqLR_to_le=Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_eqLR_to_le.con"), []) ;;
let _Rfourier_eqRL_to_le=Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_eqRL_to_le.con"), []) ;;
let _Rfourier_ge_to_le  =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_ge_to_le.con"), []) ;;
let _Rfourier_gt_to_lt         =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_gt_to_lt.con"), []) ;;
let _Rfourier_le=Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_le.con"), []) ;;
let _Rfourier_le_le =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_le_le.con"), []) ;;
let _Rfourier_le_lt =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_le_lt.con"), []) ;;
let _Rfourier_lt=Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_lt.con"), []) ;;
let _Rfourier_lt_le =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_lt_le.con"), []) ;;
let _Rfourier_lt_lt =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_lt_lt.con"), []) ;;
let _Rfourier_not_ge_lt = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_not_ge_lt.con"), []) ;;
let _Rfourier_not_gt_le = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_not_gt_le.con"), []) ;;
let _Rfourier_not_le_gt = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_not_le_gt.con"), []) ;;
let _Rfourier_not_lt_ge = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rfourier_not_lt_ge.con"), []) ;;
let _Rinv  = Cic.Const (HelmLibraryObjects.Reals.rinv_URI, []);;
let _Rinv_R1 = Cic.Const(HelmLibraryObjects.Reals.rinv_r1_URI, []);;
let _Rle = Cic.Const (HelmLibraryObjects.Reals.rle_URI, []);;
let _Rle_mult_inv_pos =  Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rle_mult_inv_pos.con"), []) ;;
let _Rle_not_lt = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rle_not_lt.con"), []) ;;
let _Rle_zero_1 = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rle_zero_1.con"), []) ;;
let _Rle_zero_pos_plus1 =  Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rle_zero_pos_plus1.con"), []) ;;
let _Rlt = Cic.Const (HelmLibraryObjects.Reals.rlt_URI, []);;
let _Rlt_mult_inv_pos = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rlt_mult_inv_pos.con"), []) ;;
let _Rlt_not_le =  Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rlt_not_le.con"), []) ;;
let _Rlt_zero_1 = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rlt_zero_1.con"), []) ;;
let _Rlt_zero_pos_plus1 = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rlt_zero_pos_plus1.con"), []) ;;
let _Rminus = Cic.Const (HelmLibraryObjects.Reals.rminus_URI, []);;
let _Rmult = Cic.Const (HelmLibraryObjects.Reals.rmult_URI, []);;
let _Rnot_le_le =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rnot_le_le.con"), []) ;;
let _Rnot_lt0 = Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rnot_lt0.con"), []) ;;
let _Rnot_lt_lt =Cic.Const ((UriManager.uri_of_string 
 "cic:/Coq/fourier/Fourier_util/Rnot_lt_lt.con"), []) ;;
let _Ropp = Cic.Const (HelmLibraryObjects.Reals.ropp_URI, []);;
let _Rplus = Cic.Const (HelmLibraryObjects.Reals.rplus_URI, []);;

(******************************************************************************)

let is_int x = (x.den)=1
;;

(* fraction = couple (num,den) *)
let rec rational_to_fraction x= (x.num,x.den)
;;
    
(* traduction -3 -> (Ropp (Rplus R1 (Rplus R1 R1)))
*)

let rec int_to_real_aux n =
  match n with
    0 -> _R0 (* o forse R0 + R0 ????? *)
  | 1 -> _R1
  | _ -> Cic.Appl [ _Rplus ; _R1 ; int_to_real_aux (n-1) ]
;;        
        

let int_to_real n =
   let x = int_to_real_aux (abs n) in
   if n < 0 then
           Cic.Appl [ _Ropp ; x ] 
   else
           x
;;


(* -1/2 -> (Rmult (Ropp R1) (Rinv (Rplus R1 R1)))
*)

let rational_to_real x =
   let (n,d)=rational_to_fraction x in 
   Cic.Appl [ _Rmult ; int_to_real n ; Cic.Appl [ _Rinv ; int_to_real d ]  ]
;;

(* preuve que 0<n*1/d
*)

let tac_zero_inf_pos (n,d) =
 let tac_zero_inf_pos (n,d) status =
   (*let cste = pf_parse_constr gl in*)
   let pall str (proof,goal) t =
     debug ("tac "^str^" :\n" );
     let curi,metasenv,_subst,pbo,pty, attrs = proof in
     let metano,context,ty = CicUtil.lookup_meta goal metasenv in
     debug ("th = "^ CicPp.ppterm t ^"\n"); 
     debug ("ty = "^ CicPp.ppterm ty^"\n"); 
   in
   let tacn=ref (mk_tactic (fun status -> 
        pall "n0" status _Rlt_zero_1 ;
        apply_tactic (PrimitiveTactics.apply_tac ~term:_Rlt_zero_1) status )) in
   let tacd=ref (mk_tactic (fun status -> 
        pall "d0" status _Rlt_zero_1 ;
        apply_tactic (PrimitiveTactics.apply_tac ~term:_Rlt_zero_1) status )) in


  for i=1 to n-1 do 
       tacn:=(Tacticals.then_ 
        ~start:(mk_tactic (fun status -> 
          pall ("n"^string_of_int i) status _Rlt_zero_pos_plus1;
          apply_tactic 
           (PrimitiveTactics.apply_tac ~term:_Rlt_zero_pos_plus1)
           status))
        ~continuation:!tacn); 
  done;
  for i=1 to d-1 do
       tacd:=(Tacticals.then_ 
        ~start:(mk_tactic (fun status -> 
          pall "d" status _Rlt_zero_pos_plus1 ;
          apply_tactic 
           (PrimitiveTactics.apply_tac ~term:_Rlt_zero_pos_plus1) status)) 
        ~continuation:!tacd); 
  done;

debug("TAC ZERO INF POS\n");
  apply_tactic 
  (Tacticals.thens 
    ~start:(PrimitiveTactics.apply_tac ~term:_Rlt_mult_inv_pos)
    ~continuations:[!tacn ;!tacd ] )
  status
 in
  mk_tactic (tac_zero_inf_pos (n,d))
;;



(* preuve que 0<=n*1/d
*)
 
let tac_zero_infeq_pos gl (n,d) =
 let tac_zero_infeq_pos gl (n,d) status =
  (*let cste = pf_parse_constr gl in*)
  debug("inizio tac_zero_infeq_pos\n");
  let tacn = ref 
   (*(if n=0 then
     (PrimitiveTactics.apply_tac ~term:_Rle_zero_zero ) 
    else*)
     (PrimitiveTactics.apply_tac ~term:_Rle_zero_1 )
  (* ) *)
   in
   let tacd=ref (PrimitiveTactics.apply_tac ~term:_Rlt_zero_1 ) in
   for i=1 to n-1 do 
       tacn:=(Tacticals.then_ ~start:(PrimitiveTactics.apply_tac 
        ~term:_Rle_zero_pos_plus1) ~continuation:!tacn); 
   done;
   for i=1 to d-1 do
       tacd:=(Tacticals.then_ ~start:(PrimitiveTactics.apply_tac 
        ~term:_Rlt_zero_pos_plus1) ~continuation:!tacd); 
   done;
   apply_tactic 
    (Tacticals.thens 
     ~start:(PrimitiveTactics.apply_tac ~term:_Rle_mult_inv_pos) 
     ~continuations:[!tacn;!tacd]) status 
 in
  mk_tactic (tac_zero_infeq_pos gl (n,d))
;;


 
(* preuve que 0<(-n)*(1/d) => False 
*)

let tac_zero_inf_false gl (n,d) =
 let tac_zero_inf_false gl (n,d) status =
   if n=0 then 
    apply_tactic (PrimitiveTactics.apply_tac ~term:_Rnot_lt0) status
   else
    apply_tactic (Tacticals.then_ 
     ~start:(mk_tactic (apply_tactic (PrimitiveTactics.apply_tac ~term:_Rle_not_lt)))
     ~continuation:(tac_zero_infeq_pos gl (-n,d))) 
    status
 in
  mk_tactic (tac_zero_inf_false gl (n,d))
;;

(* preuve que 0<=n*(1/d) => False ; n est negatif
*)

let tac_zero_infeq_false gl (n,d) =
 let tac_zero_infeq_false gl (n,d) status =
  let (proof, goal) = status in
  let curi,metasenv,_subst,pbo,pty, attrs = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  
  debug("faccio fold di " ^ CicPp.ppterm
         (Cic.Appl
           [_Rle ; _R0 ;
            Cic.Appl
             [_Rmult ; int_to_real n ; Cic.Appl [_Rinv ; int_to_real d]]
           ]
         ) ^ "\n") ;
  debug("apply di _Rlt_not_le a "^ CicPp.ppterm ty ^"\n");
  (*CSC: Patch to undo the over-simplification of RewriteSimpl *)
  apply_tactic 
   (Tacticals.then_
    ~start:
      (ReductionTactics.fold_tac
        ~reduction:(const_lazy_reduction CicReduction.whd)
        ~pattern:(ProofEngineTypes.conclusion_pattern None)
        ~term:
          (const_lazy_term
            (Cic.Appl
            [_Rle ; _R0 ;
              Cic.Appl
               [_Rmult ; int_to_real n ; Cic.Appl [_Rinv ; int_to_real d]]])))
    ~continuation:
      (Tacticals.then_ 
        ~start:(PrimitiveTactics.apply_tac ~term:_Rlt_not_le)
        ~continuation:(tac_zero_inf_pos (-n,d))))
   status 
 in
  mk_tactic (tac_zero_infeq_false gl (n,d))
;;


(* *********** ********** ******** ??????????????? *********** **************)

let apply_type_tac ~cast:t ~applist:al = 
 let apply_type_tac ~cast:t ~applist:al (proof,goal) = 
  let curi,metasenv,_subst,pbo,pty, attrs = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let fresh_meta = ProofEngineHelpers.new_meta_of_proof proof in
  let irl =
   CicMkImplicit.identity_relocation_list_for_metavariable context in
  let metasenv' = (fresh_meta,context,t)::metasenv in
   let proof' = curi,metasenv',_subst,pbo,pty, attrs in
    let proof'',goals =
     apply_tactic 
      (PrimitiveTactics.apply_tac 
       (*~term:(Cic.Appl ((Cic.Cast (Cic.Meta (fresh_meta,irl),t))::al)) *)
       ~term:(Cic.Appl ((Cic.Meta (fresh_meta,irl))::al))) (* ??? *)
      (proof',goal)
    in
     proof'',fresh_meta::goals
 in
  mk_tactic (apply_type_tac ~cast:t ~applist:al)
;;

let my_cut ~term:c =
 let my_cut ~term:c (proof,goal) =
  let curi,metasenv,_subst,pbo,pty, attrs = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let fresh_meta = ProofEngineHelpers.new_meta_of_proof proof in
  let irl =
   CicMkImplicit.identity_relocation_list_for_metavariable context in
  let metasenv' = (fresh_meta,context,c)::metasenv in
   let proof' = curi,metasenv',_subst,pbo,pty, attrs in
    let proof'',goals =
     apply_tactic 
      (apply_type_tac 
       ~cast:(Cic.Prod(Cic.Name "Anonymous",c,CicSubstitution.lift 1 ty)) 
       ~applist:[Cic.Meta(fresh_meta,irl)])
      (proof',goal)
    in
     (* We permute the generated goals to be consistent with Coq *)
     match goals with
        [] -> assert false
      | he::tl -> proof'',he::fresh_meta::tl
 in
  mk_tactic (my_cut ~term:c)
;;

let exact = PrimitiveTactics.exact_tac;;

let tac_use h = 
 let tac_use h status = 
  let (proof, goal) = status in
  debug("Inizio TC_USE\n");
  let curi,metasenv,_subst,pbo,pty, attrs = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  debug ("hname = "^ CicPp.ppterm h.hname ^"\n"); 
  debug ("ty = "^ CicPp.ppterm ty^"\n");
  apply_tactic 
   (match h.htype with
      "Rlt" -> exact ~term:h.hname 
    | "Rle" -> exact ~term:h.hname 
    | "Rgt" -> (Tacticals.then_ 
                 ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_gt_to_lt) 
                 ~continuation:(exact ~term:h.hname)) 
    | "Rge" -> (Tacticals.then_ 
                 ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_ge_to_le)
                 ~continuation:(exact ~term:h.hname)) 
    | "eqTLR" -> (Tacticals.then_ 
                   ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_eqLR_to_le)
                   ~continuation:(exact ~term:h.hname)) 
    | "eqTRL" -> (Tacticals.then_ 
                   ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_eqRL_to_le)
                   ~continuation:(exact ~term:h.hname)) 
    | _->assert false)
   status
 in
  mk_tactic (tac_use h)
;;

let is_ineq (h,t) =
    match t with
       Cic.Appl ( Cic.Const(u,boh)::next) ->
         (if UriManager.eq u HelmLibraryObjects.Reals.rlt_URI or
             UriManager.eq u HelmLibraryObjects.Reals.rgt_URI or
             UriManager.eq u HelmLibraryObjects.Reals.rle_URI or
             UriManager.eq u HelmLibraryObjects.Reals.rge_URI then true
          else if UriManager.eq u HelmLibraryObjects.Logic.eq_URI then
                   (match (List.hd next) with
                       Cic.Const (uri,_) when
                        UriManager.eq uri HelmLibraryObjects.Reals.r_URI
                         -> true
                     | _ -> false)
           else false)
     |_->false
;;

let list_of_sign s = List.map (fun (x,_,z)->(x,z)) s;;

let mkAppL a =
   Cic.Appl(Array.to_list a)
;;

(* Résolution d'inéquations linéaires dans R *)
let rec strip_outer_cast c = match c with
  | Cic.Cast (c,_) -> strip_outer_cast c
  | _ -> c
;;

(*let find_in_context id context =
  let rec find_in_context_aux c n =
          match c with
        [] -> failwith (id^" not found in context")      
        | a::next -> (match a with 
                        Some (Cic.Name(name),_) when name = id -> n 
                              (*? magari al posto di _ qualcosaltro?*)
                        | _ -> find_in_context_aux next (n+1))
  in 
  find_in_context_aux context 1 
;;

(* mi sembra quadratico *)
let rec filter_real_hyp context cont =
  match context with
  [] -> []
  | Some(Cic.Name(h),Cic.Decl(t))::next -> (
                                  let n = find_in_context h cont in
                                debug("assegno "^string_of_int n^" a "^CicPp.ppterm t^"\n");
                          [(Cic.Rel(n),t)] @ filter_real_hyp next cont)
  | a::next -> debug("  no\n"); filter_real_hyp next cont
;;*)

let filter_real_hyp context _ =
  let rec filter_aux context num =
   match context with
     [] -> []
   | Some(Cic.Name(h),Cic.Decl(t))::next -> 
       [(Cic.Rel(num),t)] @ filter_aux next (num+1)
   | a::next -> filter_aux next (num+1)
  in
   filter_aux context 1
;;


(* lifts everithing at the conclusion level *)        
let rec superlift c n=
  match c with
    [] -> []
  | Some(name,Cic.Decl(a))::next  -> 
     [Some(name,Cic.Decl(CicSubstitution.lift n a))]@ superlift next (n+1)
  | Some(name,Cic.Def(a,ty))::next   -> 
     [Some(name,
      Cic.Def((CicSubstitution.lift n a),CicSubstitution.lift n ty))
      ] @ superlift next (n+1)
  | _::next -> superlift next (n+1) (*??  ??*)
 
;;

let equality_replace a b =
 let equality_replace a b status =
 debug("inizio EQ\n");
  let module C = Cic in
   let proof,goal = status in
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
   let metano,context,ty = CicUtil.lookup_meta goal metasenv in
    let a_eq_b = C.Appl [ _eqT ; _R ; a ; b ] in
    let fresh_meta = ProofEngineHelpers.new_meta_of_proof proof in
    let irl =
     CicMkImplicit.identity_relocation_list_for_metavariable context in
    let metasenv' = (fresh_meta,context,a_eq_b)::metasenv in
 debug("chamo rewrite tac su"^CicPp.ppterm (C.Meta (fresh_meta,irl)));
    let (proof,goals) = apply_tactic 
     (EqualityTactics.rewrite_simpl_tac
       ~direction:`LeftToRight
       ~pattern:(ProofEngineTypes.conclusion_pattern None)
       (C.Meta (fresh_meta,irl)) [])
     ((curi,metasenv',_subst,pbo,pty, attrs),goal)
    in
    let new_goals = fresh_meta::goals in
 debug("fine EQ -> goals : "^string_of_int( List.length new_goals)  ^" = "
   ^string_of_int( List.length goals)^"+ meta\n");
     (proof,new_goals)
 in 
  mk_tactic (equality_replace a b)
;;

let tcl_fail a (proof,goal) =
  match a with
    1 -> raise (ProofEngineTypes.Fail (lazy "fail-tactical"))
  | _ -> (proof,[goal])
;;

(* Galla: moved in variousTactics.ml 
let assumption_tac (proof,goal)=
  let curi,metasenv,pbo,pty = proof in
  let metano,context,ty = CicUtil.lookup_meta goal metasenv in
  let num = ref 0 in
  let tac_list = List.map 
          ( fun x -> num := !num + 1;
                match x with
                  Some(Cic.Name(nm),t) -> (nm,exact ~term:(Cic.Rel(!num)))
                  | _ -> ("fake",tcl_fail 1)
        )  
          context 
  in
  Tacticals.first ~tactics:tac_list (proof,goal)
;;
*)
(* Galla: moved in negationTactics.ml
(* !!!!! fix !!!!!!!!!! *)
let contradiction_tac (proof,goal)=
        Tacticals.then_ 
                (*inutile sia questo che quello prima  della chiamata*)
                ~start:PrimitiveTactics.intros_tac
                ~continuation:(Tacticals.then_ 
                        ~start:(VariousTactics.elim_type_tac ~term:_False) 
                        ~continuation:(assumption_tac))
        (proof,goal) 
;;
*)

(* ********************* TATTICA ******************************** *)

let rec fourier (s_proof,s_goal)=
  let s_curi,s_metasenv,_subst,s_pbo,s_pty, attrs = s_proof in
  let s_metano,s_context,s_ty = CicUtil.lookup_meta s_goal s_metasenv in
  debug ("invoco fourier_tac sul goal "^string_of_int(s_goal)^" e contesto:\n");
  debug_pcontext s_context;

(* here we need to negate the thesis, but to do this we need to apply the 
   right theoreme,so let's parse our thesis *)
  
  let th_to_appl = ref _Rfourier_not_le_gt in   
  (match s_ty with
   Cic.Appl ( Cic.Const(u,boh)::args) ->
    th_to_appl :=
    (if UriManager.eq u HelmLibraryObjects.Reals.rlt_URI then
      _Rfourier_not_ge_lt
     else if UriManager.eq u HelmLibraryObjects.Reals.rle_URI then
               _Rfourier_not_gt_le
     else if UriManager.eq u HelmLibraryObjects.Reals.rgt_URI then
               _Rfourier_not_le_gt
     else if UriManager.eq u HelmLibraryObjects.Reals.rge_URI then
               _Rfourier_not_lt_ge
     else failwith "fourier can't be applyed")
   |_-> failwith "fourier can't be applyed"); 
   (* fix maybe strip_outer_cast goes here?? *)

   (* now let's change our thesis applying the th and put it with hp *) 

   let proof,gl = apply_tactic 
    (Tacticals.then_ 
      ~start:(PrimitiveTactics.apply_tac ~term:!th_to_appl)
      ~continuation:(PrimitiveTactics.intros_tac ()))
    (s_proof,s_goal) 
   in
   let goal = if List.length gl = 1 then List.hd gl 
                                    else failwith "a new goal" in

   debug ("port la tesi sopra e la nego. contesto :\n");
   debug_pcontext s_context;

   (* now we have all the right environment *)
   
   let curi,metasenv,_subst,pbo,pty, attrs = proof in
   let metano,context,ty = CicUtil.lookup_meta goal metasenv in

   (* now we want to convert hp to inequations, but first we must lift
      everyting to thesis level, so that a variable has the save Rel(n) 
      in each hp ( needed by ineq1_of_term ) *)
    
    (* ? fix if None  ?????*)
    (* fix change superlift with a real name *)

  let l_context = superlift context 1 in
  let hyps = filter_real_hyp l_context l_context in
  
  debug ("trasformo in diseq. "^ string_of_int (List.length hyps)^" ipotesi\n");
  
  let lineq =ref [] in
  
  (* transform hyps into inequations *)
  
  List.iter (fun h -> try (lineq:=(ineq1_of_term h)@(!lineq))
                        with _-> ())
              hyps;
            
  debug ("applico fourier a "^ string_of_int (List.length !lineq)^
         " disequazioni\n");

  let res=fourier_lineq (!lineq) in
  let tac=ref Tacticals.id_tac in
  if res=[] then 
          (print_string "Tactic Fourier fails.\n";flush stdout;
         failwith "fourier_tac fails")
  else 
  (
  match res with (*match res*)
  [(cres,sres,lc)]->
  
     (* in lc we have the coefficient to "reduce" the system *)
     
     print_string "Fourier's method can prove the goal...\n";flush stdout;
         
     debug "I coeff di moltiplicazione rit sono: ";
     
     let lutil=ref [] in
     List.iter 
        (fun (h,c) -> if c<>r0 then (lutil:=(h,c)::(!lutil);
           (* DBG *)Fourier.print_rational(c);print_string " "(* DBG *))
                                     )
        (List.combine (!lineq) lc); 
        
     print_string (" quindi lutil e' lunga "^
      string_of_int (List.length (!lutil))^"\n");                   
       
     (* on construit la combinaison linéaire des inéquation *)
     
     (match (!lutil) with (*match (!lutil) *)
       (h1,c1)::lutil ->
       debug ("elem di lutil ");Fourier.print_rational c1;print_string "\n"; 
          
       let s=ref (h1.hstrict) in
          
          
       let t1 = ref (Cic.Appl [_Rmult;rational_to_real c1;h1.hleft] ) in
       let t2 = ref (Cic.Appl [_Rmult;rational_to_real c1;h1.hright]) in

       List.iter (fun (h,c) ->
               s:=(!s)||(h.hstrict);
               t1:=(Cic.Appl [_Rplus;!t1;Cic.Appl 
                     [_Rmult;rational_to_real c;h.hleft ]  ]);
               t2:=(Cic.Appl [_Rplus;!t2;Cic.Appl 
                     [_Rmult;rational_to_real c;h.hright]  ]))
               lutil;
               
       let ineq=Cic.Appl [(if (!s) then _Rlt else _Rle);!t1;!t2 ] in
       let tc=rational_to_real cres in


(* ora ho i termini che descrivono i passi di fourier per risolvere il sistema *)
       
       debug "inizio a costruire tac1\n";
       Fourier.print_rational(c1);
          
       let tac1=ref ( mk_tactic (fun status -> 
         apply_tactic
          (if h1.hstrict then 
           (Tacticals.thens 
             ~start:(mk_tactic (fun status -> 
              debug ("inizio t1 strict\n");
              let curi,metasenv,_subst,pbo,pty, attrs = proof in
              let metano,context,ty = CicUtil.lookup_meta goal metasenv in
              debug ("th = "^ CicPp.ppterm _Rfourier_lt ^"\n"); 
              debug ("ty = "^ CicPp.ppterm ty^"\n"); 
              apply_tactic 
               (PrimitiveTactics.apply_tac ~term:_Rfourier_lt) status))
            ~continuations:[tac_use h1;
              tac_zero_inf_pos (rational_to_fraction c1)])
          else 
           (Tacticals.thens 
             ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_le)
             ~continuations:[tac_use h1;tac_zero_inf_pos
              (rational_to_fraction c1)]))
          status))
                   
       in
       s:=h1.hstrict;
       List.iter (fun (h,c) -> 
         (if (!s) then 
           (if h.hstrict then 
             (debug("tac1 1\n");
             tac1:=(Tacticals.thens 
               ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_lt_lt)
               ~continuations:[!tac1;tac_use h;tac_zero_inf_pos
                (rational_to_fraction c)]))
            else 
             (debug("tac1 2\n");
             Fourier.print_rational(c1);
             tac1:=(Tacticals.thens 
              ~start:(mk_tactic (fun status -> 
                debug("INIZIO TAC 1 2\n");
                let curi,metasenv,_subst,pbo,pty, attrs = proof in
                let metano,context,ty = CicUtil.lookup_meta goal metasenv in
                debug ("th = "^ CicPp.ppterm _Rfourier_lt_le ^"\n"); 
                debug ("ty = "^ CicPp.ppterm ty^"\n"); 
                apply_tactic 
                 (PrimitiveTactics.apply_tac ~term:_Rfourier_lt_le) 
                 status))
              ~continuations:[!tac1;tac_use h;tac_zero_inf_pos 
                (rational_to_fraction c)])))
          else 
           (if h.hstrict then 
             (debug("tac1 3\n");
             tac1:=(Tacticals.thens 
               ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_le_lt)
               ~continuations:[!tac1;tac_use h;tac_zero_inf_pos  
                (rational_to_fraction c)]))
            else 
             (debug("tac1 4\n");
             tac1:=(Tacticals.thens 
               ~start:(PrimitiveTactics.apply_tac ~term:_Rfourier_le_le)
               ~continuations:[!tac1;tac_use h;tac_zero_inf_pos  
                (rational_to_fraction c)]))));
         s:=(!s)||(h.hstrict)) (* end fun -> *)
         lutil;(*end List.iter*)
                     
       let tac2 = 
         if sres then 
           tac_zero_inf_false goal (rational_to_fraction cres)
         else 
           tac_zero_infeq_false goal (rational_to_fraction cres)
       in
       tac:=(Tacticals.thens 
         ~start:(my_cut ~term:ineq) 
         ~continuations:[Tacticals.then_  
           ~start:( mk_tactic (fun status ->
             let (proof, goal) = status in
             let curi,metasenv,_subst,pbo,pty, attrs = proof in
             let metano,context,ty = CicUtil.lookup_meta goal metasenv in
             apply_tactic 
              (ReductionTactics.change_tac
                ~pattern:(ProofEngineTypes.conclusion_pattern (Some ty))
                (const_lazy_term (Cic.Appl [ _not; ineq])))
              status))
           ~continuation:(Tacticals.then_ 
             ~start:(PrimitiveTactics.apply_tac ~term:
               (if sres then _Rnot_lt_lt else _Rnot_le_le))
             ~continuation:(Tacticals.thens 
               ~start:(mk_tactic (fun status ->
                 debug("t1 ="^CicPp.ppterm !t1 ^"t2 ="^
                  CicPp.ppterm !t2 ^"tc="^ CicPp.ppterm tc^"\n");
                 let r = apply_tactic 
		  (equality_replace (Cic.Appl [_Rminus;!t2;!t1] ) tc) 
                  status
                 in
                 (match r with (p,gl) -> 
                   debug("eq1 ritorna "^string_of_int(List.length gl)^"\n" ));
                 r))
               ~continuations:[(Tacticals.thens 
                 ~start:(mk_tactic (fun status ->
                   let r = apply_tactic 
		    (equality_replace (Cic.Appl[_Rinv;_R1]) _R1) 
		    status 
		   in
                   (match r with (p,gl) ->
                     debug("eq2 ritorna "^string_of_int(List.length gl)^"\n" ));
                   r))
                 ~continuations:
                   [PrimitiveTactics.apply_tac ~term:_Rinv_R1;
		    Tacticals.first 
                     ~tactics:[Ring.ring_tac; Tacticals.id_tac] 
                   ])
               ;(*Tacticals.id_tac*)
                Tacticals.then_ 
                 ~start:(mk_tactic (fun status ->
                   let (proof, goal) = status in
                   let curi,metasenv,_subst,pbo,pty, attrs = proof in
                   let metano,context,ty = CicUtil.lookup_meta goal metasenv in
                   (* check if ty is of type *)
                   let w1 = 
                     debug("qui c'e' gia' l'or "^CicPp.ppterm ty^"\n");
                     (match ty with
                     Cic.Prod (Cic.Anonymous,a,b) -> (Cic.Appl [_not;a])
                     |_ -> assert false)
                   in
                   let r = apply_tactic 
		    (ReductionTactics.change_tac
                      ~pattern:(ProofEngineTypes.conclusion_pattern (Some ty))
                      (const_lazy_term w1)) status
                   in
                   debug("fine MY_CHNGE\n");
                   r)) 
                 ~continuation:(*PORTINGTacticals.id_tac*)tac2]))
         ;(*Tacticals.id_tac*)!tac1]);(*end tac:=*)

    |_-> assert false)(*match (!lutil) *)
  |_-> assert false); (*match res*)
  debug ("finalmente applico tac\n");
  (
  let r = apply_tactic !tac (proof,goal) in
  debug("\n\n]]]]]]]]]]]]]]]]]) That's all folks ([[[[[[[[[[[[[[[[[[[\n\n");r
  
  ) 
;;

let fourier_tac = mk_tactic fourier


