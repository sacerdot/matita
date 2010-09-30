(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

(* $Id: nCic.ml 9058 2008-10-13 17:42:30Z tassi $ *)

let rec repeat f l = match f l with None -> l | Some l -> repeat f l;;

type ('s,'g) tree = Node of 's * ('g * ('s,'g) tree) list | Nil

type ('s,'g) tree_ctx = 
  | Ctx of ('s,'g) tree_ctx * 's * 
             ('g * ('s,'g) tree) list * 'g *  ('g * ('s,'g) tree) list 
  | Top

type ('a,'s,'g) position = Loc of ('s,'g) tree_ctx * ('s,'g) tree

let start (t : ('s,'g) tree) : ('a,'s,'g) position = Loc (Top, t);;

let down = function 
  | Loc (_,(Nil|Node (_,[]))) -> None
  | Loc (ctx, Node (s,(x,t)::tl)) -> Some (Loc (Ctx (ctx,s,[],x,tl),t))
;;

let downr = function 
  | Loc (_,(Nil|Node (_,[]))) -> None
  | Loc (ctx, Node (s,(_::_ as l))) -> 
     match List.rev l with
     | [] -> assert false
     | (x,t) :: tl ->     
         Some (Loc (Ctx (ctx,s,tl,x,[]),t))
;;

let up = function
  | Loc (Top,_) -> None
  | Loc (Ctx(ctx,s,l,x,r),t) -> Some (Loc (ctx,Node (s,(List.rev l)@[x,t]@r)))
;;

let right = function
  | Loc (Top,_) | Loc (Ctx(_,_,_,_,[]),_) -> None
  | Loc (Ctx(ctx,s,l,x,(rx,rt)::tl),t)-> Some (Loc(Ctx(ctx,s,(x,t)::l,rx,tl),rt))
;;

let left = function
  | Loc (Top,_) | Loc (Ctx(_,_,[],_,_),_) -> None
  | Loc (Ctx(ctx,s,(lx,lt)::tl,x,r),t)->Some (Loc(Ctx(ctx,s,tl,lx,(x,t)::r),lt))
;;

let get = function
  | Loc(Top,_) -> assert false
  | Loc(Ctx(_,s,_,x,_),_) -> s,x
;;

let is_top = function Loc(Top,_) -> true | _ -> false;;

let set s x = function
  | Loc(Top,_) -> assert false
  | Loc(Ctx(c,_,l,_,r),t) -> Loc(Ctx(c,s,l,x,r),t)
;;

let root t =
  match repeat up t with
  | Loc(Top,t) -> t
  | _ -> assert false
;;

let eject (Loc (_,t)) = t ;;

let inject t (Loc (c,_)) = Loc(c,t) ;;

let dump ppg pps pos fmt =
  let module Pp = GraphvizPp.Dot in
  let c = ref 0 in
  let skip = Node (Obj.magic (),[]) in
  let rec aux_t = function 
    | Nil -> 
        Pp.node ("node"^string_of_int !c) ~attrs:["shape","point"] fmt
    | Node (s,l) ->
        let j = !c in
        Pp.node ("node"^string_of_int j) ~attrs:["shape","record"; 
          "label",String.concat "|"
            (HExtlib.list_mapi 
              (fun (x,_) i -> "<f"^string_of_int i^"> " ^ ppg x)
            l)] fmt;
        pps s ("node"^string_of_int j) fmt;
        ignore(HExtlib.list_mapi 
          (fun (_,t) i -> if t != skip then begin 
             incr c;
             let k = !c in
             Pp.edge 
               ("node"^string_of_int j^":f"^string_of_int i)
               ("node"^string_of_int k) fmt;
               aux_t t end)
          l)
  in
  let rec aux pos = 
    match pos with
    | Top -> ()
    | Ctx(ctx,s,l,x,r) ->
        let t = Node(s,(List.rev l)@[x,skip]@r) in
        let cur = !c in
        aux_t t;
        incr c;
        if ctx <> Top then
          Pp.edge 
            ("node"^string_of_int !c)
            ("node"^string_of_int cur^":f"^string_of_int( List.length l))
            fmt; 
        aux ctx
  in
  let Loc (ctx, t) = pos in
  let l = match ctx with Top -> assert false | Ctx (_,_,l,_,_)->List.rev l in
  let cur = !c in
  Pp.node ("node"^string_of_int !c) 
    ~attrs:["style","filled";"fillcolor","red";"color","red"] fmt;
  Pp.edge  ("node"^string_of_int !c)  ("node"^string_of_int !c) fmt;
  aux_t t;
  incr c;
  Pp.edge 
    ("node"^string_of_int !c^":f"^string_of_int (List.length l))
    ("node"^string_of_int cur)
    fmt; 
  aux ctx
;;

