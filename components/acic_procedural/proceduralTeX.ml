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

module F   = Format
module C   = Cic
module DTI = DoubleTypeInference
module H   = ProceduralHelpers
module T   = ProceduralTypes

type sorts = (Cic.id, Cic2acic.sort_kind) Hashtbl.t

let num n =
   if n < 2 then "" else
   if n < 27 then String.make 1 (Char.chr (n - 2 + Char.code 'b')) else
   assert false

let quote str =
   Pcre.replace ~pat:"_" ~templ:"\\_" str

let xn frm = function
   | C.Anonymous -> assert false
   | C.Name r    -> F.fprintf frm "%s" (quote r)

let xr c frm j =
   try match List.nth c (pred j) with
      | Some (r, _) -> xn frm r
      | None        -> assert false
   with Invalid_argument "nth" -> assert false

let xs frm = function
   | C.Set     -> F.fprintf frm "\\Set"
   | C.Prop    -> F.fprintf frm "\\Prop"
   | C.CProp _ -> F.fprintf frm "\\CProp"
   | C.Type _  -> F.fprintf frm "\\Type"

let rec xt c frm = function
   | C.Sort s                     ->
      xs frm s  
   | C.Const (i, [])              ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i None None))
   | C.MutInd (i, n, [])          ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i (Some n) None))
   | C.MutConstruct (i, n, m, []) ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i (Some n) (Some m)))
   | C.Rel j                      ->
      F.fprintf frm "\\LRef{%a}" (xr c) j
   | C.Cast (t, u)                ->
      F.fprintf frm "\\Cast{%a}{%a}" (xt c) u (xt c) t
   | C.Appl (t :: vs)             ->
      let z = num (List.length vs) in      
      F.fprintf frm "\\%sAppl%a{%a}" z (xts c) vs (xt c) t
   | C.MutCase (_, _, u, v, ts)   ->
      let z = num (List.length ts) in
      F.fprintf frm "\\%sCase{%a}{%a}%a" z (xt c) u (xt c) v (xts c) ts
   | C.LetIn (r, v, w, t)         ->
      let d = Some (r, C.Def (v, w)) :: c in
      F.fprintf frm "\\Abbr{%a}{%a}{%a}" xn r (xt c) v (xt d) t
   | C.Lambda (r, w, t)           ->
      let d = Some (r, C.Decl w) :: c in
      if DTI.does_not_occur 1 t then
         F.fprintf frm "\\CFun{%a}{%a}" (xt c) w (xt d) t
      else
         F.fprintf frm "\\Abst{%a}{%a}{%a}" xn r (xt c) w (xt d) t
   | C.Prod (r, w, t)             ->
      let d = Some (r, C.Decl w) :: c in
      if DTI.does_not_occur 1 t then
         F.fprintf frm "\\LImp{%a}{%a}" (xt c) w (xt d) t
      else if H.is_prop d t then
         F.fprintf frm "\\LAll{%a}{%a}{%a}" xn r (xt c) w (xt d) t
      else
         F.fprintf frm "\\Prod{%a}{%a}{%a}" xn r (xt c) w (xt d) t
   | C.Const _                    -> assert false
   | C.MutInd _                   -> assert false
   | C.MutConstruct _             -> assert false
   | C.Var _                      -> assert false
   | C.Fix _                      -> assert false
   | C.CoFix _                    -> assert false
   | C.Meta _                     -> assert false
   | C.Implicit _                 -> assert false
   | C.Appl []                    -> assert false

and xts c frm vs =
   let map v = F.fprintf frm "{%a}" (xt c) v in
   List.iter map vs

let tex_of_term frm c t = xt c frm t

let tex_of_obj frm = function
   | C.InductiveDefinition (_, [], _, _) -> ()
   | C.Constant (_, None, _, [], _)      -> ()
   | C.Constant (_, Some t, _, [], _)    -> 
      F.fprintf frm "%a@\n" (xt []) t
   | C.Constant _                        -> assert false
   | C.InductiveDefinition _             -> assert false
   | C.Variable _                        -> assert false
   | C.CurrentProof _                    -> assert false

let is_prop sorts id =
   try match Hashtbl.find sorts id with
      | `Prop -> true
      | _     -> false
   with Not_found -> false

let tex_of_annterm frm sorts t = 

let rec xat frm = function
   | C.ASort (_, s)                   ->
      xs frm s  
   | C.AConst (_ ,i, [])              ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i None None))
   | C.AMutInd (_, i, n, [])          ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i (Some n) None))
   | C.AMutConstruct (_, i, n, m, []) ->
      F.fprintf frm "\\GRef{%s}" (quote (H.name_of_uri i (Some n) (Some m)))
   | C.ARel (_,_, _, r)               ->
      F.fprintf frm "\\LRef{%s}" (quote r)
   | C.ACast (_, t, u)                ->
      F.fprintf frm "\\Cast{%a}{%a}" xat u xat t
   | C.AAppl (_, t :: vs)             ->
      let z = num (List.length vs) in      
      F.fprintf frm "\\%sAppl%a{%a}" z xats vs xat t
   | C.AMutCase (_, _, _, u, v, ts)   ->
      let z = num (List.length ts) in
      F.fprintf frm "\\%sCase{%a}{%a}%a" z xat u xat v xats ts
   | C.ALetIn (_, r, v, w, t)         ->
      F.fprintf frm "\\Abbr{%a}{%a}{%a}" xn r xat v xat t
   | C.ALambda (_, r, w, t)           ->
      if DTI.does_not_occur 1 (H.cic t) then
         F.fprintf frm "\\CFun{%a}{%a}" xat w xat t
      else
         F.fprintf frm "\\Abst{%a}{%a}{%a}" xn r xat w xat t
   | C.AProd (id, r, w, t)            ->
      if DTI.does_not_occur 1 (H.cic t) then
         F.fprintf frm "\\LImp{%a}{%a}" xat w xat t
      else if true then
         F.fprintf frm "\\LAll{%a}{%a}{%a}" xn r xat w xat t
      else
         F.fprintf frm "\\Prod{%a}{%a}{%a}" xn r xat w xat t
   | C.AConst _                       -> assert false
   | C.AMutInd _                      -> assert false
   | C.AMutConstruct _                -> assert false
   | C.AVar _                         -> assert false
   | C.AFix _                         -> assert false
   | C.ACoFix _                       -> assert false
   | C.AMeta _                        -> assert false
   | C.AImplicit _                    -> assert false
   | C.AAppl (_, [])                  -> assert false

and xats frm = function
   | [] -> F.fprintf frm "{}"
   | vs -> 
      let map v = F.fprintf frm "{%a}" xat v in
      List.iter map vs

in
xat frm t

let xx frm = function
   | None   -> assert false
   | Some r -> F.fprintf frm "%s" (quote r)

let xh how =
   if how then "\\dx" else "\\sx"

let tex_of_steps frm sorts l =

let xat frm t = tex_of_annterm frm sorts t in

let rec xl frm = function
   | []                                                    -> ()
   | T.Note _ :: l 
   | T.Statement _ :: l
   | T.Qed _ :: l                                          ->
      xl frm l
   | T.Reflexivity _ :: l                                  ->
      F.fprintf frm "\\Reflexivity"; xl frm l   
   | T.Exact (t, _) :: l                                   ->
      F.fprintf frm "\\Exact{%a}" xat t; xl frm l   
   | T.Intros (_, [r], _) :: l                             ->
      F.fprintf frm "\\Intro{%a}{%a}" xx r xl l
   | T.LetIn (r, v, _) :: l                                ->
      F.fprintf frm "\\Pose{%a}{%a}{%a}" xx r xat v xl l
   | T.LApply (r, v, _) :: l                               ->
      F.fprintf frm "\\LApply{%a}{%a}{%a}" xx r xat v xl l
   | T.Change (u, _, None, _, _) :: l                      ->
      F.fprintf frm "\\Change{%a}{}{%a}" xat u xl l
   | T.Change (u, _, Some (s, _), _, _) :: l               ->
      F.fprintf frm "\\Change{%a}{%s}{%a}" xat u (quote s) xl l
   | T.Rewrite (b, t, None, _, _) :: l                     ->
      F.fprintf frm "\\Rewrite{%s}{%a}{}{}{%a}" (xh b) xat t xl l
   | T.Rewrite (b, t, Some (s1, Some s2), _, _) :: l       ->
      F.fprintf frm "\\Rewrite{%s}{%a}{%s}{%s}{%a}"
         (xh b) xat t (quote s1) (quote s2) xl l
   | T.Rewrite (b, t, Some (s1, None), _, _) :: l          ->
      F.fprintf frm "\\Rewrite{%s}{%a}{%s}{%s}{%a}"
         (xh b) xat t (quote s1) (quote s1) xl l
   | T.Apply (t, _) :: T.Branch (ls, _) :: l               ->
      let z = num (List.length ls) in
      F.fprintf frm "\\%sApply{%a}%a" z xat t xls ls; xl frm l
   | T.Apply (t, _) :: l                                   ->
      F.fprintf frm "\\Apply{%a}{%a}" xat t xl l
   | T.Cases (v, _, _) :: T.Branch (ls, _) :: l            ->
      let z = num (List.length ls) in
      F.fprintf frm "\\%sCases{%a}%a" z xat v xls ls; xl frm l
   | T.Cases (v, _, _) :: l                                ->
      F.fprintf frm "\\Cases{%a}{%a}" xat v xl l
   | T.Elim (v, Some t, _, _) :: T.Branch (ls, _) :: l     ->
      let z = num (List.length ls) in
      F.fprintf frm "\\%sElim{%a}{%a}{}{}%a" z xat v xat t xls ls; xl frm l
   | T.Elim (v, Some t, _, _) :: l                         ->
      F.fprintf frm "\\Elim{%a}{%a}{}{}{%a}" xat v xat t xl l
   | T.Cut (r, w, _) :: T.Branch ([l1; [T.Id _]], _) :: l2 ->
      F.fprintf frm "\\Cut{%a}{%a}{%a}{%a}" xx r xat w xl l1 xl l2
   | T.Record _ :: _                                       -> assert false
   | T.Inductive _ :: _                                    -> assert false
   | T.Id _ :: _                                           -> assert false
   | T.Clear _ :: _                                        -> assert false
   | T.ClearBody _ :: _                                    -> assert false
   | T.Branch _ :: _                                       -> assert false
   | T.Intros _ :: _                                       -> assert false
   | T.Elim _ :: _                                         -> assert false
   | T.Cut _ :: _                                          -> assert false

and xls frm = function
   | [] -> F.fprintf frm "{}"
   | ls -> 
      let map l = F.fprintf frm "{%a}" xl l in
      List.iter map (List.rev ls)

in
F.fprintf frm "%a@\n" xl l
