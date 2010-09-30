(*
 * Copyright (C) 2003:
 *    Stefano Zacchiroli <zack@cs.unibo.it>
 *    for the HELM Team http://helm.cs.unibo.it/
 *
 *  This file is part of HELM, an Hypertextual, Electronic
 *  Library of Mathematics, developed at the Computer Science
 *  Department, University of Bologna, Italy.
 *
 *  HELM is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License
 *  as published by the Free Software Foundation; either version 2
 *  of the License, or (at your option) any later version.
 *
 *  HELM is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with HELM; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 *  MA  02111-1307, USA.
 *
 *  For details, see the HELM World-Wide-Web page,
 *  http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open Hbugs_types;;
open Printf;;

let rec string_of_hint = function
  | Use_ring -> "Use Ring, Luke!"
  | Use_fourier -> "Use Fourier, Luke!"
  | Use_reflexivity -> "Use reflexivity, Luke!"
  | Use_symmetry -> "Use symmetry, Luke!"
  | Use_assumption -> "Use assumption, Luke!"
  | Use_contradiction -> "Use contradiction, Luke!"
  | Use_exists -> "Use exists, Luke!"
  | Use_split -> "Use split, Luke!"
  | Use_left -> "Use left, Luke!"
  | Use_right -> "Use right, Luke!"
  | Use_apply term -> sprintf "Apply %s, Luke!" term
  | Hints hints -> String.concat "; " (List.map string_of_hint hints)
;;

