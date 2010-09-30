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

type flags = {
  maxwidth: int;
  maxsize: int;
  maxdepth: int;
  maxgoalsizefactor : int;
  timeout: float;
  use_library: bool;
  use_paramod: bool;
  use_only_paramod : bool;
  close_more : bool;
  dont_cache_failures: bool;
  do_types: bool;
  skip_trie_filtering: bool;
  skip_context : bool;
}

val default_flags : unit -> flags

(* (metasenv, subst, (metano,depth)list *)
type sort = P | T;;
type and_elem =  
  (int * Cic.term * Cic.term) * Cic.metasenv * Cic.substitution * (ProofEngineTypes.goal * int * sort) list
type auto_result = 
  | Fail of string
  | Success of (int * Cic.term * Cic.term) * Cic.metasenv * Cic.substitution * and_elem list

