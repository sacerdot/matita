(* Copyright (C) 2004-2005, HELM Team.
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

(** table shape kinds *)
type tbl = [ `RefObj| `RefSort| `RefRel| `ObjectName| `Hits| `Count]

(** all functions below return either an SQL statement or a list of SQL
 * statements.
 * For functions taking as argument (string * tbl) list, the meaning is a list
 * of pairs <table name, table type>; where the type specify the desired kind of
 * table and name the desired name (e.g. create a `RefObj like table name
 * refObj_NEW) *)

val create_tables: (string * tbl) list -> string list
val create_indexes: (string * tbl) list -> string list
val drop_tables: (string * tbl) list -> string list
val drop_indexes: (string * tbl) list -> HSql.dbtype -> HSql.dbd -> string list
val rename_tables: (string * string) list -> string list

(** @param refObj name of the refObj table
 * @param hits name of the hits table *)
val fill_hits: string -> string -> string list

(** move content [t1] [t2] [buri] 
 *  moves all the tuples with 'source' that match regex '^buri' from t1 to t2
 *  *)
val move_content: (string * tbl) -> (string * tbl) -> string -> HSql.dbtype ->
        HSql.dbd -> string

(** @param refObj name of the refObj table
 * @param src uri of the desired 'source' field *)
val direct_deps: string -> UriManager.uri -> HSql.dbtype -> HSql.dbd -> string

(** @param refObj name of the refObj table
 * @param src uri of the desired 'h_occurrence' field *)
val inverse_deps: string -> UriManager.uri -> HSql.dbtype -> HSql.dbd -> string

