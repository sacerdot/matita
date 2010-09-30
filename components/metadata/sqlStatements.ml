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

(* $Id$ *)

open Printf;;
type tbl = [ `RefObj| `RefSort| `RefRel| `ObjectName| `Hits| `Count]

(* TABLES *)

let sprintf_refObj_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) not null,
    h_occurrence varchar(255) not null,
    h_position varchar(62) not null,
    h_depth integer
);" name]

let sprintf_refSort_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) not null,
    h_position varchar(62) not null,
    h_depth integer not null,
    h_sort varchar(5) not null
);" name]

let sprintf_refRel_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) not null,
    h_position varchar(62) not null,
    h_depth integer not null
);" name]

let sprintf_objectName_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) not null,
    value varchar(255) not null
);" name]

let sprintf_hits_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) not null,
    no integer not null
);" name]

let sprintf_count_format name = [
sprintf "CREATE TABLE %s (
    source varchar(255) unique not null,
    conclusion smallint(6) not null,
    hypothesis smallint(6) not null,
    statement smallint(6) not null
);" name]

let sprintf_refObj_drop name = [sprintf "DROP TABLE %s;" name]

let sprintf_refSort_drop name = [sprintf "DROP TABLE %s;" name]

let sprintf_refRel_drop name = [sprintf "DROP TABLE %s;" name]

let sprintf_objectName_drop name = [sprintf "DROP TABLE %s;" name]

let sprintf_hits_drop name = [sprintf "DROP TABLE %s;" name]

let sprintf_count_drop name = [sprintf "DROP TABLE %s;" name]

(* INDEXES *)

let sprintf_refObj_index name = [
sprintf "CREATE INDEX %s_index ON %s (source,h_occurrence,h_position);" name name;
(*sprintf "CREATE INDEX %s_index ON %s (source(219),h_occurrence(219),h_position);" name name;*)
sprintf "CREATE INDEX %s_occurrence ON %s (h_occurrence);" name name ]

let sprintf_refSort_index name = [
sprintf "CREATE INDEX %s_index ON %s (source,h_sort,h_position,h_depth);" name name]

let sprintf_objectName_index name = [
sprintf "CREATE INDEX %s_value ON %s (value);" name name]

let sprintf_hits_index name = [
sprintf "CREATE INDEX %s_source ON %s (source);" name name ;
sprintf "CREATE INDEX %s_no ON %s (no);" name name] 

let sprintf_count_index name = [
sprintf "CREATE INDEX %s_conclusion ON %s (conclusion);" name name;
sprintf "CREATE INDEX %s_hypothesis ON %s (hypothesis);" name name;
sprintf "CREATE INDEX %s_statement ON %s (statement);" name name]
 
let sprintf_refRel_index name = [
sprintf "CREATE INDEX %s_index ON %s (source,h_position,h_depth);" name name]

let format_drop name sufix dtype dbd =
  if HSql.isMysql dtype dbd then
	(sprintf "DROP INDEX %s_%s ON %s;" name sufix name)
     else
	(sprintf "DROP INDEX %s_%s;" name sufix);;

let sprintf_refObj_index_drop name  dtype dbd= [(format_drop name "index" dtype dbd)]

let sprintf_refSort_index_drop name dtype dbd = [(format_drop name "index" dtype dbd)]

let sprintf_objectName_index_drop name dtype dbd = [(format_drop name "value" dtype dbd)]

let sprintf_hits_index_drop name dtype dbd = [
(format_drop name "source" dtype dbd);
(format_drop name "no" dtype dbd)] 

let sprintf_count_index_drop name dtype dbd = [
(format_drop name "source" dtype dbd);
(format_drop name "conclusion" dtype dbd);
(format_drop name "hypothesis" dtype dbd);
(format_drop name "statement" dtype dbd)]
 
let sprintf_refRel_index_drop name dtype dbd = 
  [(format_drop name "index" dtype dbd)]

let sprintf_rename_table oldname newname = [
sprintf "RENAME TABLE %s TO %s;" oldname newname 
]
          

(* FUNCTIONS *)

let get_table_format t named =
  match t with
  | `RefObj -> sprintf_refObj_format named
  | `RefSort -> sprintf_refSort_format named
  | `RefRel -> sprintf_refRel_format named
  | `ObjectName -> sprintf_objectName_format named
  | `Hits -> sprintf_hits_format named
  | `Count -> sprintf_count_format named

let get_index_format t named =
  match t with
  | `RefObj -> sprintf_refObj_index named
  | `RefSort -> sprintf_refSort_index named
  | `RefRel -> sprintf_refRel_index named
  | `ObjectName -> sprintf_objectName_index named
  | `Hits -> sprintf_hits_index named
  | `Count -> sprintf_count_index named

let get_table_drop t named =
  match t with
  | `RefObj -> sprintf_refObj_drop named
  | `RefSort -> sprintf_refSort_drop named
  | `RefRel -> sprintf_refRel_drop named
  | `ObjectName -> sprintf_objectName_drop named
  | `Hits -> sprintf_hits_drop named
  | `Count -> sprintf_count_drop named

let get_index_drop t named dtype dbd =
  match t with
  | `RefObj -> sprintf_refObj_index_drop named dtype dbd
  | `RefSort -> sprintf_refSort_index_drop named dtype dbd
  | `RefRel -> sprintf_refRel_index_drop named dtype dbd
  | `ObjectName -> sprintf_objectName_index_drop named dtype dbd
  | `Hits -> sprintf_hits_index_drop named dtype dbd
  | `Count -> sprintf_count_index_drop named dtype dbd

let create_tables l =
  List.fold_left (fun s (name,table) ->  s @ get_table_format table name) [] l

let create_indexes l =
  List.fold_left (fun s (name,table) ->  s @ get_index_format table name) [] l
 
let drop_tables l =
  List.fold_left (fun s (name,table) ->  s @ get_table_drop table name) [] l
  
let drop_indexes l  dtype dbd=
  List.fold_left (fun s (name,table) ->  s @ get_index_drop table name dtype dbd) [] l

let rename_tables l = 
  List.fold_left (fun s (o,n) ->  s @ sprintf_rename_table o n) [] l

let fill_hits refObj hits =
  [ sprintf
        "INSERT INTO %s
        SELECT h_occurrence, COUNT(source)
        FROM %s
        GROUP BY h_occurrence;"
      hits refObj ]


let move_content (name1, tbl1) (name2, tbl2) buri dtype dbd  =
  let escape s =
      Pcre.replace ~pat:"([^\\\\])_" ~templ:"$1\\_" (HSql.escape dtype dbd s)
  in
  assert (tbl1 = tbl2);
  sprintf 
    "INSERT INTRO %s SELECT * FROM %s WHERE source LIKE \"%s%%\";"   
    name2 name1 (escape buri)

let direct_deps refObj uri dtype dbd =
  sprintf "SELECT * FROM %s WHERE source = \"%s\";"
    refObj (HSql.escape dtype dbd (UriManager.string_of_uri uri))

let inverse_deps refObj uri dtype dbd =
  sprintf "SELECT * FROM %s WHERE h_occurrence = \"%s\";"
    refObj (HSql.escape dtype dbd (UriManager.string_of_uri uri))

