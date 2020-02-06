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

type version = int list

type name = string list

type names = (bool*name) list

type obj = version * name

type objs = (bool*obj) list

type role = {
  mutable v: version;
  mutable o: objs;
  mutable n: names;
}

type roles = (bool*role) list

type status = {
  mutable r: roles;
  mutable s: version;
  mutable t: objs;
  mutable w: names;
}

type pointer = int list

type error = EWrongExt of string
           | EStage of version
           | ENoStage
           | EWaiting
           | ENameClash of name
           | EObjClash of obj
           | ERoleClash of role
           | ENoEntry
           | EWrongSelect
           | EWrongVersion
           | ETops
           | EWrongRequest of string * string

exception Error of error
