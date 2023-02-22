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

type stage = int list

type name = string list

type nobj = {
  mutable nb: bool;
  mutable nn: name;
}

type nobjs = nobj list

type oobj = {
  mutable ob: bool;
  mutable os: stage;
  mutable on: name;
}

type oobjs = oobj list

type robj = {
  mutable rb: bool;
  mutable rx: bool;
  mutable rs: stage;
  mutable ro: oobjs;
  mutable rn: nobjs;
}

type robjs = robj list

type status = {
  mutable sm: bool;
  mutable sr: robjs;
  mutable so: oobjs;
  mutable ss: stage;
  mutable sn: nobjs;
}

type step = One of int
          | Many of int list

type pointer = step list

type error = EWrongExt of string
           | EStage of stage
           | ENoStage
           | EWaiting
           | ENClash of nobj
           | EOClash of oobj
           | ERClash of robj
           | ENoEntry
           | EWrongSelect
           | EWrongVersion
           | ETops
           | EWrongRequest of string * string

exception Error of error

type each = string -> string -> bool -> string -> string -> string -> unit
