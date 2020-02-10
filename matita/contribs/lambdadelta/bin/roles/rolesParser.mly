/*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department, University of Bologna, Italy.
    ||I||
    ||T||  HELM is free software; you can redistribute it and/or
    ||A||  modify it under the terms of the GNU General Public License
    \   /  version 2 or (at your option) any later version.
     \ /   This software is distributed as is, NO WARRANTY.
      V_______________________________________________________________ */

%{
  module EU = RolesUtils
  module ET = RolesTypes
%}

%token EOF SC OP CP VER OLD NEW REL BASE TOP ROLES
%token <string> TEXT

%start status
%type <RolesTypes.status> status

%%

stage:
  | TEXT { EU.stage_of_string $1 }
;

oobj:
  | TEXT { EU.oobj_of_string $1 }
;

nobj:
  | TEXT { EU.nobj_of_string $1 }
;

robj:
  | OP REL ver olds news CP {
      {ET.rb = false; ET.rx = false; ET.rs = $3; ET.ro = $4; ET.rn = $5}
    }
;

oobjs:
  |            { []       }
  | oobj oobjs { $1 :: $2 }
;

nobjs:
  |            { []       }
  | nobj nobjs { $1 :: $2 }
;

robjs:
  |            { []       }
  | robj robjs { $1 :: $2 }
;

ver:
  | OP VER stage CP { $3 }
;

olds:
  | OP OLD oobjs CP { $3 }
;

news:
  | OP NEW nobjs CP { $3 }
;

base:
  | OP BASE robjs CP { $3 }
;

status:
  | ROLES SC OP TOP base ver olds news CP EOF {
      {ET.sm = false; ET.sr = $5; ET.ss = $6; ET.so = $7; ET.sn = $8}
    }
;
