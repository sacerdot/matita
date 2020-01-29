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

version:
  | TEXT { EU.version_of_string $1 }
;

obj:
  | TEXT { false, EU.obj_of_string $1 }
;

name:
  | TEXT { false, EU.name_of_string $1 }
;

role:
  | OP REL ver olds news CP {
      false, {ET.v = $3; ET.o = $4; ET.n = $5}
    }
;

objs:
  |          { []       }
  | obj objs { $1 :: $2 }
;

names:
  |            { []       }
  | name names { $1 :: $2 }
;

roles:
  |            { []       }
  | role roles { $1 :: $2 }
;

ver:
  | OP VER version CP { $3 }
;

olds:
  | OP OLD objs CP { $3 }
;

news:
  | OP NEW names CP { $3 }
;

base:
  | OP BASE roles CP { $3 }
;

status:
  | ROLES SC OP TOP base ver olds news CP EOF {
      {ET.r = $5; ET.s = $6; ET.t = $7; ET.w = $8}
    }
;
