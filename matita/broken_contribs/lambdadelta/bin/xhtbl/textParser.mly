%{

module S = Str
module L = List
module T = Table

let split s =
   S.split (S.regexp "[ \r\n\t]+") s

let mk_css_atom s rs =
   let cs = split s in
   let map (b, (x1, x2)) = cs, b, x1, x2 in 
   L.map map rs

let mk_string_atom s rs =
   let map (b, (x1, x2)) = s, b, x1, x2 in 
   L.map map rs

%}

%token <int> NUM
%token <string> TEXT 
%token SPACE NAME TABLE CSS URI EXT SR OC CC OB CB PS CF OP CP AT EOF

%start script
%type <(string * string) list * (string * Table.table * Table.css Attr.atoms * Table.uri Attr.atoms * Table.ext Attr.atoms) list> script

%%

space:
   | SPACE TEXT TEXT { $2, $3 }
;

spaces:
   |              { []       }
   | space spaces { $1 :: $2 }
;

text:
   | TEXT                  { T.Plain $1             }
   | AT OP TEXT TEXT CP    { T.Link (true, $3, $4)  }
   | AT AT OP TEXT TEXT CP { T.Link (false, $4, $5) }
   | AT TEXT               { T.Link (true, $2, $2)  }
   | AT AT TEXT            { T.Link (false, $3, $3) }   
;

texts:
  | text          { [$1]                    }
  | text PS texts { $1 :: T.Plain " " :: $3 }
  | text CF texts { $1 :: $3                }
;

key:
   | texts { T.Text $1        }
   | SR    { T.Glue None      }
   | NUM   { T.Glue (Some $1) }
;

css:
   |          { []       }
   | CSS TEXT { split $2 }
;

uri:
   |          { "" }
   | URI TEXT { $2 }
;

ext:
   |          { "" }
   | EXT TEXT { $2 }
;

table:
   | css uri ext name key     { T.mk_key        $5 $1 $2 $3 $4 }
   | css uri ext OC tables CC { T.mk_line false $5 $1 $2 $3 "" }
   | css uri ext OB tables CB { T.mk_line true  $5 $1 $2 $3 "" }
;

tables:
   |              { []       }
   | table tables { $1 :: $2 }
;

name:
   |           { "" }
   | NAME TEXT { $2 }
;

interval:
   | NUM     { Some $1, Some $1 }
   | SR      { None, None       } 
   | NUM NUM { Some $1, Some $2 }
   | NUM SR  { Some $1, None    }
   | SR NUM  { None, Some $2    }
   | SR SR   { None, None       }
;

range:
   | OB interval CB { true, $2  }
   | OC interval CC { false, $2 }
;

ranges:
   |              { []       }
   | range ranges { $1 :: $2 }
;

catom:
   | CSS TEXT ranges { mk_css_atom $2 $3 }
;

catoms:
   |              { []      }
   | catom catoms { $1 @ $2 }
;

uatom:
   | URI TEXT ranges { mk_string_atom $2 $3 }
;

uatoms:
   |              { []      }
   | uatom uatoms { $1 @ $2 }
;

xatom:
   | EXT TEXT ranges { mk_string_atom $2 $3 }
;

xatoms:
   |              { []      }
   | xatom xatoms { $1 @ $2 }
;

directive:
   | name TABLE table catoms uatoms xatoms { $1, $3, $4, $5, $6 }
;

directives:
   |                      { []       }
   | directive directives { $1 :: $2 }
;

script:
   | spaces directives EOF { $1, $2 }
;
