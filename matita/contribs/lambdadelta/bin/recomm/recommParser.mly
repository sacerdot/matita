%{

  module ET = RecommTypes

  let lc = String.lowercase_ascii

%}

%token <string> SP NL OP CP PP SR KW CW HW SW OT
%token EF

%start srcs
%type <RecommTypes.srcs> srcs

%%

inn_r:
  | SP { $1 }
  | NL { $1 }
  | SW { $1 }
  | OT { $1 }

inn:
  | inn_r { $1 }
  | KW      { $1 }
  | CW      { $1 }
  | HW      { $1 }

inns_r:
  | inn_r      { $1      }
  | inn_r inns { $1 ^ $2 }

inns:
  | inn      { $1      }
  | inn inns { $1 ^ $2 }

out:
  | SP { $1 }
  | SR { $1 }
  | KW { $1 }
  | CW { $1 }
  | HW { $1 }
  | SW { $1 }
  | OT { $1 }

outs:
  | out      { $1      }
  | out outs { $1 ^ $2 } 

sw:
  | HW { lc $1 }
  | SW { lc $1 }

cws:
  |           { []       }
  | SP        { []       }
  | SP CW cws { $2 :: $3 }

sws:
  |           { []       }
  | SP        { []       }
  | SP sw sws { $2 :: $3 }

src_l:
  | NL               { ET.Line  $1                     }
  | OP PP inns CP    { ET.Mark  $3                     }
  | OP KW inns CP    { ET.Key   ($2, $3)               }
  | OP CW cws CP     { ET.Title ($2 :: $3)             }
  | OP HW sws CP     { ET.Slice (lc $2 :: $3)          }
  | OP CP            { ET.Other ($1, "", $2)           }
  | OP inns_r CP     { ET.Other ($1, $2, $3)           }
  | OP SR inns CP    { ET.Other ($1, $2 ^ $3, $4)      }
  | OP SR SR inns CP { ET.Other ($1, $2 ^ $3 ^ $4, $5) }

src:
  | outs { ET.Text $1 }

srcs_l:
  | EF         { []       }
  | src_l srcs { $1 :: $2 }

srcs:
  | srcs_l     { $1       }
  | src srcs_l { $1 :: $2 }
