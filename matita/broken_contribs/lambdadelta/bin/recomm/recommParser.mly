%{

  module ET = RecommTypes

  let lc = String.lowercase_ascii

%}

%token <string> SP NL OP CP PP SR KW CW HW SW OT
%token EF

%start srcs
%type <RecommTypes.srcs> srcs

%%

sp:
  |    { "" }
  | SP { $1 }

inn_r:
  | NL { $1 }
  | SW { $1 }
  | OT { $1 }

inn:
  | inn_r { $1 }
  | SP    { $1 }
  | KW    { $1 }
  | CW    { $1 }
  | HW    { $1 }

inn_w:
  | inn   { $1 }
  | SR    { $1 }

inns_r:
  | inn_r      { $1      }
  | inn_r inns { $1 ^ $2 }

inns:
  | inn      { $1      }
  | inn inns { $1 ^ $2 }

inns_w:
  | inn_w        { $1      }
  | inn_w inns_w { $1 ^ $2 }

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

cc:
  | CW { $1 }
  | OT { $1 }

cw:
  | cc    { $1      }
  | cc cw { $1 ^ $2 }

cws:
  |           { []       }
  | SP        { []       }
  | SP cw cws { $2 :: $3 }

sc:
  | HW { lc $1 }
  | SW { lc $1 }
  | OT { $1    }

sw:
  | sc    { $1      }
  | sc sw { $1 ^ $2 }

sws:
  |           { []       }
  | SP        { []       }
  | SP sw sws { $2 :: $3 }

src_l:
  | NL                 { ET.Line  $1                        }
  | OP sp PP inns CP   { ET.Mark  $4                        }
  | OP sp KW inns_w CP { ET.Key   ($3, $4)                  }
  | OP sp CW cws CP    { ET.Title ($3 :: $4)                }
  | OP sp HW sws CP    { ET.Slice (lc $3 :: $4)             }
  | OP sp CP           { ET.Other (0, $1, $2, $3)           }
  | OP sp inns_r CP    { ET.Other (0, $1, $2 ^ $3, $4)      }
  | OP SR inns CP      { ET.Other (1, $1, $2 ^ $3, $4)      }
  | OP SR SR inns CP   { ET.Other (2, $1, $2 ^ $3 ^ $4, $5) }
  | OP SP SR inns CP   { ET.Mark  $4                        }

src:
  | outs { ET.Text $1 }

srcs_l:
  | EF         { []       }
  | src_l srcs { $1 :: $2 }

srcs:
  | srcs_l     { $1       }
  | src srcs_l { $1 :: $2 }
