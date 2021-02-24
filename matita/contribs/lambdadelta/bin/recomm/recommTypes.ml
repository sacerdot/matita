type text = string

type word = string

type words = word list

type src =
(* end of line *)
  | Line  of text 
(* other text *)
  | Text  of text 
(* mark *)
  | Mark  of text
(* Key *)
  | Key   of word * text
(* title *)
  | Title of words
(* section *)
  | Slice of words
(* other comment *)
  | Other of text * text * text

type srcs = src list

type ('s, 't) aproc = 's -> words -> words -> 't

type ('s, 't) astep = ('s, 't) aproc -> ('s, 't) aproc

type step = (bool, bool * words * words) astep
