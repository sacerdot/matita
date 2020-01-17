module L = List
module S = String
module V = Array

module T = Table
module M = Matrix
module A = Attr

type status = {
   m: M.matrix;
   c: T.css A.atoms;
   u: T.uri A.atoms;
   x: T.ext A.atoms;
}

let initial c u x m = {
   m = m; c = c; u = u; x = x
}

let process_cell st y x c =
   M.set_attrs st.m y x
      (A.get_attr L.concat [] st.c y x)
      (A.get_attr (S.concat "") "" st.u y x)
      (A.get_attr (S.concat "") "" st.x y x)
      ""

let process_row st y row =
   V.iteri (process_cell st y) row

let process css uri ext matrix =
   let st = initial css uri ext matrix in
   V.iteri (process_row st) matrix.M.m
