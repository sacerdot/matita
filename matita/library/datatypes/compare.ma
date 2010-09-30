(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

inductive compare :Set \def
| LT : compare
| EQ : compare
| GT : compare.

definition compare_invert: compare \to compare \def
  \lambda c.
    match c with
      [ LT \Rightarrow GT
      | EQ \Rightarrow EQ
      | GT \Rightarrow LT ].
