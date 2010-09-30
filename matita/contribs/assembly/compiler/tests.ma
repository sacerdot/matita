(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

(* ********************************************************************** *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "compiler/ast_to_astfe.ma".
include "compiler/preast_to_ast.ma".

definition parsingResult \def
 (PREAST_ROOT
  (PREAST_CONST_DECL
   ([ch_n;ch_1])
   (AST_TYPE_ARRAY
    (AST_TYPE_STRUCT
     (\laquo
      (AST_TYPE_ARRAY
       (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
       1
      )
      ;
      (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
      £
      (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
     \raquo)
    )
    1
   )
   (PREAST_INIT_VAL
    (PREAST_INIT_VAL_ARRAY
     (\laquo
      (PREAST_INIT_VAL_STRUCT
       (\laquo
        (PREAST_INIT_VAL_ARRAY
         (\laquo
          (PREAST_INIT_VAL_BYTE8 (\langle x0,x0 \rangle))
          £
          (PREAST_INIT_VAL_BYTE8 (\langle x0,x1 \rangle))
         \raquo)
        )
        ;
        (PREAST_INIT_VAL_WORD16 (\langle \langle x0,x0 \rangle : \langle x0,x0 \rangle \rangle))
        £
        (PREAST_INIT_VAL_WORD32 (\langle \langle \langle x0,x0 \rangle : \langle x0,x0 \rangle \rangle . \langle \langle x0,x0 \rangle : \langle x0,x0 \rangle \rangle \rangle))
       \raquo)
      )
      £
      (PREAST_INIT_VAL_STRUCT
       (\laquo
        (PREAST_INIT_VAL_ARRAY
         (\laquo
          (PREAST_INIT_VAL_BYTE8 (\langle x0,x2 \rangle))
          £
          (PREAST_INIT_VAL_BYTE8 (\langle x0,x3 \rangle))
         \raquo)
        )
        ;
        (PREAST_INIT_VAL_WORD16 (\langle \langle x0,x0 \rangle : \langle x0,x1 \rangle \rangle))
        £
        (PREAST_INIT_VAL_WORD32 (\langle \langle \langle x0,x0 \rangle : \langle x0,x0 \rangle \rangle . \langle \langle x0,x0 \rangle : \langle x0,x1 \rangle \rangle \rangle))
       \raquo)
      )
     \raquo)
    )
   )
   (PREAST_VAR_DECL
    ([ch_n;ch_2])
    (AST_TYPE_BASE AST_BASE_TYPE_WORD16)
    (Some ?
     (PREAST_INIT_VAR
      (PREAST_VAR_STRUCT
       (PREAST_VAR_ARRAY
        (PREAST_VAR_ID ([ch_n;ch_1]))
        (PREAST_EXPR_BYTE8 (\langle x0,x0 \rangle))
       )
       1
      )
     )
    )
    (PREAST_VAR_DECL
     ([ch_n;ch_3])
     (AST_TYPE_BASE AST_BASE_TYPE_BYTE8)
     (None ?)
     (PREAST_NO_DECL
      [
       (PREAST_STM_WHILE
        (PREAST_EXPR_ID
         (PREAST_VAR_ID ([ch_n;ch_2]))
        )
        (PREAST_VAR_DECL
         ([ch_n;ch_1])
         (AST_TYPE_BASE AST_BASE_TYPE_WORD32)
         (Some ?
          (PREAST_INIT_VAR
           (PREAST_VAR_STRUCT
            (PREAST_VAR_ARRAY
             (PREAST_VAR_ID ([ch_n;ch_1]))
             (PREAST_EXPR_ID
              (PREAST_VAR_ID ([ch_n;ch_2]))
             )
            )
            2
           )
          )
         )
         (PREAST_NO_DECL
          [
           (PREAST_STM_IF
            (\laquo
             £
             (pair ??
              (PREAST_EXPR_GT
               (PREAST_EXPR_ID
                (PREAST_VAR_ID ([ch_n;ch_1]))
               )
               (PREAST_EXPR_WORD32 (\langle \langle \langle x1,x2 \rangle : \langle x3,x4 \rangle \rangle . \langle \langle xA,xB \rangle : \langle xC,xD \rangle \rangle \rangle))
              )
              (PREAST_NO_DECL
               [
                (PREAST_STM_ASG
                 (PREAST_VAR_ID ([ch_n;ch_3]))
                 (PREAST_EXPR_NEG
                  (PREAST_EXPR_NOT
                   (PREAST_EXPR_COM
                    (PREAST_EXPR_OR
                     (PREAST_EXPR_AND
                      (PREAST_EXPR_SHR
                       (PREAST_EXPR_SUB
                        (PREAST_EXPR_ADD
                         (PREAST_EXPR_W32toB8
                          (PREAST_EXPR_W16toW32
                           (PREAST_EXPR_B8toW16
                            (PREAST_EXPR_ID
                             (PREAST_VAR_ID ([ch_n;ch_3]))
                            )
                           )
                          )
                         )
                         (PREAST_EXPR_BYTE8 (\langle x0,x1 \rangle))
                        )
                        (PREAST_EXPR_DIV
                         (PREAST_EXPR_MUL
                          (PREAST_EXPR_BYTE8 (\langle x0,x2 \rangle))
                          (PREAST_EXPR_BYTE8 (\langle x0,x3 \rangle))
                         )
                         (PREAST_EXPR_BYTE8 (\langle x0,x4 \rangle))
                        )
                       )
                       (PREAST_EXPR_SHL
                        (PREAST_EXPR_BYTE8 (\langle x0,x5 \rangle))
                        (PREAST_EXPR_BYTE8 (\langle x0,x6 \rangle))
                       )
                      )
                      (PREAST_EXPR_BYTE8 (\langle x0,x7 \rangle))
                     )
                     (PREAST_EXPR_XOR
                      (PREAST_EXPR_BYTE8 (\langle x0,x8 \rangle))
                      (PREAST_EXPR_BYTE8 (\langle x0,x9 \rangle))
                     )
                    )
                   )
                  )
                 )
                )
               ]
              )
             )
            \raquo)
            (None ?)
           )
           ;
           (PREAST_STM_ASG
            (PREAST_VAR_ID ([ch_n;ch_2]))
            (PREAST_EXPR_ADD
             (PREAST_EXPR_ID
              (PREAST_VAR_ID ([ch_n;ch_2]))
             )
             (PREAST_EXPR_WORD16 (\langle \langle x0,x0 \rangle : \langle x0,x1 \rangle \rangle))
            )
           )
          ]
         )
        )
       )
       ;
       (PREAST_STM_ASG
        (PREAST_VAR_ID ([ch_n;ch_3]))
        (PREAST_EXPR_ID
         (PREAST_VAR_ARRAY
          (PREAST_VAR_STRUCT
           (PREAST_VAR_ARRAY
            (PREAST_VAR_ID ([ch_n;ch_1]))
            (PREAST_EXPR_BYTE8 (\langle x0,x1 \rangle))
           )
           O
          )
          (PREAST_EXPR_BYTE8 (\langle x0,x0 \rangle))
         )
        )
       )
      ]
     )
    )
   )
  )
 ).

lemma pippo : ∃b.preast_to_ast parsingResult = Some ? b.
 normalize;
 exists;
 [ apply (match preast_to_ast parsingResult with [ None ⇒ AST_ROOT (AST_NO_DECL O empty_env []) | Some x ⇒ x]);
 | reflexivity
 ]
qed.
