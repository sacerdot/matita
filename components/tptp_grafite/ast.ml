type kinds_of_formulae = 
  | Axiom | Hypothesis | Definition | Lemma | Theorem | Conjecture
  | Lemma_conjecture | Negated_conjecture | Plain | Unknown

type source = NoSource

type info = NoInfo

type term = 
  | Variable of string
  | Constant of string 
  | Function of string * term list

type atom = 
  | Proposition of string
  | Predicate of string * term list
  | True
  | False
  | Eq of term * term
  | NotEq of term * term

type formulae = 
  | Disjunction of formulae * formulae
  | NegAtom of  atom
  | Atom of atom
  
type ast = 
  | Comment of string
  | Inclusion of string * (string list)
  | AnnotatedFormula of 
      string * kinds_of_formulae * formulae * source * info list
