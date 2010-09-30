type role = 
  Axiom 
| Hypothesis 
| Definition 
| Assumption 
| Lemma 
| Theorem 
| Conjecture 
| Negated_conjecture 
| Lemma_conjecture 
| Plain 
| Fi_domain 
| Fi_functors 
| Fi_predicates 
| Type 
| Unknown


type ast = 
  | ThfFormula of string * role * CicNotationPt.term
  | ThfDefinition of string * string * CicNotationPt.term
  | ThfType of string * string * CicNotationPt.term
  | Comment of string
  | Inclusion of string * (string list)
