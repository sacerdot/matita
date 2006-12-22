set "baseuri" "cic:/matita/library_notation/".

include "Q/q.ma".
include "higher_order_defs/functions.ma".
include "higher_order_defs/ordering.ma".
include "higher_order_defs/relations.ma".
include "nat/nth_prime.ma".
include "nat/plus.ma".
include "nat/ord.ma".
include "nat/congruence.ma".
include "nat/compare.ma".
include "nat/totient.ma".
include "nat/le_arith.ma".
include "nat/count.ma".
include "nat/orders.ma".
include "nat/minus.ma".
include "nat/exp.ma".
include "nat/gcd.ma".
include "nat/div_and_mod.ma".
include "nat/primes.ma".
include "nat/relevant_equations.ma".
include "nat/chinese_reminder.ma".
include "nat/factorial.ma".
include "nat/lt_arith.ma".
include "nat/minimization.ma".
include "nat/permutation.ma".
include "nat/sigma_and_pi.ma".
include "nat/factorization.ma".
include "nat/times.ma".
include "nat/fermat_little_theorem.ma".
include "nat/nat.ma".
(* FG: coq non c'entra con library, o sbaglio? *)
(* include "legacy/coq.ma". *)
include "Z/compare.ma".
include "Z/plus.ma".
include "Z/times.ma".
include "Z/z.ma".
include "Z/orders.ma".
include "list/sort.ma".
include "list/list.ma".
include "algebra/semigroups.ma".
include "algebra/monoids.ma".
include "algebra/groups.ma".
include "algebra/finite_groups.ma". 
include "logic/connectives.ma".
include "logic/equality.ma".
include "datatypes/constructors.ma".
include "datatypes/compare.ma".
include "datatypes/bool.ma".

notation "hvbox(x break \middot y)"
  left associative with precedence 55
for @{ 'times $x $y }.

