(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/factorization.ma".
include "list/list.ma".

definition cache ≝ 
  [2;3;5;7;11;13;17;19;23;29;31;37;41;43;47;53;59;61;67;71;
   73;79;83;89;97;101;103;107;109;113;
   127;131;137;139;149;151;157;163;167;173;
   179;181;191;193;197;199;211;223;227;229;
   233;239;241;251;257;263;269;271;277;281;
   283;293;307;311;313;317;331;337;347;349;
   353;359;367;373;379;383;389;397;401;409;
   419;421;431;433;439;443;449;457;461;463;
   467;479;487;491;499;503;509;521;523;541;
   547;557;563;569;571;577;587;593(*;599;601;
   607;613;617;619;631;641;643;647;653;659;
   661;673;677;683;691;701;709;719;727;733;
   739;743;751;757;761;769;773;787;797;809;
   811;821;823;827;829;839;853;857;859;863;
   877;881;883;887;907;911;919;929;937;941;
   947;953;967;971;977;983;991;997;1009;1013;
   1019;1021;1031;1033;1039;1049;1051;1061;1063;1069;
   1087;1091;1093;1097;1103;1109;1117;1123;1129;1151;
   1153;1163;1171;1181;1187;1193;1201;1213;1217;1223;
   1229;1231;1237;1249;1259;1277;1279;1283;1289;1291;
   1297;1301;1303;1307;1319;1321;1327;1361;1367;1373;
   1381;1399;1409;1423;1427;1429;1433;1439;1447;1451;
   1453;1459;1471;1481;1483;1487;1489;1493;1499;1511;
   1523;1531;1543;1549;1553;1559;1567;1571;1579;1583;
   1597;1601;1607;1609;1613;1619;1621;1627;1637;1657;
   1663;1667;1669;1693;1697;1699;1709;1721;1723;1733;
   1741;1747;1753;1759;1777;1783;1787;1789;1801;1811;
   1823;1831;1847;1861;1867;1871;1873;1877;1879;1889;
   1901;1907;1913;1931;1933;1949;1951;1973;1979;1987;
   1993;1997;1999;2003;2011;2017;2027;2029;2039;2053;
   2063;2069;2081;2083;2087;2089;2099;2111;2113;2129;
   2131;2137;2141;2143;2153;2161;2179;2203;2207;2213;
   2221;2237;2239;2243;2251;2267;2269;2273;2281;2287;
   2293;2297;2309;2311;2333;2339;2341;2347;2351;2357;
   2371;2377;2381;2383;2389;2393;2399;2411;2417;2423;
   2437;2441;2447;2459;2467;2473;2477;2503;2521;2531;
   2539;2543;2549;2551;2557;2579;2591;2593;2609;2617;
   2621;2633;2647;2657;2659;2663;2671;2677;2683;2687;
   2689;2693;2699;2707;2711;2713;2719;2729;2731;2741;
   2749;2753;2767;2777;2789;2791;2797;2801;2803;2819;
   2833;2837;2843;2851;2857;2861;2879;2887;2897;2903;
   2909;2917;2927;2939;2953;2957;2963;2969;2971;2999;
   3001;3011;3019;3023;3037;3041;3049;3061;3067;3079;
   3083;3089;3109;3119;3121;3137;3163;3167;3169;3181;
   3187;3191;3203;3209;3217;3221;3229;3251;3253;3257;
   3259;3271;3299;3301;3307;3313;3319;3323;3329;3331;
   3343;3347;3359;3361;3371;3373;3389;3391;3407;3413;
   3433;3449;3457;3461;3463;3467;3469;3491;3499;3511;
   3517;3527;3529;3533;3539;3541;3547;3557;3559;3571;
   3581;3583;3593;3607;3613;3617;3623;3631;3637;3643;
   3659;3671;3673;3677;3691;3697;3701;3709;3719;3727;
   3733;3739;3761;3767;3769;3779;3793;3797;3803;3821 *)
  ].
  
include "nat/sieve.ma".  
  
let rec rev (acc : list nat) l on l ≝
  match l with 
  [ nil ⇒ acc
  | cons x tl ⇒ rev (x :: acc) tl]. 

(*  
lemma foo: rev [] (sieve 594) = cache. reflexivity; qed. 
*)

definition smart_nth_prime ≝ λcache,i.nth nat cache (nth_prime i) i.

lemma nth_empty: ∀T:Type.∀n,def.nth T [] def n = def.
intros; elim n; [reflexivity]
simplify; assumption;
qed. 

lemma nth_short: ∀T:Type.∀def,n,l.length ? l ≤ n → nth T l def n = def.
intros 3; elim n 0;
[1: intro; cases l; [intros; reflexivity| simplify; intros; cases (?:False);
    apply (not_le_Sn_n (length T l1) ?).
      apply (transitive_le (S (length T l1)) O (length T l1) ? ?);
      [apply (H).
      |apply (le_O_n (length T l1))]]
|2: simplify; intros 3; elim l 0;
    [1: simplify; intros; apply nth_empty;
    |2: simplify; intros; apply H; 
        apply le_S_S_to_le; apply H2;]]
qed.

definition good_cache_spec ≝
  λcache.∀i.i ≤ length ? cache → nth_prime i = nth nat cache (nth_prime i) i.

lemma smart_nth_prime_ok:
  ∀cache.good_cache_spec cache →
    ∀i.smart_nth_prime cache i = nth_prime i.
unfold good_cache_spec; intros; unfold smart_nth_prime;
generalize in match (H i);
elim i 0;
[1: simplify; cases cache;
    [1: simplify; intros; reflexivity;
    |2: simplify; intro H; rewrite > H; [reflexivity] apply le_O_n;] 
|2: intro; cases cache;
    [1: simplify in ⊢ (?→(%→?)→?); intros; rewrite > nth_empty; reflexivity;
    |2: simplify in ⊢ (((? ? %→?)→?)→?);
        simplify in ⊢ (?→(? ? %→?)→?); 
        intros; cases (?:n < length ? l ∨ length ? l ≤ n); 
        [1: generalize in match (leb_to_Prop (length ? l) n); cases (leb (length ? l) n);
            simplify; intros;[right;assumption|left;apply not_le_to_lt; assumption;]
        |2: rewrite < H2;[reflexivity] apply le_S; assumption;
        |3: clear H2; apply nth_short; simplify; apply le_S_S; apply H3;]]]
qed.

let rec by_cases (p:nat→bool) n on n : bool ≝
  match n with
  [ O ⇒ p O
  | S m ⇒ andb (p (S m)) (by_cases p m)].
  
lemma by_cases_ok:
  ∀m,P.by_cases P m = true → ∀n.n≤m → P n = true.
intros 2; elim m;
[1: rewrite > (?:n=O);[2:
      apply (symmetric_eq nat O n ?).apply (le_n_O_to_eq n ?).apply (H1)]
    apply H;
|2: simplify in H1; 
    cases (le_to_or_lt_eq ?? H2);
    [2: rewrite > H3; apply (andb_true_true ?? H1);  
    |1: apply H;
        [1: apply (andb_true_true_r ?? H1); ] apply le_S_S_to_le; apply H3;]] 
qed.

(*    
lemma good_cache : good_cache_spec cache.
unfold; intros 2; apply eqb_true_to_eq;
apply (by_cases_ok (length ? cache) (λi. eqb (nth_prime i) (nth ? cache (nth_prime i) i)) ? i H);
reflexivity;
qed. 
*)

let rec factorize_aux2 i n b on b ≝
 match b with
  [ O ⇒ nfa_zero
  | S b' ⇒
     let p ≝ smart_nth_prime cache i in
      match p_ord n p with
       [ pair q r ⇒
          match r with
          [ O ⇒ nfa_zero
          | S r' ⇒
             match r' with
             [ O ⇒
               match q with
               [ O ⇒ nfa_one
               | _ ⇒ nfa_proper (nf_last (pred q))]
             | S _ ⇒
                let res ≝ factorize_aux2 (S i) r b' in
                 match res with
                 [ nfa_zero ⇒ nfa_zero (* impossible *)
                 | nfa_one ⇒ nfa_proper (nf_last q)
                 | nfa_proper l ⇒ nfa_proper (nf_cons q l)]]]]].

definition factorize2 ≝ λn.factorize_aux2 0 n n.

let rec nf_id l :=
  match l with
  [ nf_last n => nf_last n
  | nf_cons a l => nf_cons a (nf_id l)].
  
definition nfa_id :=
  \lambda l.match l with [ nfa_proper l => nfa_proper (nf_id l) | _ => l].

lemma foo : 
  let x ≝ (4*7*593) in factorize2 x = nfa_id (factorize2 x).
intro;
reflexivity;
qed.
