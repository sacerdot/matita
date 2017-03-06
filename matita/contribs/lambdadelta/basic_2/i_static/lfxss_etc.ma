(*
lemma lfxss_zero: ∀R,I,L1,L2,V1. L1 ⦻**[R, V1] L2 → ∀V2.
                  R L1 V1 V2 → L1.ⓑ{I}V1 ⦻**[R, #0] L2.ⓑ{I}V2.
#R #I #L1 #L2 #V1 #H

elim H -L2 /3 width=5 by lfxs_zero, inj/
#L #L2 #H0 #HL2 #IH #V2 #HV12  
lapply (IH … HV12) -IH #HL1
@(step … HL1) -HL1 @lfxs_zero

axiom pippo_fwd: ∀R,I,Y1,L2,V2,T. Y1 ⦻*[R, T] L2.ⓑ{I}V2 →
                 ∃∃L1,V1. Y1 = L1.ⓑ{I}V1.

fact pippo: ∀R,I,L1,Y,T,V. L1.ⓑ{I}V ⦻**[R, T] Y →
            ∀L2,V1. Y = L2.ⓑ{I}V1 →
            ∀V2. R L1 V V2 →
            L1.ⓑ{I}V ⦻**[R, T] L2.ⓑ{I}V2.
#R #I #L1 #Y #T #V #H elim H -Y
[ /3 width=2 by lfxs_pair_repl_dx, inj/
| #L #Y #_ #HL2 #IH #L2 #V1 #H #V2 #HV2 destruct
  elim (pippo_fwd … HL2) #L0 #V0 #H destruct 
  @step [2: @(IH … HV2) // | skip ] -IH -HV2 

lemma lfxss_pair_repl_dx: ∀R,I,L1,L2,T,V,V1.
                          L1.ⓑ{I}V ⦻**[R, T] L2.ⓑ{I}V1 →
                          ∀V2. R L1 V V2 →
                          L1.ⓑ{I}V ⦻**[R, T] L2.ⓑ{I}V2.
#R #I #L1 #L2 #T #V #V1 * #f #Hf #HL12 #V2 #HR
/3 width=5 by lexs_pair_repl, ex2_intro/
qed-.
*)
