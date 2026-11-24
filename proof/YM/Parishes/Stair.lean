import YM.Cardinal.Homage
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c f L:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
variable (x y:Label d) (q:Bool) (Pt:BudgetPoint)
set_option quotPrecheck false
namespace Stair
noncomputable def chartL (Pt:BudgetPoint)(w:ℝ)(i:Rings d) : Label d→ₗ[ℂ]ℂ:=(Stative.coord i.val).comp ((Sieve.widths Pt.threshold w).comp (labels d).subtype)
variable {w w' a b c₁ d₁ e y₃ ε ε' ε₁:ℝ}{Pt P Q R:BudgetPoint}
lemma gain (hp:0<a)(hi:0 ≤w)(hv:0≤ v)(ht:P.threshold ≤ a* Q.threshold)(hz:w ≤ a*v)(i:Rings d): ‖chartL P w i x‖ ≤ (a^life i.val.1*a^i.val.2.card)*‖chartL Q v i x‖:=by
    change ‖Stative.fare i x.val P.threshold w‖ ≤ _* ‖Stative.fare i x.val Q.threshold v‖; unfold Stative.fare; simp_rw [rank_fee,norm_mul,norm_pow,Complex.norm_real]; have he:=P.threshold_pos.le; have hE:=Q.threshold_pos.le; simp only [Real.norm_eq_abs,abs_of_nonneg hi,abs_of_nonneg hv,abs_of_nonneg he,abs_of_nonneg hE]; exact (mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ he ht _) (pow_le_pow_left₀ hi hz _) (pow_nonneg hi _) (pow_nonneg (mul_nonneg hp.le hE) _)) (norm_nonneg _)).trans_eq (by rw [mul_pow,mul_pow]; ring)
noncomputable def feeS (d:ℕ)(w:ℝ):=1+∑ i:Rings d,w^life i.val.1*w^i.val.2.card
lemma control (hP:0<a): 1 ≤feeS d a:=by unfold feeS; apply le_add_of_nonneg_right; exact sum_nonneg fun i _=> by positivity
local notation "Wd" => fun (i:Jars d)=> u^(weightJ i)*princS x i P w
local notation "Sd"=>toted u x P w
local notation "W₁"=>wealth y.val Q.threshold w'
local notation "Wi"=>wealth x.val P.threshold w
lemma wpS (i:Rings d)(j:Jars d) : chartL P w i (gradeCut d j x)= if crest i.val=j.val then chartL P w i x else 0:= size_ν ..
lemma roofS (hY: TypeBeta u w w' v a ε' ε₁ P Q x y) (hp:0<c₁)(hw:0≤w)(hu:0≤ v)(hα:P.threshold≤c₁*Q.threshold)(hg:w≤c₁*v)(hz:0≤u)(hA:0≤a)(he:0≤ε') :∀ i:Jars d, (Wd) i ≤ Fintype.card (Rings d)*feeS d c₁*(W₁+ε₁ +ε'*Wi + ∑ j∈univ.filter (fun j=>weightJ j<weightJ i), a *((Wd) j)):=by
   obtain ⟨g,hr,hW⟩:= hY.paid; let g0:= y-∑ j,g j; have hU:= (wealth_ge g0.val Q.threshold w').trans hW; let f (i:Jars d):= a*(Wd i); let h0(e:Rings d):= (u:ℂ)^weight e.val* chartL Q v e x; have hb(j:Jars d):0 ≤ Wd j:=mul_nonneg (pow_nonneg hz _) (wealth_ge ..); have hV (j:Jars d):0 ≤f j:=mul_nonneg hA (hb j)
   intro i; let J:=univ.filter (fun j:Jars d=>weightJ j<weightJ i); let Z:= W₁+ε₁+ε'*Wi+∑ j∈J,f j; have hZ:0 ≤ Z:= add_nonneg (add_nonneg (add_nonneg (wealth_ge ..) hU) (mul_nonneg he (wealth_ge ..))) (sum_nonneg fun j _ => hV j)
   have hf(e:Rings d):u^(weightJ i)* ‖chartL P w e (gradeCut d i x)‖ ≤ feeS d c₁ * Z:=by
       by_cases h: crest e.val=i.val; swap
       · rw [wpS,if_neg h,norm_zero,mul_zero]; exact mul_nonneg (zero_le_one.trans (control hp)) hZ
       rw [wpS, if_pos h]; have he':weightJ i=UV.weight e.val:= congr_arg Prod.fst h.symm; have hm:= (gain x hp hw hu hα hg e); have hp': c₁^life e.val.1*c₁^e.val.2.card≤feeS d c₁:=(single_le_sum (f:=fun i:Rings d=> c₁^life i.val.1*c₁^i.val.2.card) (fun i _=>by positivity) (mem_univ e)).trans (le_add_of_nonneg_left zero_le_one)
       let X:= chartL Q w' e
       apply le_trans (mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_right hp' (norm_nonneg _))) (pow_nonneg hz _)); rw [mul_left_comm,show u^weightJ i*‖chartL Q v e x‖=‖h0 e‖ from (by unfold h0; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz,he'])]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (control hp)); let G (j:Jars d):= X (g j) -(if i=j then h0 e else 0)
       have hQ(j:Jars d): ‖G j‖ ≤ ε'*princS x j P w+if weightJ j<weightJ i then f j else 0:=by
          by_cases hK: weightJ j<weightJ i
          · unfold G; have ht : i ≠ j:=fun he=>(by rw [← he] at hK; exact lt_irrefl _ hK); rw [if_pos hK,if_neg ht,sub_zero]; unfold f; refine ((fare_cap e (g j).val _ _).trans (hr j).1).trans ((mul_assoc ..|>.le).trans (le_add_of_nonneg_left (mul_nonneg he (wealth_ge ..))))
          rw [if_neg hK,add_zero]; have hF:= (hr j).2 e (he' ▸ le_of_not_gt hK); let A:=u^(weightJ i); have h1:(if i=j then h0 e else 0)= (u:ℂ)^(UV.weight e.val) *chartL Q v e (gradeCut d j x):=by rw [wpS,h]; by_cases ht:i=j <;> simp [ht, Subtype.coe_inj, h0]
          unfold G; rw [h1]; exact hF
       have hv: h0 e=X y-X g0-∑ j,G j:=by
            simp only [G,sum_sub_distrib]; unfold g0; rw [map_sub,map_sum]; simp
       have hs : ‖∑ j,G j‖ ≤ ε'*Wi+∑ j∈J,f j:=by
            apply (norm_sum_le ..).trans; have h': ε'*Wi+∑ j∈J,f j = ∑ j:Jars d,(ε'*princS x j P w + if weightJ j<weightJ i then f j else 0):=by rw [sum_add_distrib, coinsS,Finset.mul_sum]; unfold J; rw [sum_filter]; rfl
            rw [h']; exact sum_le_sum fun j _=> hQ j
       rw [hv]; exact (norm_sub_le ..).trans (show _ ≤ Z from ((add_le_add ((norm_sub_le ..).trans (add_le_add (fare_cap e _ _ _) ((fare_cap e _ _ _).trans hW))) hs)).trans_eq (by unfold Z; simp only [Submodule.subtype_apply]; abel))
   change u^weightJ i * (∑ j:Rings d, ‖chartL P w j (gradeCut d i.val x)‖) ≤ Fintype.card (Rings d)*feeS d c₁*Z; rw [Finset.mul_sum]; apply le_trans (sum_le_sum fun j _=>hf j); simp only [sum_const,card_univ,nsmul_eq_mul,← mul_assoc]; exact le_rfl
noncomputable def raiseS (d:ℕ)(A B:ℝ):ℕ→ℝ
   | 0=>1
   | n+1=>raiseS d A B n+A*(1+(Fintype.card (Jars d))*B*raiseS d A B n)
noncomputable def lootS (d:ℕ)(A B:ℝ):= let C:=Fintype.card (Rings d)*feeS d A; 1+ Fintype.card (Jars d)*raiseS d C B (d+1)
lemma plusP (ht:0≤A')(hb:0≤D)(i:ℕ):1 ≤ raiseS d A' D i:=by
    induction i with
    | zero=> exact le_rfl
    | succ n ih=> rw [raiseS]; have hM:=zero_le_one.trans ih; exact le_trans ih (le_add_of_nonneg_right (by positivity))
lemma positiveS (d:ℕ)(hp:0<a)(hv:0≤b): 1 ≤ lootS d a b:=by unfold lootS; have hG: 0 ≤ (Fintype.card (Rings d):ℝ)*feeS d a:=mul_nonneg (by positivity) (zero_le_one.trans (control hp)); dsimp only; exact le_add_of_nonneg_right (mul_nonneg (by positivity) (zero_le_one.trans (plusP hG hv _)))
lemma fareS (hY: TypeBeta u w w' v a ε' ε₁ P Q x y)(hp:0<c₁)(hw:0≤w)(hu:0≤ v)(hα:P.threshold≤c₁*Q.threshold)(hg:w≤c₁*v)(hz:0≤u)(hA:0≤a)(he:0≤ε') : Sd ≤ lootS d c₁ a*(W₁+ε₁+ε'*Wi):=by
    have h':= roofS x y hY hp hw hu hα hg hz hA he; have hP:0≤ε₁:=by obtain ⟨g,hr,hg⟩:= hY.paid; exact (wealth_ge ..).trans hg
    let M:= W₁+ε₁+ε'*Wi; let C:= (Fintype.card (Rings d):ℝ)*feeS d c₁; let H:= raiseS d C a; have hM:0≤M:= add_nonneg (add_nonneg (wealth_ge ..) hP) (mul_nonneg he (wealth_ge ..)); have hCV:0 ≤C:= mul_nonneg (by positivity) (zero_le_one.trans (control hp))
    have hf(n:ℕ) :∀ i:Jars d,weightJ i<n→ Wd i ≤ H n * M:=by
        induction n with
        | zero=> exact fun i hi=>by omega
        | succ n ih=>
             intro i hi; let K:=univ.filter (fun j:Jars d=>weightJ j<weightJ i); have hK :H (n+1)= H n+C*(1+Fintype.card (Jars d)*a*H n):=by unfold H; rw [raiseS]
             have hF:0≤H n:=zero_le_one.trans (plusP hCV hA n); rw [hK,add_mul]; apply le_trans (h' i)
             change C * (M+_) ≤ _; apply le_trans _ (le_add_of_nonneg_left (mul_nonneg hF hM)); rw [mul_assoc C]; apply mul_le_mul_of_nonneg_left _ hCV; rw [add_mul,one_mul]; apply add_le_add_right
             have hx : (∑ j∈K,a*(Wd j))≤∑ _j∈K,a*(H n*M):=sum_le_sum fun j hj=>mul_le_mul_of_nonneg_left (ih j (Nat.lt_of_lt_of_le ((mem_filter.mp hj).2) (by omega))) hA
             simp only [sum_const,nsmul_eq_mul] at hx; apply hx.trans; rw [show Fintype.card (Jars d)*a*H n*M=(Fintype.card (Jars d):ℝ)*(a*(H n*M)) from by ring]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast K.card_le_univ) (by positivity)
    apply le_trans (sum_le_sum (s:=Finset.univ) (fun i _=> hf (d+1) i (Nat.lt_succ_of_le (jar_w i)))); simp only [sum_const,nsmul_eq_mul]; unfold lootS; dsimp only; rw [add_mul,one_mul]; exact (mul_assoc ..|>.symm.le).trans (le_add_of_nonneg_left hM)
lemma lowerS (hz:0≤u)(hb:u ≤1): u^d*Wi ≤ Sd:=by rw [coinsS, Finset.mul_sum]; exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hz hb (jar_w i)) (wealth_ge ..)
lemma upperS (hz:0≤u)(hb:u≤1): Sd ≤ Wi :=by rw [coinsS]; exact sum_le_sum fun i _=> mul_le_of_le_one_left (wealth_ge ..) (pow_le_one₀ hz hb)
lemma smallS (hz:0 ≤u): 0 ≤ Sd:=sum_nonneg fun i _=>mul_nonneg (pow_nonneg hz _) (wealth_ge ..)
lemma descent (hY: TypeBeta u w w' v a ε' ε₁ P Q x y)(hp:0<c₁)(hw:0≤w)(hu:0≤ v)(hα:P.threshold≤c₁*Q.threshold)(hg:w≤c₁*v)(hz:0≤u)(hb:u≤1)(hA:0≤a)(he:0≤ε')(hr:lootS d c₁ a*(ε₁+ε'*Wi) ≤ (1/2)*u^d*Wi) : Sd ≤ 2*lootS d c₁ a * W₁:=by
    have h:= fareS x y hY hp hw hu hα hg hz hA he; rw [add_assoc,mul_add] at h; have hr':=(lowerS x hz hb (P:=P) (w:=w)); linarith only [h,hr',hr]
end Stair
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.roofS
