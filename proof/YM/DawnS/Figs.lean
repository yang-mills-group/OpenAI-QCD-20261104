import YM.DawnS.Mathe
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
variable {d:ℕ}
set_option maxHeartbeats 510000 in
lemma amel (p: Multi d)(a:Pinor)(b:Hue)(c:Flavor 6) : adjLine d (dnL ((p,a,b),c))= ∑ j:Pinor,-(sig p*gamma K a j) • upL ((p,j,b),c):=by
     change substitution (τK d) (conjug d (thetaBasis _ (Sum.inr ((p,a,b),c))))=_; rw[conj_base]; unfold substitution; rw [Module.Basis.constr_basis]; ext1 i; cases i with
     | inr i => simp [τK,upL,thetaBasis,Pi.single_apply]
     | inl i=>
        obtain ⟨⟨p',j',b'⟩,c'⟩:=i; simp only [Finset.sum_apply]; by_cases h:c=c' ∧ p=p' ∧ b=b'
        · obtain ⟨rfl,rfl,rfl⟩:=h; simp[τK,upL,thetaBasis,flipTable,spinTable,Lat.wave,Matrix.one_apply, Matrix.kronecker_apply,Pi.single_apply,sig,mul_ite]
        rw [Finset.sum_eq_zero]; swap
        · intro j _; change -(sig p*gamma K a j) * ((Pi.basisFun ℂ (letters d)) (Sum.inl ((p,j,b),c)) (Sum.inl ((p',j',b'),c'))) = (0:ℂ) -- purpose probe.Change.Coe
          simp[Pi.single_apply, mul_ite]; tauto
        by_cases ht:c=c'∧p=p'
        · simp only [τK,Matrix.fromBlocks_apply₂₁, flipTable,spinTable,Matrix.of_apply,if_pos ht,wave,Matrix.kronecker_apply, Matrix.one_apply,if_neg (fun e=>h ⟨ht.1,ht.2,e⟩),mul_zero]
        simp only [τK,Matrix.fromBlocks_apply₂₁,flipTable,spinTable,Matrix.of_apply,if_neg ht,mul_zero]
lemma cinders (p: Multi d)(a:Pinor)(b:Hue)(c:Flavor 6) : adjLine d (slashBar ((p,a,b),c))= ∑ i:Pinor, (sig p * gamma K a i) • slashCol ((p,i,b),c):=by
     have h(i:Axis)(q:Multi d)(h:AtNext i p q)(j:Pinor): -sig q*(gamma i *gamma K) a j=sig p*(gamma K * gamma i) a j:=by
           rw [faces _ _ i h]; by_cases hv:i=K; rw [if_pos hv,hv,neg_neg]; rw [if_neg hv,clifford hv,Matrix.neg_apply,neg_mul_neg]
     let f (i:Axis)(t:Pinor)(q:Multi d):=adjLine d (if AtNext i p q then gamma i t a • dnL ((q,t,b),c) else 0)
     let g (i:Axis)(t:Pinor)(l:Pinor)(q:Multi d):= (sig p*gamma K a t) • (if AtNext i p q then gamma i t l • upL ((q,l,b),c) else 0)
     unfold slashBar slashCol; simp_rw[map_sum]; simp only [Finset.smul_sum]; rw [Finset.sum_comm (f:=fun i:Pinor=>_)]
     change (∑ i:Axis,∑ l:Pinor,∑ q:Multi d,f i l q)=(∑ i:Axis,∑ l:Pinor,∑ j:Pinor,∑ q:Multi d,g i l j q); apply Finset.sum_congr rfl fun i _=>?_
     simp_rw [show ∀ l:Pinor, (∑ j:Pinor,∑ q:Multi d,g i l j q)=(∑ q:Multi d,∑ j:Pinor,g i l j q) from fun l=> Finset.sum_comm]; rw [Finset.sum_comm,Finset.sum_comm (f:=fun l q=> ∑ j:Pinor,g i l j q)]; refine sum_congr rfl fun q _=>?_
     unfold f g; by_cases hr:AtNext i p q; swap; · simp only [if_neg hr,map_zero,smul_zero,Finset.sum_const_zero]
     simp only [if_pos hr,map_smulₛₗ,amel,Finset.smul_sum,smul_smul]; rw[sum_comm,sum_comm (f:=fun L j=> (sig p*gamma K a L*gamma i L j) • upL ((q,j,b),c))]; refine Finset.sum_congr rfl fun j _=>?_ ; simp_rw [← Finset.sum_smul]; apply congr_arg (fun x:ℂ=> x • upL ((q,j,b),c)); have ht:=h i q hr j; rw [Matrix.mul_apply,Matrix.mul_apply,Finset.mul_sum, Finset.mul_sum] at ht; refine Eq.trans (Finset.sum_congr rfl fun t _=>?_) (ht.trans (Finset.sum_congr rfl fun t _=>?_))
     · change star (gamma _ _ _)*_= _; rw [star_gamma]; ring
     ring
end YM.DawnS
#print axioms YM.DawnS.cinders
#print axioms YM.DawnS.climbs
