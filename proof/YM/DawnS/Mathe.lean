import YM.DawnS.Tastes
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
variable {d:ℕ}
abbrev upL {d:ℕ}(i:SpinMode d):beam d:=thetaBasis (Pairs (SpinMode d)) (Sum.inl i)
abbrev dnL {d:ℕ}(i:SpinMode d):beam d:=thetaBasis (Pairs (SpinMode d)) (Sum.inr i)
noncomputable abbrev sig (p:Multi d):ℂ:=(-1:ℂ)^power p K
noncomputable abbrev τK (d:ℕ): Matrix (letters d) (letters d) ℂ:= Matrix.fromBlocks 0 (flipTable K (-(gamma K).transpose)) (flipTable K (-gamma K)) 0
noncomputable def conjug (d:ℕ): beam d→ₛₗ[starRingEnd ℂ] beam d where
    toFun v:= fun y=> star (v y)
    map_add' x y:=by ext1 i; exact star_add ..
    map_smul' t x:=by ext1 i; change star (_*_)=star t*_; rw [star_mul,mul_comm]
noncomputable abbrev adjLine (d:ℕ): beam d→ₛₗ[starRingEnd ℂ] beam d:= (Grass.substitution (τK d)).comp (conjug d)
noncomputable abbrev τSpin (d:ℕ):SpinPol d→ₛₗ[starRingEnd ℂ]SpinPol d:= (changeVars (τK d)).toLinearMap.comp dagger
lemma conj_base (i:letters d):conjug d (thetaBasis _ i)=thetaBasis _ i:=by ext1 j; change star (thetaBasis _ i j)=_; simp [thetaBasis,Pi.single_apply, apply_ite star]
lemma legged (b:beam d): τSpin d (line b)=line (adjLine d b):=by
     rw [← (thetaBasis _).sum_repr b]; simp only [map_sum,map_smul,map_smulₛₗ]; refine Finset.sum_congr rfl fun i _=>congr_arg _ ?_; change changeVars _ (dagger (atom i))= _; rw [dagger_atom]; unfold adjLine; rw[LinearMap.comp_apply,conj_base]; exact ExteriorAlgebra.map_apply_ι _ _ -- exterior coefficient ? map_apply
set_option maxHeartbeats 510000 in
lemma alum (p: Multi d)(a:Pinor)(b:Hue)(c:Flavor 6) : adjLine d (upL ((p,a,b),c))= ∑ j:Pinor,-(sig p*gamma K j a) • dnL ((p,j,b),c):=by
     change substitution (τK d) (conjug d (thetaBasis _ (Sum.inl ((p,a,b),c))))=_; rw[conj_base]; unfold substitution; rw [Module.Basis.constr_basis]; ext1 i; cases i with
     | inl i => simp [τK,dnL,thetaBasis,Pi.single_apply]
     | inr i=>
        obtain ⟨⟨p',j',b'⟩,c'⟩:=i; simp only [Finset.sum_apply]; by_cases h:c=c' ∧ p=p' ∧ b=b'
        · obtain ⟨rfl,rfl,rfl⟩:=h; simp[τK,dnL,thetaBasis,flipTable,spinTable,Lat.wave,Matrix.one_apply, Matrix.kronecker_apply,Pi.single_apply,sig,mul_ite]
        rw [Finset.sum_eq_zero]; swap
        · intro j _; change -(sig p*gamma K j a) * ((Pi.basisFun ℂ (letters d)) (Sum.inr ((p,j,b),c)) (Sum.inr ((p',j',b'),c'))) = (0:ℂ) -- purpose probe.Change.Coe
          simp[Pi.single_apply, mul_ite]; tauto
        by_cases ht:c=c'∧p=p'
        · simp only [τK,Matrix.fromBlocks_apply₁₂, flipTable,spinTable,Matrix.of_apply,if_pos ht,wave,Matrix.kronecker_apply, Matrix.one_apply,if_neg (fun e=>h ⟨ht.1,ht.2,e⟩),mul_zero]
        simp only [τK,Matrix.fromBlocks_apply₁₂,flipTable,spinTable,Matrix.of_apply,if_neg ht,mul_zero]
lemma faces(p q:Multi d)(a:Axis)(h:AtNext a p q): sig q= if a=K then -sig p else sig p:=by unfold sig; rw[h]; by_cases ht:a=K <;> first | solve | simp [ht,pow_succ] | solve | simp [ht,Ne.symm ht]
lemma star_gamma(i:Axis)(a b:Pinor): star (gamma i a b)=gamma i b a:= by nth_rw 2 [←gamma_star i]; rfl
lemma climbs (p: Multi d)(a:Pinor)(b:Hue)(c:Flavor 6) : adjLine d (slashCol ((p,a,b),c))= ∑ i:Pinor, (sig p * gamma K i a) • slashBar ((p,i,b),c):=by
     have h(i:Axis)(q:Multi d)(h:AtNext i p q)(j:Pinor): -sig q*(gamma K *gamma i) j a=sig p*(gamma i * gamma K) j a:=by
           rw [faces _ _ i h]; by_cases hv:i=K; rw [if_pos hv,hv,neg_neg]; rw [if_neg hv,clifford (Ne.symm hv),Matrix.neg_apply,neg_mul_neg]
     let f (i:Axis)(t:Pinor)(q:Multi d):=adjLine d (if AtNext i p q then gamma i a t • upL ((q,t,b),c) else 0)
     let g (i:Axis)(t:Pinor)(l:Pinor)(q:Multi d):= (sig p*gamma K t a) • (if AtNext i p q then gamma i l t • dnL ((q,l,b),c) else 0)
     unfold slashCol slashBar; simp_rw[map_sum]; simp only [Finset.smul_sum]; rw [Finset.sum_comm (f:=fun i:Pinor=>_)]
     change (∑ i:Axis,∑ l:Pinor,∑ q:Multi d,f i l q)=(∑ i:Axis,∑ l:Pinor,∑ j:Pinor,∑ q:Multi d,g i l j q); apply Finset.sum_congr rfl fun i _=>?_
     simp_rw [show ∀ l:Pinor, (∑ j:Pinor,∑ q:Multi d,g i l j q)=(∑ q:Multi d,∑ j:Pinor,g i l j q) from fun l=> Finset.sum_comm]; rw [Finset.sum_comm,Finset.sum_comm (f:=fun l q=> ∑ j:Pinor,g i l j q)]; refine sum_congr rfl fun q _=>?_
     unfold f g; by_cases hr:AtNext i p q; swap; · simp only [if_neg hr,map_zero,smul_zero,Finset.sum_const_zero]
     simp only [if_pos hr,map_smulₛₗ,alum,Finset.smul_sum,smul_smul]; rw[sum_comm,sum_comm (f:=fun L j=> (sig p*gamma K L a*gamma i j L) • dnL ((q,j,b),c))]; refine Finset.sum_congr rfl fun j _=>?_ ; simp_rw [← Finset.sum_smul]; apply congr_arg (fun x:ℂ=> x • dnL ((q,j,b),c)); have ht:=h i q hr j; rw [Matrix.mul_apply,Matrix.mul_apply,Finset.mul_sum, Finset.mul_sum] at ht; refine Eq.trans (Finset.sum_congr rfl fun t _=>?_) (ht.trans (Finset.sum_congr rfl fun t _=>?_))
     · change star (gamma _ _ _)*_= _; rw [star_gamma]; ring
     ring
end YM.DawnS
