import YM.Play.Moselle
/-! # skew covariance charging. In strange grade first, no sight-mask.
     No physical antisym convention on raw tickets. Kept as presentation with optional entries; antisymmetric amount `Q-Q.transpose` is the final derivative sign. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Anomaly
open Cove Function MeasureTheory Filter Finset NormedSpace Creek Ledge Grass Matrix
open scoped BigOperators Topology ContDiff Classical Matrix
variable {A B T: Type*}[Fintype A][Fintype B]{X U V:Finset A}{Z :Finset B}{n m i k:ℕ}{C D K s t:ℝ}
def Wand (Q:Matrix A A ℂ): EndA A:=∑ i,∑ j,Q i j • (Creek.v j*Creek.v i)
-- no factorial >d powers
lemma moll (Q:Matrix A A ℂ)(a:Finset A)(h:a ⊆U): Wand Q (mono a)∈ Rim U (a.card-1):=by
    unfold Wand; rw [ContinuousLinearMap.sum_apply]; refine Submodule.sum_mem _ fun i _=>?_ ; rw [ContinuousLinearMap.sum_apply]; apply Submodule.sum_mem; intro j _; rw [ContinuousLinearMap.smul_apply]; exact (Rim U _).smul_mem _ (Rim.monotone (Finset.Subset.refl _) (Nat.sub_le _ 1) (Rim.clip j (Rim.clip i (Rim.layerIn h le_rfl)))) -- weaker easier
lemma mellow (Q:Matrix A A ℂ){x:Alg A}(h:x∈ Rim U n): Wand Q x ∈ Rim U (n-1):=by
    rw [Rim.record h,map_sum]; refine Submodule.sum_mem _ fun i hi=>?_ ; rw [map_smul]; exact Submodule.smul_mem _ _ (Rim.monotone (Finset.Subset.refl U) (Nat.sub_le_sub_right (mem_filter.mp hi|>.2) 1) (moll Q i (mem_powerset.mp (mem_filter.mp hi|>.1))))
lemma vacant (Q:Matrix A A ℂ){x:Alg A}(h:x∈Rim U 0): Wand Q x=0:=by
    unfold Wand; rw [ContinuousLinearMap.sum_apply]; apply sum_eq_zero; intro i _; rw [ContinuousLinearMap.sum_apply]; refine sum_eq_zero fun j _=>?_ ; rw [ContinuousLinearMap.smul_apply,ContinuousLinearMap.mul_apply,Rim.vacated i h,map_zero,smul_zero]
lemma stout (Q:Matrix A A ℂ): Stays (Wand Q) (univ:Finset A):= Stays.shine _ _ (fun i _=> Stays.shine _ _ fun j _=> (gammaT (mem_univ j) (mem_univ i)).pumps _)
lemma streak (Q:Matrix A A ℂ)(k:ℕ){x:Alg A}(h:x∈Rim U n):((Wand Q)^k:EndA A) x∈ Rim U (n-k):=by
   induction k with
   | zero=> simp only [pow_zero,ContinuousLinearMap.one_apply,Nat.sub_zero]; exact h
   | succ k ih=> rw [pow_succ']; exact (Nat.sub_sub n k 1) ▸ mellow Q ih
lemma sent (Q:Matrix A A ℂ)(k:ℕ){x:Alg A}(h:x∈Rim U n)(hh:n<k): ((Wand Q)^k:EndA A) x=0:=by
    cases k with | zero=> omega| succ k=> rw [pow_succ']; exact vacant Q (U:=U) ((Nat.sub_eq_zero_of_le (show n≤k by omega)) ▸ streak Q k h)
lemma boughs (Q:Matrix A A ℂ){x:Alg A}(h:x∈ Rim U n): birth (Wand Q) x= ∑ i∈range (n+1),(i.factorial:ℂ)⁻¹ • ((Wand Q)^i:EndA A) x:=by
    let Y i:=(i.factorial:ℂ)⁻¹ • ((Wand Q)^i:EndA A) x; have hX:HasSum Y (birth (Wand Q) x):= Stays.birther _ x; refine hX.tsum_eq.symm.trans (tsum_eq_sum (fun i hi=>?_)); unfold Y; rw [sent Q i h (by rw [Finset.mem_range] at hi; omega),smul_zero]
lemma meadow (Q:Matrix A A ℂ){x:Alg A}(h:x∈Rim U n): birth (Wand Q) x ∈Rim U n:=by rw [boughs Q h]; exact Submodule.sum_mem _ fun i _=>Submodule.smul_mem _ _ (Rim.monotone (Finset.Subset.refl _) (Nat.sub_le _ _) (streak Q i h))
private lemma creditV (i:A) (x:Alg A): ‖Creek.v i x‖≤‖x‖:=by
    let u (j:A):= (1:ℝ); have he:= fee u (fun i=>zero_lt_one) i x; have hz (x: Alg A):load u x=‖x‖ :=by rw [dry u (fun i=>zero_lt_one),Grass.norm_def]; simp [u] -- edit
    rw [hz,hz] at he; simpa [u] using he
lemma money (Q:Matrix A A ℂ) (h:∀ i∈U,∀ j∈U, ‖Q i j‖ ≤ C) (he:X⊆U):
    ‖Wand Q (mono X)‖ ≤ (X.card:ℝ)^2*C:=by
     let f (i j:A): Alg A:= Q i j • Creek.v j (Creek.v i (mono X))
     have hz : Wand Q (mono X)=∑ i∈X,∑ j∈X,f i j :=by
        unfold Wand; simp_rw [ContinuousLinearMap.sum_apply]; symm
        change _=∑ i:A,∑ j:A,f i j; refine Eq.trans (b:=∑ i∈X,∑ j:A,f i j) ?_ (sum_subset (subset_univ X) (?_)) -- e eta
        · refine sum_congr rfl fun i _=> sum_subset (subset_univ _) (fun j _ hj=>by
              change f i j=0; unfold f; rw [show Creek.v j (Creek.v i (mono X))=0 from lock j (preserves _ (Rim.monoIn X)) hj,smul_zero])
        intro i _ hi; apply sum_eq_zero; intro j _; change f i j=0; unfold f; rw [lock i (Rim.monoIn X) hi,map_zero,smul_zero]
     rw [hz]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> ∑ _j∈X,C) ?_).trans (by simp [nsmul_eq_mul,pow_two,mul_assoc]))
     intro i hi; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j hj; unfold f; rw [norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) ((creditV j _).trans ((creditV i _).trans (norm_mono _|>.le)))).trans (h i (he hi) j (he hj))
lemma moneyB (Q:Matrix A A ℂ) (h:∀ i∈U,∀ j∈U, ‖Q i j‖≤ C)(hC:0 ≤ C){x:Alg A}(hx:x∈ Rim U n): ‖Wand Q x‖ ≤ ((n:ℝ)^2*C)* ‖x‖:=by
    conv_lhs=>rw [Rim.record hx,map_sum]
    let p:=(n:ℝ)^2*C; rw [Grass.norm_def x]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> p*‖coef i x‖) ?_).trans (?_)); intro j hj; rw [map_smul,norm_smul,mul_comm]; obtain ⟨hp,hj⟩:=mem_filter.mp hj; exact mul_le_mul_of_nonneg_right ((money Q h (mem_powerset.mp hp)).trans (by unfold p; gcongr)) (norm_nonneg _)
    rw [Finset.mul_sum]; apply sum_le_sum_of_subset_of_nonneg (subset_univ _); intro i _ _; unfold p; positivity
lemma minus (Q Y: Matrix A A ℂ) (x :Alg A): Wand Q x-Wand Y x=Wand (Q-Y) x:=by
    unfold Wand; simp only [ContinuousLinearMap.sum_apply,← sum_sub_distrib, Matrix.sub_apply]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> (sub_smul (Q i j) (Y i j) (Creek.v j (Creek.v i x))).symm
/-- logarithmic cost without paying for higher moments or losing relative aperture -/
def dime (n:ℕ)(C:ℝ):ℝ:= (n+1:ℕ) * (((n:ℝ)^2*C+1)^n)
lemma stable_wand (Q:Matrix A A ℂ)(h:∀ i∈U,∀ j∈U,‖Q i j‖≤ C)(hC:0≤C){x:Alg A}(hx:x∈Rim U n)(k:ℕ): ‖(Wand Q^k:EndA A) x‖ ≤ (((n:ℝ)^2*C+1)^k)*‖x‖:=by
    induction k with
    | zero=> simp
    | succ i ih=>
      let A₀:=(n:ℝ)^2*C; change _ ≤ (A₀+1)^(i+1)*_; rw [pow_succ',pow_succ' (A₀+1)];  have hp:= moneyB Q h hC (Rim.monotone (Finset.Subset.refl _) (Nat.sub_le n _) (streak Q i hx)); refine (hp.trans (?_ : A₀* _ ≤ _)); change A₀ * _ ≤ ((A₀+1)*_)*_; rw [mul_assoc (A₀+1)]; exact mul_le_mul ((le_add_of_nonneg_right zero_le_one)) ih (norm_nonneg _) (add_nonneg (mul_nonneg (sq_nonneg _) hC) zero_le_one)
lemma coupon (Q:Matrix A A ℂ)(h:∀ i∈U,∀ j∈U,‖Q i j‖≤ C)(hC:0 ≤ C){x:Alg A}(hx:x∈Rim U n): ‖birth (Wand Q) x‖ ≤ dime n C*‖x‖:=by
    let V:=(n:ℝ)^2*C+1; rw [boughs Q hx]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> V^n*‖x‖) (?_)).trans (by simp only [dime,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc]; exact le_rfl))
    intro i hi; rw [norm_smul]; have h0 : 1 ≤ (i.factorial:ℝ):= Nat.one_le_cast.mpr i.factorial_pos; have hv:1 ≤ V:=le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hC); refine (mul_le_of_le_one_left (norm_nonneg _) (show ‖(i.factorial:ℂ)⁻¹‖ ≤1 from ?_)).trans ((stable_wand Q h hC hx i).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hv (Nat.le_of_lt_succ (mem_range.mp hi))) (norm_nonneg _)))
    rw [norm_inv,Complex.norm_natCast]; exact inv_le_one_of_one_le₀ h0
lemma returnX (Q Y:Matrix A A ℂ)(h:∀ i∈U,∀ j∈U,‖Q i j‖≤ C)(he:∀ i∈U,∀ j∈U, ‖Y i j‖ ≤C)(h':∀ i∈U,∀ j∈U,‖Q i j-Y i j‖≤ s)(hs:0≤s)(hC:0 ≤ C){x:Alg A}(hx:x∈Rim U n)(k:ℕ):
    ‖(Wand Q^k:EndA A) x-(Wand Y^k:EndA A) x‖ ≤ ((k:ℝ)*(n:ℝ)^2*s*((n:ℝ)^2*C+1)^k)*‖x‖:=by
    induction k with
    | zero=>simp
    | succ i ih=>
      rw [pow_succ' (Wand Q),pow_succ' (Wand Y),pow_succ' (_*_+1) i]; let V:=(n:ℝ)^2*C; have hv:0 ≤ V:=by unfold V; positivity
      let a:=(Wand Q^i:EndA A) x; let b:=(Wand Y^i:EndA A) x; have ha:a ∈ Rim U n:= Rim.monotone (Subset.refl _) (Nat.sub_le ..) (streak Q i hx); have hb:b∈ Rim U n:= Rim.monotone (Subset.refl _) (Nat.sub_le ..) (streak Y i hx)
      have h₁: ‖Wand Q a-Wand Q b‖ ≤ V*((i:ℝ)*(n:ℝ)^2*s*(V+1)^i*‖x‖):= by rw [← map_sub]; exact ((moneyB Q h hC (Submodule.sub_mem _ ha hb)).trans (mul_le_mul_of_nonneg_left ih hv))
      have h₂: ‖Wand Q b-Wand Y b‖ ≤ ((n:ℝ)^2*s)*((V+1)^i*‖x‖):=by rw [minus]; exact (moneyB (Q-Y) h' hs (U:=U) hb).trans (mul_le_mul_of_nonneg_left (stable_wand Y he hC hx i) (mul_nonneg (sq_nonneg _) hs))
      refine (norm_sub_le_norm_sub_add_norm_sub (Wand Q a) (Wand Q b) (Wand Y b)).trans ((add_le_add h₁ h₂).trans ?_)
      let b':=(n:ℝ)^2*s*(V+1)^i*‖x‖; change _ ≤ _ *‖x‖; suffices he : V*((i:ℝ)*b')+b' ≤ (i+1)*((V+1)*b') by unfold b' V at he; push_cast; unfold V; linarith only [he]
      have h:0 ≤ b':= by unfold b'; positivity
      nlinarith only [mul_nonneg hv h, mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) h]

def percent (n:ℕ)(C:ℝ):ℝ:= (n:ℝ)*(n:ℝ)^2*dime n C
lemma interest (Q Y:Matrix A A ℂ)(h:∀ i∈U,∀ j∈U,‖Q i j‖≤ C)(he:∀ i∈U,∀ j∈U, ‖Y i j‖ ≤C)(h':∀ i∈U,∀ j∈U,‖Q i j-Y i j‖≤ s)(hs:0 ≤ s)(hC:0 ≤ C){x:Alg A}(hx:x∈Rim U n): ‖birth (Wand Q) x-birth (Wand Y) x‖ ≤ percent n C* s *‖x‖:=by
     let V:=(n:ℝ)^2*C+1; have hv:1 ≤ V:= le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hC); rw [boughs Q hx,boughs Y hx, ← Finset.sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> ((n:ℝ)*(n:ℝ)^2*s*V^n)*‖x‖) (?_)).trans (by rw [sum_const,card_range,nsmul_eq_mul]; unfold percent dime V; exact le_of_eq (by ring)))
     intro i hi; have hp:i≤n:=Nat.le_of_lt_succ (mem_range.mp hi); rw [← smul_sub,norm_smul]; have h0:1 ≤ (i.factorial:ℝ):= Nat.one_le_cast.mpr i.factorial_pos
     exact (mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_inv,Complex.norm_natCast]; exact inv_le_one_of_one_le₀ h0)).trans ((returnX Q Y h he h' hs hC hx i).trans (by gcongr))
end YM.QCD.Anomaly
#print axioms YM.QCD.Anomaly.interest
