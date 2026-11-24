import YM.QCD.Stew.Wave
/-! # Whole-family coefficient. independent pre-cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ} {o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
-- moment coordinate sup vs E input
lemma surge (b:Flavor N)(X:EvenA c N)(i:SampleX) (h:0≤w)(p q:Pinor): w^2*‖shape o (feeF b X) i p q‖ ≤ Sen o w X :=by
   let g:=lens (N:=N) o; let I (x:Site c): Modes c N:= ((x,(p,0)),b); let J (x:Site c):Modes c N:=((x,(q,0)),b); let t (v:Site c × Site c):=tag (I v.1) (J v.2)
   let W x y := (shine o x*shine o y*mark o i x y)* blot b X x y p q
   have hg: shape o (feeF b X) i p q= ∑ v:Site c × Site c,W v.1 v.2:=by unfold shape; simp_rw [Matrix.sum_apply,Matrix.smul_apply,Fintype.sum_prod_type]; rfl
   let f j:= starch g w j * ‖coef j X.val‖; have h1 s: (t s).card=2:=by simp [t,tag]
   have hv : Injective t:=by rintro ⟨i,j⟩ ⟨x,y⟩ he; obtain ⟨hA,hB⟩:= (tagged ..).1 he; exact Prod.ext (congr_arg (Prod.fst ∘ Prod.fst : Modes c N→ Site c) hA) (congr_arg (Prod.fst ∘ Prod.fst : Modes c N→ Site c) hB)
   have hk (x y) : ‖blot b X x y p q‖= ‖coef (t (x,y)) X.val‖:=by
      change ‖bit (I x) (J y)*_‖=_; rcases bitS (I x) (J y) with ht|ht
      · rw [ht,one_mul]
      rw [ht,neg_mul,one_mul,norm_neg]
   have he (x y): ‖mark o i x y‖ ≤ pieD g (t (x,y)) := by
      cases i with
      | none=> rw [show mark _ _ _ _=1 from rfl,norm_one]; apply Nat.one_le_cast.mpr; exact one_le_pow₀ (by omega)
      | some i=>
         let D:= (t (x,y)).sup g; have hp : ∀ p:Keys c N,p∈t (x,y)→ g p ≤ pieD g (t (x,y)):=by
            intro p hp; apply (le_sup (f:=g) hp).trans; unfold pieD; have h: D ≤ 1+D := by omega
            refine h.trans (le_self_pow₀ (by omega) (by decide))
         have hx : separation x o ≤ pieD g (t (x,y)):=hp _ (show Sum.inr (I x)∈t (x,y) by simp [t,tag]); have hy : separation y o≤pieD g (t (x,y)):= hp _ (show Sum.inl (J y)∈ t (x,y) by simp [t,tag]); rcases i with ⟨j,_|_⟩
         · simpa only [AnalyticBridge.VerifiedReset.coord,mark,Option.elim, if_false,Bool.false_eq_true,↓reduceIte, Complex.norm_intCast] using (AnalyticBridge.VerifiedReset.small_coord o x j).trans (Nat.cast_le.mpr hx) -- test
         simpa only [AnalyticBridge.VerifiedReset.coord,mark,Option.elim,↓reduceIte, Complex.norm_intCast] using (AnalyticBridge.VerifiedReset.small_coord o y j).trans (Nat.cast_le.mpr hy)
   have hC (u:Site c×Site c): w^2* ‖W u.1 u.2‖≤ f (t u):=by
      have hx x : ‖shine o x‖=1:=by rcases shines o x with hp|hp <;> simp [hp]
      unfold W; simp_rw [norm_mul,hx,one_mul,hk]; unfold f starch; rw [h1]; simp only [← mul_assoc]; rw [mul_comm ((pieD g (t u):ℝ))]; gcongr; exact he ..
   rw [hg]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (sq_nonneg _)).trans; rw [mul_sum]
   apply (sum_le_sum (fun s _=> hC s)).trans; rw [← sum_image hv.injOn, Sen, plank,pricesD _ h]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> mul_nonneg (starch_pos g h _) (norm_nonneg _)
lemma defend : ∃ T:ℝ,0 ≤ T ∧∀ (X:Spike) (a:ℝ), (∀ p q, ‖X p q‖ ≤ a)→ ‖X‖≤T*a:=by
   let s i j:= Matrix.single i j (1:ℂ) (m:=Pinor) (n:=Pinor)
   let V (i j:Pinor):= s i j; let T:= ∑ i:Pinor,∑ j:Pinor, ‖V i j‖
   refine ⟨T,sum_nonneg (f:=fun i:Pinor=>∑ j,‖V i j‖) fun _ _=>sum_nonneg fun _ _=> norm_nonneg _,fun X a h=>?_⟩
   have ht:X=∑ i,∑ j,X i j • V i j:=by ext i j; simp [V,s,Matrix.sum_apply,Matrix.smul_apply,Matrix.single, ite_and]
   nth_rw 1 [ht]; apply (norm_sum_le ..).trans; unfold T; rw [sum_mul]; refine sum_le_sum fun i _=>?_ ; apply (norm_sum_le ..).trans; rw [sum_mul]; refine sum_le_sum fun j _=> ?_; rw [norm_smul,mul_comm _ a]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
lemma preMoment : ∃ K:ℝ,1≤K∧∀ (c:Side) (N:ℕ)(b:Flavor N)(i: Site c)(X:EvenA c N)(j: SampleX)(w:ℝ), 0 ≤ w→ w^2 * ‖shape i (feeF b X) j‖ ≤ K*Sen i w X:=by
    obtain ⟨T,hT,he⟩:=defend; refine ⟨max 1 T, le_max_left ..,fun c N b i X p w ht=>?_⟩
    let v:=shape i (feeF b X) p; let z:ℂ:=w^2; have hh:‖z‖=w^2:=by change ‖(w:ℂ)^_‖=_; rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg ht]
    have hf k j : ‖(z • v) k j‖ ≤ Sen i w X:=by rw [Matrix.smul_apply, norm_smul,hh]; exact surge b X p ht k j
    rw [← hh,← norm_smul]; exact (he (z • v) _ hf).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)) -- syntax
end YM.QCD.Stew
