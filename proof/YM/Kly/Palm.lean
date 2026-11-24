import YM.Kly.Fact
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
variable (hA: B.Comparison (bloom P H w))
lemma scalarLimit {M:Type}[NormedAddCommGroup M][NormedSpace ℂ M][FiniteDimensional ℂ M]
        (A: ℕ→ M→ₛₗ[starRingEnd ℂ]M→ₗ[ℂ]ℂ)(h:∀ x y:M,∃ s:ℂ,Tendsto (fun i=>A i x y) atTop (𝓝 s))(v:ℕ→M)(p:M)(ht:Tendsto v atTop (𝓝 p)) (s:ℂ)(hs:Tendsto (fun i=>A i p p) atTop (𝓝 s)):Tendsto (fun i=> A i (v i) (v i)) atTop (𝓝 s):=by
       choose a ha using h; let b:= Module.finBasis ℂ M; let c(j i)(z:M):= star (b.coord i z)*(b.coord j z); have he(i:ℕ)(z:M): A i z z=∑ k,∑ j, c j k z * A i (b k) (b j):=by
            conv_lhs=> enter [1,2]; rw [← b.sum_repr z] -- mess
            rw [_root_.map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun k _=>?_ ; rw[map_smulₛₗ,LinearMap.smul_apply]; nth_rw 2 [← b.sum_repr z]; rw [_root_.map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul]; exact (mul_assoc ..).symm
       have hv (v:ℕ→M)(h:Tendsto v atTop (𝓝 p)): Tendsto (fun i=>A i (v i) (v i)) atTop (𝓝 (∑ k,∑ j,c j k p*a (b k) (b j))):=by
             refine (show Tendsto (fun i=>∑ k,∑ j,c j k (v i)*A i (b k) (b j)) atTop _ from ?_).congr (fun i=> (he i _).symm); apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; refine Tendsto.mul (?_) (ha (b i) (b j)); exact (((b.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp h).star).mul ((b.coord j).continuous_of_finiteDimensional.continuousAt.tendsto.comp h)
       exact (tendsto_nhds_unique hs (hv (fun _=>p) tendsto_const_nhds)) ▸ hv v ht
include P H Y E U w hA
lemma regain (k:F.W)(h:k≠0):∃ r:ℝ,0<r∧0<chart Sα (r • basis t₀) k k:=by
       by_contra! ht
       obtain ⟨d,hd⟩:= E.exhaustive k; let W:= F.level d; haveI:= E.finite d; letI: ProperSpace ↥W:=FiniteDimensional.proper ℂ _; let f(i):= B.frame 0 d ((B.frame i d).symm (⟨k,hd⟩:W)); have hv(i:ℕ):f i≠0:=by intro hx; unfold f at hx; have hz:(⟨k,hd⟩:W)=0:= map_eq_zero_iff _ (B.frame i d).symm.injective|>.mp (map_eq_zero_iff _ (B.frame 0 d).injective|>.mp hx); exact h (congr_arg Subtype.val hz)
       let u(i:ℕ):↥W:= (((‖f i‖⁻¹):ℝ):ℂ) • f i; have hu(i:ℕ):‖u i‖=1:=by unfold u; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i))]
       obtain ⟨y,hy,g,hg,hY⟩:= (isCompact_sphere (0:↥W) 1).tendsto_subseq (fun i:ℕ=> Metric.mem_sphere.mpr ((dist_zero_right ..).trans (hu i)))
       have hN:y≠0:=by rintro rfl; simp at hy
       let K:= (B.frame 0 d).symm
       let A(i:ℕ):W →ₛₗ[starRingEnd ℂ] W→ₗ[ℂ]ℂ:=
            { toFun:=fun x=> (invoices P H w (B:=B) d (g i) (K x)).comp K.toLinearMap,map_add':=fun p q=>LinearMap.ext fun v=> by simp,map_smul':=fun c p=>LinearMap.ext fun v=> by simp }
       obtain ⟨z,hz⟩:= onto (K y); let a:ℂ:= wick (fun _ : Fin 2=>d) (points ![0,basis t₀]) (![C.sym.adj d t₀ z,z]); have he:Tendsto (fun i=> A i (u (g i)) (u (g i))) atTop (𝓝 a):=by
            refine scalarLimit A ?_ _ y hY a ?_; · intro x v; obtain ⟨z,hz⟩:= onto (K x); obtain ⟨t,ht⟩:= onto (K v); change ∃ s,Tendsto (fun i=>invoices P H w (B:=B) _ _ (K x) (K v)) _ _; simp_rw [←hz,←ht]; exact ⟨_,(boxP P H Y E U w hA _ z t).comp hg.tendsto_atTop⟩
            change Tendsto (fun i=> invoices P H w (B:=B) _ _ (K y) (K y)) _ _; simp_rw [←hz]; exact (boxP P H Y E U w hA d z z).comp hg.tendsto_atTop
       have hm:0<a:=by simpa only [one_smul] using U.detects d z (hz ▸ ((map_ne_zero_iff K K.injective).2 hN)) 1 zero_lt_one -- map syntax
       apply hm.ne; refine tendsto_nhds_unique (?_ : Tendsto (fun i=> A i (u (g i)) (u (g i))) _ (𝓝 0)) he; apply tendsto_const_nhds.congr'; refine Eventually.of_forall fun i=>?_ ; have hp : chart Sα (B.radius (g i) • basis t₀) k k=0:=by
             have h₁:= trueP P H Y E k w (B.radius (g i)) (U.positive _); exact ((eq_or_lt_of_le h₁).resolve_right (ht _ (U.positive _))).symm
       have hv : A i (f (g i)) (f (g i))=0:=by change chart Sα _ ((B.frame (g i) _ (K (f _))).val) ((B.frame (g i) _ (K (f _))).val)=_; unfold f K; rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]; exact hp
       change 0=A i (u _) (u _); unfold u; rw [map_smulₛₗ,map_smulₛₗ (A i),LinearMap.smul_apply,hv,smul_zero,smul_zero]
variable (ha:∀ x:F.W,F.adj t₀ (F.parity x)= F.parity (F.adj t₀ x))(hL:∀ i:Axis,∃ p:EuPin,Leads F i p)
include hL ha R hx
lemma qualified: Fields.Euclidean (bloom P H w) :=rising P H Y R E U w hx ha hL (fun x h=>by obtain ⟨r,hr,he⟩:=regain P H Y E U w hA x h; rw [charter] at he; exact ⟨r,hr,he⟩)
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.qualified
