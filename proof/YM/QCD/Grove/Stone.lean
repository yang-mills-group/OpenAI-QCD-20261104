import YM.QCD.Grove.Cusp
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio.Sharp
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c C F L:Side}{w b j:ℕ}{B:BudgetPoint}{U V:Config G c}{t d p:ℝ}
lemma downturn (U: Directions G c) (w:ℕ)(x:Site c) (h:B.dirBound x U) : B.dirBound (delta w x) (((1+(w:ℝ))^B.power)⁻¹ • U):=by
    let C:=(1+(w:ℝ))^B.power; have hc:0<C:=by unfold C; positivity
    have hm (i:Site c): 1+(separation i x:ℝ) ≤ (1+(w:ℝ))*(1+(separation i (delta w x):ℝ)):=by
       have hh : (separation i x :ℝ) ≤ (separation i (delta w x):ℝ)+w:=by exact_mod_cast ((separation_triangle i (delta w x) x).trans (Nat.add_le_add_left (show separation (delta w x) x≤w from (separation_comm ..).trans_le (countD w x)) _)) -- signature
       have hz:0≤ (w:ℝ)*(separation i (delta w x):ℝ):=by positivity
       linarith only [hh,hz]
    intro i; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hc).le]; apply (mul_le_mul_of_nonneg_left (h i) (inv_nonneg.mpr hc.le)).trans
    let a:=1+(separation i.1 x:ℝ); let b:=1+(separation i.1 (delta w x): ℝ)
    change C⁻¹* (B.threshold*a^B.power)≤B.threshold*b^B.power; have hp:(a^B.power) ≤ C*b^B.power:= by unfold C; rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (hm i.1) _
    calc C⁻¹* _ ≤ C⁻¹*(B.threshold*(C*b^B.power)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp B.threshold_pos.le) (inv_nonneg.mpr hc.le)
         _ = _:= by field_simp
-- ALL strict Seam estimates needed. θ independent ν
abbrev ticketR (B : BudgetPoint)(w:ℕ)(d:ℝ):ℝ:= ((1+(w:ℝ))^B.power)^B.order*(2^B.order*((1+(2*w:ℕ):ℝ)^(B.power*B.order))*d)
variable (h:Isle G B w c t p) (S:2*(2*w) ≤ C.val) (x:Site c)(j:Site C)(f: Config G c→ℝ)(g:Config G C→ℝ) (hf:LocalOn (neighbors w x) f)(hx:∀ (U : Config G c), flags B.threshold U=∅→ f U=g (shapeL S x j U))
variable (hc:∀ U, flags B.threshold U=∅→ Push.Local.Chart B.order g U)
include hf hc hx h
lemma sapling (U:Config G c)(hk:Healthy B.threshold (neighbors (w+(2*w+1)) x) U)(ht:Push.Local.Chart B.order f U)
    (he: ∀ U, flags B.threshold U=∅ → landscape B C t p U → ∀ l:List (Directions G C), l.length ≤ B.order→ (∀ i∈ l,‖i‖≤B.threshold)→ ‖leftDerivs g l U‖ ≤ d) (l: List (Directions G c))(hl:l.length ≤ B.order)(hp:∀ i∈l,B.dirBound x i): ‖leftDerivs f l U‖ ≤ ticketR B w d:=by
    apply threshold h x f hf l hl _ U hk ht
    intro i hi; have hv:= Boulevard.smoky hi
    have hT V: Healthy B.threshold V i:=by unfold Healthy; rw [hv]; simp
    have hh:=flare S x j i (hT _); let M:= shapeL S x j i; have hG: f=ᶠ[𝓝 i] g∘ shapeL S x j:= ((Boulevard.sky _).mem_nhds hi|>fun h=> Eventually.mono h (fun i hi=> hx i (Boulevard.smoky hi)))
    have he:= he _ hh (h.fruit C S j x i (hT _)); let c:=(1+(w:ℝ))^B.power; have hz:1≤c:=one_le_pow₀ (by simp)
    let X:=l.map (fun i=>c⁻¹ • i); have hL:X.length ≤B.order:=by simpa only [X,List.length_map] using hl
    have h1:X.map (fun i=> c • i)=l:=by simp [X,List.map_map,Function.comp_def,smul_smul,(zero_lt_one.trans_le hz).ne']
    let u:= leftDerivs (g ∘ shapeL S x j) X i; rw [(UVNext.PricedKernels.left_congr hG l).self_of_nhds, ← h1, March.expands,norm_smul,Real.norm_of_nonneg (pow_pos (zero_lt_one.trans_le hz) _).le]
    unfold ticketR; exact mul_le_mul (pow_le_pow_right₀ hz hL) (rests S x j i g (hc _ hh) he X hL (fun i hi=> by obtain ⟨i,hii,rfl⟩:=List.mem_map.mp hi; exact downturn _ w x (hp _ hii))) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hz) _)
end YM.PhysicalNext.Repeat.Trio.Sharp
#print axioms YM.PhysicalNext.Repeat.Trio.Sharp.sapling
