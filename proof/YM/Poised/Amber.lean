import YM.Poised.Facets
/-! # sections & support upgrades used in conditioning.Price relative.Sights.Weak and strong masks, actual emitted/priced.Legility. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k n:ℕ}{c l:Side}
namespace Facets
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource
open Counting Counting.Click Display Costs Sieve Chute PhysicalNext.Repeat PhysicalNext.Repeat.Brim MassiveQCD.Plate
variable {R:BudgetPoint}{V:Support c}{o:Site c}{F:Grid c→Lat.Fields c 6}{a t:ℝ}{r K n:ℕ}
-- Region of local F jets
lemma byLane (s:List (Directions su c))(hs:s.length ≤ R.order)(U:Grid c)(hV: Healthy R.threshold V U)(hf:Sight V o K R t F a): leftDerivs F s U ∈ region (limits V):=by
   let y:= leftDerivs F s U; change y∈_; rw [← write y]; apply Subalgebra.sum_mem; intro i _
   by_cases h:i⊆limits (F:=6) V; · apply Subalgebra.smul_mem; obtain ⟨f,-,hm,H⟩:=expression i; rw [H]; refine Subalgebra.list_prod_mem _ ?_; simp only [List.mem_ofFn]; rintro _ ⟨j,hj⟩; rw [← hj]; exact Creek.marked _ _ (h ((hm _).mpr ⟨j,rfl⟩))
   let L:= ((coef i).restrictScalars ℝ).toContinuousLinearMap; rw [show coef i y=0 from ?_, zero_smul]; rotate_left
   · change L _=0; rw [←Push.Local.left_linear L s (hf.use U hV) hs]; rw [show L∘ F=(fun _=>0) from funext fun i=> ember _ (hf.gate i) _ h]; simpa only [ite_self] using! (Work.G07.left_const (0:ℂ) s U)
   exact Subalgebra.zero_mem _
open QCD.Stew
lemma tiers {X:Support c} (h: Sight X o 2 R t F a)(r n i:ℕ)(ht:i ≤n)(hv:0<t)(hh:∀ i∈ X,separation i o ≤ k): R.supBounds o X (framesF (purseX o r t)∘ (mantel i ∘ F)) (((1+(k:ℝ))^r)^n*a):=by
    let C:= (1+(k:ℝ))^r; have hg:1 ≤ C:= one_le_pow₀ (by simp); have h0:= h.travels
    refine ⟨by positivity,fun V hV l hl hp=>?_⟩; let A:= framesF (purseX o r t); let P:=A.comp (mantel i); change ‖leftDerivs (P∘F) l V‖≤ _; rw [Push.Local.left_linear _ _ (h.use V hV) hl]; let Y:= leftDerivs F l V
    let S:=mantel i Y; change Creek.load _ _ ≤ _; apply le_trans (b:= C^n*MassiveQCD.Plate.view o 2 Y t) _ (mul_le_mul_of_nonneg_left (h.pole _ hV _ hl hp) (by positivity))
    unfold MassiveQCD.Plate.view; rw [Creek.dry (purseX o r t) (purse_pos o r t hv), Finset.mul_sum]; apply sum_le_sum; intro j _
    change (∏ k∈j,purseX o r t k)*‖coef j (panel i Y)‖ ≤ _; rw [Stew.angel]; split; swap
    · rw [norm_zero,mul_zero]; unfold MassiveQCD.Plate.toll; positivity
    next hG=>
       by_cases hx:j⊆limits (F:=6) X; swap
       · rw [ember _ (byLane l hl _ hV h) _ hx,norm_zero,mul_zero,mul_zero,mul_zero]
       have ht' : t*C>0:= by positivity
       have hh' : ∀ p∈j, purseX o r t p≤ t*C:=by intro p hp; apply mul_le_mul_of_nonneg_left _ hv.le; exact pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (hh _ ((mem_filter.mp (hx hp)).2))) _) _
       rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (prod_le_prod (fun i _=> (purse_pos _ _ _ hv _).le) hh').trans; rw [prod_const,mul_pow,mul_comm _ (C^j.card)]; apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hg (hG ▸ ht)) (by positivity)) (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by simp))) (by positivity))
lemma extended (h: Sight V o 2 R t F a)(hF:∀ i∈ V,separation i o ≤ k)(hv:0<t)(r n :ℕ): Flame F R V o t r n (((1+(k:ℝ))^r)^n*a):=
   ⟨Counting.Terrain.padded _ (le_mul_of_one_le_left h.travels (one_le_pow₀ (one_le_pow₀ (by simp)))) h,fun i hi=> tiers h _ _ i hi.le hv hF⟩
lemma leFlame (h: Flame F R V o t r n a)(c₀:ℝ)(ht:a ≤ c₀): Flame F R V o t r n c₀:= ⟨Counting.Terrain.padded c₀ ht h.sight,fun i hi=>⟨h.sight.travels.trans ht,fun U hU l hl hp=> ((h.issues i hi).2 _ hU _ hl hp).trans ht⟩⟩
lemma across (h: Flame F R V o t r n a)(X:Support c) (hX: V⊆X): Flame F R X o t r n a:=by
   refine ⟨⟨fun i j hi=> h.sight.room _ _ (agrees_mono hi hX), fun i=> regionMon (limitsMon _ _ hX) (h.sight.gate _),fun U hU=>h.sight.use _ (hU.mono_left hX),fun U hU=>h.sight.pole _ (hU.mono_left hX),h.sight.borel,h.sight.travels⟩,?_⟩; intro i hi; refine ⟨(h.issues i hi).1,fun U hU=> (h.issues i hi).2 U (hU.mono_left hX)⟩
open Carte.Hem Lining Lining.Temper Collage Papyrus
variable (U: Source.Hol su)(A:Exhibit U)(F₀: Basis (Fog d) ℂ (Label d)) {p D:ℕ}
lemma placed_s (d:ℕ)(i:Site c)(b:Cover)(h:i∈ pot d c b): separation i (wrap c b) ≤ d:=by obtain ⟨t,h,h1⟩:= halo_spec.mp h; rw [Finset.mem_singleton.mp h,separation_comm] at h1; exact h1
lemma massy (h: Permit.used_bound (A.t d) p)(m k D' i:ℕ): ∃ t:ℝ,0≤t∧ ∀ (b:Cover)(B:BudgetPoint)(c:Side),B.power=m→B.order=k→ 2*(p+1)< c.val→ ∀ (v:ℝ),0<v→ ∀ x:Label d, Flame (Realize.placed (A.t d) c b (A.lead d x)) B (pot (p+1) c b) (wrap c b) v D' i (t*watch F₀ x B.threshold v):= by
    obtain ⟨t,h0,H⟩:= Counting.Click.wide U A F₀ h m k 2
    let C:= ((1+(↑(p+1):ℝ))^D')^i; refine ⟨C*t,mul_nonneg (by unfold C; positivity) h0,fun b B c hp hB hV v hv x=>?_⟩; rw [mul_assoc]; exact extended (H b B c hp hB hV v hv x) (fun k=> placed_s _ _ _) hv D' i
end Facets
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Facets.massy
