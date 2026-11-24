import YM.Hypnos.Sere
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}
open Current
-- work on full color native lift
namespace Fruit
open UVNext.PricedKernels FreeResolvent
variable {ι κ:Type}{v s t:ℝ}
local notation "points'"=> S.ratio.parent ∘ Prod.fst
local notation "b'"=> (S.patch.L.val:ℝ)
variable {H:Bed}{B:Bed}{p p':Clip}{T₀:Towers S.patch.L}
def stuns (i:ι→Site c)(j:κ→Site c)(V:Matrix ι κ ℝ)(b:ℕ): Matrix ι κ ℝ:= Matrix.of fun a u=> if j u∈halo b {i a} then V a u else 0
abbrev sprig (G:Gauge)(S:StepData c f)(H B:Bed)(T:Towers S.patch.L):= stuns (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) (curtain G S H B T)
abbrev cones (G:Gauge)(S:StepData c f)(H B:Bed)(T:Towers S.patch.L):= stuns (S.ratio.parent ∘ Prod.fst) Prod.fst (view G S H B T)
lemma stinging [Fintype κ](i:ι→Site c)(j:κ→Site c)(V:Matrix ι κ ℝ)(b:ℕ)(hA: (native c).Rows i j s A V)(hp:0≤ s):
    (native c).Rows i j 0 (Real.exp (-s*b)*A) (V-stuns i j V b):=by
    have hB a u : (V-stuns i j V b) a u≠0→ (b:ℝ)≤ (native c).d (i a) (j u):=by
       intro h; rw [Matrix.sub_apply,stuns,Matrix.of_apply] at h; split at h
       next => simp at h
       next hg =>
          have hz:b< separation (i a) (j u):= lt_of_not_ge fun he=> (show j u∉ halo b {i a} from ‹_›) (halo_spec.mpr ⟨_,mem_singleton_self _,he⟩)
          change (b:ℝ)≤ ((separation (i a) (j u)):ℝ)
          exact_mod_cast hz.le
    simpa only [sub_zero] using! (hA.far _ hp hB (fun a u=> by rw [Matrix.sub_apply,stuns,Matrix.of_apply]; split<;>simp))
-- all consumes paid actual.Quotas.X. schedule.Event_A.Form support here if kr etc.
structure Myth (G:Gauge)(S:StepData c f)(H B: Bed)(T:Towers S.patch.L)(b:ℕ)(C v:ℝ):Prop where
    broad: (native c).Rows (S.ratio.parent ∘ Prod.fst) Prod.fst 0 C (view G S H B T)
    tight : (native c).Rows (S.ratio.parent ∘ Prod.fst) Prod.fst 0 v (view G S H B T-cones G S H B T b)
    paysC: (native c).Rows (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) 0 C (curtain G S H B T)
    tightC : (native c).Rows (S.ratio.parent ∘ Prod.fst) (S.ratio.parent ∘ Prod.fst) 0 v (curtain G S H B T-sprig G S H B T b)
lemma Anthe (G:Gauge) {K:KernelChoices}(J:Patch)(v s M:ℝ)(hv:0<v)(hs:0<s)(hM:0≤M)(L:Side)(d:ℝ):∃ C:ℝ, ∃ W:ℝ→ℝ,0 ≤ C ∧ Rate G L d W ∧∀ᶠ x:ℝ in atTop, ∀ (c f:Side)(S:StepData c f)(F:Tree.Forest S.ratio)(H B:Bed)(p p':Clip)(T₀:Towers S.patch.L),S.patch=J→S.kernel=K→ Larger (G:=G) S→ H.covered s M→B.covered s M → Floor H p f v M → Floor B p' c v M → Towers.Diagonal S H B T₀→T₀.T.strip s (M/(S.patch.L.val:ℝ)^2)→
    Myth G S H B T₀ (radiusB x) C (W x):=by
    obtain ⟨u,C,hu,hC,h⟩:=floats G (K:=K) J v s M hv hs hM
    let C':= pla_cost s M J.L.val; let ε:= s/J.L.val; have hε : 0<ε:= by unfold ε; positivity
    let E':= max C C'; let t:= min u ε; have ht:= lt_min hu hε
    let Y x:=Real.exp (-t*radiusB x); have hy: Rate G L d Y:=by
       apply ((Rate.cutoff (δ:=t) ht)).compare; filter_upwards with x; rw [abs_of_pos (show 0<Y x from Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; exact mul_le_mul_of_nonpos_left (show ((till x):ℝ) ≤ radiusB x from Nat.cast_le.mpr (Nat.div_le_self ..)) (neg_nonpos.mpr ht.le)
    refine ⟨E',_,hC.trans (le_max_left ..), hy.mul_right E', Eventually.of_forall ?_⟩
    intro x c f S F H B p p' T₀ hp hK hZ hD hB hh he hz ht'
    have hf: (native c).Rows (S.ratio.parent ∘ Prod.fst) Prod.fst ε C' (view G S H B T₀):= by
       unfold C' ε; rw [← hp]; exact upl G S hD.2.2.2.2 hB.1 ht' hM hs
    have hy:= hf.mono (min_le_right u ε) (le_max_right C C'); have hJ:=(h c f S F H B p p' T₀ hp hK hZ hD.2.1 hh he hz).mono (min_le_left u ε) (le_max_left C C')
    exact ⟨hy.mono ht.le le_rfl, stinging _ _ _ _ hy ht.le,hJ.mono ht.le le_rfl,stinging _ _ _ _ hJ ht.le⟩
end Fruit
end YM.Hypnos
#print axioms YM.Hypnos.Fruit.Anthe
