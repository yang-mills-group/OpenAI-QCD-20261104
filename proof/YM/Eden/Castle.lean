import YM.Eden.Tick
/-! # Quotas at weighted rate, approximate normalized projection. usable launch budgets. α corrective weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Filter Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r g q N:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit
variable (p:Bard d)(Q:SourceRead.TaperHol)(K:Hol su)(hk:Drops.Peg K (d/2))(hp:p∈ Rgl d i g q)
local notation "Y"=> wide d 1 p
local notation "Wt"=>oink d g q
local notation "D"=> wide d 1 ∘ motto
local notation "markₚ"=> setas d (revere d p)
-- collect universals with grants split
structure ProofB (Q:SourceRead.TaperHol)(X:Drape)(p:Mini d)(P:BudgetPoint)(v:ℝ) (M:ℕ)(ε:ℝ) : Prop where
    sells : ∃ y:Mini d,(∀ (n:Side)(o:Cover),M≤ n.val→ Beacon.ActionTest Q o (X n o) y.val) ∧ ‖PrismD.prism P.threshold v d y-p‖ < ε -- Norm drift.ψ.
variable (ε:ℝ) (he:0<ε)
include hp hk he
lemma earned :∃ m:ℕ,∃ Z:ℝ,0≤ Z ∧ ∀ᶠ r:ℕ in atTop,∀ k₀ m₀ f j:ℕ,∃ C:ℝ,1≤ C ∧∀ X:ℝ,0≤ X→ ∃ δ M:ℝ,0<δ∧0 < M ∧∀ (P:BudgetPoint)(W η v:ℝ),0<W →0<η →0<v → P.threshold<δ→ M≤ η*P.threshold→ M≤ v →∀ (K:Side)(j':ℕ)(F:Train j')(H:Bed)(hQ:(milky 0 H K (G:=su) (d':=d)).IsSymm), Farm (wager 0 H K hQ) (corsage F K d 0) X→ (let U:=doll i g q W η P.threshold v (flareR d H K F hQ W η p); ProofB Q U (setas d (revere d p)) P v m ε∧∀ (l:Side)(b:Cover),P.order=k₀ → P.power=m₀ → 2*(r+1)<l.val → Priced (U l b) P b r f j v C (Z*(P.threshold^g)⁻¹)):=by
    obtain ⟨m,D',L,hD,hL,H⟩:= book p Q K hk hp ε he; obtain ⟨Z,hZ,h⟩:= offersL p Q K hk hp; refine ⟨m,Z+Z,add_nonneg hZ hZ,?_⟩; filter_upwards [h] with r hr k₀ m₀ f j'; obtain ⟨C,hC,H',hz⟩:=hr k₀ m₀ f j'; refine ⟨C+C,by linarith,fun X h0=>?_⟩; obtain ⟨A,hA,hu⟩:= YM.Eden.sunny X h0 p hp
    have hM :∀ᶠ M:ℝ in atTop,A/M≤1 ∧ (A/M)*L < ε/2:=by
        have ht:Tendsto (fun x:ℝ=> A/x) atTop (𝓝 0):=by simp only [div_eq_mul_inv]; simpa only [mul_zero] using (tendsto_inv_atTop_zero (𝕜:=ℝ)).const_mul A -- signature
        have he':Tendsto (fun x:ℝ=> A/x*L) atTop (𝓝 0):=(zero_mul L) ▸ ht.mul_const L
        exact (Eventually.mono (ht.eventually (gt_mem_nhds zero_lt_one)) (fun _ h=> le_of_lt (show _ from h))).and (he'.eventually (gt_mem_nhds (by linarith[he]))) -- inference
    obtain ⟨M,hM,hV⟩:= (hM.and (eventually_ge_atTop (1:ℝ))).exists; refine ⟨min D' 1,M,lt_min hD (by norm_num),by linarith,fun P W η v hw hv hv' ht h₁ h₂ c j F Y' hv0 hf0=>?_⟩; intro U
    let τ:= P.threshold; have hT:0 < τ:= P.threshold_pos; have hm:P.threshold ≤1:= ht.le.trans (min_le_right ..)
    obtain ⟨X,hX,h⟩:= hu W η c Y' hv0 j F hf0; let t(i:Pad d):= weaveT g q i η τ v (X i); have he: ∑ i∈ oink d g q,‖t i‖ ≤ _ := weave_amt q g η τ v X M A h₁ h₂ hV hX -- signature
    have hx: U = warpP g q τ v (wide d 1 p)+ ∑ i∈oink d g q, t i • warpP i.1.length i.2.length τ v (wide d 1 (motto i)):=by unfold U; rw[h]; exact credit0 q g W η _ v hw hv hT hv' _ _ _ _
    rw [hx]; refine ⟨⟨H τ v hT hv' (ht.trans_le (min_le_left ..)) t ((mul_le_mul_of_nonneg_right he (zero_le_one.trans hL)).trans_lt hM.2)⟩,?_⟩; intro l b ha hb hp; rw[add_mul]; exact (coinW hv' b H' ha hb hp).shelter (show Priced ((∑ i∈oink d g q, t i • warpP i.1.length i.2.length τ v (wide d 1 (motto i))) l b) P b r f j' v C (Z*(τ^g)⁻¹) from (by simp only [Finset.sum_apply,Pi.smul_apply]; exact coinΦ hv' b t hz hZ (zero_le_one.trans hC) (he.trans hM.1) ha hb hp hm)) hv'.le -- parens
end YM.Massive.Evo
#print axioms YM.Massive.Evo.earned
