import YM.Infer.Dream
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {K:KernelChoices}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R: BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P: SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
open Suburb Rails
namespace Tribute
open Massive.Poised Massive Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.Poised.Pipes
open Bank Hike Stative Stair -- Hike nested? open Bank before
variable {D U M A:Type}(Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0 Gn :ℕ)
variable {θ tol:ℝ}(Y:Metros P J θ F₀ χ)
-- same base.Cliff. Pre prices per node; Lois K-neighbor max in bootstrap of progress; simple sum bound†.
namespace Nacre
open Bounce Ivy MeasureTheory
variable (f:Fluke Θ Uv Gn) (V:PreLoan Θ Uv i0 Y Gn f)
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised.Sieve Orientation
open QCD
variable (p: Massive.UV.Label Gn)(W:Gallery.Knot p)(h:Requisite Θ p W)(ε:ℝ)
open Rails.Reference.Sharp Suburb.Melt Conductor Conductor.Quant
open MassiveQCD.Sample MassiveQCD.Sample.GreenCap.Works
variable (Φ:Capsule Θ Uv Gn f p W ε)(E: RiseBook Y)(b:ChangeQ)(L:Side)
-- packed together before billing.Beta cap rank disputes
variable {I : Type}[Fintype I]
open Finset
lemma stability (u:I→UV.Label Gn)(h:LinearIndependent ℂ u) : ∃ ε C:ℝ,0 < ε ∧ 1 ≤ C∧∀ v:I→UV.Label Gn,(∀ i,‖v i-u i‖<2* ε)→∀ p:I→ℂ,‖p‖ ≤ C*‖∑ i,p i • v i‖ :=by
    let T (x:I→UV.Label Gn) : (I→ℂ) →ₗ[ℂ] UV.Label Gn:=∑ i:I,(LinearMap.toSpanSingleton ℂ (UV.Label Gn) (x i)).comp (LinearMap.proj i)
    have ht(x p):T x p= ∑ i,p i • x i:= LinearMap.sum_apply ..
    obtain ⟨B,b',hB⟩:= LinearMap.exists_antilipschitzWith (T u) (show LinearMap.ker (T u)=⊥ from (LinearMap.ker_eq_bot'.mpr fun p hp=> funext fun i=> (Fintype.linearIndependent_iff.mp h p ((ht u p).symm.trans hp) i)))
    let k := (Fintype.card I : ℝ); let q:ℝ:= max (B:ℝ) 1; let ε := 1/(4*q*(k+1)); have hk :0 ≤ k:= Nat.cast_nonneg _; have hq :1≤ q:= le_max_right ..; have he:0 < ε:=by unfold ε; positivity
    refine ⟨ε,2*q,he,by linarith only [hq],fun v h p=>?_⟩; let w : ℝ:=2*ε; have he:‖∑ i,p i • (u i-v i)‖≤ k*‖p‖*w:=by
          calc
            _ ≤ ∑ i:I, ‖p i • (u i-v i)‖:= norm_sum_le ..
            _ ≤ ∑ _:I,‖p‖*w:=by apply Finset.sum_le_sum; intro i hi; rw [norm_smul,norm_sub_rev]; exact mul_le_mul ((pi_norm_le_iff_of_nonneg (norm_nonneg p)).mp le_rfl i) (h i).le (norm_nonneg _) (norm_nonneg _)
            _ = _ := by simp [k,mul_assoc]
    have hh:(T u) p=(∑ i,p i • v i)+ (∑ i,p i • (u i-v i)):=by simp_rw [smul_sub, ht, Finset.sum_sub_distrib]; abel
    have hv := ((hB.le_mul_norm (map_zero _) p).trans (mul_le_mul_of_nonneg_right (show (B:ℝ)≤ q from le_max_left ..) (norm_nonneg _))).trans (mul_le_mul_of_nonneg_left (show ‖T u p‖ ≤ ‖∑ i,p i • v i‖+k*‖p‖*w from (hh ▸ (norm_add_le _ _)).trans (add_le_add_right he _)) (zero_le_one.trans hq))
    have hy:q*k*w ≤1/2:=by apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (zero_le_one.trans hq)) (show 0≤w from by unfold w; positivity)).trans_eq; unfold w ε; field_simp <;> norm_num
    nlinarith only [hv, mul_le_mul_of_nonneg_left hy (norm_nonneg p)]
lemma prestige :∃ C:ℝ,1 ≤ C∧∀ (x:UV.Label Gn)(t v:ℝ), ‖dimming t v Gn x‖ ≤ C*wealth x.val t v:=by
    let B:= Module.finBasis ℂ (UV.Label Gn); obtain ⟨C,hC,h⟩:= payFrame B; let g:= B.equivFun.toContinuousLinearEquiv; let f:= g.symm.toContinuousLinearMap; refine ⟨max 1 (‖f‖*C),le_max_left ..,?_⟩; intro x p q
    let y:= dimming p q Gn x; have hv :‖y‖ ≤ ‖f‖*watch B x p q:= by change ‖y‖ ≤ ‖f‖*‖g y‖; nth_rw 1 [show y=f (g y) from (g.symm_apply_apply y).symm]; apply f.le_opNorm (g y) -- nth_rw 1 likely rewrites RHS dependent
    exact hv.trans ((mul_le_mul_of_nonneg_left (h x p q) (norm_nonneg _)).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right (le_max_right ..) (wealth_ge ..))))
noncomputable abbrev Venus (d:ℕ):= Fin (Gallery.sizeD d)
local notation "Ω!"=> Venus Gn
set_option quotPrecheck false
-- t-α choice made during trajectory; can raise independently.
structure Symph where
    u : Venus Gn → UV.Label Gn
    F : (i:Venus Gn)→Gallery.Knot (u i)
    score i: Requisite Θ (u i) (F i)
    ε : ℝ
    K : ℝ
    J : ℝ
    T₁ : (i:Venus Gn)→ Capsule Θ Uv Gn f (u i) (F i) ε
    pos:0<ε
    help:1 ≤ K
    up: 1 ≤ J
    high:∀ (v:Venus Gn→UV.Label Gn),(∀ i,‖v i-u i‖ <2*ε) → ∀ p:Venus Gn→ℂ,‖p‖ ≤ K*‖∑ i,p i • v i‖
    tall :∀ (x: UV.Label Gn)(t v:ℝ),‖dimming t v Gn x‖ ≤ J*wealth x.val t v
lemma shoot :Nonempty (Symph Θ Uv Gn f):=by
    obtain ⟨U,h,H⟩:= Gallery.chosen Θ Vb Gn fun k=> Work.G02.answer Work.G01.answer su Vb k
    obtain ⟨ε,C,hε,hC,hϕ⟩:= stability Gn U H; choose F hF using (show ∀ i: Venus Gn,∃ F:Gallery.Knot (U i), Requisite Θ (U i) F from h)
    obtain ⟨J,hJ,hS⟩:= prestige Gn; exact ⟨U,F,hF,ε,C,J,(fun i=> Classical.choice (predawns Θ Uv Gn f _ _ (hF i) ε hε)), hε,hC,hJ,hϕ,hS⟩
end Nacre
end Tribute
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.Nacre.shoot
