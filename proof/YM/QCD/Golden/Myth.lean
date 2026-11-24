import YM.QCD.Golden.Shine
import YM.QCD.Stew.Cipher
/-! # Upgrades for tableau. Meristem receipt no rate yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Golden
open ConnectedActivityE6 Blaze Golden
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet
open Port Bay Strut Run
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}{η p a v:ℝ}{b k B:ℕ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V:E→Grid c}{x:E}
local notation "I"=> Pipe.Clump S ι
local notation "C'"=>Coat T
variable (Y:Fleet H ι N)
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
-- frob cert to coordinates
lemma leaning (he:Mode V x k v)(i:Bond c)(j l: Hue): ContDiffAt ℝ (↑k : WithTop ℕ∞) (fun y=> colour (V y i) j l) x:=by
    let A:su.Mat→ₗ[ℝ]ℂ:={toFun:=fun X=> Fork.colourRead X j l,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; exact A.toContinuousLinearMap.contDiff.contDiffAt.comp x (he.atLink i).smooth
open Jets Kit
end YM.QCD.Golden
-- switch scopes Matrix without contaminating.
namespace YM.QCD.Golden
open ConnectedActivityE6 Blaze Golden
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture
open Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt Loom Fleet Port Bay Run Jets Leaf Orbit Flume Pine YM.Next.Free
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{P:Teller su}{δ β τ μ W C:ℝ} {T:Tube su S}{R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι:Type}{N:ℕ}{η p a v z C' d:ℝ}{b k n B m j l:ℕ} {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V:E→Grid c}{x:E}
variable (Y:Fleet H ι N) {g: St c}{Γ: Land c (Site c) (Site c)}{Y':Pays c (Site c) (Site c)}
lemma formed {I:Type}[Fintype I][DecidableEq I] (a:E→Matrix I I ℂ) :ContDiffAt ℝ (↑k : WithTop ℕ∞) a x ↔ ∀ i j,ContDiffAt ℝ (↑k :WithTop ℕ∞) (fun i'=> a i' i j) x:=by
    let L : Matrix I I ℂ→ₗ[ℝ](I→I→ℂ):={toFun:=fun i p j=> i p j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
    let M : (I→ I→ℂ)→ₗ[ℝ] Matrix I I ℂ:={toFun:=Matrix.of,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; let f:=L ∘ a
    constructor
    · intro h i j; have hh:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x:= L.toContinuousLinearMap.contDiff.contDiffAt.comp x h; exact contDiffAt_pi.1 (contDiffAt_pi.1 hh i) j
    intro h; have hv:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x:= contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr (fun j=> h i j)
    exact M.toContinuousLinearMap.contDiff.contDiffAt.comp x hv
lemma slopeG (he: Mode V x k v) : ContDiffAt ℝ (↑k : WithTop ℕ∞) (Kit.settled ∘ V) x:= by
    have hh i:ContDiffAt ℝ (↑k : WithTop ℕ∞) (fun y=> colour (V y i)) x:=by
        apply (formed _).2; intro l j; exact leaning he i l j
    exact ( (contDiffAt_pi.mpr hh).prodMk (contDiffAt_pi.mpr (fun i=> (starL ℝ).contDiff.contDiffAt.comp x (hh i))))
lemma zestΦ (h: Pack id id η p b g a Γ Y') (ht:0<η)(hV: Mode V x k v)(i:Gaze c) (H:Cash W τ μ L Q o C T R): Zest (fun U y=> (sailP H Γ N).works i U (V y)) x k :=by
    let D:=radiusB τ; let φ:= sheetP Γ D i
    have hs : ContDiffAt ℝ (↑k : WithTop ℕ∞) (φ ∘ V) x:=by
       apply (formed _).2; intro j l
       let M:=chipK i.1 D Γ j.1 l.1 i.2; let F':= M ∘ (Kit.settled ∘ V)
       have he:ContDiffAt ℝ (↑k : WithTop ℕ∞) F' x:=by
          refine ((PolyDisc.finiteD M ?_).contDiffAt.restrict_scalars ℝ).comp x (slopeG hV)
          exact Filter.mem_of_superset ((country _ _).mem_nhds (citizenship _ ht (V x))) (cups h _ _ _ _ _).2.2.1 -- indices
       unfold φ sheetP batch Function.comp; simp_rw [monotype]
       have hx: ContDiffAt ℝ (↑k : WithTop ℕ∞) (fun x=> sale i.1 j.1 l.1 (F' x)) x:= he.const_smul (_:ℂ)
       exact (formed _).1 hx _ _ -- norms
    let B:= Stew.nozzle c N; let w := fun U:Grid f=> φ (lowC S.ratio U)
    have hz: Continuous w:=by
       have hh:Continuous φ:=by
          refine continuous_pi fun x=>continuous_pi fun y=>?_ ; unfold φ sheetP batch; simp_rw [monotype]; have he:= Jets.Sun.breeze (cups h i.1 x.1 y.1 D i.2) ht
          have hs :Continuous (fun U:Grid c=> sale i.1 x.1 y.1 (chipK i.1 D Γ x.1 y.1 i.2 (Kit.settled U))):= he.const_smul (_:ℂ)
          exact (continuous_apply y.2).comp ((continuous_apply x.2).comp hs)
       exact hh.comp (show Continuous (lowC S.ratio) from (by unfold lowC; fun_prop))
    obtain ⟨i',hi',hϕ⟩:= isCompact_univ.exists_isMaxOn Set.univ_nonempty hz.norm.continuousOn
    let q : Config su f → E→ EvenA c N := fun i x=> B (-(φ (V x)-w i))
    have hp: Zest q x k:= (( (Zest.single hs).plusminus (Zest.parallel (f:=w) (norm_nonneg _) (fun i=>hϕ (Set.mem_univ i)))).against).replay (B.restrictScalars ℝ)
    exact ((hp.wand (p:=NormedSpace.exp) (contDiff_iff_contDiffAt.mpr fun i=> (NormedSpace.exp_analytic (𝕂:=ℝ) (𝔸:=EvenA c N) i).contDiffAt)).plusminus (Zest.still _)) -- defeq
end YM.QCD.Golden
