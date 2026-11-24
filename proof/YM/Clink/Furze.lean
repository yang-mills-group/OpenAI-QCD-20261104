import YM.Clink.Rice
/-! Canonical costs.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal.Surge
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {c f L:Side}{v t x δ α β κ ρ C C' ξ M B3 G3 σ B1 G1 a D_:ℝ}{P:BudgetPoint}{k n l m N:ℕ}
open QCD.Ruby Cove NormedSpace
open Massive.PCAC Massive.PCAC.Oren WindowU
local notation "b₂"=>(25/256:ℝ)
local notation "τ"=>(1/512:ℝ)
local notation "b₁"=>(24/256:ℝ)
local notation "b₀"=>(1/8:ℝ)
local notation "ε"=>(1/256:ℝ)
-- Pe Year Uniform startup, after wallet allowable H0=l.slot; κ estimated by scheduler below. caps.h.J
noncomputable def loomR (P:BudgetPoint)(F:ℕ)(M y:ℝ):= mCash P.B P.power P.order F τ b₂ (M*y)
noncomputable def hkappa (P:BudgetPoint):= anth ε (b₂+2*ε) P.B
noncomputable def cleanA (P:BudgetPoint)(F n:ℕ)(M T ξ L K:ℝ):= loomR P F M ξ*(hkappa P*(T*K^2)) + (n:ℝ)*(ξ*cashZ K b₂) -- Z surcharge + absorbs.L ignored
noncomputable def pl (P:BudgetPoint)(F n:ℕ)(M T C ξ d K:ℝ):= (n:ℝ)*(ξ*(C*K^2*P.threshold)) + 6* cleanA P F n M T (d*ξ) d K
noncomputable def pu (P:BudgetPoint)(F n:ℕ)(M T C ξ d K:ℝ):= (n:ℝ)*(ξ*(C*K^2)) + 6* cleanA P F n M T (d*ξ) d K
noncomputable def scarf :ℝ:= Real.exp (b₁-b₀)
noncomputable def ubi (P:BudgetPoint)(F:ℕ)(M η P0 T0 B:ℝ):= loomR P F M η *(hkappa P*P0)+B+ loomR P F M η *(Stags.bonus F P.B ε*0+ T0)
noncomputable def foe (P:BudgetPoint)(m n:ℕ)(B:ℝ):= riseP m n P.B ε b₁ * B
structure Capital (P:BudgetPoint)(F m n:ℕ)(a b M η P0 T0 B V H:ℝ):Prop where
       economic : hullP P.B F*(Real.exp (b₂+τ)*(M*η*2^P.order)) ≤ τ
       toll : 0 ≤ ubi P F M η P0 T0 B
       vigor : let v:= foe P m n (ubi P F M η P0 T0 B); Stags.bonus F P.B ε*(v+b*(a*v)) ≤1
       porch : ubi P F M η P0 T0 V ≤ 1
       rise : Real.exp (b₁-b₀)*T0 + ubi P F M η P0 T0 B ≤ T0
       beams : (1+b*a)*foe P m n (ubi P F M η P0 T0 B)≤H
       plane : a*foe P m n (ubi P F M η P0 T0 B) ≤H
lemma ubi_nn (hh:0≤M)(hp:0≤ξ)(hk:0≤v)(hz:0≤B1)(hn:0≤C):0 ≤ ubi P k M ξ C B1 v:=by
       unfold ubi; have he:0 ≤ loomR P k M ξ:=by unfold loomR mCash mRent beamFee polyPrice hullP; dsimp only; positivity
       exact add_nonneg (add_nonneg (mul_nonneg he (mul_nonneg (earnA ..) hn)) hk) (mul_nonneg he (by rw[mul_zero,zero_add]; exact hz))
-- permit linearity M wallet depends only B and v^2. purchases later.
end YM.MassiveQCD.Sample.Basal.Surge
#print axioms YM.MassiveQCD.Sample.Basal.Surge.ubi_nn
