import YM.Clink.Vilax
import YM.Kai.Nines
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
lemma loomρ (M η:ℝ) (n k m B:ℕ):mCash B n k m τ b₂ (M*η)= η* mCash B n k m τ b₂ M:=by unfold mCash mRent beamFee; dsimp only; ring
lemma zest_v : cashZ v b₂=v^2*cashZ 1 b₂:=by unfold cashZ; ring
open Rates
open Animals
-- deterministic envelope shared small currency costs. C clock multiplier W(B) sufficiently after.L independent any Pt. let target χ(B)*v² even for unscaled. Fee surcharge.
variable (nF kF pF nL kL iF:ℕ)(vM vT At M₀ Ξ₀:ℝ)
local notation "cM"=>M₀ + 6*(M₀+M₀)
local notation "Rz" B:arg=> anth ε (b₂+2*ε) B
local notation "FP" B:arg=> mCash B pF kF nF τ b₂ M₀
local notation "Φp" B:arg=> mCash B pF kF nF τ b₂ cM
noncomputable def prepV (B:ℕ):ℝ:=let F:= (FP B); F*(Rz B)*At + (iF:ℝ)*cashZ 1 b₂
local notation "Tτ" y:arg=> prepV nF kF pF iF At M₀ y
noncomputable def trekV (C _:ℝ)(B:ℕ):ℝ:= let S:= Φp B; S*(Rz B)+ B* (0:ℝ)+(iF:ℝ)*C+ 6*(prepV nF kF pF iF At M₀ B)+S -- use two budgets.Precall
#print trekV
local notation "Tu" C:arg y:arg=> trekV nF kF pF iF At M₀ C 0 y
local macro "payments_aes" : tactic => `(tactic| repeat' first | exact Fuel.cons _|exact Fuel.self | apply Fuel.add|apply Fuel.mul|apply Fuel.pow)
lemma cost_traits : Fuel (fun B=>Tu vT B) ∧ Fuel (fun B=>riseP nL kL B ε b₁) ∧ Fuel (fun B=> Stags.bonus nF B ε) ∧ Fuel (fun B=> hullP B nF):=by
      have hb: Fuel (fun B=> Stags.bonus nF B (1/256)):=by unfold Stags.bonus Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
      have hw: Fuel (fun B=> anth (1/256) (25/256+2*(1/256)) B):=by unfold anth Footprint.payment Footprint.degreeIncome Footprint.spread ballCost; push_cast; payments_aes
      have hc (A:ℝ):Fuel (fun B=>mCash B pF kF nF τ b₂ A):=by unfold mCash mRent beamFee hullP polyPrice; dsimp only; payments_aes
      have h: Fuel (fun B=> hullP B nF):=by unfold hullP; payments_aes
      have hr: Fuel (fun B=>riseP nL kL B ε b₁):=by unfold riseP; payments_aes
      refine ⟨?_,hr,hb,h⟩; unfold trekV prepV; dsimp only; repeat' first | exact hc _ | exact hw | exact hb| exact Fuel.cons _| exact Fuel.self| apply Fuel.add| apply Fuel.mul
variable (B:ℕ)
lemma fortune (h: P.order=kF)(h₁:P.power=pF)(hr: P.B=B): cleanA P nF iF M₀ At ξ t v = (Tτ B)* ξ* v^2:=by
       unfold prepV cleanA hkappa loomR; rw[h,h₁,hr,loomρ,zest_v]; ring
variable (hz0:0 ≤ ξ)(hm:0 ≤ M₀)(ht:0 ≤ vT)(hv: 1 ≤ v)(he:0 ≤ At)(hT:P.threshold≤1)
lemma joys (M B:ℕ) (v:ℝ)(h:0≤v):0 ≤ mCash M pF kF B τ b₂ v:=by unfold mCash mRent beamFee polyPrice hullP; dsimp only; positivity
lemma pre_pos (hh:0 ≤ M₀)(h':0 ≤ At): 0≤Tτ B:=by
       unfold prepV; have he:= joys kF pF B nF M₀ hh; have ht:0 ≤ cashZ 1 b₂:=by unfold cashZ veinFare; positivity
       refine add_nonneg ?_ (mul_nonneg (Nat.cast_nonneg _) ht); exact mul_nonneg (mul_nonneg he (earnA ..)) h'
lemma supple (hh:0 ≤ M₀)(hf:0 ≤ vT)(he:0 ≤ At): 0 ≤ Tu vT B:=by
       unfold trekV; dsimp only; have hQ:0≤ (Φp B):=joys kF pF _ _ _ (by positivity)
       have ht:= pre_pos nF kF pF iF At M₀ B hh he; have hu:=mul_nonneg hQ (show 0 ≤ Rz B from earnA ..); positivity
local notation "Tz"=> t -- C?
local notation "CQ"=> cleanA P nF iF M₀ At ξ 1 v
local notation "U★"=> (Tτ B)
local notation "V★"=> (Tu vT B)
variable (h:P.order=kF)(h₁:P.power=pF)(h₂:P.B=B)
variable (hA: C ≤P.threshold*v^2) (hG:G1 ≤P.threshold*v^2)
variable (hK:0 ≤ C)(hΨ:0 ≤ G1)
include h h₁ h₂ hz0 hm ht hv he hT hA hG
lemma trajectory : ubi P nF M₀ ξ C G1 CQ ≤ V★ * ξ * v^2 :=by
       unfold ubi hkappa loomR; rw[fortune nF kF pF iF At M₀ B h h₁ h₂,h,h₁,h₂,loomρ,mul_zero,zero_add]
       have hx: P.threshold*v^2 ≤ v^2:=by simpa using mul_le_mul_of_nonneg_right hT (sq_nonneg v)
       have hvT: Φp B=(FP B) + 6*(FP B+ FP B):=by unfold mCash mRent beamFee polyPrice hullP; dsimp only; ring
       have hr:0 ≤(FP B):=joys kF pF B nF M₀ hm; have hR:0 ≤ (Φp B):= joys kF pF B nF _ (by positivity)
       let Y:= v^2; let T:= FP B; let u:= Rz B; have hp:0 ≤U★:= pre_pos nF kF pF iF At M₀ B hm he; have hU:0 ≤ u:=earnA ..; have hY:0≤Y:=sq_nonneg _; have hα:0 ≤ ξ*T:=mul_nonneg hz0 hr
       have hZ: T*u + U★ + T ≤ V★:=by unfold trekV; dsimp only; rw [hvT]; change T*u+U★+T ≤ (T+6*(T+T))*u+_+_+_+_; have hf:=mul_nonneg (Nat.cast_nonneg (α:=ℝ) iF) ht; nlinarith only [hR,ht,hT,hU,hp,hr,hvT,hf,show T=FP B from rfl, mul_nonneg hr hU]
       refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hA.trans hx) hU) hα) (le_refl (U★*ξ*v^2))) (mul_le_mul_of_nonneg_left (hG.trans hx) hα)).trans ?_
       calc ξ*(FP B)*(Rz B*v^2)+ U★*ξ*v^2 + ξ*(FP B)*v^2=(T*u+U★+T)*ξ*Y:=by unfold u T Y; ring
            _ ≤_:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZ hz0) hY
local notation "qt"=> P.threshold
local notation "Cp"=> pl P nF iF M₀ At vT ξ t v
local notation "Cw"=> pu P nF iF M₀ At vT ξ t v
-- uniform upper startup across interference. book.Linear cap
lemma trail_v (hy:0 ≤ t)(hp:t ≤ P.threshold): (ubi P nF cM ξ C G1 Cp ≤ V★*ξ*(P.threshold*v^2)) ∧ (ubi P nF cM ξ C G1 Cw ≤ V★*ξ*v^2):=by
         unfold ubi loomR hkappa pl pu; rw[fortune nF kF pF iF At M₀ B h h₁ h₂,h,h₁,h₂,loomρ,mul_zero,zero_add]; let X:= Φp B; let u:= Rz B; let S:= iF*vT; let Y:= v^2; let Q:= U★; have hx:0 ≤ X :=joys kF pF B nF _ (by positivity); have hQ:0 ≤ Q:= pre_pos nF kF pF iF At M₀ B hm he; have hU:0 ≤ u:=earnA ..; have hα:0 ≤ ξ*X:=mul_nonneg hz0 hx
         have hα'(a:ℝ)(h:t≤a)(hs: C ≤ a*Y) (hG: G1≤ a*Y): ξ*X*(u*C)+(S*ξ*(a*Y)+6*(Q*(t*ξ)*Y)) +ξ*X*G1 ≤ V★*ξ*(a*Y):=by
             refine (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hU) hα) (add_le_add (le_refl (S*ξ*(a*Y))) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hz0) hQ) (sq_nonneg _)) (by norm_num:(0:ℝ) ≤6)))) (mul_le_mul_of_nonneg_left hG hα)).trans_eq ?_; unfold trekV X u S Q; ring
         have hh:qt*Y ≤1*Y:=mul_le_mul_of_nonneg_right hT (sq_nonneg _); constructor
         · rw[show (iF:ℝ)*(ξ*(vT*v^2*qt)) = S*ξ*(qt*Y) from by unfold S Y; ring]; exact hα' qt hp hA hG
         rw[show (iF:ℝ)*(ξ*(vT*v^2)) = S*ξ*(1*Y) from by unfold S Y; ring]; exact (hα' 1 (hp.trans hT) (hA.trans hh) (hG.trans hh)).trans_eq (by unfold Y; ring)
end YM.MassiveQCD.Sample.Basal.Surge
#print axioms YM.MassiveQCD.Sample.Basal.Surge.cost_traits
#print axioms YM.MassiveQCD.Sample.Basal.Surge.trajectory
#print axioms YM.MassiveQCD.Sample.Basal.Surge.trail_v
