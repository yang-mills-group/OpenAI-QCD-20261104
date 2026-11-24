import YM.Rebus.Ponds
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Metering
/-! # Use TRUE sigma physical.Y tokens
   TRUE covariance law forecasts compare at Therm axes.S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open Play.Camp
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Current
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Bera.Oce Matrix
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁:ℝ}{S: StepData c f}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {T:Tube su S}{N i j n k m l B Q: ℕ}
open FreeResolvent
local notation "X!"=> Kh f
section PlaneQ
-- observation
variable (F:Tree.Forest S.ratio)(X:Coat T F)
abbrev smold (F:Tree.Forest S.ratio): Active su F→ Tubular f su:=fun i=> (i.1.val,i.2)
abbrev planeK (F:Tree.Forest S.ratio): Matrix (Kh f) (Active su F) ℝ:= Current.plane S F
def dove : Matrix (Kh f) (Tubular f su) ℝ := planeK F*(insertion (smold F)).transpose
lemma reduced (i:Active su F)(z:Air f su):((insertion (smold F)).transpose *ᵥ z.ofLp) i=purseK X z i:=by simp only [purseK]; simp [Matrix.mulVec,dotProduct,Matrix.transpose_apply,insertion]
lemma foster (z:Air f su): dove F *ᵥ z.ofLp=Fruit.jet (growSeed X z):=by rw [dove,← Matrix.mulVec_mulVec, funext (fun i=> reduced F X i z)]; exact Fruit.pore ..
-- SUPPORT exact. via pore testing chosen all air.
include X
lemma relatedP (a:Kh f)(i:Active su F) (h:(Current.plane S F (G:=su)) a i≠0): i.1.val.1 ∈ RG.touched (bleep a):=by
    let w:Air f su:= WithLp.toLp 2 (Pi.single (smold F i) (1:ℝ))
    by_contra he
    apply h; have hf (x y: Active su F) : smold F x=smold F y↔ x=y:=⟨fun h=> Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (congr_arg (fun z:Tubular f su=> z.2) h),congr_arg _⟩ -- syntax
    have hh:purseK X w= Pi.single i 1:=by
        funext x; change (Pi.single (smold F i) (1:ℝ) : Tubular f su→ℝ) (smold F x)=_; by_cases hk:x=i; · subst x; simp
        rw [Pi.single_eq_of_ne (fun h=>hk ((hf ..).mp h)),Pi.single_eq_of_ne hk]
    have hp:= congr_fun (Fruit.pore X w) a
    have hx: Hypnos.tide (growSeed X w) (bleep a)=0:=by
        rw [Hypnos.tide_local _ (y:=0) (?_),Hypnos.tide_round]; simp
        intro j h; unfold growSeed; split; rfl; ext u; change (Pi.single (smold F i) (1:ℝ) : Tubular f su →ℝ) (j,u)=0; apply Pi.single_eq_of_ne (by
             intro he'; apply he; injection he' with e; exact e ▸ h) -- types
    rw [Fruit.peal,hx,hh,Matrix.mulVec_single_one] at hp -- name
    exact hp
local notation "Vk"=> (dove F)
def groveV (h:X.relating.PosSemidef): Next.Rank.Normal.Symmetric (Kh f):= Oce.knock ((dove F)*X.relating*(dove F).transpose) (Bera.Oce.quant X.relating h (dove F))
-- def quant implicit inspect
variable (hX:X.relating.PosSemidef)
include hX
local notation "Y0"=> groveV F X hX
lemma collects (m: Kh f→ℝ): Oce.Corolla X.dice (Oce.surge (dove F) m) m Y0:=by
    exact Oce.holler _ hX (dove F) m
omit hX
local notation "S0"=> X.relating.submatrix (smold F) (smold F)
local notation "Q!"=> planeK F
lemma concert : Vk*X.relating*(Vk).transpose=Q!*S0*(Q!).transpose:=by
     unfold dove; rw [←FreeResolvent.insertion.compress, Matrix.transpose_mul,Matrix.transpose_transpose]; simp only [Matrix.mul_assoc]
omit X
section
attribute [-instance] Sample.LoomT.instFintypeTo
lemma showers (i:Kh f): ∑ j,‖Current.plane S F (G:=su) i j‖ ≤ Current.curlTariff su S.patch 0:=by
     simpa only [FreeResolvent.Cost.weight_zero,one_mul,Real.norm_eq_abs] using ((Current.plane_price (G:=su) S F 0 le_rfl).rows.bound i)
section
end -- actually inserted `section` immediately before. Undo
attribute [instance] Sample.LoomT.instFintypeTo
-- precision sale
variable (W : Support c)(H:Bed){M:Finset (Kh f)}{ε:ℝ} (he:0≤ε)
local notation "Z"=> (FreeResolvent.treeMatrix su S F H.metric)⁻¹
local notation "PP"=> Current.curlTariff su S.patch 0
include X he
lemma echoP (hm:∀ i∈M,(RG.touched (bleep i)).image S.ratio.parent⊆W) (hp:∀ i j:Active su F,S.ratio.parent j.1.val.1 ∈ W → |S0 i j- Z i j| ≤ ε):∀ i∈ M,∀ j∈M, |(dove F * X.relating * (dove F).transpose-Q!*Z*(Q!).transpose) i j| ≤ PP*PP*ε:=by
    intro i hi j hj; rw [concert,←Matrix.sub_mul,←Matrix.mul_sub]
    have hs k (hk: Current.plane (G:=su) S F j k ≠0) : ‖(Q!*(S0-Z)) i k‖ ≤ PP*ε:=by
        rw [Matrix.mul_apply]; exact (norm_sum_le ..).trans ((sum_le_sum (g:=fun p=>‖Q! i p‖*ε) fun m _=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hp m k (hm j hj (mem_image_of_mem _ (relatedP F X j k hk)))) (norm_nonneg _)).trans (by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (showers ..) he))
    have hg:= Current.curlTariff_nn su S.patch 0
    rw [show PP*PP*ε=PP*(PP*ε) from by ring,Matrix.mul_apply,←Real.norm_eq_abs]; apply (norm_sum_le ..).trans
    refine (sum_le_sum (g:=fun k=> ‖Q! j k‖ * (PP*ε)) (?_)).trans (?_)
    · intro k _; rw [transpose_apply,norm_mul,mul_comm]; by_cases h:Q! j k=0; simp [h]; exact mul_le_mul_of_nonneg_left (hs k h) (norm_nonneg _)
    rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (showers ..) (mul_nonneg hg he)
end
end PlaneQ
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.echoP
#print axioms YM.MassiveQCD.Rebus.collects
