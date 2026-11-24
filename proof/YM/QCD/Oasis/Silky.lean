import YM.QCD.Oasis.Law
import YM.QCD.King.Fable
import YM.QCD.Golden.Shine
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens
/-!
# Scaled sustainable derivatives. Linear defect around zero LARGE T but
 powers ~ Reserve, no norms per volume used (quot). Gives Brush in ALL directions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Input Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure
open ConnectedActivityE6 Blaze Brush Poll Coat
open PhysicalNext.Repeat Lapis Lantern Sienna Fare Tidings
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {σ C U D b E' W u M : ℝ} {n j k : ℕ}
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] {x:E}
variable {g h:E→F}
lemma streamR (h:0≤u)(hp:Brush k b W g (u • x)):Brush k b (W*u) (fun i=>g (u • i)) x:=by
  let S:=u • ContinuousLinearMap.id ℝ E
  exact Brush.reading S hp (ContinuousLinearMap.opNorm_le_bound _ h fun i=> by change ‖u • i‖≤_; rw [norm_smul,Real.norm_of_nonneg h])
lemma reverseR (h:0<u)(hp:Brush k b 1 (fun i=>g (u • i)) (u⁻¹ • x)): Brush k b u⁻¹ g x:=by
    have he:= streamR (g:=fun i=>g (u • i)) (inv_pos.mpr h).le hp; rw [one_mul] at he; apply he.shimmy; exact Eventually.of_forall fun i=> by dsimp only; rw [smul_inv_smul₀ h.ne']
-- downward from fixed order jets
lemma dropR (hh:1≤k)(he:0<U)(hw:h 0=0)(hg:∀ i∈ball (0:E) U,Brush k M 1 h i)(hx:x ∈ball (0:E) U): ‖h x‖ ≤ M*U:=by -- h shadow!
    have hp:= (convex_ball (0:E) U).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> ((hg i hi|>.smaller hh).smooth).differentiableAt (by norm_num)) (fun i hi => (norm_iteratedFDeriv_one (𝕜:=ℝ) _).symm.trans_le ((Brush.offer.mp (hg _ hi)).2 1 hh)) (mem_ball_self he) hx
    rw [hw, sub_zero, sub_zero] at hp; exact hp.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (hg x hx).nonneg)
lemma droppingR (hA:1≤k)(he:0<U)(hm:U≤1)(hw:h 0=0)(hg:∀ i∈ball (0:E) U,Brush k M 1 h i)(hx:‖x‖<1): Brush k (M*U) 1 (fun i=>h (U • i)) x := by
    have hv: U • x∈ball (0:E) U:= mem_ball_zero_iff.mpr (by rw [norm_smul,Real.norm_of_nonneg he.le]; exact mul_lt_of_lt_one_right he hx)
    have hp:= hg _ hv; have hb:= streamR he.le hp; rw [one_mul] at hb
    refine Brush.offer.2 ⟨hb.smooth,?_⟩; rintro (_|i) hi
    · unfold normJ; rw [norm_iteratedFDeriv_zero]; exact dropR hA he hw hg hv
    exact (hb.order _ hi).trans (mul_le_mul_of_nonneg_left (by rw [pow_succ]; exact mul_le_of_le_one_left he.le (pow_le_one₀ he.le hm)) hp.nonneg)
-- central  angle votes. x all directions
variable {ι:Type}[Fintype ι][DecidableEq ι]
variable [FiniteDimensional ℝ E]
local notation "R"=> Poll.Body ι
variable {φ ψ:E×Poll.Body ι→ℝ}{ρ:E→Poll.Body ι}{A:E→ Matrix ι ι ℝ}
variable (H:Golf φ ψ ρ A k D U U M)
include H
local notation "Y"=> grace φ ψ ρ A
variable {X:ℝ×E} {z:Poll.Body ι} {a:ℝ}
lemma stallR (hj:1≤k)(hv: fee k M D *U ≤1)(hs : ∀ i∈Icc (-1:ℝ) 1, Brush k a 1 Real.exp i)
    (hx:‖X‖<1)(he:‖z‖ ≤ D): Brush k ((clump k (fee k M D) a+1)*U) 1 (fun i:ℝ×E=> Real.exp (Y z (U • i))-1) X:=by
    let f (y:ℝ×E):= Real.exp (Y z y)-1
    have hp : f 0=0:=by change Real.exp (Y z (0,0))-1=0; rw [zeroC]; simp -- z named?
    apply droppingR hj H.pos H.small hp _ hx; intro i hi; obtain ⟨hx,hX⟩:= max_lt_iff.mp (mem_ball_zero_iff.mp hi); have ht:= Lantern.ether D H hX hx hj (by simpa using hv) _ he
    have hw:= composite (compel D H hX hx he) (hs _ ht); simpa only [norm_one] using! hw.separating (Brush.certified zero_le_one (1:ℝ))
end YM.QCD.Oasis
