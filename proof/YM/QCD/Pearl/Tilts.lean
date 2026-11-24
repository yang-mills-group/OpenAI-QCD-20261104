import YM.QCD.Pearl.Shine
import YM.Next.STATIONARY.OneLoop.MomentumIntegral

/-! # Integration tiles on the (finite, half-shifted) frequency cube -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lat Cost Lattice Wilson Function Filter Finset Kit Flume Laurent Bloch Metric YM.Next.Free RG Rudder Free Para Pinch MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology ContDiff ENNReal
abbrev Gₐ:= Stationary.Gaia
abbrev ix:= Stationary.exileE
variable {n:Side}

def beamH (n:Side):ℝ:=2*Real.pi/n.val
lemma beamP (n:Side):0<beamH n:=div_pos (by positivity) (side_pos n)
lemma beam0:Tendsto beamH atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp exhausting)

def centerZ (p:Site n):Gₐ:= ix.symm (menu p)
lemma radius (p:Gₐ) : ‖p‖ = fry (ix p):= by
  have he := Stationary.geode_sum p; apply (sq_eq_sq₀ (norm_nonneg p) (fry_nn _)).mp; rw [fry_sq]; exact he.symm
lemma whirl (p:Site n): ‖centerZ p‖=fry (menu p):=by rw [radius,centerZ, ix.apply_symm_apply]
lemma who (p:Site n)(i:Axis) : menu p i= (↑(lift p i)-1/2)*beamH n:=by simp only [menu,spacer,beamH,fixed,Pi.smul_apply,smul_eq_mul]; ring
lemma minSize (p:Site n): beamH n/2≤ ‖tuning p‖:= by
  have hk : spacer n*Real.pi ≤ |menu p 0|:=by
    change spacer n*Real.pi ≤ |spacer n * fixed (lift p) 0|; rw [abs_mul,abs_of_pos (fine _)]; exact mul_le_mul_of_nonneg_left (fixed_lower ..) (fine _).le
  exact le_trans (le_of_eq (by unfold spacer beamH; ring : beamH n/2= spacer n*Real.pi)) (hk.trans ((show ‖tuning p 0‖=|menu p 0| from by rw [tuning,Complex.norm_real,Real.norm_eq_abs]).symm.trans_le (norm_le_pi_norm _ _)))

def plate (p:Site n)(i:Axis): Set ℝ:= Set.Ioc ((lift p i-1:ℤ)*beamH n) (lift p i*beamH n)
def table (p:Site n) : Set ReP:= Set.univ.pi (plate p)
def seat (p:Site n): Set Gₐ := ix ⁻¹' table p
lemma tableM (p:Site n): MeasurableSet (table p):=MeasurableSet.univ_pi fun i=> measurableSet_Ioc
lemma chair (p:Site n): MeasurableSet (seat p):= (tableM _).preimage ix.measurable
lemma seating (p:Site n): volume (seat p)= ENNReal.ofReal ((beamH n)^4):= by
  let T:=EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis
  have he : volume (seat p) = volume (table p):=by
    calc _ = (Measure.map ix volume) (table p):= (Measure.map_apply ix.measurable (tableM p)).symm
         _ = _:= by rw [show Measure.map ix volume=_ from T.map_eq]
  rw [he]; change Measure.pi (fun _ : Axis=>volume) _=_; unfold table; rw [Measure.pi_pi]; unfold plate
  simp_rw [Real.volume_Ioc, Int.cast_sub, Int.cast_one,show ∀ (i:Axis), (lift p i:ℝ)*beamH n-((lift p i:ℝ)-1)*beamH n= beamH n from fun i=> by ring,prod_const,card_univ]; rw [ENNReal.ofReal_pow (beamP n).le]; rfl
lemma seatVolume (p:Site n): volume.real (seat p)=(beamH n)^4:=by rw [Measure.real,seating, ENNReal.toReal_ofReal]; positivity
lemma seated {p:Site n}{x:Gₐ}: x∈seat p ↔ ∀ i,x i∈plate p i := by
  change ix x∈Set.univ.pi (plate p) ↔ _; rw [Set.mem_univ_pi]; rfl
lemma seat_far {p:Site n}{x:Gₐ}(h:x∈ seat p): dist x (centerZ p)≤beamH n:=by
  rw [dist_eq_norm]; apply le_of_sq_le_sq _ (beamP _).le; rw [← Stationary.geode_sum];
  have he(i): |x i-centerZ p i|≤ beamH n/2:=by
    apply abs_le.mpr; change _≤ x i-menu p i∧ x i-menu p i≤_; rw [who]; have H:=seated.mp h i; change _<_∧_ ≤ _ at H; obtain ⟨hr,ht⟩:=H
    push_cast at *; constructor <;> linarith
  apply (sum_le_sum (s:=univ) (g:=fun i:Axis=> (beamH n/2)^2) ?_).trans (le_of_eq (by simp [Axis]; ring)); intro i _; change (x i-centerZ p i)^2≤ _; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (he i) _
lemma order_eq {a b:Site n}{p:Gₐ}(ha:p∈seat a)(hb:p∈seat b):a=b:= by
  apply lift_inj; funext i
  let t:=beamH n; have ht:0<t:=beamP n
  have he (x:Site n) (hp:p∈seat x): lift x i = Int.ceil (p i/t):=by
    have hL := seated.mp hp i; change ↑(lift x i-1:ℤ)*t < p i ∧ p i ≤ (lift x i:ℝ)*t at hL
    exact Eq.symm (Int.ceil_eq_iff.mpr ⟨(lt_div_iff₀ ht).mpr (by simpa using hL.1),(div_le_iff₀ ht).mpr hL.2⟩)
  rw [he a ha,he b hb]
lemma seatingBall (u:Gₐ) (h:‖u‖ ≤1) (hc: beamH n≤1):∃ p:Site n,u∈seat p:=by
  let t:=beamH n; have ht:0<t:=beamP n; have hp : n.val*t=2*Real.pi:=by unfold t beamH; field_simp
  let x:Cover:=fun i=>Int.ceil (u i/t)
  have he i: ↑(x i-1:ℤ)*t < u i ∧ u i ≤ (x i:ℝ)*t :=by
    have hu := (Int.ceil_eq_iff).mp (show ⌈u i/t⌉= x i from rfl); refine ⟨?_,(div_le_iff₀ ht).mp hu.2⟩; push_cast; exact (lt_div_iff₀ ht).mp hu.1
  have hx : lift (wrap n x)=x:=by
    apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; obtain ⟨h₁,h₂⟩:=he i
    have hX:= fry_sub (ix u) i; rw [← radius u] at hX
    have hu:=abs_le.mp (le_trans (show |u i| ≤ _ from hX) h); change t ≤ 1 at hc; push_cast at h₁
    constructor
    · have hi: - (n.val:ℝ)< 2*↑(x i):= lt_of_mul_lt_mul_right (a:=t) (by nlinarith [Real.pi_gt_three, hu.1]) ht.le
      exact_mod_cast hi
    have hi: 2* (x i:ℝ)≤n.val:= le_of_mul_le_mul_right (a:=t) (by nlinarith [Real.pi_gt_three, hu.2]) ht; exact_mod_cast hi
  exact ⟨_,seated.mpr (fun i=> by unfold plate; rw [hx]; exact he i)⟩
end YM.QCD.Pearl
