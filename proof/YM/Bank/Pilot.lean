import YM.Bank.Live
import YM.QCD.Pearl.Tilts
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
/-! Shifted tiles. No losses in root uniform costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Pilot
open Function Lattice Laurent Bloch Metric Precision Filter MeasureTheory
open Next.Free Finset
open QCD.Pearl (beamH beamP beam0 ix)
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
variable {σ:Bool}{c f:Side}
def grid (σ:Bool)(p:Site c) : Momentum:= if σ then QCD.Flume.tuning p else mon p
lemma cubic (σ:Bool)(p:Site c) : grid σ p ∈ baseCube:=by unfold grid; split; exact QCD.Flume.keyboard _; exact mon_mem ..
abbrev earth (p:Momentum): E4:= ix.symm fun i=> (p i).re -- ℝ^4
lemma inland {p: Momentum}(h:physical p)(i): (earth p i:ℂ)= p i := QCD.Flume.cast_real h _
lemma inch {p:Momentum}(h: physical p): ‖p‖≤ ‖earth p‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>by rw [← inland h, Complex.norm_real]; exact PiLp.norm_apply_le (earth p) _)
lemma pace {p:Momentum}(h:physical p): ‖earth p‖ ≤ 2*‖p‖:= by
    rw [←sq_le_sq₀ (by positivity) (by positivity),EuclideanSpace.norm_sq_eq]
    apply (sum_le_sum (g:=fun (i:Axis)=> ‖p‖^2) ?_).trans_eq
    · simp [Axis]; ring
    intro i _; exact pow_le_pow_left₀ (norm_nonneg _) ((le_of_eq (by rw [← Complex.norm_real,inland h i] : ‖earth p i‖=‖p i‖)).trans (norm_le_pi_norm p i)) _

def κ (σ:Bool) : ℝ:= if σ then -(1/2) else 0
lemma brick (p:Site c)(i) (σ:Bool): earth (grid σ p) i=((lift p i:ℝ)+ κ σ)*beamH c:=by
    change Complex.re (grid σ p i)=_; cases σ <;> simp only [grid,Bool.false_eq_true,↓reduceIte,κ]
    · unfold mon beamH; simp only [Pi.smul_apply,smul_eq_mul,Laurent.reciprocal]; simp; ring
    rw [←sub_eq_add_neg,←QCD.Pearl.who]; rfl

def tile (σ:Bool)(p:Site c): Set (Axis→ℝ) := Set.univ.pi (fun i=> Set.Ioc (earth (grid σ p) i- beamH c/2) (earth (grid σ p) i+beamH c/2))
def place (σ:Bool)(p:Site c): Set E4 := ix ⁻¹' tile σ p
lemma tileM (σ:Bool)(p:Site c) : MeasurableSet (tile σ p):= MeasurableSet.univ_pi fun i=> measurableSet_Ioc
lemma placeM (σ:Bool)(p:Site c): MeasurableSet (place σ p) := (tileM ..).preimage ix.measurable
lemma atPlace {p:Site c}{x:E4}: x∈place σ p ↔ ∀ i, x i ∈ Set.Ioc (earth (grid σ p) i- beamH c/2) (earth (grid σ p) i + beamH c/2):=Set.mem_univ_pi
lemma parcel (σ:Bool)(p:Site c):volume (place σ p)= ENNReal.ofReal (beamH c^4):=by
    let T:=EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis; have he: volume (place σ p)=volume (tile σ p):=by
      calc _ = (Measure.map ix volume) (tile σ p):= (Measure.map_apply ix.measurable (tileM ..)).symm
           _ = _:=by rw [show Measure.map ix volume=_ from T.map_eq]
    rw [he]; change Measure.pi (fun _ : Axis=>volume) _=_; unfold tile; rw [Measure.pi_pi]
    simp_rw [Real.volume_Ioc,show ∀ i:Axis, earth (grid σ p) i+beamH c/2 - (earth (grid σ p) i-beamH c/2)=beamH c from fun _=> by ring, prod_const,card_univ]; rw [ENNReal.ofReal_pow (beamP c).le]; rfl
lemma parcelV (σ:Bool)(p:Site c):volume.real (place σ p)=beamH c^4:=by rw [Measure.real,parcel, ENNReal.toReal_ofReal]; positivity
lemma place_far {p:Site c}{x:E4}(h:x∈place σ p):dist x (earth (grid σ p)) ≤ beamH c:=by
    rw [dist_eq_norm,←sq_le_sq₀ (norm_nonneg _) (beamP c).le,EuclideanSpace.norm_sq_eq]; apply (sum_le_sum (g:= fun i:Axis=> (beamH c/2)^2) ?_).trans_eq
    · simp[Axis]; ring
    intro i _; apply pow_le_pow_left₀ (norm_nonneg _); change ‖x i - earth (grid σ p) i‖≤_
    rw [Real.norm_eq_abs,abs_le]; have hi:= atPlace.mp h i; change _<_∧_≤_ at hi; constructor <;> linarith [hi.1,hi.2]
def canopy (σ:Bool)(A:Finset (Site c)) := ⋃ p ∈ A, place σ p
lemma canopy_dis (σ:Bool)(A:Finset (Site c)) : Set.PairwiseDisjoint (A:Set (Site c)) (place σ):=by
   intro x _ y _ he; apply Set.disjoint_left.mpr; intro p hp hk
   apply he; apply lift_inj; funext i
   have hy:= atPlace.mp hp i; have hx:=atPlace.mp hk i; simp_rw [brick] at hy hx
   change _ <_ ∧ _≤_ at hx hy; have hB:=beamP c
   have he : (-1:ℤ)< lift x i - lift y i ∧ lift x i-lift y i < 1:=by
       suffices (-1:ℝ)< (lift x i:ℝ)-lift y i ∧ (lift x i:ℝ)-lift y i<1 by exact_mod_cast this
       constructor <;> apply lt_of_mul_lt_mul_right (a:=beamH c) _ hB.le <;> nlinarith [hy.1,hy.2,hx.1,hx.2]
   omega
lemma canopyM (σ:Bool)(A:Finset (Site c)) : MeasurableSet (canopy σ A):= Finset.measurableSet_biUnion _ fun _ _=> placeM ..
lemma skyMeasure (σ:Bool)(A:Finset (Site c)):volume.real (canopy σ A)=A.card*beamH c^4 := by rw [canopy,measureReal_biUnion_finset (canopy_dis ..) (fun _ _=>placeM ..) (fun _ _=>by rw [parcel]; exact ENNReal.ofReal_ne_top)]; simp_rw [parcelV,sum_const,nsmul_eq_mul]
lemma sky_size (σ:Bool)(A:Finset (Site c))(r:ℝ)(hr:0≤r)(h:∀ i∈A,‖grid σ i‖≤r): (beamH c)^4*A.card≤(2*r+beamH c)^4*(Real.pi^2/2):=by
   set B:= closedBall (0:E4) (2*r+beamH c); have hs:= beamP c
   have he : canopy σ A ⊆ B:=by
       unfold canopy; refine Set.iUnion₂_subset ?_; intro i hi x hx; rw [mem_closedBall,dist_zero_right]; have hb := place_far hx; rw [dist_eq_norm] at hb
       have hP: ‖earth (grid σ i)‖≤2*r:= (pace (cubic _ i).1).trans (by linarith [h i hi]); linarith [norm_sub_norm_le x (earth (grid σ i))]
   rw [mul_comm,← skyMeasure σ A]; apply (measureReal_mono (μ:=volume) he ((isCompact_closedBall ..).measure_ne_top)).trans_eq; unfold B; rw [Stationary.solidGaia (by positivity)] -- order
lemma pole_length (σ:Bool)(p:Site c)(hp:grid σ p≠0): beamH c/2 ≤ ‖grid σ p‖:=by
   cases σ; swap; · exact QCD.Pearl.minSize p
   obtain ⟨i,h⟩:= Function.ne_iff.mp hp; let q:=grid false p; have he:=brick p i false; change _ = _ at he
   have hx : lift p i ≠ 0 :=by
      intro hv; apply h; change grid false p i=0; rw [← inland (cubic false p).1 i]; rw [he,hv]; simp [κ]
   rw [κ,if_neg (by simp),add_zero] at he; -- maybe if
   have ht:=congr_arg (fun x:ℝ=>‖x‖) he; have hi :1≤|(lift p i:ℝ)|:=by rw [abs_nat]; exact_mod_cast (show 1≤ (lift p i).natAbs by omega)
   calc _ ≤ ‖q i‖:= by rw [show q i=((earth (grid false p) i:ℝ):ℂ) from (inland (cubic _ p).1 i).symm,Complex.norm_real,ht,norm_mul,Real.norm_eq_abs (lift p i:ℝ),Real.norm_of_nonneg (beamP c).le]; linarith [beamP c, le_mul_of_one_le_left (beamP c).le hi]
        _ ≤ _:=norm_le_pi_norm q _
end YM.Bank.Pilot
#print axioms YM.Bank.Pilot.sky_size
#print axioms YM.Bank.Pilot.pole_length
