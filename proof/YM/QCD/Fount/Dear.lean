import YM.QCD.Fount.Price
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR
variable {L:Side} {t a u r w b B τ σ η s c H p ξ α:ℝ} {J k N:ℕ}{g f v z h:ℝ→ℝ}
variable {M:ParcelR}
lemma houseY (P:Plan J) (hx:Rates M t):∃ δ W:ℝ,0<δ ∧ 0 ≤ W ∧ ∃ j:ℕ,∀ (n:Side) (S:SunR M)(x y:ℝ),0<x → x≤ y → y≤1→∀ U:Train J,Own n (δ*x^2) 0 j (FieldB M S n y P U) W :=by
   obtain ⟨c,A,v,hp,hQ,H⟩:= vaultP hx.hr hx.hs (show 0 ≤ (0:ℝ) from le_rfl) M.d M.c
   obtain ⟨b,z,V,hZ,he,hF⟩:= banner P 0 le_rfl
   refine ⟨min c z,V+A,lt_min hp hZ,by positivity,max v b,fun n S x y hz hx hr U=>?_⟩
   have ht:= H S.X S.Y n _ (le_max_left v b) y 0 (hz.trans_le hx) hr
   let W:=Pine.wood P 0 U (n:=n)
   have hh : FieldB M S n y P U= W+trunkM S.X S.Y y 0 n:=by simp [FieldB,W,trunkM]; rfl -- name
   rw [hh]; have hy:  min c z*x^2 ≤ c*y^2:=by gcongr; exact min_le_left ..
   have hu: min c z*x^2 ≤ z:= (mul_le_of_le_one_right (lt_min hp hZ).le (pow_le_one₀ hz.le (hx.trans hr))).trans (min_le_right ..)
   refine ((pieties (hF n U) (le_max_right ..) le_rfl).clip hu).plus ((ht.clip hy).mono ?_)
   rw [abs_zero,add_zero]; exact mul_le_of_le_one_right hQ.le hr
-- X.s needed μ ≤ small on scaled ball. From golf.
variable {c' i:Side}{S:StepData c' i} {q:ℕ} {F: Forest S.ratio} {ρ:Bid.Dir su c'→AxisChart su F}
local notation "X'"=> Positions (Primary c' su)
lemma lampA (h:1≤q)(ht:∀ x:X', ‖x‖<u → Brush q w 1 (Lapis.orbit F ρ) x)(hp:ρ 0=0)(hx:u ≤ 1) (he:w*u≤1) {x:X'}(hy: ‖x‖<u)(J:ℕ)(hj:J ≤ q):
    let X:= fun y:X'=> (y,Lapis.orbit F ρ y); Brush J (1+w+(1+w)) 1 X x ∧ ‖X x‖ ≤ 1:=by
   intro W; let f:= Lapis.orbit F ρ; have hF : f 0=0:= by unfold f Lapis.orbit Uniform.station; simp [hp]
   have hv:= ht x hy; have hFx:= hv.smaller hj
   have hB: Brush J (1+ w) 1 (fun x:X'=> x) x:= by
      let i:=ContinuousLinearMap.id ℝ X'; apply ((Brush.linearB i (u:=1) ?_ ?_ zero_le_one).climb (le_add_of_nonneg_right hv.nonneg) le_rfl)
      · exact (hy.le.trans hx)
      simp only [i,mul_one]; exact ContinuousLinearMap.norm_id_le
   refine ⟨hB.pair (hFx.climb (le_add_of_nonneg_left zero_le_one) le_rfl), max_le (hy.le.trans hx) ?_⟩
   have hz:= norm_nonneg _|>.trans_lt hy; let s:=ball (0:X') u; have hy':x∈s:= mem_ball_zero_iff.mpr hy
   have hk:= (convex_ball (0:X') u).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (C:=w) (f:=f) (fun z hz=>((ht _ (mem_ball_zero_iff.mp hz)).smaller h).smooth.differentiableAt (by norm_num)) (fun z hz=>by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (ht _ (mem_ball_zero_iff.mp hz))).2 _ h) (mem_ball_self hz) hy'
   rw [hF,sub_zero,sub_zero] at hk; exact hk.trans ((mul_le_mul_of_nonneg_left hy.le hv.nonneg).trans he)
abbrev dues (L:Side)(x:ℝ):=lull L x+3*lull L x
end YM.QCD.Fount
