import YM.Needle.Patch
import YM.Needle.Pond
/-!
  # Box rank detector in stable units
  Interval of physical lengths against true regulator averages of whole calibrated point primaries.
  Includes fine unaligned lifts; permits convex kernels even when span weights before persistence
  exceed reference normalization budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}(Z:Laurel d) (J:Landing P.sym Z)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Vᴮ" i:arg => (C.A i).regulator
local notation "Ω"=>Intag.Vale.Stokes d
local notation "a" i:arg=> C.S.spacing (C.N i)
open YM.Bloom YM.Bloom.Jar YM.Bank YM.Bank.Jule
variable {β ν:ℝ}(hC:C.Path β ν)
noncomputable def duet (C:Sequence) (i:ℕ) (x:stalk C i) (u v: Cover): stalk C i →ₗ[ℂ]ℂ where
   toFun y:= ((C.A i).regulator).average (x u*y v)
   map_add' f g:=by simp [mul_add]
   map_smul' s f:=by simp_rw [Pi.smul_apply,mul_smul_comm,map_smul,RingHom.id_apply]
structure GaugeP (P:Calibration C)(Z:Laurel d) (J:Landing P.sym Z) where
    r:ℝ
    pos : 0<r
    price:ℝ
    realH : 0≤ price
    (g h:ℕ→ Stokes d→Label d)
    tall : ∀ᶠ i:ℕ in atTop, ∀ j:Stokes d, ‖g i j‖ ≤ price ∧ ‖h i j‖≤ price
    shore : ∀ᶠ i:ℕ in atTop, ∀ (x:Cover), digit (C.S.spacing (C.N i)) x∈ Metric.closedBall (r • J.a) (r*J.l) → nearG P.sym Z J.ε (fun t v:Stokes d=> duet C i (stem P d i (g i t)) 0 x (stem P d i (h i v)))
variable {P Z J}
namespace GaugeP
variable (K: GaugeP P Z J)
noncomputable abbrev coast: E4:= K.r • J.a
noncomputable abbrev extent :ℝ:= K.r*J.l
noncomputable abbrev beach := Metric.closedBall K.coast K.extent
noncomputable abbrev heads (i:ℕ):= stem P d i ∘ K.g i
noncomputable abbrev fault(i:ℕ)(x:Cover):Prop:= digit (a i) x∈ K.beach
noncomputable def ridge (i:ℕ):(Stokes d→ℂ)→ₗ[ℂ]Label d where
   toFun p:=∑ j,p j • K.h i j
   map_add' t v:=by simp only [Pi.add_apply,add_smul,sum_add_distrib]
   map_smul' t v:=by simp only [Pi.smul_apply,RingHom.id_apply,smul_sum, smul_eq_mul,smul_smul]
lemma breadth : 0< K.extent:=mul_pos K.pos J.breadth
lemma reach : 0∉ K.beach:=by
    intro h; have hw:= K.pos; have hx:0∈Metric.closedBall J.a J.l:=by
         have hh:=Metric.mem_closedBall.mp h; rw [dist_zero_left,norm_smul, Real.norm_of_nonneg hw.le] at hh; rw [Metric.mem_closedBall,dist_zero_left]; exact le_of_mul_le_mul_left hh hw
    have hp:2*J.e≤0:=(J.pose _ hx).2.1 timeAxis; exact (by linarith [J.far]: False)
lemma gained (J:Landing P.sym Z)(r V:ℝ)(hp:0<r)(ht:0≤V)(hV:∀ᶠ i:ℕ in atTop,∃ g h: Stokes d → UV.Label d, (∀ j:Stokes d, ‖g j‖≤ V ∧ ‖h j‖≤V)∧ ∀ x:Cover,Ibis.screen C.S (C.N i) r x ∈Metric.closedBall J.a J.l→ nearG P.sym Z J.ε (fun t v:Stokes d=> ((C.A i).regulator).average (P.physical none i (g t) 0 * P.physical none i (h v) x))): ∃ K:GaugeP P Z J,K.r=r∧K.price=V:=by
     obtain ⟨N,h⟩:=eventually_atTop.mp hV; choose! g H hg hx using h; refine ⟨⟨r,hp,V,ht,g,H,eventually_atTop.mpr ⟨N,hg⟩,eventually_atTop.mpr ⟨N,?_⟩⟩,rfl,rfl⟩
     intro i hi x he; apply hx i hi x; rw [Metric.mem_closedBall]; have hv: digit (a i) x= r • Ibis.screen S (C.N i) r x:=by unfold digit Ibis.screen Ibis.rescaling; rw [smul_smul]; field_simp
     rw [Metric.mem_closedBall,hv,dist_eq_norm,←smul_sub, norm_smul, Real.norm_of_nonneg hp.le] at he; rw [dist_eq_norm]; exact le_of_mul_le_mul_left he hp
include hC
lemma lively : ∀ᶠ i:ℕ in atTop, ∃ x, K.fault i x:= ((approaches hC K.coast).eventually (Metric.closedBall_mem_nhds _ K.breadth)).mono fun i h=>⟨_,h⟩
lemma sepF : ∃ e:ℝ,0 < e ∧∀ᶠ i:ℕ in atTop,∀ x:Cover,K.fault i x → localSep C i (![0,x]) e:=by
    have hr := K.reach; rw [GaugeP.beach,Metric.mem_closedBall,not_le,dist_zero_left] at hr
    let e:= ‖K.coast‖-K.extent; have hp: 0 < e := sub_pos.mpr hr
    refine ⟨e/2,half_pos hp,?_⟩; filter_upwards [fullPrice hC e (‖K.coast‖+K.extent)] with i hi x hx
    have h:= Metric.mem_closedBall.mp hx; rw[dist_eq_norm] at h
    let y:= digit (a i) x
    have hh : e ≤ dist (digit (a i) 0) y:=by rw [digit_zero,dist_zero_left]; have H:= norm_sub_le y (y-K.coast); rw[sub_sub_self] at H; linarith only [H, h,show ‖y-K.coast‖ ≤ _ from h,show ‖K.coast‖-K.extent=e from rfl]
    have he :dist (digit (a i) 0) y ≤‖K.coast‖ + K.extent:=by rw [digit_zero,dist_zero_left]; have H:= norm_add_le K.coast (y-K.coast); rw [add_sub_cancel] at H; exact H.trans (add_le_add le_rfl h)
    have hl := hi 0 x hh he; intro t j ht; fin_cases t <;> fin_cases j <;> first |contradiction| exact hl|rwa [separation_comm] at hl
omit hC
noncomputable abbrev heightM:ℝ:= Fintype.card (Stokes d) * K.price
lemma h_positive: 0 ≤ K.heightM:=mul_nonneg (by positivity) K.realH
lemma pluck : ∀ᶠ i:ℕ in atTop,∀ p: Stokes d→ ℂ, ‖K.ridge i p‖ ≤ K.heightM*‖p‖:=by
    filter_upwards [K.tall] with i hi p
    change ‖∑ j,p j • K.h i j‖ ≤ _; apply (norm_sum_le ..).trans; have h(j:Stokes d): ‖p j • K.h i j‖ ≤ K.price * ‖p‖:=by rw[norm_smul, mul_comm]; exact mul_le_mul ((hi j).2) (norm_le_pi_norm p j) (norm_nonneg _) K.realH
    apply (sum_le_sum fun i _=> h i).trans; simp only [sum_const,card_univ,nsmul_eq_mul, heightM,mul_assoc,le_refl]
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.gained
#print axioms YM.Massive.Needle.GaugeP.sepF
