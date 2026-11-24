import YM.QCD.Oasis.Year
import YM.QCD.Oasis.Floss
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Tidings Token Shield Beam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {x y v b w u a U D p C s t r:ℝ}{j k c:ℕ}{i:E}{φ:E → F}
open Cove Golden NormedSpace
-- orbit navigation. Λ aux persistent.
variable {ι:Type}[Fintype ι][DecidableEq ι][FiniteDimensional ℝ E]
local notation "P'"=>ℝ×E
local notation "R"=>Poll.Body ι
variable {ρ:E→Poll.Body ι}{z : Poll.Body ι}
variable {δ: Side}{N:ℕ}{τ:E×Poll.Body ι→ EvenA δ N}
structure TellerX (F:E×Poll.Body ι→EvenA δ N)(C U v w:ℝ)(k:ℕ):Prop where
  lien : ∃ L:(E×Poll.Body ι)→L[ℝ] EvenA δ N, ‖L‖≤v ∧ ∀ x,‖x‖ <1 → Brush k (w*(C*U)^2) 1 (fun i=> F ((C*U) • i)-F 0-L ((C*U) • i)) x
-- navigation divided station
variable {Z:E× Poll.Body ι→L[ℝ] EvenA δ N}
def hpoint (ρ:E→Poll.Body ι) (U:ℝ)(z:R) := fun i:ℝ×E=> ((U • i.2),ρ (U • i.2)+(U*i.1) • z)
def spanV (D p:ℝ) := 2+p+D
local notation "M"=> spanV D p
open Lantern
lemma springsP (h:∀ x, ‖x‖<U → Brush k p 1 ρ x)(hu:0<U)(hs: U≤1)(hp:ρ 0=0)(hN:‖z‖≤D)(hj:1≤k)(x:P')(hx:‖x‖ < 1):
   let g y:= ((spanV D p)*U)⁻¹ • hpoint ρ U z y
   Brush k 2 1 g x ∧ ‖g x‖ <1:=by
    intro g; obtain ⟨hx₁,hx₂⟩:=max_lt_iff.mp (show max ‖x.1‖ ‖x.2‖ < (1:ℝ) from hx)
    have hv := droppingR (x:=x.2) hj hu hs hp (fun y hy=>h _ (mem_ball_zero_iff.mp hy)) hx₂; have hD:0 ≤ D:=(norm_nonneg _).trans hN; have hp:0 ≤ p:=nonneg_of_mul_nonneg_left hv.nonneg hu
    have ht:= reading (ContinuousLinearMap.snd ℝ ℝ E) hv (ContinuousLinearMap.norm_snd_le ..); rw [one_mul] at ht
    have hh : Brush k (U*D) 1 (fun i:P'=> (U*i.1) • z) x:= moneyL (fun (_:Poll.Body ι) => z) z hN hu.le x hx.le
    have hM:0 < M:=by unfold spanV; positivity
    let v:= M*U; have hm:0<v:=mul_pos hM hu
    have h1':p*U+U*D<v:=by unfold v spanV; linarith only [hu]
    have h1:=inv_pos.mpr hm
    have hw:= (ht.gathering hh).smul v⁻¹; rw [Real.norm_of_nonneg h1.le] at hw
    let L:= U • ContinuousLinearMap.snd ℝ ℝ E
    have hy: ‖L‖ ≤ U:= ContinuousLinearMap.opNorm_le_bound _ hu.le (fun i=>by change ‖U • i.2‖≤_; rw [norm_smul,Real.norm_of_nonneg hu.le]; exact mul_le_mul_of_nonneg_left (le_max_right ..) hu.le)
    have hb := L.le_opNorm x; have hz:= (linearB L ((L.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hx.le).trans hy)) (show ‖L‖≤U*1 by rwa [mul_one]) zero_le_one (k:=k)).smul v⁻¹; rw [Real.norm_of_nonneg h1.le] at hz
    have hl:v⁻¹*(p*U+U*D)<1:=by rw [mul_comm,←div_eq_mul_inv]; exact (div_lt_one hm).2 h1'
    have he:v⁻¹*U<1:=by rw [mul_comm,←div_eq_mul_inv]; apply (div_lt_one hm).2; unfold v spanV; nlinarith
    constructor; · rw [show (2:ℝ)=1+1 by norm_num]; exact (hz.climb he.le le_rfl).pair (hw.climb hl.le le_rfl)
    exact max_lt (hz.bound.trans_lt he) (hw.bound.trans_lt hl)

def lyric (F:E×Poll.Body ι→EvenA δ N)(ρ:E→ Poll.Body ι)(z:R) (x:P'):= F (hpoint ρ 1 z x)-F (hpoint ρ 1 0 x)
def medium (j:ℕ)(m p D w :ℝ):= clump j 2 (w*(spanV D p)^2)+clump j 2 (w*(spanV D p)^2)
lemma hymnR (h:∀ x, ‖x‖<U → Brush k p 1 ρ x)(hu:0<U)(hs: U≤1)(hp:ρ 0=0)(hN:‖z‖≤D)(hj:1≤k)(x:P')(hx:‖x‖ < 1) (H:∀ i:E×R,‖i‖<1→ Brush k (w*((spanV D p)*U)^2) 1 (fun i=> τ (((spanV D p)*U) • i)-τ 0-Z (((spanV D p)*U) • i)) i):
    Brush k (U^2*medium k U p D w) 1 (fun i:P'=> lyric τ ρ z (U • i) - (U*i.1) • Z (0,z)) x:=by
    have hD:0 ≤ D:=(norm_nonneg _).trans hN; let v:= M*U
    have hp':0 ≤ p:=(h 0 (by simpa using hu)).nonneg; have hm:0<v:=mul_pos (by unfold spanV; positivity) hu
    have hh z (hz:‖(z:Poll.Body ι)‖≤D) : Brush k (clump k 2 (w*v^2)) 1 (fun i=> τ (hpoint ρ U z i)-τ 0-Z (hpoint ρ U z i)) x:=by
       let A i:=v⁻¹ • hpoint ρ U z i; obtain ⟨hB,hH⟩:=springsP h hu hs hp hz hj x hx
       refine (composite hB (H (A x) hH)).shimmy (Eventually.of_forall fun i=>?_); dsimp only [Function.comp_apply]; simp only [show M*U=v from rfl,smul_inv_smul₀ hm.ne'] -- syntax
    apply ((hh z hN).separating (hh 0 (norm_zero.trans_le hD))).climb ?_ le_rfl |>.shimmy; swap -- order
    · unfold v medium clump; apply le_of_eq; ring
    exact Eventually.of_forall fun i=> by
       have hg : hpoint ρ 1 z (U • i)= hpoint ρ U z i:=by simp [hpoint]
       have hx : hpoint ρ 1 (0:Poll.Body ι) (U • i)= hpoint ρ U 0 i:=by simp [hpoint]
       have he:hpoint ρ U z i - hpoint ρ U 0 i=(U*i.1) • ((0,z):E×R):= Prod.ext (by simp [hpoint]) (by simp [hpoint])
       dsimp only [lyric]; rw [hg,hx,show Z (hpoint ρ U z i) = (U*i.1) • Z (0,z)+Z (hpoint ρ U 0 i) from (sub_eq_iff_eq_add).mp (by rw [←map_sub,he,map_smul])]; abel
end YM.QCD.Oasis
