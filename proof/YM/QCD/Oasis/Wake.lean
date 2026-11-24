import YM.QCD.Oasis.Note
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 120000
noncomputable section
namespace YM.QCD.Oasis
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Input Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure
open ConnectedActivityE6 Blaze Brush Poll Coat
open PhysicalNext.Repeat Lapis Lantern Sienna Fare Tidings
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {n j k : ℕ}{σ C U D b W M w u v d a : ℝ}
open Cove Golden Shield
variable {ι:Type}[Fintype ι][DecidableEq ι]
local notation "R"=> Poll.Body ι
variable {φ ψ:E×Poll.Body ι→ℝ}{ρ:E→Poll.Body ι}{A:E→ Matrix ι ι ℝ}
variable {c:Side}{N:ℕ} (h:Golf φ ψ ρ A (k+2) D U U M)
local notation "X"=>EvenA c N
set_option quotPrecheck false
variable {K: Poll.Body ι→ EvenA c N} {T:Poll.Body ι→ℝ×E→EvenA c N}(hz:Cello T K u v D U (k+2))
variable (hM: Lantern.fee (k+2) M D *U≤1)(hs:∀ i∈ Set.Icc (-1:ℝ) 1, Brush (k+2) a 1 Real.exp i)
local notation "g"=> humV φ ψ ρ A T D
include hz hM hs h
lemma lineR (y:E)(hy:‖y‖<U)(he:0<b)(ht:b<U) : Brush k (b^2*mast u v M D a (k+2)) U⁻¹ (fun x=> g (b,x)) y :=by
    let f i:= g (U • i); let z : E:=U⁻¹ • y; let j:=U⁻¹*b
    have hA:= h.pos; have hj': j=b/U:=by unfold j; rw [div_eq_mul_inv,mul_comm]
    have hj:0<j:=mul_pos (inv_pos.mpr hA) he; have hk:j<1:= hj' ▸ (div_lt_one hA).2 ht
    have hp: ‖z‖ < 1:=by unfold z; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hA).le, mul_comm, ← div_eq_mul_inv]; exact (div_lt_one hA).2 hy
    have hw: U*j = b:=by rw [hj',mul_comm, div_mul_cancel₀ _ hA.ne']
    have ht := shoots f k z j hj (funext fun i=>by change g (U • (-i.1,i.2))= g _; rw [← balanced h hz (U • i), show U • (-i.1,i.2)=( -(U • i).1, (U • i).2) from Prod.ext (smul_neg ..) rfl]) (fun p hp'=> wakenV h hz (by omega) hM hs _ (show max _ _ < 1 from max_lt (hp'.trans_lt hk) hp))
    apply reverseR hA; apply (ht.climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
    · apply le_of_eq; rw [← hw] -- fix
      ring
    change g _= g (U • (j,i))-g (U • (0,i)); rw [show U • (j,i)=(b,U • i) from Prod.ext hw rfl, show U • ((0:ℝ),i)=(0,U • i) from Prod.ext (smul_zero U) rfl]
    simp [humV,hz.drone]
end YM.QCD.Oasis
