import YM.Fir.Soot
import YM.Analysis.Multilinear
import YM.Extraction.Simultaneous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
/-! Basis-uniform limit calculus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Fir
open Set Function Filter Metric Module
open scoped Topology BigOperators Classical ContDiff
variable {I Α:Type*}
namespace Lantern
-- reusable air.Subseq.P
lemma armor [Countable I]{W:I→ Type*}[∀ i,NormedAddCommGroup (W i)][∀ i, ProperSpace (W i)] (f:∀ i,ℕ→ W i)(hf:∀ i,∃ B:ℝ,0≤B∧∀ᶠ k in atTop, ‖f i k‖ ≤ B): ∃ φ:ℕ→ℕ,StrictMono φ ∧ ∃ F:∀ i,W i,∀ i,Tendsto (f i ∘ φ) atTop (𝓝 (F i)):=by
   choose T hT H using hf; obtain ⟨z,y,hy⟩:= Extraction.simultaneous f (K:=fun i=>closedBall 0 (T i)) (fun _=> isCompact_closedBall ..) (fun i=>(H i).mono fun k hk=>Metric.mem_closedBall.mpr (by rwa [dist_zero_right])); exact ⟨_,z.monotone,y,fun i=>(hy i).2⟩ -- conversion
variable [Fintype I][DecidableEq I]{V : I→ Type*} {o:I→Type*}
variable [∀ i,Fintype (o i)][∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)][∀ i,FiniteDimensional ℂ (V i)]
variable (B:∀ i,Basis (o i) ℂ (V i))
lemma expansion (T:MultilinearMap ℂ V ℂ)(v: ∀ i,V i): T v=∑ x: (∀ i,o i),(∏ i, (B i).repr (v i) (x i)) * T (fun i=> B i (x i)):=by
    have hx(i): ∑ j,(B i).repr (v i) j • B i j=v i:=(B i).sum_repr (v i)
    conv_lhs=> rw [← funext hx]
    rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun e _=> T.map_smul_univ _ _
lemma horizons {F:Filter Α}(T:Α→ MultilinearMap ℂ V ℂ) (Z: MultilinearMap ℂ V ℂ)(h:∀ x:(∀ i,o i),Tendsto (fun i=> T i (fun j=> B j (x j))) F (𝓝 (Z (fun j=> B j (x j))))) (v:Α→ (i:I)→ V i) (w:(i:I)→ V i) (hv:Tendsto v F (𝓝 w)):Tendsto (fun i=> T i (v i)) F (𝓝 (Z w)):=by
     suffices hh :∀ x: (∀ i,o i), Tendsto (fun k=> (∏ i, (B i).repr (v k i) (x i)) * T k (fun i=> B i (x i))) F (𝓝 ((∏ i,(B i).repr (w i) (x i))*Z (fun i=> B i (x i)))) by rw [expansion B Z w]; exact (tendsto_finsetSum Finset.univ fun i _=> hh i).congr fun k=> (expansion B (T k) _).symm
     refine fun x=> Tendsto.mul (tendsto_finsetProd _ fun i _=> (?_ : Tendsto _ F (𝓝 ((B i).repr (w i) (x i))))) (h x); exact (((B i).coord (x i)).continuous_of_finiteDimensional.tendsto (w i)).comp (tendsto_pi_nhds.mp hv i)
end Lantern
end YM.Fir
#print axioms YM.Fir.Lantern.horizons
#print axioms YM.Fir.Lantern.armor
