import YM.Poised.Pipes
/-!
# All spin-ward obligations through the entire (joint grade) chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {J B : Type}{d a l k n:ℕ}{c:Side}
namespace Pipes
open Beacon Gem MultiNext.SignedSource YM.Next.Foundations
variable (T:Taper) (b:Cover) [Fintype B]
local notation "C"=> su.Color
local notation "S"=> Flet B
local notation "Q"=> C × S
lemma scaleG_cost (n:ℕ)(w: Fin n→ ℕ)(X: Fin n→E4→su.Color)(A: Fin n→ E4 → Flet B)(hx: ∀ i,X i∈rangeLt C (w i/2+1))(hA: ∀ i,A i ∈ rangeLt S ((w i-1)/2)) :
   (fun p:E4=>iteratedFDeriv ℝ n scaleG (0:Q) (fun i=> (X i p,A i p))) ∈rangeLt S (((∑ i,w i)-1)/2) :=by
    let X₁:= ContinuousLinearMap.inl ℝ C S; let A₁ := ContinuousLinearMap.inr ℝ C S; let R i (x:Bool) (p:E4):= if x then A₁ (A i p) else X₁ (X i p); let M:=iteratedFDeriv ℝ n scaleG (0:Q)
    rw [show (fun p:E4=>iteratedFDeriv ℝ n scaleG (0:Q) (fun i=>(X i p,A i p)))=∑ s : Fin n→Bool,fun p=>M (fun i=> R i (s i) p) from funext fun p=> by rw [Finset.sum_apply]; rw [← M.map_sum (fun i s=>R i s p)]; simp [R,X₁,A₁,M]]
    apply Submodule.sum_mem; intro s _; by_cases h:∀ i,s i=false
    · have hh:scaleG ∘ X₁=0:=funext forfeit; have ht:M.compContinuousLinearMap (fun _=>X₁)=0:=by rw [show M= _ from rfl, ← jets_linear X₁ (((scaleG_live (B:=B)).contDiffAt).of_le le_top),hh,iteratedFDeriv_zero]; rfl -- show bug
      rw [show (fun p:E4=> M fun i=>R i (s i) p)=0 from funext fun p=>by simp only [R,h]; exact DFunLike.congr_fun ht (fun i=> X i p)]; exact Submodule.zero_mem _
    by_cases ht:∃ i, s i=true ∧ w i<3
    · obtain ⟨i,hi,hf⟩:=ht; have ha:A i=0:=by have hx:= hA i; rw [show (w i-1)/2=0 from by omega,rangeLt] at hx; exact Submodule.mem_bot _|>.1 hx
      rw [show (fun p:E4=>M fun i=>R i (s i) p)=0 from funext fun p=> M.map_coord_zero i (by unfold R; rw [if_pos hi,ha,Pi.zero_apply,map_zero])]; exact Submodule.zero_mem _
    let a i:=if s i then (w i-3)/2 else w i/2; let z i:= if s i then 3 else 0
    have hZ(i):s i=true → 3≤w i :=fun hi=> le_of_not_gt (fun hc=> ht ⟨i,hi,hc⟩)
    have hi(i):2*a i+z i ≤ w i:=by
       unfold a z; split; next hi=> have :=hZ i hi; omega
       next _=>omega -- whitespace
    have hp (i) : (fun p=> R i (s i) p) ∈ rangeLt Q (a i+1):=by
       unfold R a; split; next hi=>
          have he:=hA i; have h':(w i-3)/2+1=(w i-1)/2:=by have:=hZ i hi; omega
          exact linear_band _ _ (show A i∈rangeLt S ((w i-3)/2+1) from h'.symm ▸ he)
       next _=>exact linear_band _ _ (hx i)
    apply grows S _ (multi_band M (fun i=> R i (s i)) a hp); have he:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hi i); rw [sum_add_distrib, ← mul_sum] at he
    push Not at h; obtain ⟨i,hi⟩:= h; have hg: z i≤ ∑ i,z i:= Finset.single_le_sum (fun i _=> Nat.zero_le (z i)) (Finset.mem_univ i); rw [show z i=3 from if_pos (Bool.eq_true_of_not_eq_false hi)] at hg; omega
end Pipes
end YM.Massive.Poised
