import YM.Alum.Chord
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station Finset
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace CardsT
open QCD QCD.Lat Tide Plum QCD.Grass MassiveQCD Cupola Sample LoomT
variable (S:Scheme){c:Side}{F m:ℕ}{j k p N:ℕ} {I:Type}[Fintype I]
set_option quotPrecheck false
variable (R:Regulator c F)
open Lyre Goblet
lemma chantsE (X:Fin m→Stud c F) (Y:Fin m→ I→Stud c F) (f:Fin m→ I→ℝ)(hf:∀ j i,0 ≤ f j i)(hB:∀ j,(∑ i,f j i)=1)(hY:∀ i,X i=∑ j, f i j • Y i j)(hX:∀ i j,Stays (Y i j))(ε:ℝ)(w:ℂ)(hV:∀ t:Fin m→ I, ‖valueH R (List.ofFn fun i=>Y i (t i)).prod-w‖ ≤ ε): ‖valueH R (List.ofFn X).prod -w‖ ≤ ε:=by
    let M:=MultilinearMap.mkPiAlgebraFin ℝ m (Stud c F); let P(i:Fin m)(j:I):=f i j • Y i j; let u(t:Fin m→ I):ℝ:= ∏ i:Fin m,f i (t i); let Z(t:Fin m→I):= M (fun i=>Y i (t i));
    have ht:(List.ofFn X).prod=∑ t:Fin m→I,u t • Z t:=by
         change M X=_; rw [show X=(fun i=> ∑ j, P i j) from funext hY, M.map_sum]; exact sum_congr rfl fun i _=> M.map_smul_univ (fun j=>f j (i j)) _
    have hu : ∑ t: Fin m→ I,u t=1:=by unfold u; rw [← Fintype.prod_sum]; simp [hB]
    have hx : w=∑ t: Fin m→I,u t • w:=by rw[←sum_smul,hu,one_smul]
    have hS(t:Fin m→I):Stays (Z t):=by
        suffices h:∀ l: List (Fin m),Stays (l.map fun i=>Y i (t i)).prod by
             let l:=List.ofFn (fun i : Fin m=>i); have ht:=h l; unfold l at ht; rw [List.map_ofFn] at ht; exact ht
        intro l; induction l with|nil=>exact Plum.Fence.one (A:=Set.univ) (F:=F) |>.hp| cons i l ih=> exact (hX i _).mult ih
    rw [ht,sumsV R _ (fun i=>u i • Z i) (fun i _=> (hS i).flows (f:=fun x:Lat.Fields c F=>u i • x) (continuous_id.const_smul (u i)))]
    have hp(t:Fin m→I):valueH R (u t • Z t)=u t • valueH R (Z t):=spend R _ (↑(u t):ℂ)
    have he (i: Fin m→ I):0≤ u i:= prod_nonneg fun _ _=> hf ..
    simp_rw[hp]; rw [hx,← sum_sub_distrib]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun i=>u i*ε) (fun i _=>?_)).trans_eq (?_); · rw [←smul_sub, norm_smul, Real.norm_of_nonneg (he _)]; exact mul_le_mul_of_nonneg_left (hV i) (he i)
    rw [← sum_mul,hu,one_mul]
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.chantsE
