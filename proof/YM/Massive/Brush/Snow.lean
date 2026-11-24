import YM.Massive.PCAC.Echo
import YM.Massive.Brush.Prices
/-! Absolute quartic Lap price even over all position triples. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.PCAC
open QCD QCD.Grass QCD.Lat Lattice Wilson RG Function Filter MeasureTheory QCD.Grass.Ward
open YM.Next.Free
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator Classical ComplexOrder
variable {A B:Type*} [Fintype A][Fintype B]
variable {c f:Side}{n N j k F:ℕ}
variable (P:Flight j k)(K:KernelChoices)(h:f.val=c.val*P.L.val) (β w:ℝ)(hk:P.patch.Branches K su)
namespace Brave
open Finset NormedSpace Loft
local notation "Γ"=> Modes c F
-- square finite index sum; may cost senior order of Fiber norms
def spinPrice (X: Spike):ℝ := ‖Lat.wave X‖ -- L² operator
lemma spinPrice_nn (X: Spike):0 ≤ spinPrice X:=norm_nonneg _
lemma hC(X:Spike)(i j:Lat.Fiber) : ‖Lat.wave X i j‖ ≤ spinPrice X:= Cost.north ..
variable (X:Spike)(a b:Flavor F)
lemma sizeL(i j:Γ): ‖flavorW X a b c i j‖ ≤ spinPrice X:=by
    have ht:‖spot a b i.2 j.2‖≤1:=by unfold spot; split<;> norm_num
    have hz : ‖onSpin c X i.1 j.1‖ ≤ spinPrice X:=by
       unfold onSpin; rw [Lat.rr]; split; exact hC ..; simpa using spinPrice_nn X
    unfold flavorW; rw [Matrix.kronecker_apply,norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) ht).trans hz

section Fee
-- lift to value of `traceP(lap)`
lemma snow(n:ℕ)(x:Alg A) : 0 ≤ slate x n:=by induction n generalizing x with|zero=>exact norm_nonneg _|succ n ih=> rw [slate]; exact sum_nonneg fun i _=> ih _
private lemma twice(n:ℕ)(x:Dirac A) : ∑ i:A,∑ j:A, slate (pairD j i x) n ≤ slate x ((n+1)+1):=by
    rw [slate, Fintype.sum_sum_type]; apply le_trans _ (le_add_of_nonneg_left (sum_nonneg fun i _=> snow ..)); apply sum_le_sum; intro i _; rw [slate, Fintype.sum_sum_type]; exact le_add_of_nonneg_right (sum_nonneg fun j _=>snow ..)
lemma accountant(x:Dirac A) : ∑ i:A,∑ j:A,‖traceP x i j‖≤ slate x 2:=by have hp:=twice 0 x; unfold traceP; simp only [Matrix.of_apply,norm_neg]; exact hp
lemma accountant4(x:Dirac A) : ∑ i:A,∑ j:A, slate (pairD i j x) 2 ≤ slate x 4:=by rw [sum_comm]; exact twice 2 x
lemma account(V:Sour A)(x:Dirac A)(g:ℝ)(hv:0≤g)(h:∀ i j:A, ‖V i j‖≤g): ∑ i:A,∑ j:A,‖traceP (lap V x) i j‖ ≤ g*(4:ℕ).factorial * ‖Stew.panel 4 x‖:=by
    apply le_trans (accountant _)
    let p(i:A×A):= V i.1 i.2 • pairD i.1 i.2 x
    have he(i:A×A): slate (p i) 2 ≤ g*slate (pairD i.1 i.2 x) 2:=by unfold p; rw [slate_scale]; exact mul_le_mul_of_nonneg_right (h i.1 i.2) (snow ..)
    have hL(s:Finset (A×A)): slate (∑ i∈s,p i) 2 ≤ ∑ i∈s,slate (p i) 2:=by induction s using Finset.induction_on with | empty=> simp [slate_null]| @insert i s h ih=> rw [sum_insert h,sum_insert h]; exact (slate_sub _ _ _).trans (add_le_add (le_refl _) ih)
    have hx:lap V x=∑ i,p i:=by rw [Fintype.sum_prod_type,lap_apply]; rfl
    rw [hx]; apply ((hL univ).trans (sum_le_sum fun i _=>he i)).trans; rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((accountant4 x).trans (slate_cost x 4)) hv
end Fee
-- spectral height.Panel
local notation "V"=> (Fintype.card (Site c):ℂ)
local notation "d"=> (Fintype.card Lat.Fiber:ℂ)
noncomputable def artPrice(x:Sheet c):ℂ := (∑ i:Site c,∑ j:Site c, star (Run.plane i)*spinTest X i j x* Run.plane j)/(V * d)
lemma art_sub (x y: Sheet c): artPrice X (x+y)=artPrice X x+artPrice X y:=by unfold artPrice spinTest; simp only [QCD.Run.cell_add,add_mul,mul_add,Matrix.trace_add,sum_add_distrib,add_div]
lemma art_mul(x:Sheet c)(u:ℂ): artPrice X (u • x)=u • artPrice X x:=by unfold artPrice spinTest; simp only [QCD.Run.cell_scale, Matrix.trace_smul,mul_smul_comm,smul_mul_assoc,← Finset.smul_sum]; rw [smul_eq_mul]; ring -- rewriting under sums ambiguous
lemma art_horn(x: Fields c F)(u:ℂ): horn X a b u x= u⁻¹ • artPrice X (piece a b (traceP x)):=by unfold horn artPrice; rw [smul_eq_mul]; ring
lemma plane_cost (i:Site c): ‖Run.plane i‖=1:=by
    rw [Run.plane,Complex.norm_exp]; simp -- chiral
lemma extensive (x:Sheet c)(i j:Site c): ‖spinTest X i j x‖ ≤ spinPrice X * ∑ u:Lat.Fiber,∑ v:Lat.Fiber, ‖x (i,u) (j,v)‖ :=by
    unfold spinTest Matrix.trace; simp only [Matrix.diag_apply,Matrix.mul_apply]; apply (norm_sum_le ..).trans; rw [Finset.mul_sum]; apply sum_le_sum; intro u _; apply (norm_sum_le ..).trans; rw [Finset.mul_sum]; apply sum_le_sum; intro v _; rw [norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (hC ..) (norm_nonneg _)
lemma summit (x: Sour Γ) : let cZ:= Fintype.card (Site c); let dZ:= Fintype.card Lat.Fiber
     cZ * dZ * ‖artPrice X (c:=c) (piece a b x)‖ ≤ spinPrice X * ∑ i:Γ,∑ j:Γ, ‖x i j‖:=by -- cZ*dZ first nat? see
    intro cZ dZ; let Y:= piece a b x; unfold artPrice; let A (i j : Site c):= star (Run.plane i)*spinTest X i j Y* Run.plane j; rw [norm_div,norm_mul,Complex.norm_natCast,Complex.norm_natCast];
    have h₀:(cZ:ℝ)*dZ≠0:=by unfold cZ dZ; positivity
    rw [mul_div_cancel₀ _ h₀]; apply (norm_sum_le ..).trans; apply le_trans (b:=spinPrice X* (∑ i:Lat.Row c,∑ j:Lat.Row c, ‖Y i j‖)) -- `le_trans`?
    · change ∑ i,‖∑ j,A i j‖≤_; unfold Lat.Row; rw [Fintype.sum_prod_type,Finset.mul_sum]; apply sum_le_sum; intro i _; apply (norm_sum_le ..).trans; unfold A; simp_rw [norm_mul,norm_star,plane_cost,one_mul,mul_one,Fintype.sum_prod_type (α₁:=Site c) (α₂:=Lat.Fiber)]; rw [sum_comm (s:=(univ:Finset Lat.Fiber)),Finset.mul_sum]; exact sum_le_sum fun j _=>extensive X _ i j
    apply mul_le_mul_of_nonneg_left _ (spinPrice_nn X); unfold Modes; rw [Fintype.sum_prod_type (α₁:=Row c) (α₂:=Flavor F)]; refine sum_le_sum fun i _=>?_ ; apply le_trans _ (single_le_sum (f:=fun a:Flavor F=>∑ j, ‖x (i,a) j‖) (fun i _=>sum_nonneg fun _ _=> norm_nonneg _) (mem_univ a)); rw [Fintype.sum_prod_type (α₁:=Row c) (α₂:=Flavor F)]; refine sum_le_sum fun j _=> ?_; exact single_le_sum (f:=fun b:Flavor F=>‖x (i,a) (j,b)‖) (fun i _=>norm_nonneg _) (mem_univ b)
end Brave
end YM.Massive.PCAC
#print axioms YM.Massive.PCAC.Brave.summit
#print axioms YM.Massive.PCAC.Brave.account
