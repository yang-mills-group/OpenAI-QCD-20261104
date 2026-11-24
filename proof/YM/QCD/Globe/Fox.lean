import YM.QCD.Globe.Nest
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {D E:Type*} [Fintype D][Fintype E][DecidableEq D][DecidableEq E]{A B:ℝ}
lemma meal_cost (B m:ℕ):∃ Q:ℝ,0 ≤ Q∧∀ (c:Side)(S:Support c), ∀ x ∈ S,∀ y∈ S, costS m x y ≤ Q* Run.rent 1 B S:=by
    obtain ⟨C,hC,H⟩:= eats m 1 zero_lt_one; let p:ℝ:=6*(B+1); have hp :0<p:=by unfold p; positivity
    refine ⟨p^m*C,mul_nonneg (pow_nonneg hp.le _) hC.le,fun c S x hx y hy=>?_⟩; have he: separation x y ≤ coverNumber B S*(4*B+2)+2*B:= Corona.extent _ _ hx hy
    let k:= coverNumber B S
    have hv : costS m x y ≤ p^m * (1+k:ℝ)^m:=by
        rw [← mul_pow]; unfold costS; apply pow_le_pow_left₀ (by positivity); have ht : (separation x y:ℝ) ≤ k*(4*(B:ℝ)+2)+2*B:=by unfold k; exact_mod_cast he;
        unfold p; have hx:= Nat.cast_nonneg (α:=ℝ) B; have hy:= Nat.cast_nonneg (α:=ℝ) k; nlinarith only [hx,hy,ht]
    exact hv.trans ((mul_le_mul_of_nonneg_left (H k) (pow_nonneg hp.le _)).trans_eq (by rw [mul_assoc]; rfl))
lemma skirt (X:Grid f→ArrayL D E)(u:D→ Site f)(v:E→Site f)(ht: Heritage u v A 1 j X B)(hz:0<A)(Q:ℝ)(he:0 ≤ Q)(h:∀ (S:Support f) , ∀ x ∈ S,∀ y∈ S, costS m x y ≤ Q*Run.rent 1 j S): Ton u v m (Q*B) (X 1):=by
    obtain ⟨P,R,H⟩:=ht; have hp(i j'): costS m (u i) (v j')* ‖cell (X 1) i j'‖ ≤ Q*duel R i j' 1 j:=by
        rw [← H.sells]; unfold duel; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (cost_nn ..)); rw [mul_sum,mul_sum]; apply sum_le_sum; intro S _;
        have ht:=H.crop i j' S; have hp := ht.2.2.2.1 _ (Run.citizenship f hz (1:Grid f)); rw [← mul_assoc]; by_cases hk:R i j' S=0; · rw [hk] at hp; rw [hk,norm_eq_zero.mpr (norm_le_zero_iff.mp hp)]; simp
        exact mul_le_mul (h S _ (ht.2.1 hk).1 _ (ht.2.1 hk).2) hp (norm_nonneg _) (mul_nonneg he (Real.exp_pos _).le)
    constructor
    · intro i; unfold Gan; apply le_trans _ (mul_le_mul_of_nonneg_left (H.spends i) he); rw [mul_sum]; apply sum_le_sum; intro x _; exact hp ..
    intro i; unfold Gan; apply le_trans _ (mul_le_mul_of_nonneg_left (H.dues i) he); rw [mul_sum]; apply sum_le_sum; intro j _; rw [cell_flip,norm_star,cost_symm]; exact hp ..
lemma bounces (P:Plan j)(m:ℕ): ∃ C:ℝ,0≤ C ∧∀ (v:Train j)(c:Side), Beam (sunny P v c) m C:=by
    obtain ⟨B,r,p,h,hp,hP⟩:= Loom.banner P 1 zero_le_one; obtain ⟨q,hq,H⟩:= meal_cost B m; exact ⟨q*p,mul_nonneg hq hp.le,fun v c=>skirt _ id id (hP c v) h q hq (H c)⟩
set_option quotPrecheck false
lemma choiceH (P:Plan j)(k m:ℕ)(L:Side):∃ C:ℝ,0≤ C ∧∀ (S:Flight j k)(f c:Side)(h:f.val=c.val*S.L.val), S.L=L→
    let M:= sliceL S h
    let X:= father S h
    Beam X⁻¹ m C ∧Ton M.embed id m C (barP S h)∧ Ton id M.embed m C (proton S h) ∧ IsUnit X.det:=by
    obtain ⟨a,b,z,R,t,hA,hB,B,H⟩:= planted P (b:=1) zero_le_one k L; obtain ⟨q,hq,G⟩:= meal_cost B m; let D:=max 0 (q*R)
    refine ⟨D,le_max_left ..,fun S f c h he=>?_⟩; intro M X; have ht:∀ U:Grid f, Cost.Chiral (chirality f) (0:Sheet f):=by intro U; simp [Cost.Chiral]
    have hx:= H B le_rfl S he _ _ h (0:St f) b hB le_rfl (Heritage.vacant.mono hA.le) ht; rw [pesto,add_zero] at hx
    have heq:vaultF P S h 0 1=X:= tree_zero P S h
    have h1:=skirt _ _ _ hx.hashed hB _ hq (G f); have h2:=skirt _ _ _ hx.links hB _ hq (G f); have h3:=skirt _ _ _ hx.reigns hB _ hq (G f)
    unfold inverser at h1; unfold leftL inverser at h2; unfold rightL inverser at h3; rw [heq] at h1 h2 h3; exact ⟨h1.up (le_max_right ..), h2.up (le_max_right ..), h3.up (le_max_right ..), heq ▸ hx.sole 1⟩
end YM.QCD.Globe
