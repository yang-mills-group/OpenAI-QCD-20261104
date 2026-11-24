import YM.QCD.Nola.Whittle
import YM.QCD.Gas.Froof
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A B:Type*} {n : Side} {k:ℕ} [Fintype A][Fintype B]{s t a χ δ b:ℝ}
open Kites Pads Creek.Ledge
variable (p: Pairs A→Site n)(V:Matrix A A ℂ)(X:Patio (Pairs A))
abbrev fade (V:Matrix A A ℂ): EndA (Pairs A):= birth (pond (Embedding.refl _) V)
lemma ebbs (i:A×A): excess (engineT V i)=engineT V i:=by
     let T:=engineT V i; letI : NormedAlgebra ℚ (EndA (Pairs A)):= .restrictScalars ℚ ℂ _; have hu : NormedSpace.exp T=1+T:=by
           simp only [exp_eq_tsum ℂ]; rw [tsum_eq_sum (s:=range 2) ?_]; · simp [sum_range_succ] -- smul
           intro b hb; rw [pow_eq_zero_of_le (show 2 ≤ b from le_of_not_gt (mt mem_range.mpr hb)) (show T^2=0 from engine_sq V i)]; exact smul_zero _ -- check
     change NormedSpace.exp T -1=T; rw [hu, add_sub_cancel_left]
lemma fueling : ∑ s: Finset (A×A),(mist p X V).ping s=fade V:=by
     have he: (pond (Embedding.refl _) V)=∑ i:A × A,engineT V i:=by rw [Fintype.sum_prod_type]; rfl
     let S:=mist p X V; unfold fade; rw [he, ← Cove.dripe (engineT V) (engine_comm V)]; simp_rw [Finset.powerset_univ]; -- powerset_univ
     have hu : (fun i=> excess (engineT V i))=S.buys:= funext fun i=> ebbs ..
     exact sum_congr rfl (fun s _=>by unfold ping; congr 1; exact hu.symm)
lemma flow (h: coef ∅ X.val=0): ∑ s:Finset (Peak (Pairs A)), (mist p X V).grape s=NormedSpace.exp X:=by
     have he : exp X= exp (∑ j, interesting X j):= by rw [lamp X h]
     rw [he, Cove.flicker]; simp_rw [very]; -- univ
     rfl -- check
lemma dotted (h:coef ∅ X.val=0):
   fade V (exp X.val)=light (Pairs A) (∑ s,(mist p X V).ham s) :=by
     let S:= mist p X V
     rw [show X.val=light _ X from rfl, ← light_exp,← flow p V X h, ← fueling p V X,map_sum,map_sum];
     simp_rw [ContinuousLinearMap.sum_apply, map_sum]; rw [← Equiv.sum_comp (packEquiv (Peak (Pairs A)) (A×A)) (fun i=> light _ (S.ham i)), Fintype.sum_prod_type]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; change S.ping i (light _ (S.grape j))= S.ping (j.disjSum i).toRight (light _ (S.grape (j.disjSum i).toLeft)); rw [Finset.toLeft_disjSum,Finset.toRight_disjSum]
lemma twirl (t:ℝ) (hp:0<t)(i:A×A)(x:Alg (Pairs A)): load (fun _=>t) ((mist p X V).buys i x) ≤ ‖V i.1 i.2‖*t⁻¹^2*load (fun _=>t) x:=by
   change load (fun _=>t) (V i.1 i.2 • v (Sum.inr i.2) (v (Sum.inl i.1) x)) ≤ _; rw [Creek.load_scale]; apply le_trans (mul_le_mul_of_nonneg_left (Creek.fee (fun _=>t) (fun _=>hp) (Sum.inr i.2) (v (Sum.inl i.1) x)) (norm_nonneg _))
   rw [mul_assoc,pow_two, mul_assoc]; gcongr; exact Creek.fee (fun _=>t) (fun _=>hp) _ x
lemma clearH (x:Peak (Pairs A)): ((mist p X V).leaves (.inl x)).Nonempty:= Finset.Nonempty.image (Finset.card_pos.mp x.2.2) _
end YM.QCD.Nola
