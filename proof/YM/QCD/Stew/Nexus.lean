import YM.QCD.Stew.Hinge
/-! # block tickets, finite-stencil Poset estimate -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N n z:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Port
variable {B: Support c}
noncomputable def block (i j:Site c)(p: Bundle):Sheet c:=Matrix.of fun x y:Lat.Row c=> if x.1=i ∧ y.1=j then p x.2 y.2 else 0
lemma starBl (i j : Site c)(p: Bundle): star (block i j p)=block j i (star p):=by ext a b; by_cases ht:a.1=j<;> by_cases hk:b.1=i <;> simp [block, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,ht,hk]
noncomputable def blockL (i j:Site c): Bundle→L[ℂ] Sheet c:=LinearMap.toContinuousLinearMap { toFun:=block i j,map_add':=fun x y=>by ext a b; unfold block; by_cases ht:a.1=i <;> by_cases hb:b.1=j<;>simp [ht,hb], map_smul':=fun x y=> by ext a b; unfold block; by_cases ht:a.1=i <;> by_cases hb:b.1=j<;>simp [ht,hb,Matrix.smul_apply] }
lemma pairBl (i j z w:Site c)(D : Bundle): cell (block i j D) z w=if z=i ∧ w=j then D else 0:=by ext a b; by_cases h:z=i <;> by_cases hp:w=j <;> simp [cell,block,h,hp]
lemma padBl (i j:Site c)(M:Bundle)(hi:i∈B)(hj:j∈B): Gated B (paleF N (block i j M)):=stackP _ (fun x y hp=> by rw [pairBl,if_neg]; rintro ⟨rfl,rfl⟩; tauto) N
lemma siteBl (i:Site c)(X:Spike): localX i X=block i i (wave X):=by apply Sway.whist; intro a b; rw [pairBl,Stew.placed]; congr 1; apply propext; grind
lemma couple (o:Site c)(X:Spike)(p:Step)(U:Grid c): localX o X*leg 0 U p=block o (o+p.vec) (wave X*touch (hitch 0 U p o)):=by
   apply Sway.whist; intro i j; rw [pairBl]; unfold localX; rw [leg_day, ride_mul,board, Equiv.refl_trans]; by_cases he:i=o
   · subst i; simp only [Equiv.refl_apply]; change (if _ then (if True then _ else _)* _ else _)=(if _ then _ else _); rw [if_true]; refine if_congr ?_ rfl rfl; change o+p.vec=j↔_; simp [eq_comm]
   rw [if_neg (show ¬ (i=o ∧ j=o+p.vec) from fun h=>he h.1)]; split; next h=> rw [if_neg (Ne.symm he), zero_mul]
   next _=> rfl
open Jets Jets.Sun
lemma senCamp (U: Support c)(hr:∀ i∈U,separation i o ≤ n)(X:EvenA c N)(hp:0<a)(h:Gated U X): Sen o a X ≤ (1+n:ℝ)^2* ‖token c N a X‖ :=by
    let g:= lens (N:=N) o; apply le_trans _ (Cove.camps (U:=limits U) (fun (_:Keys c N)=>hp) g 2 (Cove.light (Keys c N) X) h n (fun i hi=> hr _ (mem_filter.mp hi).2))
    change visc g a X.val ≤ _; rw [pricesD g hp.le]; unfold camp; exact (sum_le_sum fun i _=> by unfold Cove.weight starch; push_cast [pieD,regionW]; simp only [prod_const]; exact le_rfl)
lemma budgetBl (M: Bundle)(i j:Site c)(hx:i∈ stand o)(hj:j∈ stand o)(ht:0<a) (N:ℕ): Sen o a (paleF N (block i j M)) ≤9*a^2*fingers N^2 * ‖M‖:=by
    let X:= paleF N (block i j M)
    have hf: jacket (Modes c N) (Lat.copies N (block i j M)) a ≤ a^2*fingers N^2* ‖M‖ :=by
       let Z:= Lat.copies N (block i j M); let w x y:= if x=i ∧ y=j then ‖M‖ else 0
       have he x y : 0 ≤ w x y:=ite_nonneg (norm_nonneg _) le_rfl
       have h(i':Modes c N)(j':Modes c N): ‖Z i' j'‖≤ w (headF i') (headF j'):=by
          unfold Z copies; rw [Matrix.blockDiagonal_apply]; split
          next hp=> unfold w; change _ ≤ if i'.1.1=i ∧ j'.1.1=j then ‖M‖ else 0; rw [block,Matrix.of_apply]; split
                    next ht=> exact Cost.north ..
                    next ht=> rw [norm_zero]
          next hp=> rw [norm_zero]; apply he
       unfold jacket
       apply (mul_le_mul_of_nonneg_left (paddleB (F:=N) 0 (∅:Support c) 0 (fun i j=> ‖Z i j‖) w h) (sq_nonneg _)).trans; rw [mul_assoc, show (∑ i,∑ j,w i j)=‖M‖ from ?_]
       unfold w; rw [sum_eq_single i]; · simp
       · intro x _ hx; simp [hx]
       simp
    refine le_trans (senCamp (stand o) (n:=2) (fun i hk=> by simpa only [stand,halo_spec,mem_singleton, exists_eq_left,separation_comm i o] using hk) _ ht (padBl i j M hx hj)) ?_
    apply (mul_le_mul_of_nonneg_left ((Port.fauna (Lat.copies N (block i j M)) ht).trans hf) (by norm_num : (0:ℝ) ≤ (1+((2:ℕ):ℝ))^2)).trans_eq; push_cast; ring
end YM.QCD.Stew
