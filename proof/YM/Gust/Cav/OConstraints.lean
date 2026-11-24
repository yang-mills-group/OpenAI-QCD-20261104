import YM.Next.ROTATIONS.Constraints
import YM.Gust.Cav.OPier
/- Variant of YM.Next.ROTATIONS.Constraints, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}
lemma BL_law {R J D} (H : Portrait (S:=S) J D R) (i : Axis) : BL R i=Pmul 2 i (SelfB R i)+DB R i := by
  have he : Cash1 R i = liftP i (Mux R i)+BL R i := by
    unfold Cash1 Mux BL
    simp_rw [cash0 R i i _ i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; rw [H.UD i i j i,Pcomm]
  rw [DB,he,cash0 R i i i i,map_add]
  rw [show liftP i (liftP i _) = Pmul 2 i (SelfB R i) from Pplus ..]
  unfold Mux; abel
lemma CL_law {R J D} (H : Portrait (S:=S) J D R) (i : Axis) : CL R i=Pmul 2 i (BL R i)+DC R i := by
  have he : Cash2 R i=liftP i (BL R i)+Mex R i := by
    unfold Cash2 BL Mex; simp_rw [cash0 R i _ _ i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro a _
    rw [H.LR i a,Pcomm 1 1 a i,Pcomm 1 1 j i]
  have hh : Cash3 R i=liftP i (Mex R i)+CL R i := by
    unfold Cash3 CL Mex; simp_rw [cash0 R i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    rw [H.LR i j,H.UD j i a b,H.LR a b,Pcomm 1 1 b i,Pcomm 1 1 a i,Pcomm 1 1 j i]
  rw [DC,hh,he,map_add]
  rw [show liftP i (liftP i (BL R i))=Pmul 2 i (BL R i) from Pplus ..]; abel
lemma accounts_cost {R J D} (H : Portrait (S:=S) J D R) (hd : 0<D) (P : DiffPlan S) (hP : P.Derivatives S)
    (hr : S.Hierarchy) (hp : Conserved P hr.spin J) (he : Strong J P D) (a : ℝ) (ha : a≤0) (w) (hw : ∀ j,w j≤a) (i) :
    Ach w (a*4) (DB (joint R) i) ∧ Ach w (a*6) (DC (joint R) i) := by
  let F := joint R
  have ht b c d : Ach w (a*3) (source F b c d) := source_cost hr P hP hd H hp he a ha b c d w hw
  refine ⟨?_,?_⟩
  · rw [show a*4=a*3+a by ring]; exact (Ach.sum w _ _ _ fun j _ => (ht _ _ _).one _ (hw j)).sub ((ht _ _ _).one _ (hw i))
  rw [show a*6=a*3+a+a+a by ring]
  apply Ach.sub
  · exact Ach.sum w _ _ _ fun j _ => Ach.sum w _ _ _ fun k _ => Ach.sum w _ _ _ fun l _ => (((ht j k l).one _ (hw l)).one _ (hw k)).one _ (hw j)
  · apply Ach.one _ i (hw i)
    exact Ach.sum w _ _ _ fun j _ => Ach.sum w _ _ _ fun k _ => ((ht k j i).one _ (hw k)).one _ (hw j)
lemma accounts_sink {R J D} (H : Portrait (S:=S) J D R) (P : DiffPlan S) (hP : P.Derivatives S) (hr : S.Hierarchy)
    (hp : Conserved P hr.spin J) (he : Strong J P D) (i) : Disappears i (D+1+1) (DB R i) ∧ Disappears i (D+1+1+1+1) (DC R i) := by
  have ht b c d : Disappears i (D+1) (source R b c d) := by
    intro f hf; change I*delta _ _ _ _ (polar f)=_; rw [closed_shell hr P hP H hp he b c d (polar f) i (polar_flat f i _ hf),mul_zero]
  refine ⟨?_,?_⟩
  · unfold DB Cash1; exact (Disappears.sum _ _ _ _ fun j _ => (ht i j i).pmul j 1).sub ((ht _ _ _).pmul _ 1)
  apply Disappears.sub
  · exact Disappears.sum _ _ _ _ fun j _ => Disappears.sum _ _ _ _ fun k _ => Disappears.sum _ _ _ _ fun l _ => (((ht _ _ _).pmul l 1).pmul k 1).pmul j 1
  · apply Disappears.pmul _ _ 1
    exact Disappears.sum _ _ _ _ fun j _ => Disappears.sum _ _ _ _ fun k _ => ((ht _ _ _).pmul k 1).pmul j 1
lemma accounts_fixed (V : ∀ i, Chamber S i) (K : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation K.spin)
    (J : Stress S) (C : Conserved P K.spin J) (Y : RawTensor K.spin J)
    {D : ℕ} {R : Series} (hR : Portrait J D R) (δ : ℝ) (hd : 0<δ) (i) (w) (he : w i=0) (a : ℝ) (ha : a≤0) (hw : ∀ j,j≠i → w j≤a) :
    Quest w i (fun _ => false) δ (SelfB R i) ∧ Quest w i (fun _ => false) (δ+a+a) (BL R i) ∧
      Quest w i (fun _ => false) (δ+a+a+a+a) (CL R i) := by
  have H j k l m : Quest w i (axes j k l m) δ (sent (R j k l m)) := fun f h g t =>
    fixed V K P hp ho J C Y hR j k l m i f g h t w he (fun i' => by
      by_cases H:i'=i
      · simp [H,he]
      exact (hw i' H).trans ha) _ hd
  have hq (k) (hk : k ∈ other i) : w k ≤ a := hw _ (Finset.mem_erase.mp hk).1
  refine ⟨(H i i i i).alters (fun j hj => ?_),?_,?_⟩
  · simp [axes,spar,hj]
  · refine Quest.sum w _ _ _ (other i) _ fun j hj => Quest.sum _ _ _ _ _ _ fun k hk => ?_
    apply (((H k i j i).inserts k (hq _ hk)).inserts j (hq _ hj)).alters
    intro x hx; unfold toggle axes spar; cases decide (x=j)<;>cases decide (x=k)<;> cases decide (x=i)<;>decide
  unfold CL
  refine Quest.sum w i _ _ _ _ fun j hj => Quest.sum w i _ _ _ _ fun k hk => Quest.sum w i _ _ _ _ fun l hl => Quest.sum w i _ _ _ _ fun m hm => ?_
  apply (((((H m j k l).inserts m (hq _ hm)).inserts l (hq _ hl)).inserts k (hq _ hk)).inserts j (hq _ hj)).alters
  intro x hx; unfold toggle axes spar
  cases decide (x=j)<;>cases decide (x=k)<;>cases decide (x=l)<;>cases decide (x=m)<;>decide
end YM.Spiral.Outer

