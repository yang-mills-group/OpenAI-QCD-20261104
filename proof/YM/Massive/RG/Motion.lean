import YM.Massive.RG.Exact

/-!
# Gauge and grading on a mass-admitting trajectory with variable strides
-/

set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson MeasureTheory Function Filter RG
open YM.Next.Free (Flight)
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator

namespace Transfer

variable {j k F : ℕ} {c f n : Side}
variable (β w : ℝ)

lemma scaleCommutes (x : Fields n F) (M : Matrix (Pairs (Modes n F)) (Pairs (Modes n F)) ℂ) :
    rescale w (changeVars M x) = changeVars M (rescale w x) := by
  classical
  unfold rescale; rw [← AlgHom.comp_apply, ← change_mul, ← AlgHom.comp_apply, ← change_mul]
  apply congr_arg (fun p : Matrix (Pairs (Modes n F)) (Pairs (Modes n F)) ℂ => changeVars p x)
  ext i j; rw [Matrix.diagonal_mul, Matrix.mul_diagonal,mul_comm]

lemma berezin_grade {A : Type*} [Fintype A] (x : Dirac A) : ber A (grade x)=ber A x := by
  conv_lhs => rw [← both x,map_add,map_add, show grade (plus x)= _ from plus_grade x,
    show grade (minus x)= _ from minus_grade x,map_neg,odd_loss (minus_grade x), neg_zero]
  nth_rw 2 [← both x]; rw [map_add,odd_loss (minus_grade x)]

lemma berezin_grade_exchange {E : Type*} [Fintype E] (x y : Dirac E) : ber E (grade x*y)=ber E (x*grade y) := by
    rw [← berezin_grade (grade x*y),map_mul,grade_twice]

lemma marginal_grade {A B : Type*} [Fintype A] [Fintype B] (x : Dirac (A⊕B)) :
    marginal A B (grade x)=grade (marginal A B x) := by
  apply (perfect B).injective; apply LinearMap.ext; intro y
  rw [perfect_apply,perfect_apply,marginal_test]
  rw [berezin_grade_exchange,berezin_grade_exchange,marginal_test]; congr 2; exact pass_grade ..

lemma sheath_grade {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (b : ℝ) (Q : Matrix B A ℂ) (x : Dirac A) : Kit.sheath b Q (grade x) = grade (Kit.sheath b Q x) := by
  unfold Kit.sheath
  rw [map_smul, ← marginal_grade,map_mul grade, (show grade (gauss _) = _ from gauss_plus _), ← show near A B (grade x) = grade (near A B x) from (pass_grade ..).symm]

variable (P : Flight j k) (K : KernelChoices) (h : f.val=c.val*P.L.val) (hk : P.patch.Branches K su)

lemma soften_grade (x : Density f F) (U : Grid f) : soften P h (grade ∘ x) U = grade (soften P h x U) := sheath_grade ..

lemma soften_gauge (x : Density f F) (g : Frame f) (U : Grid f) :
    slots F (g ∘ (coarse P K h).ratio.embed) (soften P h x (gauge g U)) =
      soften P h (fun A => slots F g (x (gauge g A))) U := by
  unfold soften
  rw [Flume.gauges,Kit.choir_mul,Kit.choir_mul,Kit.replicas (star _) _,copies_star]
  exact Kit.compat (rotates_law F g) (rotates_law F (g ∘ (Flume.sliceL P h).embed)) ..

include hk

lemma gauge (x : Insertion f F) (g : Frame f) : up P K h β w hk (transform g x) =
    transform (g ∘ (coarse P K h).ratio.embed) (up P K h β w hk x) := by
  let S := coarse P K h; let p := g ∘ S.ratio.embed
  let T : Fields c F →L[ℝ] Fields c F :=
    (LinearMap.toContinuousLinearMap (slots F p).toLinearMap).restrictScalars ℝ
  have he (U : Grid f) : T (soften P h x (Lattice.gauge g U)) = soften P h (transform g x) U := soften_gauge ..
  ext1 i
  change rescale w (S.push β _ _) = slots F p (rescale w (S.push β (soften P h x) (Lattice.gauge p i)))
  unfold slots adapter; rw [← scaleCommutes]
  congr 1
  change S.push _ _ _ = T _
  let a : Grid f → Fields c F := fun U => S.density β U (Lattice.gauge p i) • soften P h x U
  have ha : Integrable a (prior su f) := StepData.push_slice (kernel P K h β hk) _ _ (soften_pay P h x.continuous)
  have hm := prior_gauge g
  unfold StepData.push
  rw [← T.integral_comp_comm ha]; nth_rw 2 [← hm.map_eq]
  rw [integral_map hm.aemeasurable (f:=fun U=> T (a U))
    (by rw [hm.map_eq]; exact (T.integrable_comp ha).aestronglyMeasurable)]
  congr 1; funext U
  dsimp only [a]; rw [map_smul, he, S.covary hk]

omit hk in
lemma hom_iff {A : Type*} [Fintype A] (p : Bool) (v : Dirac A) : Grass.Hom p v ↔ grade v= (if p then (-1:ℂ) else 1) • v := by
    cases p <;> simp [Grass.Hom,Plus,Minus]

lemma homogeneous (x : Insertion f F) (p : Bool) (hx : ∀ U, Grass.Hom p (x U)) :
    ∀ V, Grass.Hom p ((up P K h β w hk x) V) := by
  let S := coarse P K h
  let g (U : Grid f) := soften P h x U
  let r : ℂ := if p then -1 else 1
  have hl (U : Grid f) : grade (g U)=r • g U := by
    rw [← show soften P h (grade ∘ ⇑x) U = _ from soften_grade ..];
    have ht : grade ∘ ⇑x = r • (⇑x):= by
      funext i; change grade (x i) = r • (x i); exact (hom_iff (A:=Modes f F) p (x i)).mp (hx i)
    rw [ht,soften_smul]; rfl
  intro V; rw [hom_iff]; let W : Fields c F →L[ℝ] Fields c F := grade.toLinearMap.toContinuousLinearMap.restrictScalars ℝ
  let b (U : Grid f) := S.density β U V • g U; have ht : Integrable b (prior su f):= StepData.push_slice (kernel P K h β hk) V g (soften_pay P h x.continuous)
  have hv : grade (S.push β g V) = r • S.push β g V := by
    change W (∫ i,b i ∂prior su _) = r • ∫ i,b i ∂prior su _; rw [← W.integral_comp_comm ht, ← integral_smul]
    congr 1; funext U; dsimp only [b]; rw [map_smul]; change _ • grade (g U)=_; rw [hl,smul_comm]
  change grade (changeVars _ (S.push β g V))=_; rw [changeVars,exterior_parity,hv,map_smul]; rfl

lemma invariant (x : Insertion f F) (hx : Lat.Invariant x) : Lat.Invariant (up P K h β w hk x) := by
  let S := coarse P K h
  intro k
  obtain ⟨q,hq⟩ := S.ratio.embed_injective.hasLeftInverse
  let g : Frame f := k ∘ q
  have ht : g ∘ (coarse P K h).ratio.embed=k := funext fun i => congrArg k (hq i)
  rw [← ht,← Transfer.gauge,hx]

end Transfer
end YM.Massive
