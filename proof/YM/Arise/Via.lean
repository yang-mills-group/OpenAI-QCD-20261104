import YM.Arise.Labels
import YM.Arise.Site
/-! # Sym.Ap.Color and actual scheme covariance of chart names.Back.Al.D.N.Pl.S -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Range
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Labels Maxwell
variable {r n m i j k d:ℕ}
variable {G:Gauge}
variable (L:G.Color→ₗ[ℝ] G.Color)
variable (X: Ink G d)
-- compose on each color all.Infinite jets use.
noncomputable def lampK (X:Ink G d)(l: Motif d) :G.Color:= WithLp.toLp 2 (fun i:G.ColorIndex=> X (l,i))
noncomputable def liftedK (X:Ink G d) : Ink G d:= fun k=> L (lampK X k.1) k.2
noncomputable def pigmentK : Lily G d→ₐ[ℂ]Lily G d:= MvPolynomial.aeval fun k: Tube G d=> ∑ i:G.ColorIndex, (((L (EuclideanSpace.single i 1) k.2):ℝ):ℂ) • MvPolynomial.X (k.1,i)
lemma pink(p:Lily G d): nestK X (pigmentK L p)=nestK (liftedK L X) p:=by
    suffices h:(nestK X).comp (pigmentK L)=nestK (liftedK L X) from DFunLike.congr_fun h p
    ext k; simp only [AlgHom.comp_apply,pigmentK,MvPolynomial.aeval_X,map_sum,map_smul,nestK,MvPolynomial.aeval_X,liftedK,smul_eq_mul]; let A:=lampK X k.1; rw [show lampK X k.1=∑ i:G.ColorIndex, X (k.1,i) • (EuclideanSpace.single i 1) from (by ext i; simp [lampK,Pi.single_apply]),map_sum]; simp only [map_smul]; rw [show (∑ i:G.ColorIndex, X _ • L _) k.2=∑ i, X (k.1,i)*L (EuclideanSpace.single i 1) k.2 from map_sum (EuclideanSpace.proj (𝕜:=ℝ) k.2) (fun i=> X (k.1,i) • L (EuclideanSpace.single i 1)) univ]; simp only [Complex.ofReal_sum,Complex.ofReal_mul]; exact sum_congr rfl fun _ _=>mul_comm _ _
lemma lust (i:ℕ): stripeJ G d i (liftedK L X)= L ∘ stripeJ G d i X:=by
    unfold stripeJ; split
    next h=> rfl
    next h=> funext k; simp
lemma pele (a:Axis)(x:E4)(i:ℕ): (phone d G (liftedK L X) i).value a x=L ((phone d G X i).value a x):=by
    change Taylor.value (wheel (stripeJ _ _ _ _)) _ _= L (Taylor.value (wheel (stripeJ _ _ _ _)) _ _); rw [lust]; exact pel ..
lemma colorL (P:(i:ℕ)→Module.End ℝ (Taylor G i))(h:∀ i p x v,Taylor.value (P i p) x v=L (Taylor.value p x v))(p: Labels.Pol G): pigmentK L (loCast G d p)=loCast G d (Labels.changed P p):=by
    apply futon; intro X; rw [pink,← AlgHom.comp_apply,← AlgHom.comp_apply,postK (liftedK L X), postK X, Labels.eval_changed]; apply congr_arg (fun z=>Labels.read z p); funext i; apply Taylor.value_ext; funext x v; rw [pele]; exact (h _ _ x v).symm -- show constr
section su
open Massive UV QCD Poised -- Bera maybe?
open TensorProduct
abbrev Bard (d:ℕ):= Lily su d ⊗[ℂ] SpinPol d
noncomputable def introduce (d:ℕ): UV.Pol d→ₗ[ℂ] Bard d:=TensorProduct.map (loCast su d).toLinearMap LinearMap.id
noncomputable def revere (d:ℕ): Bard d→ₗ[ℂ] UV.Pol d:=TensorProduct.map (rollK su d).toLinearMap LinearMap.id
lemma revive (v: UV.Pol d)(h:v∈UV.cap d): revere d (introduce d v)=v:=by
    refine Submodule.span_induction (p:=fun v _=>revere _ (introduce _ v)=v) ?_ (by simp) (fun x y _ _ h hp=>by rw [map_add,map_add,h,hp]) (fun i x _ h=>by rw [map_smul,map_smul,h]) h
    rintro x ⟨s,h,rfl⟩; change UV.weight s≤d at h -- s implicit.Level.At
    unfold introduce revere UV.gen; rw [TensorProduct.map_tmul,TensorProduct.map_tmul]; have hp : Labels.height s.1 ≤ d:=by unfold UV.weight at h; omega
    exact congr_arg (fun v: GPol=> v⊗ₜ[ℂ] Grass.mono s.2) (returnsX _ hp 1)
lemma flare (u:su.El)(p: UV.Pol d):introduce d (UV.colorAct u p)= TensorProduct.map (pigmentK (su.adjoint u) (d:=d)).toLinearMap (Grass.adapter (colorTable u) (star (colorTable u)).transpose).toLinearMap (introduce d p):=by
    induction p using TensorProduct.induction_on with
    | zero=>simp
    | add p q h hp=>rw [map_add,map_add,map_add,map_add,h,hp]
    | tmul x y=> unfold UV.colorAct introduce; rw [TensorProduct.map_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul,TensorProduct.map_tmul]; let P:(i:ℕ)→ Module.End ℝ (Taylor su i):= fun _ => Taylor.paint u; let Z:= (Grass.adapter (colorTable (d:=d) u) (star (colorTable u)).transpose) y; exact congr_arg (fun x: Lily su d=> x⊗ₜ[ℂ] Z) (colorL (d:=d) (su.adjoint u) P (fun _ _ _ _=>rfl) x).symm
end su
end YM.Arise.Range
