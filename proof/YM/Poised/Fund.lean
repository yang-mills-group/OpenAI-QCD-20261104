import YM.Poised.Soot
import YM.Poised.Halcyon
import YM.QCD.Fawn.Shouts
/-!
# Normalized row table. ALL spin transformations paid at native polynomial powers, per small table state only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n:ℕ}{c:Side}
namespace Pipes
open Pointwise Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad
variable [Fintype B][Fintype A]
abbrev orderR (f:A→ℝ)(g:B→ℝ)(W:A→B→ℂ) : A→B→ℂ:=fun i j=> (f i : ℂ)⁻¹*(g j:ℂ)*W i j
def framesF(f:A→ℝ) : Alg A →L[ℝ] Alg A:= ((changeVars (Matrix.diagonal (fun a=>(f a:ℂ)))).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
lemma frames_panel (f:A→ℝ)[DecidableEq A](x:Alg A)(n:ℕ):framesF f (panel n x)=panel n (framesF f x):=by
    let N(p:A→ℝ): Alg A →ₗ[ℂ] Alg A:=(changeVars (@Matrix.diagonal A ℂ (Classical.decEq A) _ (fun a=>(p a:ℂ)))).toLinearMap; exact (ponder (N f) (fun i=>exterior_layer (substitution _) (Grass.homogeneous i)) n x).symm
lemma equivalent_scale (f:A→ℝ)(hf:∀ i,0<f i)(g:B→ℝ)(W:A→B→ℂ)(x:Alg A): changeVars (orderR f g W) (wscale f x)=wscale g (changeVars W x):=by
    unfold wscale
    let S:Matrix _ _ ℂ:=Matrix.diagonal fun i=>(f i:ℂ); let U:Matrix _ _ ℂ:= Matrix.diagonal fun j=>(g j:ℂ); let Z:Matrix _ _ ℂ:= orderR f g W; let T: Matrix _ _ ℂ:= W
    have h:S*Z=T*U:=by ext1 i j; unfold S U; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; change _ * ((f i:ℂ)⁻¹*(g j:ℂ)*W i j)= _; field_simp [show (f i:ℂ)≠0 by exact_mod_cast (hf i).ne']; unfold T; ring
    change ((changeVars _).comp (changeVars S)) x= ((changeVars U).comp (changeVars T)) x; rw [←change_mul, ←change_mul,h]
lemma atom_price (v:A→B→ℂ)(i:A): ‖changeVars v (atom i)‖ ≤∑ j, ‖v i j‖:=by rw [change_atom]; exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul,norm_atom,mul_one])
def SeatD (f:A→ℝ)(g:B→ℝ) (X:A→B→ℂ) (C:ℝ):Prop:=0≤C ∧ ∀ i:A,(∑ j, ‖orderR f g X i j‖) ≤ C
abbrev attends (f:A→ℝ)(g:B→ℝ)(i:A) : (A→ B→ℂ) →L[ℝ] Alg B:= LinearMap.toContinuousLinearMap {
    toFun:=fun x=>changeVars (orderR f g x) (atom i),map_add':=fun x y=>by simp only [change_atom,orderR,Pi.add_apply,mul_add,add_smul,sum_add_distrib],map_smul':=fun r x=>by simp only [change_atom,orderR,Pi.smul_apply, mul_smul_comm,RingHom.id_apply,Finset.smul_sum]; exact sum_congr rfl fun j _=> smul_assoc .. }
namespace SeatD
variable (f:A→ℝ)(g:B→ℝ)(X Y:A→B→ℂ)(δ ε:ℝ)
lemma from_weights(hf:∀ i,0<f i)(hg:∀ j,0 ≤ g j) : SeatD f g X δ ↔ 0≤δ ∧ ∀ i, (∑ j,g j*‖X i j‖) ≤ δ*f i:=by
    unfold SeatD; suffices h:∀ i,(∑ j, ‖orderR f g X i j‖) ≤ δ ↔ (∑ j,g j*‖X i j‖) ≤δ*f i by simp_rw [h]
    intro i; unfold orderR; simp_rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hf i).le,Real.norm_of_nonneg (hg _),mul_assoc]; rw [← Finset.mul_sum,inv_mul_le_iff₀ (hf i),mul_comm (f i)]
lemma additive (h:SeatD f g X δ) (he:SeatD f g Y ε): SeatD f g (X+Y) (δ+ε):=by
   refine ⟨add_nonneg h.1 he.1,fun i=>?_⟩; apply le_trans _ (add_le_add (h.2 i) (he.2 i)); rw [← Finset.sum_add_distrib]; refine sum_le_sum fun j _=>?_ ; simp_rw [orderR,Pi.add_apply,mul_add]; exact norm_add_le ..
lemma scaledR (h:SeatD f g X δ)(p:ℝ): SeatD f g (p • X) (‖p‖*δ):=by
   refine ⟨mul_nonneg (norm_nonneg _) h.1,fun i=>?_⟩; apply le_trans _ (mul_le_mul_of_nonneg_left (h.2 i) (norm_nonneg p)); rw [Finset.mul_sum]; unfold orderR; simp only [Pi.smul_apply,mul_smul_comm,norm_smul]; rfl
lemma bills (p:E→A→B→ℂ)(t:E→ℝ)(I: Finset E)(h:∀ i∈I,SeatD f g (p i) (t i)): SeatD f g (∑ i∈I,p i) (∑ i∈I,t i):=by
   induction I using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty]; exact ⟨le_rfl,fun i=>by simp [orderR]⟩
   | insert i I hi ih=> rw [sum_insert hi,sum_insert hi]; exact additive _ _ _ _ _ _ (h i (by simp)) (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma less (h:SeatD f g X δ)(hh:δ≤ε): SeatD f g X ε:=⟨h.1.trans hh,fun i=>(h.2 i).trans hh⟩
lemma pays(i:A)(h:SeatD f g X δ): ‖attends f g i X‖ ≤ δ:= (atom_price ..).trans (h.2 i)
end SeatD

variable [NormedAddCommGroup E][NormedSpace ℝ E]
lemma lin_ember [NormedAddCommGroup X][NormedSpace ℝ X] (i:E→L[ℝ]X) {a:ℝ}(h:‖i‖ ≤ a): Ember n i a:=by
    refine ⟨i.contDiff.contDiffAt,(norm_nonneg _).trans h,fun j hj=>?_⟩; by_cases hx:j≤1; · interval_cases j <;> simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one,i.fderiv,map_zero,norm_zero]; exact (norm_nonneg _).trans h; exact h
    have he := Push.Uniform.allows_linear (n:=n) h (x:=(0:E)) (show ‖i 0‖ ≤ a by rw [map_zero,norm_zero]; exact (norm_nonneg _).trans h); exact he.norm_le _ hj
lemma affine_panel (f:A→ℝ)(g:B→ℝ)(X:A→B→ℂ)(Z:E→L[ℝ] (A→B→ℂ))(C M:ℝ)(hp:SeatD f g X C)(hv:∀ i,SeatD f g (Z i) (M*‖i‖))(hM:0≤M)[DecidableEq A] : Ember n (fun t=>banner (orderR f g (X+Z t)) d) ((2^n*(C+M))^d):=by
   refine behaved _ _ (add_nonneg hp.1 hM) (fun j=> ?_)
   let W:=attends f g j; have hx:=SeatD.pays _ _ _ _ j hp
   change Ember n (fun t=>W (X+Z t)) _; simp_rw [map_add]; change Ember n ((fun _=>W X)+fun t=>W (Z t)) _; exact Ember.join (Ember.weakening (Ember.constant _ _) hx) (lin_ember (W.comp Z) (ContinuousLinearMap.opNorm_le_bound _ hM fun i=> SeatD.pays _ _ _ _ _ (hv i)))
end Pipes
end YM.Massive.Poised
