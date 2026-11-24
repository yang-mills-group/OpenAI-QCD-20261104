import YM.TorusPCAC.Jet.Scope

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# All off-shell flavor bilinears, arbitrary legs at the same color cell

Use ordinary unweighted jets through any requested horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius

lemma spin_map_slot (g : Letter→Raw) (F : Bos→ₐ[ℂ] Bos) (l : Letter) :
    Algebra.TensorProduct.map F (spinMap g) (slot l)= (1:Bos)⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ (g l):=by
  unfold slot spinMap point; simp only [Algebra.TensorProduct.map_tmul, map_one, ExteriorAlgebra.map_apply_ι]; simp

variable (i j : Flav) (u v : Pinor) (k l : Hue) (a b : Order)
def deg (a : Order) := ∑ i, a i
def load (a b : Order) : ℕ:= 6+2*(deg a+deg b)
def element : Pol:=rim i u k a*leg j v l b
lemma element_cap : element i j u v k l a b∈cap (load a b):=by
  have h:= scope_mul (canSlot ⟨.row,i,u,k,a⟩) (canSlot ⟨.col,j,v,l,b⟩)
  exact (show spinOrder ⟨.row,i,u,k,a⟩+spinOrder ⟨.col,j,v,l,b⟩=load a b from by simp [load,deg,spinOrder]; omega) ▸ h

def duo (u : Pinor) (v : Pinor) := ∑ k : Hue,element i j u v k k a b
-- bind order inspect

def withColor (l : Letter) (i : Hue) : Letter:= {l with color:=i}
lemma paintL (g : su.El) : paint g (leg i u k a)=∑ l : Hue,su.mat g k l • leg i u l a:=by
  unfold leg paint; rw [spin_map_slot]; simp only [↓reduceIte,map_sum,map_smul]; simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]; rfl
lemma paintR (g : su.El) : paint g (rim i u k a)=∑ l : Hue,su.mat g⁻¹ l k • rim i u l a:=by
  unfold rim paint; rw [spin_map_slot]; simp only [reduceCtorEq,↓reduceIte,map_sum,map_smul]; simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul]; rfl
lemma paint_eval (g : su.El) : paint g (duo i j a b u v)=duo i j a b u v:=by
  let f:=su.mat g; let f':=su.mat g⁻¹; unfold duo; simp only [element,map_sum,map_mul,paintL,paintR]
  -- ∑ k, ∑ l,r f' l k * f k r * pol; commute k l r; delta
  let E (x y:Hue):=rim i u x a*leg j v y b
  have he (x y: Hue) : ∑ k : Hue,f' x k*f k y=(1:Mat) x y:=by have hv:= show f'*f=1 from (su.mat_mul g⁻¹ g).symm.trans (by rw [inv_mul_cancel,su.mat_one]); exact Matrix.ext_iff.mpr hv x y
  simp_rw [sum_mul,mul_sum,mul_smul_comm,smul_mul_assoc, smul_smul]
  rw [sum_comm]
  apply Eq.trans (b:=∑ x : Hue, ∑ y : Hue,(∑ k : Hue,f' x k*f k y) • E x y)
  · simp_rw [sum_smul, mul_comm (su.mat g _ _)]; refine sum_congr rfl fun _ _=>?_ ; exact sum_comm
  simp_rw [he,Matrix.one_apply,ite_smul]; simp; rfl

lemma duo_mem : duo i j a b u v∈ admitted (load a b) := ⟨Submodule.sum_mem _ (fun k _=> element_cap i j u v k k a b), (paint_fixed _).2 (fun _=> paint_eval ..)⟩

def crowd : Spike →ₗ[ℂ] Pol where
  toFun A:= ∑ u, ∑ v, A u v • duo i j a b u v
  map_add' A B:=by simp [add_smul,sum_add_distrib]
  map_smul' A B:=by simp only [Matrix.smul_apply,smul_eq_mul,mul_smul,smul_sum]; rfl
lemma crowd_mem (A : Spike) : crowd i j a b A ∈ admitted (load a b):=by
  dsimp only [crowd,LinearMap.coe_mk,AddHom.coe_mk]; exact Submodule.sum_mem (admitted _) (fun k _=> Submodule.sum_mem _ fun x _=> Submodule.smul_mem _ _ (duo_mem i j k x a b))
lemma plain0 (A : Spike) : crowd i j 0 0 A=bilinear i j A:=by simp only [bilinear,crowd,duo,LinearMap.coe_mk,AddHom.coe_mk,smul_sum]; rfl

/-- vector flavor actions, eigenvalues complex -/
def axialPhase (z : FlavorGroup) (l : Letter) := if l.kind=.col then (z l.flavor:ℂ) else (z l.flavor :ℂ)⁻¹
lemma phase (z : FlavorGroup) (l : Letter) : flavor z (slot l)=axialPhase z l • slot l:=by
  rw [flavor,spin_map_slot]; unfold slot axialPhase; cases em (l.kind= .col) <;> simp [*]
lemma phase_val (z : FlavorGroup) : flavor z (element i j u v k l a b)=((z i:ℂ)⁻¹*(z j:ℂ)) • element i j u v k l a b:=by unfold element rim leg; rw [map_mul,phase,phase,smul_mul_smul_comm]; rfl
lemma flavor_crowd (z : FlavorGroup) (A : Spike) : flavor z (crowd i j a b A)= ((z i:ℂ)⁻¹*(z j:ℂ)) • crowd i j a b A:=by simp only [crowd,duo,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,phase_val,smul_comm _ ((z i:ℂ)⁻¹*(z j:ℂ)),smul_sum]
end YM.TorusPCAC.Jet

#print axioms YM.TorusPCAC.Jet.flavor_crowd
