import YM.QCD.Raft.Tide

/-! # one-color channel and real Hessian accounting. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Lat Fog Stationary Eyrie Quarry Tavern Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace
variable {c f n:Side}{a:su.Color}

def career (n:Side)(k:ℕ)(x:su.Color): form k n→ₗ[ℝ] (Lines su n k→ℝ):=LinearMap.pi (fun d=>(x d.2.2:ℝ) • (LinearMap.proj (d.1,d.2.1)))
lemma career_apply (k:ℕ) (x:su.Color)(v:form k n)(p:Lines su n k):career n k x v p=x p.2.2 * v (p.1,p.2.1):=rfl
lemma colored_G (x: su.Color)(t:form 0 n): career n 1 x (Exterior.d 0 n *ᵥ t)=gradientA su n (career n 0 x t):=by
  funext i; rcases i with ⟨i,d,j⟩; obtain ⟨d,rfl⟩:=axisEquiv.surjective d
  rw [career_apply,show axisEquiv d=coord d from rfl, d_sites]; simp only [gradientA,LinearMap.pi_apply,LinearMap.sub_apply,show axisEquiv.symm (coord d)=d from axisEquiv.symm_apply_apply _,LinearMap.proj_apply,career_apply]; ring

-- form ellipse from score
def pairR (a:su.Color)(P:Cnr n→ℝ): form 1 n→ₗ[ℝ] form 1 n→ₗ[ℝ] ℝ :=
  let L:= fderiv ℝ (fderiv ℝ P) 0; let F:= career n 1 a
  let G x: form 1 n→ₗ[ℝ] ℝ:= (L (F x)).toLinearMap ∘ₗ F
  { toFun:=G,map_add':=fun i j=>LinearMap.ext fun q=>by simp [G],map_smul':=fun c i=>LinearMap.ext fun q=>by simp [G] }
lemma pairR_eval (a:su.Color)(T:Cnr n→ℝ)(x y:form 1 n)(h:ContDiffAt ℝ ω T 0):pairR a T x y=Jacobi.mixed (career n 1 a x) (career n 1 a y) T 0:=by rw [iter _ _ h, iteratedFDeriv_two_apply]; rfl
-- complexification conjugating second entry
variable (J:form 1 n→ₗ[ℝ] form 1 n→ₗ[ℝ] ℝ)
def pchain (x y:Lens n):ℂ:= ⟨J (vision x) (vision y)+J (desire x) (desire y), J (desire x) (vision y)-J (vision x) (desire y)⟩
variable {I:Type}
lemma vis_jump(z y:I→ℂ):vision (z+y)=vision z+vision y:=rfl
lemma joy_jump(z y:I→ℂ):desire (z+y)=desire z+desire y:=rfl
lemma vis_up (c:ℂ)(z:I→ℂ):vision (c • z)= c.re • vision z-c.im • desire z:=rfl
lemma joy_up (c:ℂ)(z:I→ℂ):desire (c • z)= c.re • desire z+c.im • vision z:=rfl
lemma vis_star(z:I→ℂ):vision (star z)=vision z:=rfl
lemma joy_star(z:I→ℂ):desire (star z)=-desire z:=rfl
lemma pchain_add(x y z:Lens n):pchain J (x+y) z=pchain J x z+pchain J y z:=by
  unfold pchain; rw [vis_jump,joy_jump]; apply Complex.ext <;> simp <;> ring
lemma pchain_add'(x y z:Lens n):pchain J x (y+z)=pchain J x y+pchain J x z:=by unfold pchain; rw [vis_jump,joy_jump]; apply Complex.ext <;> simp <;> ring
lemma pcD (c:ℂ)(x y:Lens n):pchain J (c • x) y=c*pchain J x y:=by unfold pchain; rw [vis_up,joy_up]; apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
lemma pcV (c:ℂ)(x y:Lens n):pchain J x (c • y)=star c *pchain J x y:=by unfold pchain; rw [vis_up,joy_up]; apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
lemma chain_sum (x:I→Lens n)(s:Finset I)(y:Lens n):pchain J (∑ i∈s,x i) y=∑ i∈s,pchain J (x i) y:=by induction s using Finset.induction_on with| empty=>simpa only [sum_empty,show pchain J 0 y=0 by rw [← zero_smul ℂ (0: Lens n), pcD, zero_mul]]| insert i s h hv=>rw [sum_insert h,pchain_add,hv,sum_insert h]
lemma chain_sum' (x:I→Lens n)(s:Finset I)(y:Lens n):pchain J y (∑ i∈s,x i)=∑ i∈s,pchain J y (x i):=by induction s using Finset.induction_on with| empty=>simp only [sum_empty,show pchain J y 0=0 by rw [← zero_smul ℂ (0: Lens n), pcV,star_zero,zero_mul]]| insert i s h hv=>rw [sum_insert h,pchain_add',hv,sum_insert h]
lemma symmetricP (T:Cnr n→ℝ)(hp:ContDiffAt ℝ ω T 0)(v w:form 1 n)(a:su.Color) : pairR a T v w = pairR a T w v:=hp.isSymmSndFDerivAt (by norm_num) ..
lemma coherent (T:Cnr n→ℝ)(hp:ContDiffAt ℝ ω T 0)(v w: Lens n)(a:su.Color):star (pchain (pairR a T) v w)= pchain (pairR a T) w v:=by
  unfold pchain; apply Complex.ext
  · change _+_= _+_; exact congr_arg₂ (·+·) (symmetricP T hp ..) (symmetricP T hp ..)
  change -(_-_)= _-_; rw [neg_sub]; exact congr_arg₂ (·-·) (symmetricP T hp ..) (symmetricP T hp ..)
end YM.QCD.Raft
