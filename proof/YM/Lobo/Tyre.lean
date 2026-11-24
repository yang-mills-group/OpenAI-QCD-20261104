import YM.Lobo.Curl
set_option maxHeartbeats 560000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable (K:EuPin)(a:Axis)(p:Multi 8){d:ℕ}
lemma trek(d:ℕ) : token (0:Multi d)=0:=by ext i; rw [token_act]; rfl
lemma wax(d:ℕ): UV.walk (0:Multi d)=1:=by rw[UV.walk,trek]; rfl
lemma mar (p:Multi d):multiMove K (0:Multi d) p= if p=0 then 1 else 0:=by
     rw [modal,wax,map_one, ←wax d]; simp only[UV.walk, MvPolynomial.coeff_monomial]; simp only [token_eq]; simp only [eq_comm]
open Massive.Patria.Gall.Seals
lemma sprays (a:Axis): token (UV.first a)= Finsupp.single a 1:=by
     ext1 i; rw[token_act]; unfold UV.first power; by_cases h:a=i <;> simp [h,Pi.single_apply]
lemma stilts : multiMove K (UV.first a) p=∑ i:Axis,(↑(K.coord.val i a):ℂ) * if UV.first i=p then 1 else 0:=by
     rw [modal,show walk (UV.first a)= MvPolynomial.X a from (by rw [UV.walk,sprays]; rfl),changeP,MvPolynomial.aeval_X,stencilFrame,MvPolynomial.coeff_sum]; refine sum_congr rfl fun i _=>?_ ; rw [MvPolynomial.coeff_C_mul, MvPolynomial.X,←sprays, MvPolynomial.coeff_monomial]; simp only [token_eq]
lemma lift_on {X:Type}[AddCommGroup X][Module ℂ X] (f:Multi 8→X) : ∑ p:Multi 8,multiMove K (UV.first a) p • f p= ∑ i:Axis,(↑(K.coord.val i a):ℂ) • f (UV.first i):=by
     simp_rw [stilts K a,Finset.sum_smul]; rw[sum_comm]; apply sum_congr rfl; intro i _; rw [sum_eq_single (UV.first i)]; · rw[if_pos rfl,mul_one]
     · intro p _ h; rw [if_neg h.symm,mul_zero,zero_smul]
     simp
-- slash transformations formula
lemma tarG (K:EuPin) : Oriole.conjug K (gamma a)=∑ i:Axis,(↑(K.coord.val i a):ℂ) • gamma i:=by
     have h:= (euPin_iff _ |>.1 K.property).2 (basis a); have hh:slash (basis a)=gamma a:=by simp [Massive.slash, apply_ite, ite_smul]
     rw[hh] at h; unfold Oriole.conjug; change (K.matrix.val*gamma a)*_= _; rw [show K.matrix.val*gamma a= _ from (h: K.matrix.val * gamma a= Massive.slash (Ortho.move K.coord (basis a)) * K.matrix.val),mul_assoc, show K.val.2.val*K.matrix⁻¹.val=1 from K.matrix.val_inv,mul_one]
     change Massive.slash (Ortho.move K.coord (basis a))=_; refine sum_congr rfl fun i _=>?_ ; rw [show Ortho.move K.coord (basis a) i=K.coord.val i a from M4.move_basis ..]
end YM.Lobo
#print axioms YM.Lobo.lift_on
#print axioms YM.Lobo.mar
#print axioms YM.Lobo.tarG
