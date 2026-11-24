import YM.Massive.Ribbon.Charge
/-! # Spin stencil permutation widths and axis faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass TensorProduct MvPolynomial
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d:ℕ}(s:Signed)(i j a:Multi d)(y:Axis){p:EuPin}
local notation "T" => SpinMode d

def hem : Multi d := ⟨fun z=>i.val (s.perm.symm z),by
                            convert i.property using 1; exact Equiv.sum_comp s.perm.symm (fun x=>power i x)⟩ -- bad indent
lemma hemming : power (hem s i) y=power i (s.perm.symm y):=rfl
@[simp] lemma pinned : power (hem s i) (s.perm y)=power i y:=by rw [hemming,Equiv.symm_apply_apply]
lemma borderBuck : spinWeight (hem s i)=spinWeight i:=by unfold spinWeight; congr 2; unfold UV.order; simp_rw [hemming]; exact Equiv.sum_comp s.perm.symm _
lemma hem_back : hem s⁻¹ (hem s i)=i:=by apply Subtype.ext; funext y; apply Fin.ext; change power (hem ..) y =power i y; rw [hemming,hemming,Signed.inv_perm,Equiv.symm_symm,Equiv.symm_apply_apply]
lemma hem_inv : hem s (hem s⁻¹ i)=i:=by convert hem_back s⁻¹ i using 2; group
lemma hem_mul (t:Signed): hem (s*t) i=hem s (hem t i):=rfl
noncomputable def Hem (d:ℕ): Multi d≃Multi d:=⟨hem s,hem s⁻¹,hem_back s,hem_inv s⟩
def signT(s:Signed)(y:Axis):ℝ:=if s.flip y then -1 else 1
lemma sign_sq : signT s y * signT s y=1:=by unfold signT; split <;> ring
def marked (s:Signed)(i:Multi d):ℝ:=∏ a:Axis,(signT s a)^power i a
lemma marked_sq : marked s i * marked s i=1:=by unfold marked; rw [← prod_mul_distrib]; simp_rw [← mul_pow,sign_sq]; simp
@[simp] lemma marked_root (d:ℕ) : marked s (0:Multi d)=1:=by have h(a:Axis):power (0:Multi d) a=0:=rfl; simp [marked,h]
lemma inv_sign : signT s⁻¹ y=signT s (s.perm.symm y):=rfl
lemma back_mark : marked s⁻¹ (hem s i)=marked s i:=by unfold marked; simp_rw [inv_sign,hemming]; exact Equiv.prod_comp s.perm.symm (fun y=>signT s y ^ power i y)
lemma pinHem (a:Axis): hem (Signed.mirror a) i=i:=rfl
lemma pinMark (a:Axis) : marked (Signed.mirror a) i=(-1:ℝ)^power i a:=by unfold marked; rw [prod_eq_single a]; simp [signT,Signed.mirror]; intro y _ h; simp [signT,Signed.mirror,Ne.symm h]; simp
lemma sign_at (x: Cover)(a:Axis) : ((s.act x (s.perm a):ℤ):ℝ)=signT s a*x a:=by rw [Signed.act_at]; cases h:s.flip a <;> simp [signT,h]
lemma signFrame (h:p.Lifts s) : stencilFrame p y = C (signT s y:ℂ)*X (s.perm y):=by
   unfold stencilFrame; rw [show p.coord=s.ortho from h]; rw [sum_eq_single (s.perm y)]; simp [Signed.ortho,Signed.matrix_at,signT]; intro a _ h; rw [show s.ortho.val a y=0 from by simp [Signed.ortho,Signed.matrix_at,Ne.symm h]]; simp; simp
lemma glidePoly (h:p.Lifts s) : changeP p (walk i)=(marked s i:ℂ) • walk (hem s i):=by
    rw [modulated, walking, ← C_mul']; unfold marked; rw [Complex.ofReal_prod, map_prod]; conv_rhs=> rhs; rw [← Equiv.prod_comp s.perm]
    rw [←prod_mul_distrib]; apply prod_congr rfl; intro a _; rw [pinned,signFrame s _ h, mul_pow, Complex.ofReal_pow,map_pow] 
lemma readHem (h:p.Lifts s) : multiMove p i j= if hem s i=j then (marked s i:ℂ) else 0:=by rw [modal,glidePoly s i h,walk,coeff_smul, coeff_monomial]; simp only [token_eq]; split <;> simp_all
lemma hem_turn (h:p.Lifts (Signed.mirror y))(S:Spike) : flipTable (d:=d) y S= UV.turned p (wave S):=by
    ext i j; unfold flipTable spinTable UV.turned; simp_rw [Matrix.of_apply, readHem _ _ _ h, pinHem, pinMark, Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]; by_cases hv:i.2=j.2 <;> by_cases he:i.1.1=j.1.1 <;> simp [hv,he]
end YM.Massive.UV
#print axioms YM.Massive.UV.hem_turn
