import YM.DawnS.Saga

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder ENNReal
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "η"=> sigL (d:=d) r
local notation "T"=> Vault d
local notation "S"=> expandVt (d:=d)
noncomputable def hLines(d:ℕ): Seed (Vault d)→ₗ[ℂ] beam d:=(thetaBasis _).constr ℂ lantern
                                                  -- better
lemma exp_v (c:T→ℂ): hLines d c=expandVt c:=by
     calc
       _= hLines d (∑ i:T, (thetaBasis T).repr c i • thetaBasis T i):=congr_arg _ ((thetaBasis T).sum_repr c).symm
       _= _:=by rw[map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw[map_smul, show hLines d (thetaBasis _ i)=_ from Module.Basis.constr_basis ..]; simp[thetaBasis]
noncomputable def hank (d:ℕ)(r:ℝ):Matrix (Vault d) (Vault d) ℂ:= Matrix.of fun i j=> sigL r (lantern i) (lantern j)
lemma quadratic (g p:T→ℂ): η (S g) (S p)=star g ⬝ᵥ (Matrix.mulVec (hank d r) p):=by
     unfold expandVt; simp only[map_sum,map_smul,map_smulₛₗ,LinearMap.sum_apply,LinearMap.smul_apply,Matrix.mulVec, dotProduct]; simp_rw [Finset.smul_sum,Finset.mul_sum]; rw [sum_comm]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; change p j*(star (g i)*_)=star (g i)*(η (lantern i) (lantern j)*p j); ring -- actually need distribute g outer or p? see trace
include hr
lemma inthe (w p:Seed T): star (η (S w) (S p))=η (S p) (S w):=by
     let V:= ((η).comp (hLines d)).compl₂ (hLines d)
     have hu(p:Seed T) : 0≤ V p p:= by
          by_cases h:p=0; · rw [h,map_zero]
          change 0≤η (hLines _ p) (hLines _ p); rw[exp_v]; exact (heartbeat r hr p h).le
     have h:star (V w p)=V p w:=by
           have hf(g): (V g g).im=0:= ((hu g).2.symm.trans Complex.zero_im) -- ≤ def?
           have he:= hf (w+p); have hb:= hf (w+Complex.I • p); rw [map_add] at he hb; simp only [LinearMap.add_apply,map_add, Complex.add_im,hf,add_zero,zero_add] at he hb; simp only [map_smulₛₗ,map_smul,LinearMap.smul_apply,LinearMap.coe_comp,starRingEnd_apply] at hb -- probe
           apply Complex.ext<;> simp at hb ⊢<;> linarith
     simp_rw[←exp_v] -- change
     exact h
lemma hand : (hank d r).PosDef:=by
     apply Matrix.posDef_iff_dotProduct_mulVec.mpr; refine ⟨Matrix.IsHermitian.ext (fun i j=>?_),fun p hp=> (heartbeat r hr p hp).trans_eq (quadratic _ _ _)⟩
     let V:= thetaBasis T; have h(i:T) : expandVt (V i)=lantern i:=by rw [← exp_v]; exact Module.Basis.constr_basis ..
     have he:= inthe r hr (V j) (V i); rw [h,h] at he; exact he
-- orthonormal generating columns. Basis need spans quotient.W.
open scoped MatrixOrder
lemma ample (d:ℕ):∃ C:Matrix (Vault d) (Vault d) ℂ, IsUnit C ∧ Cᴴ*(hank d r)*C=1:=by
    have hv:= hand (d:=d) r hr; obtain ⟨R,hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hv.posSemidef.nonneg
    have he:IsUnit R:=by
         have he:=hv.isUnit; rw [hR,Matrix.isUnit_iff_isUnit_det,Matrix.det_mul,IsUnit.mul_iff] at he; exact (Matrix.isUnit_iff_isUnit_det R).mpr he.2
    let L:= he.unit⁻¹; have hf:R*L.val=1:= he.unit.mul_inv
    refine ⟨↑L,L.isUnit,?_⟩; rw [hR]; simp_rw[Matrix.star_eq_conjTranspose]; rw[mul_assoc,Matrix.mul_assoc,show R*↑L=1 from hf,mul_one,← Matrix.conjTranspose_mul,hf,Matrix.conjTranspose_one]
end YM.DawnS
