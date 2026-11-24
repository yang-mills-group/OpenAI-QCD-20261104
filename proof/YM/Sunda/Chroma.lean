import YM.Sunda.Genre
set_option maxHeartbeats 610000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Set Tensor Analysis MeasureTheory QCD QCD.Lat Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny MassiveTwoEstimates Mako Lobo SpinReflection
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker ComplexOrder
abbrev orient (p:EuPin): ℝ:= LinearMap.det (p.coord.motion.toLinearEquiv.toLinearMap)
def omen(p:EuPin):Prop:= p.matrix.val*g5= ((orient p:ℂ) • g5)*p.matrix.val
@[simp]lemma orient_one:orient 1=1:=by unfold orient; rw[show _root_.LinearEquiv.toLinearMap (Ortho.motion (EuPin.coord 1)).toLinearEquiv=(1: Module.End ℝ E4) from LinearMap.ext fun x=> Ortho.move_one x,map_one]
lemma omen_one : omen 1:=by unfold omen; rw [orient_one,Complex.ofReal_one,one_smul]; change 1*_=g5*1; simp
@[simp]lemma orient_mul(p q:EuPin):orient (p*q)=orient p* orient q:=by unfold orient; rw [show _root_.LinearEquiv.toLinearMap (Ortho.motion (EuPin.coord (p*q))).toLinearEquiv=(p.coord.motion.toLinearEquiv.toLinearMap*q.coord.motion.toLinearEquiv.toLinearMap : Module.End ℝ E4) from LinearMap.ext fun x=> Ortho.move_mul ..,map_mul]
lemma omen_mul(p q:EuPin)(hp:omen p)(hq:omen q):omen (p*q):=by
      change p.matrix.val*q.matrix.val*g5=((orient (p*q):ℂ) • g5)*(p.matrix.val*q.matrix.val); rw [mul_assoc, show q.matrix.val*g5=_ from hq, ←mul_assoc p.matrix.val, mul_smul_comm,show p.matrix.val*g5=_ from hp, orient_mul,Complex.ofReal_mul,mul_smul]; simp only[smul_mul_assoc,smul_smul,mul_assoc]; rw [mul_comm (↑(orient q):ℂ)]
lemma coronal (A: Ortho):∃ p:EuPin,p.coord=A∧ omen p:=by
      have h(v:E4):∃ p:EuPin,omen p∧∀ x:E4,Ortho.move p.coord x= hyper v x:=by
            by_cases hn:v=0
            · subst v; refine ⟨1,omen_one,fun x=>?_⟩; change Ortho.move 1 x=_; rw [Ortho.move_one,hyper,Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]; simp
            let u:=‖v‖⁻¹ • v; have hu:‖u‖=1:=by simp[u,norm_smul,hn]
            have hz: u≠0:= norm_ne_zero_iff.mp (hu.symm ▸ one_ne_zero)
            obtain ⟨p,hp,hv⟩:= unitMirror hu; have he: orient p = -1:=by unfold orient; rw [show p.coord.motion=hyper u from LinearIsometryEquiv.ext hv]; change LinearMap.det (ℝ ∙ u)ᗮ.reflection.toLinearMap= _; rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hz, pow_one]
            have sp : ℝ ∙ u=ℝ ∙ v:= Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hn))) v
            refine ⟨p,?_,fun x=> (hv x).trans (congr_arg (fun V: Submodule ℝ E4=> Vᗮ.reflection x) sp)⟩
            unfold omen; rw [he,hp,blade,Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul,neg_mul,smul_mul_assoc,mul_smul_comm]; simp only [← smul_neg]; have hx: g5 * slash u= -(slash u*g5):=by rw [SpinClifford.fiveSlash,neg_neg]
            rw [← mul_assoc g5,hx,neg_mul,neg_neg]
      have chain(l:List E4):∃ p:EuPin,omen p ∧ ∀ x:E4,Ortho.move p.coord x=(l.map hyper).prod x:=by
            induction l with
            | nil=>exact ⟨1,omen_one,fun x=> Ortho.move_one x⟩
            | cons x l ih=> obtain ⟨p,hp,hx⟩:= h x; obtain ⟨v,hv,ht⟩:= ih; refine ⟨p*v,omen_mul p v hp hv,fun y=>?_⟩; rw[show (p*v).coord=p.coord*v.coord from rfl, Ortho.move_mul,hx,ht]; rfl
      obtain ⟨l,-,hl⟩:= (Ortho.motion A).reflections_generate_dim; obtain ⟨p,hp,hx⟩:= chain l; exact ⟨p,Ortho.ext _ _ (fun x=> (hx _).trans (congr_arg (fun f:E4≃ₗᵢ[ℝ] E4=> f x) hl).symm),hp⟩
lemma corona (p:EuPin): omen p:=by
       obtain ⟨q,hq,h⟩:= coronal p.coord; have he:orient q=orient p:=by unfold orient; rw [hq]
       rcases SpinGeometry.geometry.euFiber p q hq.symm with rfl|hX; · exact h
       unfold omen; rw [hX,Units.val_neg,neg_mul,mul_neg,←he]; exact congr_arg Neg.neg h
lemma violet (p:EuPin): Oriole.conjug p g5=(orient p:ℂ) • g5:=by
       unfold Oriole.conjug; rw [show p.matrix.val*g5= _ from corona p,mul_assoc,show p.matrix.val*p.matrix⁻¹.val=1 from p.matrix.val_inv,mul_one]
lemma orientV(p:EuPin):orient p*orient p=1:=by
       -- use g5^2
       apply Complex.ofReal_injective; rw [Complex.ofReal_mul,Complex.ofReal_one]; have he: g5*g5=(1:Spike):=g5_sq; let M:ℂ:= (orient p:ℂ)
       have ht : (M*M) • (1:Spike)=1:=by rw [← he, ← smul_mul_smul_comm, ← violet, ← Oriole.L_up,he]; unfold Oriole.conjug; rw [mul_one]; exact p.matrix.val_inv
       have hv:= congr_fun (congr_fun ht (0,0)) (0,0); simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,mul_one] using hv
lemma violet_path(k:Tri)(t:ℝ): orient (pathW k t)=1:=by rw[show pathW k t= pathW k (t/2)* pathW k (t/2) from by nth_rw 1[← add_halves t]; exact SpinParity.additive (treks k) ..,orient_mul,orientV]
end YM.Sunda
#print axioms YM.Sunda.violet_path
#print axioms YM.Sunda.violet
