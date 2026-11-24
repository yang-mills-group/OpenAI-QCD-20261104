import YM.Tarn.Poppy
import YM.Elms.Shake
/-! The double cover central character, and flavor continuity on all finite representatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn
open Function QCD QCD.Lat Wilson Patria Patria.Depth Patria.Hub Lattice Cylinder Dispersed Fir YM.Fir UV Filter Set TensorProduct
open Poised Poised.Plans Poised.Plans.Stamp QCD.Grass
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius TensorProduct
variable {C:Sequence} {P:Calibration C} {n:ℕ} {Q:Choir}
namespace Pollens
private lemma negG(p:EuPin)(hp:p.coord=1)(d:ℕ): turned (d:=d) p (wave (-1))= -(1:Matrix (SpinMode d) (SpinMode d) ℂ):=by
    have hv: trM d p=1:=by rw [← row_id]; ext i j; rw [tr_at,tr_at]; unfold multiMove; rw [hp]; rfl
    have he: wave (-1)= -(wave 1):=by ext i j; change (- (1:Spike)) i.1 j.1*_= -( (wave 1) i j); exact neg_mul _ _
    rw [he]; have hV: turned p (-(wave 1))= -(turned (d:=d) p (wave 1)):=by ext i j; by_cases h:i.2=j.2 <;> simp [UV.turned,h]
    rw [hV,wave_one]; rw [show turned p (1:Bundle)=turned (d:=d) 1 1 from ?_, cool]; rw [ribbon,ribbon,hv,row_id] -- namespace
private lemma ropes(d:ℕ): adapter (- (1:Matrix (SpinMode d) (SpinMode d) ℂ)) (-1)= Grass.grade:=by
     apply Grass.ext_atoms; rintro (i|i)
     · rw [grade_atom]; change adapter _ _ (psi i)=_; rw [adapt_psi]; simp [Matrix.one_apply]
     rw [grade_atom]; change adapter _ _ (bar i)=_; rw[adapt_bar]; simp [Matrix.one_apply]
private lemma coreP(pl:EuPin)(hp:pl.coord=1)(hv:pl.matrix= -1)(d:ℕ) (x: Label d) : P.sym.pin d pl x= P.sym.parity _ x:=by
    have hu (y: SpinPol d): twistPins _ pl y=Grass.grade y:=by
         unfold twistPins; rw [show pl.matrix⁻¹.val = -1 from ?_, show pl.matrix.val.transpose = -1 from ?_, negG pl hp, ropes]
         · simp [hv]
         simp [hv]
    have he (q:Pol d): pinAct pl q=parityAct q:=by
         induction q using TensorProduct.induction_on with
         | zero=> simp
         | add _ _ hx hy=> simp only [map_add,hx,hy]
         | tmul x y=> unfold pinAct parityAct; simp_rw [TensorProduct.map_tmul,hp]; exact congr_arg₂ (tmul ℂ) (burns _) (hu y)
    apply Subtype.ext; rw [RawSym.pinActs,RawSym.parityActs,he]
variable (T: Pollens P Q) (hQ:Q.Domestic)
include hQ
lemma signs (p:EuPin)(hp:p.coord=1)(hv:p.matrix= -1): T.spin p=T.parity :=by
    ext1 u; obtain ⟨d,x,H⟩:= hQ.tidal u none; rw [←H,T.w p 1 ((show p.coord=Signed.inclusionO _ from hp.trans (map_one Signed.inclusionO).symm)),T.p,coreP p hp hv]; rfl
omit hQ in
lemma glacial (d:ℕ)(v:Label d):Continuous fun u:FlavorTorus=> P.sym.flavor d u v:=by
    let X:Label d→ₗ[ℂ] Pol d:= (labels d).subtype; obtain ⟨L,hL⟩:= X.exists_leftInverse_of_injective ((labels d).ker_subtype)
    have h(y:Pol d):Continuous fun u:FlavorTorus=> L (flavorAct u y):=by
        induction y using TensorProduct.induction_on with
        | zero=> simp [continuous_const]
        | add a b ha hb=> simp only [map_add]; exact ha.add hb
        | tmul a b=>
             let p(u:FlavorTorus):= byFlavor u (f:=(Prod.snd (α:=Multi d× Lat.Fiber))); let F(u:FlavorTorus):= Matrix.fromBlocks (p u) 0 0 (p u⁻¹)
             let A:= L.comp (TensorProduct.mk ℂ GPol (SpinPol d) a); change Continuous fun u=> A (changeVars (F u) b); refine A.continuous_of_finiteDimensional.comp (Elm.SparK.Arbor.Civic.continuous_adapt _ F ?_ _ continuous_const); rintro (i|i) (j|j); rotate_left
             · exact continuous_const
             · exact continuous_const
             · change Continuous fun u: FlavorTorus=> p u⁻¹ i j; by_cases h:i=j; · subst j; simp only [p,byFlavor,Matrix.diagonal_apply_eq]; change Continuous fun u:FlavorTorus=> star ((u i.2).val); fun_prop
               simp only[p,byFlavor,Matrix.diagonal_apply_ne _ h]; exact continuous_const
             change Continuous fun u: FlavorTorus=> p u i j; by_cases h:i=j; · subst j; simp only [p,byFlavor,Matrix.diagonal_apply_eq]; fun_prop
             simp only [p,byFlavor,Matrix.diagonal_apply_ne _ h]; exact continuous_const
    have hp(u: FlavorTorus): L (flavorAct u v.val) = P.sym.flavor d u v:=by rw [← P.sym.flavorActs]; exact DFunLike.congr_fun hL _
    exact (funext hp) ▸ h v.val
lemma cadence (x:Q.W): Continuous fun u:FlavorTorus=> T.flavor u x:=by
    obtain ⟨d,p,hp⟩:=hQ.tidal x none; rw [←hp]; simp_rw [T.f]; exact (Q.focus none d).continuous_of_finiteDimensional.comp (glacial (P:=P) d p)
end Pollens
end YM.Massive.Tarn
#print axioms YM.Massive.Tarn.Pollens.signs
#print axioms YM.Massive.Tarn.Pollens.cadence
