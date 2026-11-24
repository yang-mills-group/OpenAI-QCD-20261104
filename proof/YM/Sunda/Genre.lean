import YM.Sunda.Gully
import YM.Mako.Matte
import YM.Lobo.Trident
set_option maxHeartbeats 620000
set_option autoImplicit false
noncomputable section
namespace YM.Sunda
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Iceberg Tawny Tawny.Cast Tarn MassiveTwoEstimates Mako Lobo
open Finset
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
variable (k:Tri)(g:Signed)
lemma pairedS (a b i j:Axis)(ht:a≠b)(hz:i≠j):∃ u:Signed,Mako.conjSkew u.ortho (Ortho.plane a b)=Ortho.plane i j:=by
     have he(a b:Axis)(h:a≠b):∃ t:Equiv.Perm Axis,t 0=a∧t 1=b:=by
             obtain ⟨w,h1,h2⟩:= (show ∀ a b:Fin 4,∃ c:Fin 4,a≠c∧b≠c from by decide) a b; obtain ⟨s,hs,hp,-⟩:=StressFlux.extend_three a b w h h1 h2; exact ⟨s,hs,hp⟩
     obtain ⟨x,hx,hX⟩:=he a b ht; obtain ⟨y,hy,hY⟩:=he i j hz
     let u:Signed:=⟨x.symm.trans y,fun _=>false⟩; refine ⟨u,?_⟩; change Org.orients _ _=_; rw [Maxwell.Free.Corners.bracket_orient]; change ((if false = true then -1 else (1:ℝ)) * if false=true then -1 else (1:ℝ)) • Ortho.plane (y (x.symm a)) (y (x.symm b))=_; rw [← hx,← hX,x.symm_apply_apply,x.symm_apply_apply,hy,hY]; simp
lemma genreK(H:Subgroup EuPin)(h:∀ (p:EuPin) (s: Signed),p.Lifts s→ p∈ H)(hX:∀ t:ℝ,pathW k t∈ H)(x:EuPin):x∈H:=by
    apply made H h _ x; intro i j hv t; obtain ⟨u,hu⟩:=pairedS (lieu (backK k)) (lieu (edgeK k)) i j (fun he=> threeL k (Fin.castSucc_inj.mp he)) hv
    obtain ⟨v,hv⟩:= EuPin.choice u; let q:= pathW k t; have hP:= h v u hv; let p:= v*q*v⁻¹; let r:= oathU (Ortho.plane i j) t
    have hh:euca r=euca p:=by
          rw [show euca r=Ortho.oneParameter (Ortho.plane i j) t from (tour _).2.2 t, show euca p=u.ortho*Ortho.oneParameter (Omega k) t*u.ortho⁻¹ from ?_,← hu,oneParameter_conj]; unfold p; rw [map_mul,map_mul,map_inv,show euca v=_ from hv,show euca q=_ from (treks k).2.2 t]
    have hz:EuPin.Lifts (r*p⁻¹) 1:=by change euca (r*p⁻¹) = Signed.inclusionO 1; rw [map_mul,map_inv,hh,map_one,mul_inv_cancel]
    have he:=H.mul_mem (h _ _ hz) (show p∈H from H.mul_mem (H.mul_mem hP (hX t)) (H.inv_mem hP)); rwa[mul_assoc,inv_mul_cancel,mul_one] at he
end YM.Sunda
#print axioms YM.Sunda.genreK
