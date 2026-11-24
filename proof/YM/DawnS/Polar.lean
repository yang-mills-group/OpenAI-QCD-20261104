import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import YM.Maxwell.PotentialKernel

/-! Solid-angle moments. Using only transitivity of isometries and the second jet of the even moment on one orthogonal line. -/
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Set Filter MeasureTheory Lattice Function
open scoped Classical BigOperators InnerProductSpace ContDiff Pointwise Topology ENNReal
abbrev Vertex := EuclideanSpace ℝ (Fin 3)
abbrev RingS := Metric.sphere (0:Vertex) 1
local notation "Y" => Vertex
local notation "P"=> RingS
abbrev muS : Measure ↥(RingS) := (volume:Measure Y).toSphere
variable (f : Y ≃ₗᵢ[ℝ] Y)
noncomputable def turn : ↥(RingS) ≃ₜ ↥(RingS) where
   toFun x:=⟨f x.val,by simpa only [RingS, mem_sphere_zero_iff_norm, f.norm_map] using x.property⟩ -- x.property simp need recheck
   invFun x:=⟨f.symm x.val,by simpa only [RingS, mem_sphere_zero_iff_norm, f.symm.norm_map] using x.property⟩
   left_inv x:=Subtype.ext (f.symm_apply_apply _)
   right_inv x:=Subtype.ext (f.apply_symm_apply _)
   continuous_toFun:=by fun_prop
   continuous_invFun:=by fun_prop

lemma constancy : MeasurePreserving (turn f) muS muS:=by
     let μ:=muS
     refine ⟨(turn f).measurable, Measure.ext fun s hs=>?_⟩
     rw [Measure.map_apply (turn f).measurable hs, muS, Measure.toSphere_apply' _ ((turn f).measurable hs),Measure.toSphere_apply' _ hs]
     congr 1
     have hE : Ioo (0:ℝ) 1 • (((↑):P→Y) '' ((turn f)⁻¹' s))= f⁻¹'(Ioo (0:ℝ) 1 • (((↑):P→Y) '' s)):=by
       ext x; constructor
       · rintro ⟨a,ha,_,⟨y,hy,rfl⟩,rfl⟩; refine ⟨a,ha,_,⟨turn f y,hy,rfl⟩,?_⟩; exact (f.map_smul ..).symm
       rintro ⟨a,ha,_,⟨y,hy,rfl⟩,hv⟩; refine ⟨a,ha,_,⟨(turn f).symm y,by change turn f ((turn f).symm y)∈ s; rwa [(turn f).apply_symm_apply],rfl⟩,?_⟩ -- motive? fix
       apply f.injective; rw [f.map_smul]; change a • f ((turn f).symm y).val=f x; exact Eq.trans (congr_arg (fun z:P=>a • ((z: P):Y)) ((turn f).apply_symm_apply y)) hv
     rw[hE]; exact f.measurePreserving.measure_preimage_emb f.toHomeomorph.measurableEmbedding _
lemma flash (x:P): ‖(x:Vertex)‖=1:= mem_sphere_zero_iff_norm.mp x.property
noncomputable abbrev base (a:Fin 3) : Vertex:= (EuclideanSpace.basisFun (Fin 3) ℝ) a
lemma hue (a:Fin 3) : ‖base a‖=1:=(EuclideanSpace.basisFun ..).orthonormal.1 _
noncomputable instance inhabitP : Nonempty ↥(RingS):=⟨base 0,mem_sphere_zero_iff_norm.mpr (hue _)⟩
#synth IsFiniteMeasure muS
#synth Measure.IsOpenPosMeasure muS
#check LinearIsometryEquiv.measurePreserving
#check MeasurePreserving.measure_preimage_emb
#check MeasurableEquiv.map_apply

noncomputable def surf (n:ℕ) (v:Y):ℝ:=∫ y:P, (inner ℝ v (y.val))^n ∂muS
lemma turned (n:ℕ)(v:Y): surf n (f v)=surf n v:=by
     unfold surf; rw [←(MeasurePreserving.integral_comp (constancy f) (turn f).measurableEmbedding (fun y:P=> _))]; exact integral_congr_ae (Eventually.of_forall (fun x=> congr_arg (fun a:ℝ=>a^n) (f.inner_map_map ..)))
lemma sphereNorm (n:ℕ)(v:Y): surf n v= ‖v‖^n*surf n (base 0):=by
     let z:=‖v‖ • base 0; have hz :‖z‖= ‖v‖:=by unfold z; simp [norm_smul,hue]
     let k:= Submodule.reflection (Submodule.span ℝ {z-v})ᗮ; have hp:k z=v:= Submodule.reflection_sub hz
     calc
       _ = surf n z := (congr_arg _ hp.symm).trans (turned k n z)
       _ = _ := by unfold z surf; rw[← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun x=>by dsimp only; rw[real_inner_smul_left,mul_pow])
#check inner_smul_left
lemma sphereOdd (m:ℕ)(v:Y): surf (2*m+1) v=0:=by
     let j:=2*m+1; have he:surf j (-v)=surf j v:=by rw[sphereNorm j (-v),norm_neg,sphereNorm j v];
     have hp:surf j (-v)= -surf j v:=by unfold surf; rw[← integral_neg]; exact integral_congr_ae (Eventually.of_forall fun x=> by dsimp only; rw[inner_neg_left,(show Odd j from ⟨m,rfl⟩).neg_pow])
     linarith only [he,hp]
end YM.DawnS
#print axioms YM.DawnS.sphereOdd
