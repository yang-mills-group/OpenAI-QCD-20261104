import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Complex.Basic
/-! Basis-induced norm on W. Used only for finite-dimensional interpolation tests.
No completion here! -/
set_option autoImplicit false
noncomputable section
namespace YM.Tarn
open Set Filter Function Module
open scoped Topology Classical
variable (V: Type*) [AddCommGroup V][Module ℂ V]
private noncomputable abbrev Skin:=Basis.ofVectorSpace ℂ V
private abbrev Spark:=Basis.ofVectorSpaceIndex ℂ V
private noncomputable def farF: V→ₗ[ℂ] lp (fun _ : Spark V=>ℂ) 2 where
     toFun v:= ⟨(fun i=> (Skin V).repr v i), Memℓp.of_exponent_ge (memℓp_zero_iff.mpr ((Skin V).repr v).hasFiniteSupport) zero_le⟩
     map_add' x y := by apply Subtype.ext; funext i; change (Skin V).repr (x+y) i=_; simp only [map_add]; rfl
     map_smul' t x:=by apply Subtype.ext; funext i; change (Skin V).repr (t • x) i=_; simp only [map_smul]; rfl
private lemma lively : Injective (farF V):=by intro u v h; apply (Skin V).repr.injective; ext i; exact congr_arg (fun (p:lp (fun _ : Spark V=>ℂ) 2)=> p i) h
noncomputable abbrev nerve : NormedAddCommGroup V:= NormedAddCommGroup.induced V _ (farF V) (lively V)
noncomputable abbrev starry (V: Type*)[AddCommGroup V][Module ℂ V]: letI:= nerve V; NormedSpace ℂ V:= NormedSpace.induced ℂ V _ (farF V)
end YM.Tarn
#print axioms YM.Tarn.nerve
#print axioms YM.Tarn.starry
