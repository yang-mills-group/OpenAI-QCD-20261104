import YM.MassiveTwoEstimates.SpinAxes
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Elementary boost-plus-rotation decomposition for the actual proper,
orthochronous Lorentz group in the massive field target. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveTwoEstimates.BoostRoom
open Massive Mink
open scoped BigOperators Matrix.Norms.Frobenius InnerProductSpace

private theorem clockIncrement (x : E4) :
    m (x+basis timeAxis)=m x+2*time x+1 := by simp [m]; ring

theorem fixed (g : Lorentz) (h : g.act (basis timeAxis)=basis timeAxis) :
    ∃ K : Ortho, ∃ hK : Lorentz.spatialTurn K, g=Lorentz.room K hK := by
  have keepTime (x : E4) : time (g.act x)=time x := by
    have eq := g.keeps (x+basis timeAxis)
    rw [map_add,h,clockIncrement,clockIncrement,g.keeps] at eq
    linarith
  have keepNorm (x : E4) : ‖g.act x‖=‖x‖ := by
    have eq := g.keeps x
    unfold m at eq
    rw [keepTime] at eq
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [squares,squares,keepTime]
    linarith
  let A : E4 ≃ₗᵢ[ℝ] E4 := ⟨g.sends.toLinearEquiv,keepNorm⟩
  obtain ⟨K,act⟩ := OS.Ground.columns A
  have linear : K.motion.toLinearEquiv.toLinearMap=g.act.toLinearMap :=
    LinearMap.ext (fun x=>act x)
  have hK : Lorentz.spatialTurn K := ⟨by rw [Lorentz.properTurn,linear,g.det],fun x=>by
    rw [act]; exact keepTime x⟩
  exact ⟨K,hK,Lorentz.ext _ _ (fun x=>(act x).symm)⟩

private theorem direction (z : Space3) : ∃ e : Ray, ‖z‖ • e.val=z := by
  by_cases hz : z=0
  · exact ⟨Ray.fromAxis 0,by simp [hz]⟩
  have hn : ‖(‖z‖⁻¹ : ℝ) • z‖=1 := by simp [norm_smul,hz]
  exact ⟨⟨(‖z‖⁻¹:ℝ) • z,hn⟩,by simp [smul_smul,hz]⟩

theorem reaches (g : Lorentz) : ∃ e : Ray, ∃ r : ℝ,
    (e.boost r).act (basis timeAxis)=g.act (basis timeAxis) := by
  let y := g.act (basis timeAxis)
  let z := spatial y
  let r := Real.arsinh ‖z‖
  obtain ⟨e,dir⟩ := direction z
  have rest : e.along (basis timeAxis)=0 := by simp [Ray.along]
  have sr : Real.sinh r=‖z‖ := Real.sinh_arsinh _
  have coneY : y ∈ cone := (g.keepsCone _).mpr (by simp [cone])
  have future := ((cone_self y).mp coneY).1
  have mass : time y^2-‖z‖^2=1 := by
    have eq := g.keeps (basis timeAxis)
    simpa [m,y,z] using eq
  have cr : Real.cosh r=time y := by
    apply (sq_eq_sq₀ (Real.cosh_pos _).le future).mp
    have eq := Real.cosh_sq_sub_sinh_sq r
    rw [sr] at eq
    linarith
  refine ⟨e,r,?_⟩
  change e.shift r (basis timeAxis)=y
  apply Mink.ext_by
  · simpa [Ray.newSpace,rest,sr,z] using dir
  · simp [Ray.newClock,rest,cr]

theorem decompose (g : Lorentz) : ∃ e : Ray, ∃ r : ℝ, ∃ K : Ortho, ∃ hK : Lorentz.spatialTurn K,
    g=e.boost r*Lorentz.room K hK := by
  obtain ⟨e,r,h⟩ := reaches g
  let k := (e.boost r)⁻¹*g
  have kernel : k.act (basis timeAxis)=basis timeAxis := by
    change ((e.boost r)⁻¹*g).act _=_
    rw [Lorentz.act_mul,←h,Lorentz.starts]
  obtain ⟨K,hK,hroom⟩ := fixed k kernel
  refine ⟨e,r,K,hK,?_⟩
  rw [←hroom]
  change g = e.boost r * ((e.boost r)⁻¹ * g)
  rw [←mul_assoc,mul_inv_cancel,one_mul]

end YM.MassiveTwoEstimates.BoostRoom
#print axioms YM.MassiveTwoEstimates.BoostRoom.fixed
#print axioms YM.MassiveTwoEstimates.BoostRoom.decompose
