import YM.MassiveBridge.SpinTube
import YM.Massive.Ribbon.Graft

/-!
# Verify the Euclidean intertwiner of time-adjunction

With `-gamma_t` and order reversal on the same projected Wick bases. On a Euclidean
boost plane it intertwines **with reverse parameter**; gives a commute after
continuation. Also continue the grading with the central element of the cover.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Spinor
open QCD QCD.Lat Grass
open Set Function Filter Tensor Analysis Complex Matrix TensorProduct Mink
open MassiveTwoEstimates (SpinGeometry.geometry)
open MassiveTwoEstimates.BoostRotor
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators ContDiff TensorProduct
local notation "Rf" => Signed.reflect timeAxis
local notation "Γ" => gamma timeAxis

lemma spin_unitary (p:EuPin) : star p.matrix.val = p.matrix⁻¹.val := by
   have H : star p.matrix.val * p.matrix.val =1:= (SpinGeometry.geometry.unitary p).1
   calc
     _ = star p.matrix.val * p.matrix.val * p.matrix⁻¹.val :=by rw [mul_assoc,show p.matrix.val*p.matrix⁻¹.val=1 from p.matrix.val_inv,mul_one]
     _ = _:= by rw [H,one_mul]

section
open UV
variable {d:ℕ}
private lemma star_turn (p:EuPin) (k:Spike) : Mstar (UV.turned (d:=d) p (wave k)) = UV.turned p (wave (Mstar k)) := by
    rw [←mstar_wave]; ext i j; rw [mstar]; unfold UV.turned; simp only [Matrix.of_apply]; split_ifs <;> simp only [star_mul,row_star,mstar,mul_comm,star_zero] -- split before of
private abbrev mat (p:EuPin) (d:ℕ) := fromBlocks (UV.turned (d:=d) p (wave p.matrix⁻¹.val)) 0 0 (UV.turned (d:=d) p (wave p.matrix.val.transpose))
private lemma turned_eq {p q:EuPin} (h:p.coord=q.coord)(X:Bundle): UV.turned (d:=d) p X = UV.turned q X :=by unfold UV.turned multiMove; rw [h]

lemma eye_turn (d:ℕ){p q:EuPin} (h:Rf*p.coord=q.coord*Rf) (he:Γ*p.matrix.val=q.matrix.val*Γ): Mstar (mat p d) * eyeW d timeAxis= eyeW d timeAxis * mat q d:=by
   obtain ⟨s,hs,_⟩:= SpinGeometry.geometry.reflection timeAxis
   have ht : (s*p).coord=(q*s).coord:=by change s.coord*p.coord=q.coord*s.coord; rw [hs]; exact h
   have hU : Mstar (p.matrix.val.transpose)=p.matrix⁻¹.val:=by rw [mstar_sq]; exact spin_unitary p
   have hV : Mstar (p.matrix⁻¹.val)=p.matrix.val.transpose:= hU ▸ (mstar_again _)
   unfold eyeW mat
   simp only [mstar_diag,star_turn,hU,hV,fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add]
   rw [hem_turn timeAxis hs,hem_turn timeAxis hs]; simp only [reel,wave_mul, turned_eq ht]
   have hh : p.matrix⁻¹.val*Γ=Γ*q.matrix⁻¹.val:=by -- check algebra he Γ P=Q Γ -> P^-1Γ=Γ Q^-1 yes
      have hh' : p.matrix.val * Γ = Γ*q.matrix.val:=by calc
         _ = Γ*(Γ*p.matrix.val)*Γ :=by rw [←mul_assoc, Lat.gamma_sq,one_mul]
         _ = _:=by rw [he,mul_assoc,mul_assoc,Lat.gamma_sq,mul_one]
      apply p.matrix.isUnit.mul_right_injective
      dsimp only
      calc
         _ = Γ:= by rw [←mul_assoc,show p.matrix.val*p.matrix⁻¹.val=1 from p.matrix.val_inv,one_mul]
         _ = _:= by rw [←mul_assoc,hh',mul_assoc,show q.matrix.val*q.matrix⁻¹.val=1 from q.matrix.val_inv,mul_one]
   rw [mul_neg, ← transpose_mul,mul_neg,hh,he, neg_mul,neg_mul, transpose_mul]
lemma adj_pin {p q:EuPin} (h:Rf*p.coord=q.coord*Rf) (he:Γ*p.matrix.val=q.matrix.val*Γ) (x:Pol d): UV.adj timeAxis (pinAct p x)=pinAct q (UV.adj timeAxis x) := by
   induction x using TensorProduct.induction_on with
   | zero => simp
   | add x y hx hy=>simp only [map_add,hx,hy]
   | tmul x y=>
     unfold UV.adj pinAct; simp_rw [TensorProduct.map_tmul]
     apply congr_arg₂ (tmul ℂ)
     · have hh: conjGPol (Labels.rotated p.coord x)=Labels.rotated p.coord (conjGPol x):=(conj_mobil _ x).symm
       change Labels.rotated _ (conjGPol (Labels.rotated p.coord x)) = Labels.rotated _ (Labels.rotated _ _); rw [hh, ←Labels.rotation_law,h,Labels.rotation_law]
     change changeVars (eyeW _ _) (dagger (changeVars (mat p d) y))=changeVars (mat q d) (changeVars (eyeW _ _) (dagger y)); rw [dagger_change,multipleChange,multipleChange,eye_turn d h he]
end

namespace Lift
private lemma reflectionAngle (a : SpaceAxis) (t : ℝ) : Rf * (daylight a t).coord = (daylight a (-t)).coord * Rf := by
  let F r := Ortho.oneParameter (Ortho.plane timeAxis a.castSucc) r
  have ha : timeAxis ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last _)
  apply Ortho.ext; intro x; ext1 b
  rw [Ortho.move_mul, Ortho.move_mul]
  have hl (y : E4) (r : ℝ) : (F r).move y timeAxis = Real.cos r * y timeAxis + Real.sin r * y a.castSucc :=
    (Work.A13.plane_givens ha y r).1
  have hm (y : E4) (r : ℝ) : (F r).move y a.castSucc = Real.cos r*y a.castSucc - Real.sin r*y timeAxis := (Work.A13.plane_givens ha y r).2.1
  have hk (y : E4) (r : ℝ) : ∀ b, b≠timeAxis → b≠a.castSucc → (F r).move y b=y b := (Work.A13.plane_givens ha y r).2.2
  change Ortho.move Rf ((F t).move _) b=(F (-t)).move _ b
  by_cases he : b=timeAxis
  · subst b; simp only [Signed.mirrored, if_true, hl]; simp [ha.symm]; ring
  rw [Signed.mirrored,if_neg he]; by_cases hw : b=a.castSucc
  · subst b; rw [hm,hm]; simp [ha.symm]
  rw [hk _ t b he hw,hk _ _ b he hw]; simp [he]
private lemma spinAngle (a:SpaceAxis) (t : ℝ) : Γ*(daylight a t).matrix.val=(daylight a (-t)).matrix.val*Γ:=by
    let J:= Ray.fromAxis a
    have hh : Γ * generator J = -(generator J * Γ):=by
       unfold MassiveTwoEstimates.BoostRotor.generator; rw [Matrix.mul_smul,Matrix.smul_mul,←mul_assoc,show Γ*axis J=_ from MassiveTwoEstimates.BoostRotor.reverse J]; simp only [neg_mul,smul_neg,mul_assoc]; rfl -- clocks
    change Γ*spinPart J ((t:ℂ)*I) = spinPart J ((↑(-t):ℂ)*I)*Γ
    unfold spinPart binomial
    rw [ofReal_neg,neg_mul,neg_div, Complex.cosh_neg, Complex.sinh_neg]
    simp only [mul_add, Matrix.mul_smul, add_mul, Matrix.smul_mul,hh,one_mul,mul_one,smul_neg,neg_smul,neg_mul]

lemma star_spatial {d:ℕ} (p:EuPin)(hp:Lorentz.spatialTurn p.coord)(x:UV.Pol d): UV.adj timeAxis (UV.pinAct p x)=UV.pinAct p (UV.adj timeAxis x):=by
    let q := p.coord; have hs := Maxwell.Free.spatial_axis p.coord hp
    apply adj_pin
    · apply Ortho.ext; intro x
      have hf (x) : Ortho.move Rf x=x - (2*time x) • basis timeAxis := by
         ext a; rw [Signed.mirrored]; by_cases hx:a=timeAxis <;> simp [hx,time]
         ring -- only
      rw [Ortho.move_mul,Ortho.move_mul,hf,hp.2,hf]; symm; change p.coord.motion _=_
      rw [map_sub,map_smul,Ortho.motion_at,Ortho.motion_at,hs]
    have ht := ((euPin_iff p.val).1 p.property).2 (basis timeAxis)
    change p.matrix.val * _= slash (Ortho.move p.coord (basis timeAxis))*_ at ht
    have he : slash (basis timeAxis)=Γ:=by classical simp [slash,basis_eq,ite_smul]
    rw [hs,he] at ht; exact ht.symm

lemma star_day {d:ℕ} (i:SpaceAxis) (t:ℝ) (x:UV.Pol d): UV.adj timeAxis (UV.pinAct (daylight i t) x)= UV.pinAct (daylight i (-t)) (UV.adj timeAxis x) := adj_pin (reflectionAngle ..) (spinAngle ..) _
end Lift
end YM.Massive.Bridge.Spinor
