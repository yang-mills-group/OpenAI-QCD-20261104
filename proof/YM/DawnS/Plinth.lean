import YM.DawnS.Ion
import YM.Arise.Unit

set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell Arise.Range
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
local notation "I"=>Complex.I
local notation "DΓ"=> Arise.Range.deriveL
-- coefficient all ranks with factorial prices
noncomputable def rayG (r:ℝ)(n:ℕ):ℝ:= ((n+1).factorial:ℝ)/r^(n+2)*normal/sky
lemma windC {s:ℝ} (hs:s≠0)(j:ℕ)(f:Fin j→Y): ((fromAir j Green (prelude s) f:ℝ):ℂ) = rayG |s| j * Complex.I^j * wheel j f:=by
    rcases Nat.even_or_odd j with ⟨m,hm⟩|⟨m,rfl⟩
    · have he:j=2*m:=(by omega)
      clear hm; subst j
      rw [wind_even rfl hs]
      rw [smul_apply,smul_eq_mul,pow_mul Complex.I,Complex.I_sq]; push_cast
      unfold rayG; rw [Nat.factorial_succ,pow_add]; push_cast; rw [pow_mul]; have h1:(↑(|s|) :ℂ)≠0:=by exact_mod_cast (abs_pos.mpr hs).ne'
      have h3:(↑sky:ℂ)≠0:= by exact_mod_cast sky_pos.ne'
      rw [div_pow]; field_simp
    rw [wind_odd rfl hs]; have hw:wheel (2*m+1)=0:=by apply ext_diag _ _ (wired _) (fun _ _=>rfl); funext z; rw[Tensor.diagonal, whirl,sphereOdd m z]; rfl
    rw[hw];simp
lemma waterC (v s r:ℝ)(hr:0<r)(hp:|s|=r)(he:s=v*r)(j:ℕ)(f:Fin j→Y): ((fromAir j (grad timeAxis Green) (prelude s) f:ℝ):ℂ) = rayG r (j+1) * (-v:ℝ)* Complex.I^j * wheel j f:=by
    have hs:s≠0:= by intro hc; rw[hc,abs_zero] at hp; linarith
    rcases Nat.even_or_odd j with ⟨m,hm⟩|⟨m,rfl⟩
    · have h':j=2*m:=(by omega)
      clear hm; subst j
      rw [water_even hp hs]; rw [smul_apply, smul_eq_mul, pow_mul Complex.I, Complex.I_sq]; unfold rayG; rw[he,Nat.factorial_succ,Nat.factorial_succ]; push_cast; rw[pow_add (r:ℂ),pow_add (r:ℂ), pow_mul (r:ℂ)]; have h2:(r:ℂ)≠0:=by exact_mod_cast hr.ne'
      have h3:(↑sky:ℂ)≠0:= by exact_mod_cast sky_pos.ne'
      rw [div_pow]; field_simp; ring
    rw [water_odd hp hs]; have hw:wheel (2*m+1)=0:=by apply ext_diag _ _ (wired _) (fun _ _=>rfl); funext z; rw[Tensor.diagonal, whirl,sphereOdd m z]; rfl
    rw[hw];simp
end YM.DawnS
