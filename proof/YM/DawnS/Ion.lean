import YM.DawnS.Arcs
/-! Green and its temporal derivative on a displaced slice, momentum form. -/
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
noncomputable abbrev fromAir {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U] (n:ℕ)(f:E4→U)(x:E4):T Y U n:=(iteratedFDeriv ℝ n f x).compContinuousLinearMap (fun _=>align)
noncomputable def prelude (x:ℝ):=x • B
local notation "τ"=>prelude
lemma follow (s u:ℝ)(v:Y) : time (τ s + u • align v)=s:=by unfold prelude time; simp [aperture]
lemma swept (s:ℝ)(hs:s≠0):τ s≠0:= by intro h; have hp:=follow s 0 0; rw[h] at hp; simp at hp; exact hs hp.symm -- notation.B
lemma innerB (v:Y) : inner ℝ B (align v)=0:=by rw [basis_inner,aperture]
lemma matchB (s u:ℝ)(v:Y) : ‖τ s + u • align v‖^2=s^2+ u^2* ‖v‖^2:=by
     unfold prelude; rw [norm_add_sq_real,inner_smul_right,real_inner_smul_left,innerB,norm_smul,norm_smul,mul_pow,mul_pow]; simp [spaces]
lemma jointB {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U] (n:ℕ)(f:E4→U)(x:E4)(hx:ContDiffAt ℝ n f x) : Sym (fromAir n f x):=fun v g=> sym_Jet hx (fun i=> align (v i)) g
lemma wind (s r:ℝ)(hr:|s|=r)(v:Y)(u:ℝ) : Green (τ s+u•align v)= normal*hLine r (‖v‖^2) u:=by subst r; unfold Green hLine; rw [matchB]; simp
lemma waters (s r:ℝ)(hr:|s|=r)(hs:s≠0)(v:Y)(u:ℝ) : D B Green (τ s+u•align v)=(-2*normal*s)*jLine r (‖v‖^2) u:=by
    have ht:= follow s u v; have hp:τ s+u•align v≠0:=by intro h; rw[h] at ht; simp at ht; exact hs ht.symm
    subst r; change grad timeAxis Green _=_; rw[first_Green hp,matchB,show (τ s+u•align v) timeAxis=s from ht]; simp [jLine]
variable {s r:ℝ}(h:|s|=r)(hr:s≠0)
include hr h
lemma wind_even(m:ℕ) : fromAir (2*m) Green (τ s)=(normal*(((2*m).factorial:ℝ)/r^2*(-1/r^2)^m)*(2*m+1:ℝ)/sky) • wheel (2*m) :=by
     have hx:= jointB (2*m) Green (τ s) ((freeSmooth (swept s hr)).of_le (WithTop.coe_le_coe.mpr le_top))
     let j:= 2*m; apply ext_diag _ _ hx _ -- eq maybe
     · ext1 x; change iteratedFDeriv ℝ j Green _ (fun _=>align x)= _ * wheel j (fun _=>x); rw [whirl,sloped _ _ _ _ ((freeSmooth (swept s hr)).of_le (WithTop.coe_le_coe.mpr le_top)),show (fun t:ℝ=>Green _)=fun t=> normal*hLine r (‖x‖^2) t from funext (wind s r h x), iteratedDeriv_const_mul_field]
       have hp :0<r:=h ▸ abs_pos.mpr hr; change _ * iteratedDeriv (2*m) (hLine _ _) _= _; rw[hD hp]; let F:=(j.factorial:ℝ); apply mul_left_cancel₀ (a:=sky) sky_pos.ne'
       rw [show -‖x‖^2/r^2=(-1/r^2)*‖x‖^2 by ring ,mul_pow (-1/r^2) (‖x‖^2) m,←pow_mul]
       let y := (surf (2*m) x)
       let K:= (normal*(F/r^2 * (-1/r^2)^m)); calc
          _= K*(‖x‖^j*sky) := by unfold K F j; ring
          _= _ := by rw[show ‖x‖^j*sky=y*(2*m+1:ℝ) from (evolved m x).symm]; change K*(y*_) = sky*(K*_/sky*y); field_simp[sky_pos.ne']
     intro v g; simp only [ContinuousMultilinearMap.smul_apply,wired _ v g]
lemma water_even(m:ℕ) : fromAir (2*m) (grad timeAxis Green) (τ s)=((-2*normal*s)*(((2*m).factorial:ℝ) * ((m+1:ℕ):ℝ)/r^4*(-1/r^2)^m)*(2*m+1:ℝ)/sky) • wheel (2*m) :=by
     have hx:= jointB (2*m) (grad timeAxis Green) (τ s) ((gradGradientSmooth (swept s hr) timeAxis).of_le (WithTop.coe_le_coe.mpr le_top))
     let j:= 2*m; apply ext_diag _ _ hx _ -- eq maybe
     · ext1 x; change iteratedFDeriv ℝ j (grad timeAxis Green) _ (fun _=>align x)= _ * wheel j (fun _=>x); rw [whirl,sloped _ _ _ _ ((gradGradientSmooth (swept s hr) timeAxis).of_le (WithTop.coe_le_coe.mpr le_top)),show (fun t:ℝ=>grad timeAxis Green _)=fun t=> (-2*normal*s)*jLine r (‖x‖^2) t from funext (waters s r h hr x), iteratedDeriv_const_mul_field]
       have hp :0<r:=h ▸ abs_pos.mpr hr; change _ * iteratedDeriv (2*m) (jLine _ _) _= _; rw[jD hp]; let F:=(j.factorial:ℝ); apply mul_left_cancel₀ (a:=sky) sky_pos.ne'
       rw [show -‖x‖^2/r^2=(-1/r^2)*‖x‖^2 by ring ,mul_pow (-1/r^2) (‖x‖^2) m,←pow_mul]
       let y := (surf (2*m) x)
       let K:= ((-2*normal*s)*(F * ((m+1:ℕ):ℝ) /r^4 * (-1/r^2)^m)); calc
          _= K*(‖x‖^j*sky) := by unfold K F j; ring
          _= _ := by rw[show ‖x‖^j*sky=y*(2*m+1:ℝ) from (evolved m x).symm]; change K*(y*_) = sky*(K*_/sky*y); field_simp[sky_pos.ne']
     intro v g; simp only [ContinuousMultilinearMap.smul_apply,wired _ v g]
lemma wind_odd (m:ℕ) : fromAir (2*m+1) Green (τ s)=0:=by
     let j:= 2*m+1; have hz: ContDiffAt ℝ j Green (τ s):= (freeSmooth (swept s hr)).of_le (WithTop.coe_le_coe.mpr le_top)
     apply ext_diag _ _ (jointB _ _ _ hz) (fun _ _=>rfl)
     funext x; change iteratedFDeriv ℝ j Green _ (fun _=>align x)=0; rw[sloped _ _ _ _ hz,show (fun t:ℝ=> Green (prelude s+ t• align x))=(fun t=> normal*hLine r (‖x‖^2) t) from funext fun t=>wind s r h x t,iteratedDeriv_const_mul_field,show iteratedDeriv j _ (0:ℝ)= (0:ℝ) from ?_]; rotate_left
     · exact dull (hLine r (‖x‖^2)) (by simp[hLine]) m
     ring
lemma water_odd (m:ℕ) : fromAir (2*m+1) (grad timeAxis Green) (τ s)=0:=by
     let j:= 2*m+1; have hz: ContDiffAt ℝ j (grad timeAxis Green) (τ s):= (gradGradientSmooth (swept s hr) timeAxis).of_le (WithTop.coe_le_coe.mpr le_top)
     apply ext_diag _ _ (jointB _ _ _ hz) (fun _ _=>rfl)
     funext x; change iteratedFDeriv ℝ j (grad timeAxis Green) _ (fun _=>align x)=0; rw[sloped _ _ _ _ hz,show (fun t:ℝ=> (grad timeAxis Green) (prelude s+ t• align x))=(fun t=> (-2*normal*s)*jLine r (‖x‖^2) t) from funext fun t=>waters s r h hr x t,iteratedDeriv_const_mul_field,show iteratedDeriv j _ (0:ℝ)= (0:ℝ) from ?_]; rotate_left
     · exact dull (jLine r (‖x‖^2)) (by simp[jLine]) m
     ring
end YM.DawnS
