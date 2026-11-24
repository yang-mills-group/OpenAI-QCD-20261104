import YM.TorusPCAC.Jet.Mirror

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Polar/pseudo systems exactly through weight four -/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Jet.Selector
open QCD QCD.Lat Finset Function MeasureTheory TensorProduct Set Spin
open scoped Matrix Topology BigOperators Kronecker TensorProduct Matrix.Norms.Frobenius
variable (i j : Flav) (s : Bool)
abbrev signum (s : Bool) (A : Pin) : ℂ := if s then (A.val.1.val.det:ℂ) else 1
abbrev theme (s : Bool) : Spike := if s then g5 else 1
def path (s : Bool) (a : Axis) := gamma a * theme s
abbrev ratio (s:Bool) (a:Axis):= signum s (Spin.mirror a)
def oneAxis (s:Bool) (v a:Axis):= sgn (Signed.mirror a) v*ratio s a

def rLeg (i j:Flav) (u:Bool) (a : Axis) : Spike →ₗ[ℂ] Pol:= if u then crowd i j (hit a) 0 else crowd i j 0 (hit a)
def blade (u:Bool) (v:Axis):= rLeg i j u v (path s v)
def base := crowd i j 0 0 (theme s)
def θ (u:Bool):=∑ v, blade i j s u v
lemma orientation_pure (A:Pin) : signum s A*signum s A=1:=by cases s; exact mul_one _; exact (Complex.ofReal_mul ..).symm.trans ((congr_arg _ (orientation (A.val.1))).trans Complex.ofReal_one)
lemma sgn_pure (A:Signed) (v:Axis):sgn A v*sgn A v=1:=by unfold sgn; split <;> simp
lemma oneAxis_pure (a v) : oneAxis s a v*oneAxis s a v=1:=by unfold oneAxis; rw [show sgn _ _ * _ * (sgn _ _ * _)=sgn (Signed.mirror v) a * sgn (Signed.mirror v) a*(ratio s v*ratio s v) by ring, sgn_pure, orientation_pure, mul_one]
lemma unitTheme : IsUnit (theme s):=by
  have hp : IsUnit g5:= ⟨⟨g5,g5,g5_sq,g5_sq⟩,rfl⟩
  cases s; exact isUnit_one; exact hp
lemma unitPath (v): IsUnit (path s v):= IsUnit.mul (show IsUnit (gamma v) from ⟨⟨gamma v,gamma v,gamma_sq v,gamma_sq v⟩,rfl⟩) (unitTheme s)
lemma tilt_p (A:Pin): CM A (theme s)=signum s A • theme s:=by cases s; exact (map_one _).trans (one_smul ℂ _).symm; exact MatrixColor.turn_fifth _
lemma hinge_path (A:Pin) (g:Signed) (e:A.val.1=g.ortho) (v:Axis): CM A (path s v)=(sgn g v * signum s A) • path s (g.perm v) :=by
  unfold path; rw [map_mul, MatrixColor.pivot,e, Spin.sends_signed, tilt_p]; unfold sgn; split <;> simp
lemma tune_v (v a): MColor a (path s v)=oneAxis s v a • path s v:=hinge_path s (mirror a) (Signed.mirror a) rfl v -- ?
lemma turn_rLeg (g:Signed) (p:Pin) (e:p.val.1=g.ortho) (u:Bool)(v:Axis)(A: Spike):
    Jet.rotate p (rLeg i j u v A) = sgn g v • rLeg i j u (g.perm v) (CM p A) :=by
  have hk : sgn g v≠0:= left_ne_zero_of_mul (by rw [sgn_pure]; norm_num)
  have hh : rotateMono p.val.1 (hit v)=MvPolynomial.monomial (hit (g.perm v)) (sgn g v):=e ▸ hinge g v
  cases u
  · simp only [rLeg,Bool.false_eq_true, ↓reduceIte]; rw [tilted p _ _ (unturned _) one_ne_zero hh hk,one_mul]
  simp only [rLeg,if_true]; rw [tilted p _ _ hh hk (unturned _) one_ne_zero, mul_one]
lemma turn_blade (g:Signed)(p:Pin) (e:p.val.1=g.ortho) (u:Bool)(v:Axis) :
    Jet.rotate p (blade i j s u v)=signum s p • blade i j s u (g.perm v):=by
  unfold blade; rw [turn_rLeg i j g p e, hinge_path s p g e,map_smul,smul_smul,← mul_assoc,sgn_pure,one_mul]
lemma turn_base (p:Pin) : Jet.rotate p (base i j s)= signum s p • base i j s:=by unfold base; rw [stemp,tilt_p,map_smul]
lemma turn_sum (g:Signed)(p:Pin) (e:p.val.1=g.ortho) (u:Bool): Jet.rotate p (θ i j s u)= signum s p • θ i j s u:=by
  unfold θ; rw [map_sum]; simp_rw [turn_blade i j s g p e,← smul_sum]; exact congr_arg _ (Equiv.sum_comp g.perm _)

variable (l : List Axis) (h : ∀ i:Axis,i∈l)
include h
lemma limited_v (u : Bool) (A : Spike) (v : Axis) : ∃ c:ℂ, travel (ratio s) l (rLeg i j u v A)=c • blade i j s u v:=by
  let b : Order:= if u then hit v else 0; let c:Order:= if u then 0 else hit v
  have hp: rLeg i j u v=crowd i j b c:=by cases u <;> rfl
  unfold blade; rw [hp]; apply survivor (g:=fun i=> sgn (Signed.mirror i) v) _ _ _ _ _ (unitPath ..) (fun _=> sgn_pure ..) (fun _=>orientation_pure s _) _ _ l h
  · intro A' r; rw [← hp]; exact turn_rLeg i j (Signed.mirror r) (Spin.mirror r) rfl u v A'
  intro x; rw [mul_comm]; exact tune_v s v x

def cycle (g : Axis) : Signed:= Revolve.Swing.pure (Equiv.addRight g)
-- average the 4 cyclic permutations with Spin lifts (don't choose a homomorphic section)
def homogenize (X : Axis→Pin) : Pol→ₗ[ℂ] Pol:=(4:ℂ)⁻¹ • ∑ i, signum s (X i) • (Jet.rotate (X i)).toLinearMap
variable (X : Axis→Pin) (hs : ∀ i, (X i).val.1=(cycle i).ortho)
omit h
include hs
lemma rolled (u : Bool)(v:Axis): homogenize s X (blade i j s u v)= (4:ℂ)⁻¹ • θ i j s u:=by
  unfold homogenize; simp only [LinearMap.smul_apply, LinearMap.sum_apply, AlgHom.toLinearMap_apply]; simp_rw [turn_blade i j s (cycle _) (X _) (hs _),smul_smul,orientation_pure,one_smul]
  exact congrArg (fun x:Pol=> (4:ℂ)⁻¹ • x) (Equiv.sum_comp (Equiv.addLeft v) (fun x => blade i j s u x))
omit hs in
lemma frozen : homogenize s X (base i j s)=base i j s :=by
  unfold homogenize; simp only [LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply]; simp_rw [turn_base i j s,smul_smul,orientation_pure,one_smul, Finset.sum_const,card_univ]; rw [show Fintype.card Axis = 4 from rfl, ← Nat.cast_smul_eq_nsmul ℂ, show ((↑(4:ℕ)):ℂ)=4 by norm_num, inv_smul_smul₀ (by norm_num)]
include h
theorem bundleRank {v:Pol} (he : v∈channel i j 8) : ∃ c a b : ℂ, homogenize s X (travel (ratio s) l v)=c • base i j s+a • θ i j s true+b • θ i j s false:=by
  have hp (u:Bool) (A:Spike) (v:Axis): ∃ x y w:ℂ, homogenize s X (travel (ratio s) l (rLeg i j u v A))=x • base i j s+y • θ i j s true+w • θ i j s false:=by
    obtain ⟨c,hc⟩:= limited_v i j s l h u A v; rw [hc,map_smul,rolled i j s X hs, smul_smul];
    cases u; exact ⟨0,0,c*4⁻¹,by simp⟩; exact ⟨0,c*4⁻¹,0,by simp⟩
  refine Submodule.span_induction (p:=fun v _=> ∃ c a b:ℂ, homogenize s X (travel (ratio s) l v)=c • base i j s+a • θ i j s true+b • θ i j s false) ?_ ?_ ?_ ?_ he
  · rintro z ⟨u,v,a,b,hg,rfl⟩; rw [← entryMetric]; let A := Matrix.single u v (1:ℂ); unfold load at hg
    by_cases hb: deg b=0
    · rw [firstR b hb]; by_cases ha:deg a=0
      · rw [firstR a ha]; obtain ⟨c,hc⟩:=mirrorRank (ratio s) i j (unitTheme s) (fun _=>orientation_pure ..) (fun i=> tilt_p s _) l h (X:=crowd i j 0 0 A) (by rw [show crowd i j 0 0 A=_ from entryMetric i j 0 0 u v]; apply enters; simp [load,deg]); refine ⟨c,0,0,?_⟩; rw [hc,map_smul,show crowd i j 0 0 _=base i j s from rfl,frozen i j s X]; simp
      obtain ⟨v,hv⟩:= secondR a (by omega); rw [hv]; exact hp true A v
    obtain ⟨v,hv⟩:= secondR b (by omega); rw [firstR a (by omega),hv]; exact hp false A v
  · exact ⟨0,0,0,by simp⟩
  · rintro v w _ _ ⟨c,a,b,hv⟩ ⟨C,A,B,hw⟩; refine ⟨c+C,a+A,b+B,?_⟩; rw [map_add,map_add,hv,hw]; simp_rw [add_smul]; abel
  rintro c v _ ⟨b,a,e,h⟩; exact ⟨c*b,c*a,c*e,by rw [map_smul,map_smul,h]; simp only [mul_smul,smul_add]⟩
end YM.TorusPCAC.Jet.Selector

#print axioms YM.TorusPCAC.Jet.Selector.bundleRank
