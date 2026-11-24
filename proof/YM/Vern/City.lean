import YM.Iceberg.Hay
import Mathlib.Analysis.InnerProductSpace.Trace
set_option maxHeartbeats 460000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Filter
open scoped Topology BigOperators Classical ComplexOrder InnerProductSpace
-- algebraic; don't alter Norm instances used for limits
structure Tide (W:Type*)[AddCommGroup W][Module ℂ W] where
  knot : W→ W→ℂ
  con (x y) : star (knot x y)=knot y x
  positive x : x≠0→ 0< (knot x x).re
  add (x y z) : knot x (y+z)=knot x y + knot x z
  sep (c:ℂ)(x y): knot x (c • y) = c*knot x y
variable {W: Type*}[AddCommGroup W][Module ℂ W]
variable (S:Tide W)
namespace Tide
lemma zero' (v:W): S.knot v 0=0:=by have h:= S.add v 0 0; rw [add_zero] at h; linear_combination -h
noncomputable def zz(a:W):W→ₗ[ℂ]ℂ:= {toFun:=S.knot a,map_add':=fun x y=> S.add ..,map_smul':=fun c x=> S.sep ..}
lemma other (x y z:W): S.knot (x+y) z=S.knot x z+S.knot y z:=by rw [← S.con z, ← S.con z,← S.con z,S.add, star_add]
lemma seals (x y:W)(c:ℂ):S.knot (c • x) y=star c * S.knot x y:=by rw [← S.con y, ← S.con y,S.sep, Complex.star_def,map_mul]
noncomputable abbrev coreP : InnerProductSpace.Core ℂ W:=by
   refine {inner:=S.knot,conj_inner_symm:=fun x y=> S.con .., add_left:=fun x y z=> S.other ..,smul_left:=fun x y c=> S.seals ..,re_inner_nonneg:=fun x=>?_, definite:=fun x h=>?_}
   · by_cases H:x=0; · subst x; rw [S.zero']; exact le_rfl
     exact (S.positive x H).le
   by_contra he; have hp:= S.positive x he; rw [h] at hp; exact (lt_irrefl _ hp)
def Leans (X: Module.End ℂ W):Prop:= ∀ x y,S.knot (X x) y= -S.knot x (X y)
variable [FiniteDimensional ℂ W]
lemma billQ (X: Module.End ℂ W)(h:S.Leans X)(he:X≠0): 0 < -(LinearMap.trace ℂ W (X^2)).re:=by
     let c:= S.coreP; letI : InnerProductSpace.Core ℂ W:= c
     letI :NormedAddCommGroup W:= c.toNormedAddCommGroup
     letI :PreInnerProductSpace.Core ℂ W:=c.toCore
     letI :InnerProductSpace ℂ W:= .ofCore c.toCore
     let v:= Module.finrank ℂ W; let E:=stdOrthonormalBasis ℂ W
     obtain ⟨i,hp⟩:∃ i: Fin v, X (E i) ≠ 0:=by by_contra! hf; exact he (E.toBasis.ext fun i=>hf i)
     rw [LinearMap.trace_eq_sum_inner (X^2) E]; have hx(y:W):inner ℂ y ((X^2) y)=-(S.knot (X y) (X y)):=by rw[pow_two]; change S.knot _ _=_; rw[h,neg_neg]; rfl
     simp_rw[hx,Complex.re_sum,Complex.neg_re,Finset.sum_neg_distrib,neg_neg]; exact Finset.sum_pos' (fun i _=> c.re_inner_nonneg (X (E i))) ⟨i,Finset.mem_univ _,S.positive _ hp⟩
end Tide
-- linear trace limits
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
lemma track(F:ℕ→Module.End ℂ X)(P:Module.End ℂ X)(H:∀ v:X,Tendsto (fun i=>F i v) atTop (𝓝 (P v))) : Tendsto (fun i=>LinearMap.trace ℂ X ((F i)^2)) atTop (𝓝 (LinearMap.trace ℂ X (P^2))):=by
    have h(v:X):Tendsto (fun i=>(F i^2) v) atTop (𝓝 ((P^2) v)):=by simp only [pow_two, Module.End.mul_apply]; exact Iceberg.follows_L F P H _ _ (H v)
    let B:= Module.finBasis ℂ X; have ht(f:Module.End ℂ X):LinearMap.trace ℂ X f=∑ i:Fin (Module.finrank ℂ X), B.coord i (f (B i)):=by rw [LinearMap.trace_eq_matrix_trace ℂ B]; unfold Matrix.trace; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Matrix.diag_apply, LinearMap.toMatrix_apply]; rfl
    simp_rw[ht]; exact tendsto_finsetSum _ (fun i _=> (B.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp (h (B i)))
variable [FiniteDimensional ℂ W]
lemma chord (f:X≃ₗ[ℂ]W)(p:Module.End ℂ W): LinearMap.trace ℂ X ((f.symm.toLinearMap ∘ₗ p ∘ₗ f.toLinearMap)^2)=LinearMap.trace ℂ W (p^2):=by
     rw[show _ ^ (2:ℕ)=f.symm.toLinearMap ∘ₗ (p^2) ∘ₗ f.toLinearMap from (?_ : (f.symm.toLinearMap ∘ₗ p ∘ₗ f.toLinearMap)^2=_)]; swap; · ext1; rename_i x; simp [pow_two]
     let B:=Module.finBasis ℂ X; rw[LinearMap.trace_eq_matrix_trace ℂ B, LinearMap.trace_eq_matrix_trace ℂ (B.map f)]; congr 1
-- derive magnitude. from one peak hat.
variable (D:Tide X)(p:Module.End ℂ W)(u:Module.End ℂ X)(θ:ℕ→ℝ)(h:∀ i,0<θ i)(f:ℕ→ X ≃ₗ[ℂ] W)
include h S D
lemma meter (hp:S.Leans p)(ht:D.Leans u)(hu:u≠0)(H:∀ v:X,Tendsto (fun i=> ((θ i:ℂ)⁻¹) • ((f i).symm (p (f i v)))) atTop (𝓝 (u v))) : ∃ r:ℝ,0<r ∧ Tendsto θ atTop (𝓝 r):=by
    let F(i): Module.End ℂ X:= ((θ i:ℂ)⁻¹) • ((f i).symm.toLinearMap ∘ₗ p ∘ₗ (f i).toLinearMap); have ht':= (Complex.continuous_re.continuousAt (x:=LinearMap.trace ℂ X (u^2))).tendsto.comp (track F u H); let G:= LinearMap.trace ℂ W (p^2); let a:=- (LinearMap.trace ℂ X (u^2)).re; let b:=-G.re; have ha:0<a:= Tide.billQ D u ht hu; have H:Tendsto (fun i=> (θ i^2)⁻¹*b) atTop (𝓝 a):=by
        apply ht'.neg.congr'; refine Eventually.of_forall fun i=>?_ ; have hz:LinearMap.trace ℂ X ((F i)^2)=((θ i:ℂ)^2)⁻¹ • G:=by unfold F; rw [smul_pow, _root_.map_smul, inv_pow,chord]; -- def rfl?
        change - (LinearMap.trace ℂ X ((F i)^2)).re=_; rw[hz,← Complex.ofReal_pow,← Complex.ofReal_inv,smul_eq_mul,Complex.re_ofReal_mul]; rw [show b= -G.re from rfl]; exact (mul_neg _ (G.re)).symm
    have hb:0<b:=by
        obtain ⟨i,hi⟩:= (H.eventually (lt_mem_nhds ha)).exists -- Ioi
        by_contra! he; exact not_le_of_gt hi (mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤(θ i^2)⁻¹) he)
    refine ⟨Real.sqrt (b/a),Real.sqrt_pos.2 (div_pos hb ha),?_⟩
    refine ((tendsto_const_nhds (x:=b)).div H ha.ne'|>.sqrt).congr' ?_
    refine Eventually.of_forall fun i=>?_ ; change Real.sqrt (b /((θ i^2)⁻¹*b))= _; rw [show b/(_)=θ i^2 from ?_,Real.sqrt_sq (h i).le]; field_simp [(h i).ne',hb.ne']
end YM.Vern
#print axioms YM.Vern.Tide.billQ
#print axioms YM.Vern.meter
