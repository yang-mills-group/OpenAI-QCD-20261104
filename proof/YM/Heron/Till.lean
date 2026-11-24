import YM.Heron.Finger
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct DawnS
open Maxwell.Free (exportFlux fromCenter)
open Maxwell (grad away)
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius
open Finset LinearMap
variable {d:ℕ}(x:Points 2)(hx:x∈conf 2)(Δ:Ortho.Skew)(χ:E4→ℝ)(hχ:Massive.Physics.Window x χ)
local notation "F"=> Pol d
local notation "R"=> Axis×Axis→ Label 8
local notation "T"=> plumes x χ Δ
local notation "Q"=> actS x Δ
lemma fullMap(i: R)(a:Axis)(y:E4): ∃ L:F→ₗ[ℂ] F →ₗ[ℂ]ℂ, ∀ v w, Q (![v,w]) i a y=L v w:=by
    choose W hW using fun b:Axis=> bMap (d:=d) x (i (a,b)) y; refine ⟨∑ j:Axis,(↑(fromCenter Δ.val (x 0) j y):ℂ) • W j,fun v w=> ?_⟩; unfold actS; simp_rw [hW,LinearMap.sum_apply, LinearMap.smul_apply]; rfl
include hx hχ
noncomputable def flower (i: R) : Pol d→ₗ[ℂ] Pol d→ₗ[ℂ]ℂ where
    toFun v:={ toFun:=fun w=>T i v w,map_add':=fun a b=>by unfold plumes; refine Eq.trans (b:=exportFlux (Q (![v,a]) i+ Q (![v,b]) i) χ) ?_ (value_add χ (wearθ x hx Δ χ hχ v a i) (wearθ x hx Δ χ hχ v b i)); apply congr_arg (fun f=>exportFlux f χ); funext j y; obtain ⟨L,h⟩:= fullMap (d:=d) x Δ i j y; change _= Q _ _ _ _+Q _ _ _ _; rw[h,h,h,_root_.map_add], map_smul':=fun c a=>by unfold plumes; refine Eq.trans (b:=exportFlux (c • Q (![v,a]) i) χ) ?_ (valueM χ c); apply congr_arg (fun f=>exportFlux f χ); funext j y; obtain ⟨L,h⟩:= fullMap (d:=d) x Δ i j y; change Q _ _ j y=c • Q _ _ j y; rw[h,h,_root_.map_smul] }
    map_add' a b:=by apply LinearMap.ext; intro v; change T i (a+b) v=T i a v+T i b v; unfold plumes; refine Eq.trans (b:=exportFlux (Q (![a,v]) i+Q (![b,v]) i) χ) ?_ (value_add χ (wearθ x hx Δ χ hχ a v i) (wearθ x hx Δ χ hχ b v i)); apply congr_arg (fun f=>exportFlux f χ); funext j y; obtain ⟨L,h⟩:= fullMap (d:=d) x Δ i j y; change Q _ _ j y= Q _ _ j y+Q _ _ j y; rw[h,h,h,_root_.map_add]; rfl
    map_smul' c a:=by apply LinearMap.ext; intro v; change T i (c • a) v=c • T i a v; unfold plumes; refine Eq.trans (b:=exportFlux (c • Q (![a,v]) i) χ) ?_ (valueM χ c); apply congr_arg (fun f=>exportFlux f χ); funext j y; obtain ⟨L,h⟩:= fullMap (d:=d) x Δ i j y; change Q _ _ j y=c • Q _ _ j y; rw[h,h,_root_.map_smul]; rfl
noncomputable def partyR (v w: Pol d): R →ₗ[ℂ]ℂ where
   toFun i:= T i v w
   map_add' i j:=by unfold plumes; refine Eq.trans (b:=exportFlux (Q (![v,w]) i+ Q (![v,w]) j) χ) ?_ (value_add χ (wearθ x hx Δ χ hχ v w i) (wearθ x hx Δ χ hχ v w j)); apply congr_arg (fun f=> exportFlux f χ); funext j y; unfold actS; simp only [Pi.add_apply, Submodule.coe_add,_root_.map_add,smul_add,sum_add_distrib]
   map_smul' t i:=by unfold plumes; refine Eq.trans (b:=exportFlux (t • Q (![v,w]) i) χ) ?_ (valueM χ t); apply congr_arg (fun f=> exportFlux f χ); funext j y; unfold actS; simp only [Pi.smul_apply, Submodule.coe_smul,_root_.map_smul,←smul_comm t, ← smul_sum]
omit hx hχ
lemma bil :∃ M:F →ₗ[ℂ] F →ₗ[ℂ] ℂ,∀ p q: F, ear x p q=M p q:=by
   refine ⟨Hail.dual d d x, fun p q=>?_⟩; rw [Hail.valD]; let g:Fin 2→ℕ:=![d,d]; let f:Fin 2→ℕ:=fun _=>d; let W:= Hail.petals (A:=Pol) p q; let G:= (![p,q]); change UV.Free.moment f x G= UV.Free.moment g x W; have ht:g=f:=by funext i; fin_cases i<;>rfl
   have hc(v w:Fin 2→ℕ)(hv:v=w)(p:(i:Fin 2)→Pol (v i))(q:(i:Fin 2)→Pol (w i))(h:∀ i:Fin 2,HEq (p i) (q i)):UV.Free.moment v x p=UV.Free.moment w x q:=by
       subst w; rw [show p=q from funext fun i=>eq_of_heq (h i)]
   exact (hc g f ht W G (fun i=>by fin_cases i<;> exact HEq.rfl)).symm
private lemma giant {V:Type} [AddCommGroup V][Module ℂ V] {W:Type}(U:Module.Basis W ℂ V) (L K: V→ₗ[ℂ] V →ₗ[ℂ]ℂ)(f:ℝ→Module.End ℂ V)(c:ℂ)(hh:∀ i j:W,HasDerivAt (fun t=>L (f t (U i)) (U j)) (c*K (U i) (U j)) 0)(p q:V): HasDerivAt (fun t=> L (f t p) q) (c*K p q) 0:=by
     rw[← U.linearCombination_repr p,← U.linearCombination_repr q]; simp only [Finsupp.linearCombination_apply,Finsupp.sum, _root_.map_sum,_root_.map_smul, LinearMap.sum_apply,LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum];
     refine HasDerivAt.fun_sum (fun i _=> HasDerivAt.fun_sum (fun j _=>?_)); refine HasDerivAt.congr_deriv ((((hh j i).const_mul _).const_mul _)) ?_; ring
include hx hχ
lemma carries (i:R)(f:ℝ→ EuPin×PClan)(c:ℂ)(H:∀(p q:GPol) (u v:List (letters d)), HasDerivAt (fun t:ℝ=> ear x (carr (f t) d (p⊗ₜ[ℂ] Hail.tagD u)) (q⊗ₜ[ℂ] Hail.tagD v)) (c * T i (p⊗ₜ[ℂ] Hail.tagD u) (q⊗ₜ[ℂ] Hail.tagD v)) 0)(p q: Pol d): HasDerivAt (fun t=> ear x (carr (f t) d p) q) (c*T i p q) 0:=by
     obtain ⟨L,h⟩:= bil (d:=d) x; let K:= flower (d:=d) x hx Δ χ hχ i; have hp(v w:F):T i v w=K v w:=rfl; simp_rw[h,hp] at *; let U:= UV.Free.basisU d; have hh(u v: PowerPair d) : HasDerivAt (fun t:ℝ=> L (carr (f t) d (U u)) (U v)) (c*K (U u) (U v)) 0:=by unfold U; rw [Hail.sweet x hx,Hail.sweet x hx]; exact H ..
     exact giant U L K (fun t=>carr (f t) d) c hh p q
end YM.Heron
#print axioms YM.Heron.partyR
#print axioms YM.Heron.flower
#print axioms YM.Heron.bil
