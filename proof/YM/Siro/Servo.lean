import YM.Siro.Rush
set_option maxHeartbeats 420000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Fields (SimpleK)
open Ward (inc)
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff BigOperators
variable {F:Fields}{a b:Axis}{S:F.Kernel}(V:Chamber S a)(H:Brawl S)
variable {d e:ℕ}(hd:8 ≤ d)(he:8 ≤e)(v:F.level d)(w:F.level e)(K:Ortho.Skew)
set_option quotPrecheck false
local notation "A"=> ↥(F.level d)
local notation "B"=> ↥(F.level e)
noncomputable def whip: Module.End ℂ (F.level d):= (F.lie K).restrict fun x hx=> H.lie_p K _ hd x hx
section
-- Need NormedSpace ℝ (F.level). Instances
noncomputable local instance levR(F:Fields)(d:ℕ): NormedSpace ℝ ↥(F.level d):=NormedSpace.restrictScalars ℝ ℂ _
noncomputable def bell(t:ℝ): A:=by
     haveI:= H.anchored d; let U:= LinearMap.toContinuousLinearMap (whip H hd K); exact Ward.LieTick U t v
include hd
lemma tick (t:ℝ):AnalyticAt ℝ (fun s=>bell H hd v K s) t ∧ HasDerivAt (fun s=>bell H hd v K s) (bell H hd (whip H hd K v) K t) t:=by
     haveI:= H.anchored d; letI : CompleteSpace (F.level d) := FiniteDimensional.complete ℂ _; let M:= LinearMap.toContinuousLinearMap (whip H hd K); exact Ward.ticking v M t
lemma baseK : bell H hd v K 0=v:=by unfold bell; apply Ward.stuck
variable (p: ↥(F.level d)×↥(F.level e))
def lit{F:Fields}{S:F.Kernel}{d e:ℕ}(v:F.level d)(w:F.level e)(x:E4):= pairQ S v.val w.val x -- S implicit ambiguity
omit hd
lemma stars (J : Module.Basis (Fin (Module.finrank ℂ A)) ℂ A) (Z : Module.Basis (Fin (Module.finrank ℂ B)) ℂ B) (x:E4) : lit (S:=S) v w x=∑ i, ∑ j, J.coord i v * Z.coord j w * lit (S:=S) (J i) (Z j) x := by
     let s:= S 2 (points ![0,x]); let L(z:A)(x:B):= s (![z.val,x.val]); let P(v:A)(w:B):= (![v.val,w.val]); let Y(x:A):B→ₗ[ℂ]ℂ:= (s.toLinearMap (P x w) 1) ∘ₗ (F.level e).subtype; let M(w:B): A →ₗ[ℂ]ℂ:= (s.toLinearMap (P v w) 0) ∘ₗ (F.level d).subtype
     have he(i:A)(j:B):L i j=Y i j:=by unfold Y L; rw[LinearMap.comp_apply,MultilinearMap.toLinearMap_apply]; apply congr_arg; funext k;fin_cases k<;>simp[P]
     have ht(i:A)(j:B):L i j=M j i:=by unfold M L; rw[LinearMap.comp_apply,MultilinearMap.toLinearMap_apply]; apply congr_arg; funext k; fin_cases k<;>simp[P]
     change L v w=_; rw[ht]; conv_lhs=> arg 2; rw[← J.sum_repr v]
     rw[map_sum]; -- conv bug newline
     apply Finset.sum_congr rfl; intro i _; rw[map_smul,←ht,he]
     conv_lhs=>rhs; arg 2; rw[← Z.sum_repr w]
     rw [map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw[map_smul,←he,mul_assoc]; rfl
open Ward.Circle
noncomputable def ann (p:↥(F.level d)×↥(F.level e))(a:Axis)(x:PDE.V):ℂ:= lit (S:=S) (bell H hd p.1 K (-θ x)) (bell H he p.2 K (-θ x)) (r x • basis a)
include V hd
lemma ann_at(p:A×B)(x:PDE.V)(hx:x∈PDE.side):AnalyticAt ℝ (ann H hd he K p a) x:=by
     haveI:= H.anchored d; haveI:=H.anchored e; let M:= Module.finBasis ℂ A; let L:= Module.finBasis ℂ B
     unfold ann; simp_rw [stars (v:=bell H hd _ _ _) (w:=bell H he _ _ _) M L]
     obtain ⟨hθ,hr⟩:= uniform hx; apply ContDiffAt.analyticAt; apply ContDiffAt.sum; intro i hi; apply ContDiffAt.sum; intro j hj
     let A':=(LinearMap.toContinuousLinearMap (M.coord i)).restrictScalars ℝ; let B':=(LinearMap.toContinuousLinearMap (L.coord j)).restrictScalars ℝ; let h:=((((A'.analyticAt _).comp (((tick H hd p.1 K _).1).comp hθ.neg)).mul ((B'.analyticAt _).comp (((tick H he p.2 K _).1).comp hθ.neg))).mul ((radial V H (M i).val (L j).val _ (pos hx)).comp hr)).contDiffAt (n:=ω); exact h
omit V
noncomputable def rising (p:A × ↥(F.level e)): A× B := (whip H hd K p.1,p.2)
noncomputable def rising' (p:↥(F.level d)× B): A × B := (p.1,whip H he K p.2)
include V
lemma settles(x:PDE.V)(hx:x∈PDE.side): PDE.law (rising H hd K) (rising' H he K) (fun p x=> ann H hd he K p a x) p x=0:=by
  let L:=fun p x=> ann H hd he K p a x; have hp:= Ward.Circle.transport ((ann_at V H hd he K p x hx).differentiableAt)
  suffices he' :HasDerivAt (fun t=> ann H hd he K p a (shift x t)) (-(L (rising H hd K p) x)+ -(L (rising' H he K p) x)) 0 by
       unfold PDE.law; rw [PDE.vector (show PDE.C _ from (fun v hv=>(ann_at V H hd he K p v hv).contDiffAt)) hx]; rw [show (-x.2 • PDE.e+x.1 • PDE.i)= Ward.Circle.u x from rfl, hp.unique he']; unfold L; abel
  haveI:= H.anchored d; haveI:= H.anchored e
  let M:=Module.finBasis ℂ A; let N:=Module.finBasis ℂ B; obtain ⟨hθ,hR⟩:= Ward.Circle.vector hx
  let f(s:ℝ):= -θ (shift x s); let r(s:ℝ):= Ward.Circle.r (shift x s); have hw:f 0= -θ x:=by simp[f]
  have hy:r 0=Ward.Circle.r x:=by simp[r]
  let X(i):=(M.coord i).toContinuousLinearMap.restrictScalars ℝ; let Y(j):=(N.coord j).toContinuousLinearMap.restrictScalars ℝ
  unfold L ann; change HasDerivAt (fun t=> lit (S:=S) (bell H hd p.1 K (f t)) (bell H he p.2 K (f t)) (r t • basis a)) (-lit (S:=S) (bell H hd (whip H hd K p.1) K (-θ x)) (bell H he p.2 K (-θ x)) (Ward.Circle.r x • basis a) + -lit (S:=S) (bell H hd p.1 K (-θ x)) (bell H he (whip H he K p.2) K (-θ x)) (Ward.Circle.r x • basis a)) 0
  rw[←hw,←hy]; simp_rw [stars (v:=bell H hd _ _ _) (w:=bell H he _ _ _) M N]; simp_rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]; apply HasDerivAt.fun_sum; intro i hi; apply HasDerivAt.fun_sum; intro j hj
  have htt:HasDerivAt f (-1) 0:= hθ.neg; have he':HasDerivAt r 0 0:=hR; have hr(t:ℕ)(h:8≤t)(v:F.level t): HasDerivAt (fun r=> bell H h v K (f r)) (-bell H h (whip H h K v) K (f 0)) 0:=by
        have hv:= (tick H h v K (f 0)).2.scomp 0 htt; exact hv.congr_deriv (neg_one_smul ..)
  have hV: HasDerivAt (fun t=>X i (bell H hd p.1 K (f t))) (-X i (bell H hd (whip H hd K p.1) K (f 0))) 0 :=by
        refine ((X i).hasFDerivAt.comp_hasDerivAt 0 (hr _ hd p.1)).congr_deriv (map_neg ..)
  have hU: HasDerivAt (fun t=>Y j (bell H he p.2 K (f t))) (-Y j (bell H he (whip H he K p.2) K (f 0))) 0 := ((Y j).hasFDerivAt.comp_hasDerivAt 0 (hr _ he p.2)).congr_deriv (map_neg ..)
  let g(t:ℝ):= lit (S:=S) (M i) (N j) (t • basis a); have hG:HasDerivAt (g∘r) 0 0:=by
        have hv:AnalyticAt ℝ g (r 0):= radial V H _ _ (r 0) (hy.symm ▸ pos hx); simpa using! hv.differentiableAt.hasDerivAt.scomp (0:ℝ) he'
  change HasDerivAt _ (-(X i (bell H hd (whip H hd K p.1) K (f 0)) * Y j (bell H he p.2 K (f 0))*g (r 0))+ -(X i (bell H hd p.1 K (f 0))* Y j (bell H he (whip H he K p.2) K (f 0))*g (r 0))) _
  apply HasDerivAt.congr_deriv ((hV.mul hU).mul hG); dsimp only[Pi.mul_apply,Function.comp_apply]; ring
end
end YM.Massive.Siro
#print axioms YM.Massive.Siro.settles
#print axioms YM.Massive.Siro.baseK
