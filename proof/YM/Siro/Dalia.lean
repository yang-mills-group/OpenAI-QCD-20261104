import YM.Siro.Obel
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Function Set Filter Analysis
open Fields (SimpleK)
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {F :Fields}{a b:Axis}{n:ℕ}{S:F.Kernel}(H:Brawl S)
lemma decomposePoints (x : Points n) :
    ∑ i : Fin n, ∑ a : Axis, x i a • Points.direction i a = x := by
  apply PiLp.ext
  intro j
  have he : ∑ a : Axis, x j a • basis a = x j := by
    apply PiLp.ext
    intro b
    simp
  simpa [Points.direction, Pi.single_apply, smul_ite] using he

lemma mul_move (s r : Ortho) (x : Points n) :
    Points.move (s*r) x = Points.move s (Points.move r x) :=
  PiLp.ext fun i => Ortho.move_mul s r (x i)

lemma one_move (x : Points n) : Points.move 1 x = x :=
  PiLp.ext fun i => Ortho.move_one (x i)

lemma unmove (s : Ortho) (x : Points n) :
    Points.move s (Points.move s⁻¹ x) = x :=
  PiLp.ext fun i => Ortho.move_inv s (x i)

/-- Positions have velocity Kx (evaluated at the moving point). -/
theorem velocity (K : Ortho.Skew) (x : Points n) (t : ℝ) :
    HasDerivAt (fun s => Points.move (Ortho.oneParameter K s) x)
      (points fun i => M4.move K.val ((Points.move (Ortho.oneParameter K t) x) i)) t := by
  let A : M4 →L[ℝ] Points n := LinearMap.toContinuousLinearMap {
    toFun m := points fun i => M4.move m (x i)
    map_add' m l := by
      ext1 i
      change (Matrix.toEuclideanLin (m+l)) (x i) =
        (Matrix.toEuclideanLin m) (x i) + (Matrix.toEuclideanLin l) (x i)
      rw [map_add, LinearMap.add_apply]
    map_smul' a m := by
      ext1 i
      change (Matrix.toEuclideanLin (a • m)) (x i) = a • (Matrix.toEuclideanLin m) (x i)
      rw [map_smul, LinearMap.smul_apply] }
  have he : HasDerivAt (fun s => Points.move (Ortho.oneParameter K s) x)
      (A (K.val * NormedSpace.exp (t • K.val))) t :=
    A.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' K.val t)
  have hm : A (K.val * NormedSpace.exp (t • K.val)) =
      points fun i => M4.move K.val ((Points.move (Ortho.oneParameter K t) x) i) :=
    PiLp.ext fun i => M4.move_mul K.val (NormedSpace.exp (t • K.val)) (x i)
  rw [hm] at he
  exact he

noncomputable local instance levRR(F:Fields)(d:ℕ): NormedSpace ℝ ↥(F.level d):=NormedSpace.restrictScalars ℝ ℂ _
private lemma descend {d:ℕ}(f:ℝ→↥(F.level d))(v:F.level d)(x:ℝ)(h:HasDerivAt (fun t:ℝ=>(f t).val) v.val x):HasDerivAt f v x:=by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr; apply tendsto_subtype_rng.mpr; exact h.tendsto_slope_zero
include H
lemma moveDer (v:Fin n→ F.W)(y:ℝ→Points n)(t:ℝ)(hx:y t∈conf n)(dy:Points n)(hy:HasDerivAt y dy t): HasDerivAt (fun u=> readQ S v (y u))
      (∑ i : Fin n, ∑ a : Axis, dy i a • readQ S (update v i (F.partialD a (v i))) (y t)) t:=by
    have he:= ((discC H hx v).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hy
    apply he.congr_deriv; conv_lhs=>arg 2; rw[← decomposePoints dy]
    simp only[map_sum, map_smul]; simp_rw [←fromQ H hx]; rfl
variable (d:Fin n→ℕ)
private abbrev Tuple (F:Fields)(d:Fin n→ℕ):=(i:Fin n)→ ↥(F.level (d i))
private def meter (p: Points n× Tuple F d):ℂ:= S n p.1 (fun i=>(p.2 i).val)
private lemma fuse (x:Points n)(hx:x∈conf n)(v:Tuple F d): ContDiffAt ℝ ∞ (meter (S:=S) d) (x,v):=by
     let M(i:Fin n):= Fin (Module.finrank ℂ (F.level (d i))); haveI(i:Fin n): Fintype (M i):=inferInstanceAs (Fintype (Fin _))
     haveI(i:Fin n):FiniteDimensional ℂ (F.level (d i)):= H.anchored _; let B(i:Fin n):= Module.finBasis ℂ (F.level (d i)); let b(r:(i:Fin n)→ M i)(i):= ((B i) (r i)).val; let a(r:(i:Fin n)→M i)(i:Fin n) (p:Points n× Tuple F d):= (B i).coord (r i) (p.2 i); rw [show meter (S:=S) d=(fun p=> ∑ r:(i:Fin n)→ M i,(∏ i:Fin n,a r i p)* S n p.1 (b r)) from ?_]; swap
     · funext p; unfold meter
       let f(i:Fin n)(j:M i):F.W:= (B i).repr (p.2 i) j • ((B i) j).val
       have he(i:Fin n): (p.2 i).val=∑ j:M i, f i j:=by
             unfold f; nth_rw 1[← (B i).sum_repr (p.2 i)]; rw[Submodule.coe_sum]; rfl
       change S n _ _=_; rw[show (fun i=>(p.2 i).val)=(fun i=> ∑ j:M i, f i j) from funext he, MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro i _; exact (S n p.1).map_smul_univ _ _ -- eval underscore stuck
     apply ContDiffAt.sum; intro r _; apply (contDiffAt_prod (fun i _=> ?_)).mul ((discC H hx (b r)).comp (x,v) contDiffAt_fst)
     let P:Tuple F d →L[ℝ] ↥(F.level (d i)):= ContinuousLinearMap.proj i; let U:= ((B i).coord (r i)).toContinuousLinearMap.restrictScalars ℝ; change ContDiffAt ℝ ∞ (fun p:Points n × Tuple F d=>U (P p.2)) _; exact ((U.comp P).contDiff.contDiffAt.comp (x,v) contDiffAt_snd)
private lemma lights (x :Points n)(hx:x∈conf n)(w:ℝ→ Tuple F d)(t:ℝ)(dw:Tuple F d)(hw:HasDerivAt w dw t): HasDerivAt (fun u=> meter (S:=S) d (x,w u)) (∑ i: Fin n, readQ S (update (fun j=>(w t j).val) i (dw i).val) x) t:=by
    let Q : ContinuousMultilinearMap ℝ (fun i=> ↥(F.level (d i))) ℂ:={ toMultilinearMap:=((S n x).compLinearMap fun i=>(F.level (d i)).subtype).restrictScalars ℝ
                                                                       cont:=by refine continuous_iff_continuousAt.mpr (fun (v:Tuple F d)=>?_); exact ((fuse H d x hx v).comp v (contDiffAt_const.prodMk contDiffAt_id)).continuousAt }
    have he:HasDerivAt (fun u=> meter (S:=S) d (x,w u)) (Q.linearDeriv (w t) dw) t:= (Q.hasFDerivAt _).comp_hasDerivAt t hw
    rw [ContinuousMultilinearMap.linearDeriv_apply] at he; apply he.congr_deriv; apply Finset.sum_congr rfl; intro i _; unfold Q; apply congr_arg (S n x); funext j; by_cases h:j=i; · subst j; simp
    simp only[update_of_ne h]; rfl
variable (ha:∀ d,8 ≤ d→∀ v∈ F.level d,∀ p:EuPin,F.action p v∈ F.level d)
variable (ht:∀ (v:F.W) (g:Ortho.Skew)(p:ℝ→EuPin),EuPin.Path g p→∀ t,HasDerivAt (fun r=> F.action (p r) v) (F.lie g (F.action (p t) v)) t)
include ha ht
lemma lines (K:Ortho.Skew) (p:ℝ→ EuPin)(h:EuPin.Path K p)(x:Points n)(hx:x∈conf n)(v:Fin n→ F.W)(r:ℝ): S n (Points.move (p r).coord x) (F.action (p r) ∘ v) = S n x v:=by
    choose d hD hu using fun i=> H.high (v i)
    let w(t:ℝ):Tuple F d:= fun i=> ⟨F.action (p t) (v i), ha _ (hD i) _ (hu i) _⟩; let y(t):= Points.move (p t).coord x; let f(t:ℝ):= meter (S:=S) d (y t,w t); have he(t:ℝ):HasDerivAt f 0 t:=by
          let dy:= points fun i=> M4.move K.val (y t i); let dw:Tuple F d:= fun i=> ⟨F.lie K (w t i), H.lie_p _ _ (hD i) (w t i) (w t i).property⟩; have hv : y t∈conf n:= Points.move_in _ hx
          have hy : HasDerivAt y dy t:=by unfold dy y; simp_rw[h.2.2]; exact velocity ..
          have hw: HasDerivAt w dw t:= hasDerivAt_pi.mpr fun i=> descend _ (dw i) t (ht (v i) K p h t)
          let D:= fderiv ℝ (meter (S:=S) d) (y t,w t); have hD : HasFDerivAt (meter (S:=S) d) D (y t,w t):=((fuse H _ _ hv _).differentiableAt (by simp)).hasFDerivAt
          let U(i:Fin n):=(w t i).val; have h₁: HasDerivAt (fun s=>readQ S U (y s)) (D (dy,0)) t:= HasFDerivAt.comp_hasDerivAt (l:=meter (S:=S) d) t hD (hy.prodMk (hasDerivAt_const t _)); have h₂ : HasDerivAt (fun s=>meter (S:=S) d (y t,w s)) (D (0,dw)) t:= HasFDerivAt.comp_hasDerivAt (l:=meter (S:=S) d) t hD ((hasDerivAt_const t _).prodMk hw)
          apply HasDerivAt.congr_deriv (show HasDerivAt f (D (dy,dw)) t from HasFDerivAt.comp_hasDerivAt (l:=meter (S:=S) d) t hD (hy.prodMk hw)); rw [show D (dy,dw)=D (dy,0)+D (0,dw) from by rw[← map_add]; simp,h₂.unique (lights H d _ hv w t dw hw),h₁.unique (moveDer H U _ _ hv _ hy)]; rw[add_comm,← Finset.sum_add_distrib]; exact opened H (y t) hv U K
    have hp : f r=f 0:= is_const_of_deriv_eq_zero (fun u=>(he u).differentiableAt) (fun u=>(he u).deriv) r 0; change f r=_; rw[hp]; unfold f meter; dsimp only [y,w]; rw[h.1,map_one]; change S n (Points.move 1 _) _= S n _ _; rw [one_move]; rfl
end YM.Massive.Siro
#print axioms YM.Massive.Siro.lines
