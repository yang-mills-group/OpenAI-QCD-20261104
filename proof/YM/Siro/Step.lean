import YM.Siro.Cape
import YM.Ward.Circles
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Siro
open Set Function Filter Analysis
open Fields (SimpleK)
open scoped Topology ContDiff BigOperators InnerProductSpace
variable {F : Fields} {a b : Axis} {n:ℕ}{S : F.Kernel}
-- same kernel. Unicode Lie notation. vector real dot.
def readQ(S:F.Kernel)(p:Fin n→F.W)(x:Points n):ℂ:= S n x p
def angQ(S:F.Kernel)(p:Fin n→F.W)(K:Ortho.Skew)(x:Points n):=
       ∑ i:Fin n, (readQ S (update p i (F.lie K (p i))) x +∑ j:Axis,M4.move K.val (x i) j • readQ S (update p i (F.partialD j (p i))) x)
structure Brawl (S:F.Kernel):Prop extends SimpleK S where
     anchored (d:ℕ):FiniteDimensional ℂ (F.level d)
     high (x:F.W) : ∃ d:ℕ,8 ≤ d ∧ x∈F.level d
     lie_p(g:Ortho.Skew)(d:ℕ)(h:8 ≤ d) (x:F.W)(he:x∈F.level d):F.lie g x∈ F.level d
     mixed(P Q:Axis)(v:F.W): F.partialD P (F.partialD Q v)= F.partialD Q (F.partialD P v)
     acts(g:Ortho.Skew)(a:Axis)(x:F.W): F.partialD a (F.lie g x)+ ∑ i:Axis,(g.val i a:ℂ) • F.partialD i x= F.lie g (F.partialD a x)
     line(n:ℕ)(p:Fin n→ F.W)(K:Ortho.Skew)(x:Points n)(l:Axis)(h:Ward.onLine l x)(hv:x∈conf n): angQ S p K x=0
     parity₂:Involutive F.parity
     adj_flip(a:Axis):Involutive (F.adj a)
     mirror (a:Axis):∃ f:F.W≃ₗ[ℂ]F.W,∀ (n:ℕ)(p:Fin n→F.W)(x:Points n)(hv:x∈conf _),S n x p= S n (Points.move (Signed.reflect a) x) (f ∘ p)
variable (H:Brawl S){x:Points n}(hx:x∈conf n)
include H hx
lemma discC (q:Fin n→ F.W):ContDiffAt ℝ ∞ (readQ S q) x:= (H.smooth n q _ hx)|>.contDiffAt ((conf_open _).mem_nhds hx) -- H.Smooth signature
lemma fromQ (i: Fin n)(a:Axis)(p:Fin n→F.W) :Analysis.D (Points.direction i a) (readQ S p) x= readQ S (update p i (F.partialD a (p i))) x:= H.derivatives n p i x hx a -- check
lemma acrossQ (q:Fin n→F.W)(a:Axis)(k:Fin n)(K:Ortho.Skew) : D (Points.direction k a) (angQ S q K) x= angQ S (update q k (F.partialD a (q k))) K x:=by
  let r:= update q k (F.partialD a (q k)); let t:= Points.direction k a
  let g (i) := readQ S (update q i (F.lie K (q i)))
  let L (i) (b : Axis) := readQ S (update q i (F.partialD b (q i)))
  let y (i) (b) (z : Points n) := Ward.factor i b K z • L i b z
  let f (i) z := g i z + ∑ b, y i b z
  have hu (i : Fin n) b : DifferentiableAt ℝ (L i b) x := (discC H hx _).differentiableAt (by simp)
  have hh i b : DifferentiableAt ℝ (y i b) x := (Ward.factor i b K).differentiableAt.smul (hu i b)
  have hz i : DifferentiableAt ℝ (g i) x := (discC H hx _).differentiableAt (by simp)
  have hp i : DifferentiableAt ℝ (f i) x := (hz i).add (DifferentiableAt.fun_sum fun b hb => hh i b)
  have hm (i : Fin n) : D t (f i) x=D t (g i) x+∑ b, D t (y i b) x := by
    simp only [f,D,fderiv_fun_add (hz i) (DifferentiableAt.fun_sum (fun b hb => hh i b)),
      fderiv_fun_sum (fun b hb => hh i b),_root_.sum_apply, _root_.add_apply]
  change fderiv ℝ (fun z => ∑ i, f i z) x t= _
  rw [fderiv_fun_sum (fun i hi => hp i),_root_.sum_apply]; unfold angQ
  apply Finset.sum_congr rfl; intro i hi
  change D t (f i) x=_; rw [hm]
  by_cases hv : i=k
  · subst i; simp only [r,update_self,update_idem]
    have hvb b : D t (y k b) x=(K.val b a) • readQ S (update q k (F.partialD b (q k))) x + Ward.factor k b K x • readQ S
        (update q k (F.partialD b (F.partialD a (q k)))) x := by
      unfold y; rw[Ward.D_prod _ _ _ _ (hu k b)]; dsimp only[t,L]; rw[Ward.fac, if_pos rfl,fromQ H hx,update_self,update_idem,H.mixed a b]
    simp_rw [hvb,Finset.sum_add_distrib,← add_assoc]; congr 1; unfold g; rw [fromQ H hx,update_self,update_idem]; let A:= (S n x).toLinearMap q k; change A (F.partialD a _)+ (∑ i:Axis,(K.val i a:ℂ) • A (F.partialD i (q k)))=_; apply Eq.trans _ (show A (F.lie K _) = _ from rfl); rw[←H.acts, map_add,map_sum]; simp only [map_smul]
  have Hq:update q k (F.partialD a (q k)) i=q i:= update_of_ne hv ..; rw[Hq]; congr 1
  · unfold g; rw[fromQ H hx,update_of_ne (Ne.symm hv),update_comm (show k≠i from Ne.symm hv)]
  apply Finset.sum_congr rfl; intro b hb; unfold y; rw [Ward.D_prod _ _ _ _ (hu i b)]; dsimp only [L,t]; rw[Ward.fac,if_neg (Ne.symm hv),zero_smul,zero_add,fromQ H hx,update_of_ne (Ne.symm hv),update_comm (show k ≠ i from Ne.symm hv)]; rfl
lemma axe (K : Ortho.Skew) (q : Fin n → F.W) : ContDiffAt ℝ ∞ (angQ S q K) x := by
  apply ContDiffAt.sum
  intro i hi; apply ContDiffAt.add (discC H hx _); apply ContDiffAt.sum
  exact fun b _ => (Ward.factor i b K).contDiff.contDiffAt.smul (discC H hx _)
-- jets on every extreme
omit hx
lemma trips (K : Ortho.Skew) (q : Fin n → F.W)
    (x : Points n) (j b s) (ht : Ward.cast x j b s∈conf _) :
    HasDerivAt (angQ S q K ∘ Ward.cast x j b) (angQ S (update q j (F.partialD b (q j))) K (Ward.cast x j b s)) s:=by
     rw[← acrossQ H ht]; exact ((axe H ht K q).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (Ward.moves x j b s)
lemma jet_line (K : Ortho.Skew) (q : Fin n → F.W)
    (x : Points n) (i b s) (ht : Ward.cast x i b s∈conf _) (hp : ∀ w, angQ S w K (Ward.cast x i b s)=0) (m:ℕ) : iteratedDeriv m (angQ S q K ∘ Ward.cast x i b) s=0:=by
     induction m generalizing q with
     | zero=>simp[hp]
     | succ m ih=>
            have hx:∃ w, deriv (angQ S q K ∘ Ward.cast x i b) =ᶠ[𝓝 s] angQ S w K ∘ Ward.cast x i b:=⟨_, Eventually.mono (p:=fun k=>Ward.cast x i b k∈conf _) ((Ward.moves x i b s).continuousAt.preimage_mem_nhds ((conf_open _).mem_nhds ht)) (fun k hk=>(trips H K q x i b k hk).deriv)⟩
            obtain ⟨w,hw⟩:= hx; rw [iteratedDeriv_succ',hw.iteratedDeriv_eq (n:=m)]; exact ih _
end YM.Massive.Siro
#print axioms YM.Massive.Siro.jet_line
