import YM.QCD.King.Nacre
/-! # dimension-independent open Cauchy and stacked price. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tidings
open Filter Function Lattice RG Pressure Finset ConnectedActivityE6 Blaze Port Grass Cove Loom Fleet Creek Kit Run Metric
open scoped BigOperators Topology InnerProductSpace ContDiff Classical Matrix.Norms.L2Operator
open Brush
section cyl
variable {E F G:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
variable [NormedAddCommGroup F][NormedSpace ℂ F][FiniteDimensional ℂ F]
variable {δ R M:ℝ}{k:ℕ}{x:E}{f:E→ F}
lemma polar (δ:ℝ)(h:0<δ)(k):0≤ Kit.toll δ k:=by induction k with
   | zero=> exact zero_le_one
   | succ k ih=> exact div_nonneg ih (by positivity)
-- same as Kit.buys but open-ball
lemma asks (h:0<δ)(hv:∀ i∈ ball x δ,DifferentiableAt ℂ f i)(he:∀ y∈ball x δ, ‖f y‖≤R)(k:ℕ):∀ y ∈ ball x (δ/2^k), ‖iteratedFDeriv ℂ k f y‖ ≤ Kit.toll δ k*R:=by
   induction k with
   | zero=> intro y hy; rw [norm_iteratedFDeriv_zero,Kit.toll,one_mul]; exact he y (by simpa using hy)
   | succ k ih=>
    intro y hy
    have he' : δ/2^(k+1)=(δ/2^k)/2 := by ring
    rw [← norm_fderiv_iteratedFDeriv,Kit.toll,he',div_mul_eq_mul_div]; rw [he'] at hy; refine Run.wind (by positivity) ?_ ih hy
    intro z hz
    have hT: z∈ ball x δ:= ball_subset_ball (div_le_self h.le (one_le_pow₀ (by norm_num))) hz
    have hf:AnalyticAt ℂ f z:= PolyDisc.finiteD _ (Filter.mem_of_superset (isOpen_ball.mem_nhds hT) hv)
    exact (hf.contDiffAt (n:=ω)).differentiableAt_iteratedFDeriv (WithTop.coe_lt_top _)
def letterP (δ:ℝ)(k:ℕ):=∑ i∈Finset.range (k+1), Kit.toll δ i
lemma let_pos (h:0<δ)(k:ℕ):0≤letterP δ k:= Finset.sum_nonneg fun i _=> polar _ h i
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E][NormedSpace ℝ F][IsScalarTower ℝ ℂ F][CompleteSpace F]
lemma beau (h:0<δ)(hv:∀ i∈ ball x δ,DifferentiableAt ℂ f i)(he:∀ y∈ball x δ, ‖f y‖≤R)(k:ℕ): Brush k (letterP δ k*R) 1 f x:=by
   have hp : AnalyticAt ℂ f x:=PolyDisc.finiteD _ (Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self h)) hv)
   apply offer.mpr; refine ⟨(hp.contDiffAt).restrict_scalars ℝ,fun i hi=>?_⟩
   unfold normJ; have hs: ContDiffAt ℂ (↑i : WithTop ℕ∞) f x:=hp.contDiffAt; rw [← hs.restrictScalars_iteratedFDeriv,comp_apply,ContinuousMultilinearMap.norm_restrictScalars]; exact (asks h hv he i _ (mem_ball_self (by positivity))).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> polar _ h i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) ((norm_nonneg _).trans (he x (mem_ball_self h))))
end cyl
section price
open NormedSpace
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E]{c:Side}{N:ℕ}
variable {s u v w e:ℝ}{x:E}{V:E → EvenA c N}{k:ℕ}
lemma fumage {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{f:E → F}(h:Brush k v u f x)(hq:u≤1) : Brush k (v*u) 1 (fun i=>f i-f x) x:=by
   apply offer.mpr; refine ⟨h.smooth.sub contDiffAt_const,?_⟩; rintro (_|i) hi
   · unfold normJ; rw [norm_iteratedFDeriv_zero]; simp only [sub_self,norm_zero]; exact mul_nonneg h.nonneg h.pos
   change ‖iteratedFDeriv ℝ (i+1) (f - fun _=> f x) x‖ ≤v*u; rw [iteratedFDeriv_sub_apply (h.smaller hi).smooth contDiffAt_const, iteratedFDeriv_succ_const, Pi.zero_apply,sub_zero]; exact (h.order _ hi).trans (mul_le_mul_of_nonneg_left ((pow_succ u i) ▸ (mul_le_of_le_one_left h.pos (pow_le_one₀ h.pos hq))) h.nonneg)
lemma stipend (z: EvenA c N)(h:‖z‖ ≤u): ‖exp z-1‖ ≤ Real.exp u - 1 :=by
    let g:=fun _: Keys c N=> (1:ℝ)
    have he (w:EvenA c N): Creek.load g (light _ w)=‖w‖:=by
       unfold Creek.load wscale g; rw [show Matrix.diagonal _= (1:Matrix (Keys c N) _ ℂ) from ?_, Grass.change_one]; rfl
       ext i j; simp [Matrix.diagonal_apply,Matrix.one_apply]
    rw [← he]; exact Cove.bought g _ u ( (he z).trans_le h)
def heartQ (k:ℕ):= k.factorial*(letterP 1 k*Real.exp 1)* (1+(1+(1:ℝ)))^k -- carefully
set_option maxHeartbeats 330000 in
lemma sprig (h:Brush k v 1 V x)(hv:v≤1)(hz:V x=0): Brush k (heartQ k*v) 1 (fun i=>exp (V i)-1) x:=by
    let A:=EvenA c N
    by_cases he : v=0
    · subst v; rw [mul_zero]; apply offer.mpr
      have hk : ContDiff ℝ ω (fun i:EvenA c N=> exp i-1):=(show ContDiff ℝ ω (fun i:EvenA c N=> exp i) from contDiff_iff_contDiffAt.mpr fun i=> (NormedSpace.exp_analytic (𝕂:=ℝ) (𝔸:=EvenA c N) i).contDiffAt).sub contDiff_const
      obtain ⟨t,_,hp⟩:= Brush.neighborhood (k:=k) (V x) (show ContDiffAt ℝ (↑k:WithTop ℕ∞) _ (V x) from hk.contDiffAt.of_le le_top); have hy:= Brush.compound hp.self_of_nhds h.smooth (show 0≤ (0:ℝ) from le_rfl) (fun i hi h' =>by have hf:= h.order i h'; rw [zero_pow hi.ne']; rwa [zero_mul] at hf)
      refine ⟨hy.smooth,fun i hi=>?_⟩; by_cases he:i=0; · subst i; unfold normJ; rw [norm_iteratedFDeriv_zero]; simp [hz]
      exact (hy.order i hi).trans (by rw [zero_pow he,mul_zero])
    have he:0<v:=lt_of_le_of_ne h.nonneg (Ne.symm he)
    let f (i:EvenA c N):= exp (v • i) -1
    have hf:AnalyticOnNhd ℂ f Set.univ:=fun x hx=> ((NormedSpace.exp_analytic (𝕂:=ℂ) (𝔸:=EvenA c N) _).comp (show AnalyticAt ℂ (fun i:EvenA c N=> v • i) x from (?_))).sub analyticAt_const
    rotate_left
    · let K : EvenA c N →L[ℂ] EvenA c N := (v:ℂ) • ContinuousLinearMap.id ℂ (EvenA c N); exact K.analyticAt _ -- ↑
    let p i:= v⁻¹ • V i
    have hp : p x=0:= by unfold p; rw [hz,smul_zero]
    have ht: Brush k (letterP 1 k*(Real.exp 1*v)) 1 f (p x):=by
       rw [hp]; refine beau zero_lt_one (fun i _=> (hf i (Set.mem_univ _)).differentiableAt) (fun i hi=> ?_) _; apply (stipend _ (show ‖v • i‖ ≤ v from ?_)).trans (Port.fastR v he.le hv); rw [norm_smul, Real.norm_of_nonneg he.le]; exact mul_le_of_le_one_right he.le (le_of_lt (mem_ball_zero_iff.mp hi))
    have hS:Brush k 1 1 p x:=by have h':= h.smul v⁻¹; rwa [Real.norm_of_nonneg (inv_pos.mpr he).le,inv_mul_cancel₀ he.ne'] at h'
    refine ((hS.pine ht).trim.climb ?_ le_rfl).shimmy (Eventually.of_forall fun i=> ?_)
    · apply le_of_eq; unfold heartQ; ring
    change exp (V i)-1= f (p i); dsimp only [f,p]; rw [smul_inv_smul₀ he.ne'] -- rw let
-- Pea with independently controlled v' and shift L. No radius exceeded.
def tomato (x y :ℝ)(k:ℕ):= (Real.exp x-1) + Real.exp x*(heartQ k*y)
lemma swelled (h: Brush k v 1 (fun i=> V i- V x) x)(hz:v ≤1)(hv:‖V x‖≤u): Brush k (tomato u v k) 1 (fun i=>exp (V i)-1) x:=by
   have he:= sprig (V:=fun i=>V i- V x) h hz (by simp)
   have hh : ‖exp (V x)‖ ≤ Real.exp u := by linarith [(norm_sub_norm_le (exp (V x)) (1:EvenA c N)).trans (stipend _ hv), show ‖(1:EvenA c N)‖=1 from norm_one]
   have hpe := ((Brush.certified (x:=x) (k:=k) (le_refl 0) (exp (V x))).climb hh le_rfl).paints he; rw [zero_add] at hpe
   apply (((Brush.certified zero_le_one _).climb (stipend _ hv) le_rfl).gathering hpe).shimmy; exact Eventually.of_forall (fun i=> by
      change exp (V i) - 1= exp (V x)-1 + exp (V x)*(exp (V i-V x)-1); rw [mul_sub,← exp_add,mul_one]; rw [add_sub_cancel]; abel) -- add_sub etc
end price
end YM.QCD.Tidings
