import YM.MassiveQCD.Mayer.Products
/-! # Same polynomial axis and analytic branch unmasked
 All Ordered derivatives before masking. E phases include complex λ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c} {t p q a s r:ℝ} {k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
open YM.MassiveQCD.Analysis.Many
lemma rate_one (ht:0<t): Q 1=1:=by change visc (lens (N:=N) o) t (1:Alg (Keys c N))=_; rw [← mono_empty,sturdy _ ∅ ht.le]; simp [starch,pieD]
lemma sub_zero_pow (x:Z)(ht:0<t)(n:ℕ): Q (x^n) ≤ Q x^n:=by -- Q x^n ambiguity
    induction n with
    | zero=> rw [pow_zero,pow_zero,rate_one ht]
    | succ n ih=> rw [pow_succ,pow_succ]; apply (submult ht.le (x^n) x).trans; exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
lemma sub_fact (x:Z)(p:ℝ): Q (p • x)= ‖p‖*Q x:=by change visc _ _ ((p:ℂ) • x.val)=_; rw [vc_scale,Complex.norm_real]; rfl
lemma pass_high (x:Z)(ht:1 ≤ t): ‖x‖ ≤ Q x:= (Loom.tore x ht).trans (shot (lens o) x.val _ (zero_lt_one.trans_le ht))
lemma subGeom (x:Z)(ht:1≤t)(hp:Q x≤1/2): Q (Ring.inverse (1+x)) ≤ 2 := by
    have hx:0<t:=zero_lt_one.trans_le ht
    have hK:= ringGeom x ((pass_high x ht (o:=o)).trans hp|>.trans_lt (by norm_num))
    let f n:=MassiveQCD.Analysis.Many.alternate n • x^n; change HasSum f _ at hK
    have he: HasSum (fun i=> (1/2:ℝ)^i) 2:= by convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤1/2) (by norm_num : (1/2:ℝ)<1) using 1; norm_num
    let T:=needle o N t
    apply (HasSum.norm_le_of_bounded (T.hasSum hK) he ?_) -- find signature
    intro i;  change ‖T (f i)‖ ≤ _; exact (le_of_eq (show ‖T (f i)‖=Q (x^i) from (sub_fact (x^i) (MassiveQCD.Analysis.Many.alternate i) (o:=o) (t:=t)).trans (by rw [pace,one_mul]))).trans ((sub_zero_pow x hx _).trans (pow_le_pow_left₀ (norm_nonneg _) hp _))
lemma subRoll (x:Z)(ht:1≤t)(hp:Q x≤1/2): Q (logM x) ≤ 2*Q x:=by
    let a:=Q x; let g n:= coeffM (n+1) • x^(n+1)
    have hp':= pass_high x ht (o:=o) |>.trans hp; have hr :0<t:=zero_lt_one.trans_le ht
    have hx:=logs (x:=x) (lt_of_le_of_lt hp' (by norm_num))|>.of_norm
    have h: Summable g:= (summable_nat_add_iff 1 (f:=fun i=> coeffM i • x^i)).2 hx
    have he : HasSum g (logM x):=by
        rw [logM,← hx.sum_add_tsum_nat_add 1]; simp only [Finset.sum_range_one,coeffM, zero_smul,zero_add]; exact h.hasSum
    have hz: HasSum (fun i=> (1/2:ℝ)^i) 2:= by convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤1/2) (by norm_num : (1/2:ℝ)<1) using 1; norm_num
    apply (HasSum.norm_le_of_bounded ((needle o N t).hasSum he) (hz.mul_right a) ?_)
    intro i; unfold g; rw [measures, sub_fact]; calc
        _ ≤ 1*(Q x^(i+1)):= mul_le_mul (horizon _) (sub_zero_pow x hr _) (norm_nonneg _) zero_le_one
        _ ≤ _:= by rw [one_mul,pow_succ]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hp _) (norm_nonneg _)
variable {V:Config su c}{f g:Grid c → EvenA c N}
open Next.Foundations
noncomputable def sideH (x:Z): Z:=Ring.inverse (1+x)
private lemma visit (x:Z)(h:‖x‖<1) : HasFDerivAt sideH (revBasis Z (-(sideH x*sideH x))) x:=by
    obtain ⟨v,hv⟩:= plusUnit h
    have ht:= hasFDerivAt_ringInverse (𝕜:=ℝ) v
    have he : (↑v⁻¹:Z)= sideH x:= (Ring.inverse_unit v).symm.trans (congr_arg _ hv)
    rw [he, hv] at ht; apply (ht.comp x ((hasFDerivAt_const (𝕜:=ℝ) (1:Z) x).add (hasFDerivAt_id (𝕜:=ℝ) _))).congr_fderiv
    ext i : 1; change -(sideH x*(0+i)*sideH x)=-(sideH x*sideH x)*i; rw [zero_add]; ring
lemma shallow (ht:Chart k f V)(h:‖f V‖<1) : Chart k (logM ∘ f) V ∧ Chart k (sideH ∘ f) V:=by
    have he : ((f ∘ increment V) 0)= f V:=by rw [comp_apply,Work.G07.at_zero_increment]
    have hv:AnalyticAt ℝ sideH (f V):= (hasFPowerSeriesOnBall_inverse_one_add ℝ (EvenA c N)).analyticAt_of_mem (by simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using h)
    exact ⟨(((congr_arg (fun x=>AnalyticAt ℝ logM x) he : _).mpr (cont_log _ h)).contDiffAt).comp (f:=f ∘ increment V) _ ht, (he.symm ▸ hv).contDiffAt.comp (f:=f ∘ increment V) _ ht⟩ -- conflict
lemma crossingF (F:Z→Z)(G : Z →L[ℝ] Z)(h:HasFDerivAt F G (f V))(hf: Chart 1 f V)(A:Directions su c): leftDerivs (F ∘ f) [A] V= G (leftDerivs f [A] V):=by
    have hv := left_has (f:=f) (U:=V) A (l:=[]) (by simp) hf
    have he : (fun t:ℝ=>leftDerivs f [] (increment V (t • A))) 0=f V:=by dsimp only; rw [zero_smul, Work.G07.at_zero_increment]; rfl
    rw [← he] at h; exact (h.comp_hasDerivAt _ hv).deriv
lemma nearlog (A:Directions su c)(hf:Chart 1 f V) (h:‖f V‖<1): ∀ᶠ x in 𝓝 (0:Directions su c), let X:= increment V x; leftDerivs (logM ∘ f) [A] X= (sideH ∘ f) X *leftDerivs f [A] X∧ leftDerivs (sideH ∘ f) [A] X= -(((sideH ∘ f)*(sideH ∘ f)) * leftDerivs f [A]) X:=by
    have hh : ∀ᶠ x in 𝓝 0, Chart 1 f (increment V x):=Push.Local.chart_eventually (by rw [Work.G07.at_zero_increment]; exact hf) fun i=> by simp only [increment,su.mat_mul]; exact ((su.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
    have hz: ∀ᶠ x in 𝓝 0, ‖f (increment V x)‖<1:=  (eventually_lt_nhds (show ‖(f ∘ increment V) 0‖< 1 by rw [comp_apply, Work.G07.at_zero_increment]; exact h)) |> hf.continuousAt.norm.tendsto.eventually
    filter_upwards [hh,hz] with x hi hA; intro X; refine ⟨crossingF logM (revBasis (EvenA c N) (Ring.inverse (1+f X))) (dlogM hA) hi A,?_⟩
    exact (crossingF sideH (revBasis (EvenA c N) (-(sideH (f X)*sideH (f X)))) (visit (f X) hA) hi A).trans (neg_mul (sideH (f X)*sideH (f X)) (leftDerivs f [A] X))
end YM.QCD.Stew.Phased
