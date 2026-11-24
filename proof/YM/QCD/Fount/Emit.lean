import YM.QCD.Fount.Stem
import YM.QCD.Fount.Wealth
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth
variable {t a u r w b m R y C τ Θ η Ω σ z κ d s p H α θ:ℝ}{K :KernelChoices}{J k N B l:ℕ}{c f:Side}
variable {T:Flight J l}{e:f.val=c.val*T.L.val}
def amber (m s:ℝ)(H:Grid f→Sheet f)(V:Grid c→Sheet c)(F:Flight J l)(e:f.val=c.val*F.L.val)(N:ℕ)(W:ℕ→Atom su 2){S:StepData c f}{P:Forest S.ratio}(ρ: Bid.Dir su c→AxisChart su P): Positions (Primary c su)→EvenA c N:= favor ρ (tonic e (houseK m H) W N s-tonic e H W N s) (fun U=> m • powerZ c N s (V U)) -- type class
abbrev liftMass (m:ℝ)(X:Grid f→Sheet f): Grid f→Sheet f:= fun i=> Run.lap (debt m X i)
lemma minted (X: Grid f→Sheet f)(hp: Species T e C R t 0 p B X)(hv: Species T e C R t 0 p B (houseK m X))(ht:0<t)(hs:|m| ≤ d)(hq: d*R≤1/2):
   let V:= liftMass m X; Own f t 0 B V (2*(d*R)) ∧ ∀ q:Grid f,alti f (V q) = Real.log ((houseK m X q).det.re)- Real.log ((X q).det.re) :=by
    intro V; have hc:=hp.forest
    have he: Own f t 0 B (debt m X) (d*R):=by have he:=hp.hashed.scalar (-(m:ℂ)); rw [norm_neg,Complex.norm_real,Real.norm_eq_abs] at he; exact he.mono (mul_le_mul_of_nonneg_right hs hc.le)
    have hd : 0 ≤ d:=(abs_nonneg _).trans hs; have hP : 0≤ d*R:=by positivity
    exact ⟨volts hP hq he ht,fun i=> (cinder m X hp hv i ((he.value ht le_rfl hP i).trans_lt (lt_of_le_of_lt hq (by norm_num)))).symm⟩
lemma tonus {X Y: Grid f→Sheet f}(V: Grid f→Sheet f)(h:∀ q:Grid f, alti f (V q)=Real.log (Y q).det.re-Real.log (X q).det.re) (s:ℝ)(W:ℕ→Atom su 2)(N:ℕ) (i:Grid f):
   tonic e Y W N s i-tonic e X W N s i=baker _ N (N*((alti f) (V i) -(alti f) (V 1)))+powerZ c N s (foam T e Y i-foam T e X i) :=by
   simp only [Octave.tonic,Function.comp_apply,mica,map_add,map_sub]
   have ht (x:ℝ): wearK c N s (baker _ N x)=baker _ N x:=by
      rw [gets, show wearK _ _ _ _=x • wearK c N s 1 from map_smul ((wearK c N s).toLinearMap.restrictScalars ℝ) _ _,map_one]
   rw [ht,ht,h,h]; change baker _ N _ + powerZ c N s _-(baker _ N _ + powerZ c N s _)= _; simp only [mul_sub,map_sub]; abel
-- FOUNT budgets shape
abbrev rose (Z t D G w A R d s Y:ℝ)(i N:ℕ):= (clump i (1+G+(1+G)) (N*(w*Fintype.card Lat.Fiber* noteC t (2*(d*R)) Z i)+s^2*Y^2*noteC t (d*(R*R)) Z i))+d*(s^2*Y^2*chord D A Z i)
variable {S:StepData c f}{P:Forest S.ratio}
variable {X:Grid f→Sheet f}{Y:Grid c→Sheet c} (hp:Species T e C R t 0 p B X)(hv:Species T e C R t 0 p B (houseK m X))(ht:0<t)(hs:|m| ≤ d)(hq:d*R ≤ 1/2)
include hp hv ht hs hq
lemma lively (s:ℝ)(hs':0<s)(W:ℕ→Atom su 2)(N:ℕ)(hP: PaintSupply su k z)(x:Positions (Primary c su) × Poll.Body (Precision.Key P su))(hx:‖x‖≤1)(hy: (Fintype.card (Site f):ℝ)≤ w)(hA:(Fintype.card (Modes c N):ℝ) ≤ a)(hk:0<k):let T':=(Octave.tonic e (houseK m X) W N s -Octave.tonic e X W N s) ∘ Octave.projection P
    let K:=N*(w*Fintype.card Lat.Fiber* noteC t (2*(d*R)) z k)+s^2*a^2*noteC t (d*(R*R)) z k; ∃ c:ℝ, Brush k K 1 (T'-(fun _=>baker _ N c)) x:=by
    intro Z T'; let f':= uplift m X T e
    obtain ⟨hf,ha⟩:=minted X hp hv ht hs hq
    have hh := (tempoP P hP x hx)
    let q:=liftMass m X; let Z':= Octave.projection (G:=su) P
    have hd:0≤d:= (abs_nonneg _).trans hs; have he:=hp.forest; have hE:0≤d*(R*R):=by positivity
    have ht' := (meter P hf ht (by positivity) le_rfl hh).report (alti f) ((ascent f).trans (mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg _)))
    have hu := (unfelt ht hp hv le_rfl).1.mono (mul_le_mul_of_nonneg_right hs (by positivity))
    have hp' := ((ht'.smul (N:ℝ)).report _ (colP c N)); rw [Real.norm_of_nonneg (by positivity : 0 ≤ (N:ℝ)),one_mul] at hp'
    have ht := ((meter P (T:=f') hu ht hE le_rfl hh).report _ ((billed hs' c N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hA _) (sq_nonneg _))))
    refine ⟨-(N:ℝ)*alti f (q 1),(hp'.gathering ht).shimmy (Eventually.of_forall fun i=>?_)⟩
    change (tonic (O:=T) e _ _ _ _ (Z' i)-tonic (O:=T) e _ _ _ _ (Z' i))-baker _ _ _=baker _ _ ((N:ℝ)*_) + _; rw [tonus _ ha,mul_sub,map_sub,neg_mul,map_neg]; change _=baker c N ((N:ℝ)*alti f (q (Z' i)))+powerZ c N s _; abel
end YM.QCD.Fount
