import YM.QCD.Raft.Tracks

/-! # zero-cutoff Ornamental seed and beta interpretation

Calibration of actual *free Gaussian step* with stationary gauge tree only. Masks/remainders and quantum inputs must be handled separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior ParcelR Rudder
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α:ℝ}
variable (P:Plan j) (Q: Journey E K p u v η Ω Θ j N) (R:ParcelR) {X:ℕ→SunR R}{Y:ℕ→ℝ}
lemma virgin (k:ℕ)(hp:0 ≤ s)(h:0≤t) : ∃ V:Offer k s t,V.lamp=0:=by
  let W : Empty → Bloom k:=Empty.elim; have he:dust W=0:=by ext i U; simp[dust]
  have h': Vital (dust W):= by rw [he]; exact Vital.solozero
  refine ⟨⟨_,W, ⟨hp,fun i=>i.elim,Summable.of_finite,?_⟩,h'⟩,he⟩; simpa using h
lemma soil (hp:0<s)(h:0 ≤ t):∃ O:Ornament s t,∀ k,(O.page k).coeff=0:=by
  let W: Empty→ PairG su:=Empty.elim; refine ⟨⟨Empty,W, ?_⟩,?_⟩
  · exact ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,Summable.of_finite,by simpa using h⟩
  intro i; unfold Ornament.page installG padded Function.comp; cases numbering ((Empty × BranchG 2) ⊕ ℕ) i with
  | inl i=> exact i.1.elim
  | inr i=> rfl
lemma sourceG (h:ReadyR R P E K p u v η Ω Θ) :∃ (X :ℕ→SunR R)(Y:ℕ→ℝ), (X 0).X.lamp=0∧(X 0).Y.lamp=0∧ (∀ i,((X 0).Z.page i).coeff=0)∧∀ i (p:i<N), BirthR R P (Q.station i p) (Q.engine i p) (X i) (X (i+1)) (Y i):=by
  obtain ⟨u,hU⟩:=virgin 1 h.1.hr.le h.1.hc; obtain ⟨v,hV⟩:= virgin 2 h.1.hs.le h.1.hd; obtain ⟨w,hW⟩:=soil h.1.ht h.1.he; obtain ⟨X,Y,hp,H⟩:= forging P Q R h ⟨u,v,w⟩; refine ⟨X,Y,?_,?_,?_,H⟩ <;> rw [hp] <;> first | exact hU| exact hV| exact hW

def betaQ (f:ℕ):ℝ:= su.slopeConstant - f*Pearl.chargeF
lemma qbeta (f:ℕ): betaQ f=(3/(4*Real.pi^2))*(11- 2*f/3):=by unfold betaQ Gauge.slopeConstant Pearl.chargeF; rw [Roots.casimir]; ring
lemma ultraviolet (f:ℕ): 0 < betaQ f ↔ f ≤ 16:=by
  rw [qbeta]; have h : 0< (3/(4*Real.pi^2)):=by positivity
  rw [mul_pos_iff_of_pos_left h]; constructor
  · intro hi; by_contra! hp; have hh:17 ≤ f:=by omega
    have he : (17:ℝ) ≤ f:= by exact_mod_cast hh
    linarith
  intro hp; have he : (f:ℝ)≤16:= by exact_mod_cast hp
  linarith
-- given a pure sum already running, shell sums in sign convention negative βα.
lemma slope_hit (F:ℕ)(h:Cumulative P E K p R u v η Ω Θ D)(hs:∀ i (p:i<N), BirthR R P (Q.station i p) (Q.engine i p) (X i) (X (i+1)) (Y i)) (A:ℕ→ℝ)
    (n i)(p:n+i ≤ N)(B:ℝ)(hh:|Tally n i A+i*(su.slopeConstant*Real.log E.L.val)|≤B): |Tally n i (fun j=> A j+F*Y j)+i*(betaQ F*Real.log E.L.val)|≤ B+F*D:=by
  have hm:= h.2 N Q X Y hs n i p
  rw [show Tally n i (fun j=> A j+F*Y j)= Tally n i A+F*Tally n i Y by unfold Tally; rw [sum_add_distrib,Finset.mul_sum]]
  unfold betaQ; rw [show (_:ℝ)+_+_*(_*Real.log E.L.val)=Tally n i A+i*(su.slopeConstant*Real.log E.L.val)+ F*(Tally n i Y - i*(Pearl.chargeF*Real.log E.L.val)) from ?_]
  · apply (abs_add_le ..).trans; rw [abs_mul,abs_of_nonneg (show 0 ≤ (F:ℝ) by positivity)]; exact add_le_add hh (mul_le_mul_of_nonneg_left hm (by positivity))
  ring
end YM.QCD.Raft
