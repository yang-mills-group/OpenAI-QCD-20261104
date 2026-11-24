import YM.QCD.Raft.Venus
-- avoid importing Matter until integration. ceremonial pre

/-!
# cumulative α χ intercept ALL subintervals in uniform Price/Gates window.
Post-L constants width includes arbitrary chosen stationary-action polynomial bound. No repeated ℓ² comparison. No inference when actual forests held at lacking premises.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior ParcelR
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α:ℝ}
variable (P:Plan j) (Q: Journey E K p u v η Ω Θ j N) (R:ParcelR) {X:ℕ→SunR R}{Y:ℕ→ℝ}

lemma delayG (i l:ℕ)(n:ℕ)(h: i+l ≤N): Real.log ((Q.Periods i n).val)=Real.log (Q.Periods (i+l) n).val+ l * Real.log E.L.val:=by
  induction l with
  | zero=> simp
  | succ l ih=>
    have hp:i+l<N:=by omega
    rw [ih hp.le,← Q.topUp (i+l) hp]; let B:= Q.station (i+l) hp
    have hm:(localG B n).val=(Q.Periods (i+l+1) n).val*E.L.val:=by rw [← Q.aligns (i+l) hp]; rw [show (localG B n).val=_ from (anchor B n).sizes]; change (B.chain.n n).val*B.fly.L.val= _; rw [B.has]
    rw [show (localG (Q.station (i+l) hp) n).val=_ from hm]; push_cast; rw [← Nat.add_assoc, Real.log_mul (by positivity) (by positivity)]; ring

def Cumulative (P:Plan j)(E:Patch)(K:KernelChoices)(p:Clip)(R:ParcelR)(u v η Ω Θ D:ℝ):Prop:= 0≤ D ∧∀ (N:ℕ)(Q:Journey E K p u v η Ω Θ j N)(X:ℕ→SunR R)(Y:ℕ→ℝ),
    (∀ i (h:i<N), BirthR R P (Q.station i h) (Q.engine i h) (X i) (X (i+1)) (Y i)) → ∀ i l,i+l ≤ N→ |Tally i l Y-l*(Pearl.chargeF* Real.log E.L.val)|≤D

lemma funds (P:Plan j) (he:0<η)(hr:Rates R η)(E:Patch)(K:KernelChoices)(p:Clip)(u v Ω Θ:ℝ):∃ D,Cumulative P E K p R u v η Ω Θ D:=by
  let a:=EuclideanSpace.single Fog.lodging (1:ℝ)
  have hx:‖a‖=1:= lodging_st
  obtain ⟨b,h⟩:= Raft.calibrated P a hx hr.hr hr.hs R.c R.d
  refine ⟨|b|+|b|,by apply add_nonneg <;> apply abs_nonneg,fun n Q X Y H i l hp=>?_⟩
  have ht (j)(hk:j≤n):∀ᶠ t in atTop, |Calories R P Q X a j t-Pearl.chargeF* Real.log (Q.Periods j t).val|≤ |b|:= ((Q.height j hk).eventually h).mono fun t hx=> le_trans (hx (X j).X (X j).Y _) (le_abs_self _)
  have he := embark P Q R a hx hr he H i l hp
  let F:= Calories R P Q X a; apply le_of_tendsto ((he.sub_const (l*(Pearl.chargeF*Real.log E.L.val))).abs)
  filter_upwards [ht i (by omega), ht (i+l) hp] with t hi hj
  change |F i t-F (i+l) t -_| ≤ _; refine le_trans (le_of_eq (show |_ - _|=|(F i t-Pearl.chargeF*Real.log (Q.Periods i t).val)-(F (i+l) t-Pearl.chargeF*Real.log (Q.Periods (i+l) t).val)| from ?_)) ((abs_sub _ _).trans (add_le_add hi hj))
  rw [delayG Q i l t hp]; ring_nf

lemma forging (h:ReadyR R P E K p u v η Ω Θ)(K₀: SunR R):∃ (X:ℕ→ SunR R)(Y:ℕ→ℝ), X 0 =K₀ ∧ ∀ i (H:i<N), BirthR R P (Q.station i H) (Q.engine i H) (X i) (X (i+1)) (Y i):=by
  have he(i:ℕ)(x:SunR R): ∃ y c,∀ H:i<N,BirthR R P (Q.station i H) (Q.engine i H) x y c:=by
    by_cases hi:i<N; · obtain ⟨y,c,h⟩:= h.2 (Q.station i hi) (Q.engine i hi) x; exact ⟨y,c,fun _=>h⟩ -- syntax
    exact ⟨x,0,fun h'=> False.elim (hi h')⟩
  choose M c H using he
  let X(i:ℕ):SunR R:= Nat.rec (motive:=fun _=> SunR R) K₀ (fun j x => M j x) i
  exact ⟨X,fun j=> c j (X j), rfl,fun i h=> H i (X i) h⟩
namespace ParcelR
lemma issuesG (P:Plan j)(hj:4≤ j)(he:0<η)(hΩ:0≤Ω)(hΘ:0≤Θ):∃ M:ℕ,∀ E:Patch,M ≤ E.L.val →∀ (K:KernelChoices)(p:Clip)(u v:ℝ)(N:ℕ)(B:Push.Uniform.Before su u v E.J K N),∃ Q D, ReadyR Q P E K p u v η Ω Θ∧ Cumulative P E K p Q u v η Ω Θ D:=by
  obtain ⟨M,h⟩:=ranges P hj he hΩ hΘ; refine ⟨M,fun E hp K p u v N B=>?_⟩; obtain ⟨Q,H⟩:=h E hp K p u v N B; obtain ⟨D,h⟩:=funds Q P he H.1 E K p u v Ω Θ -- check
  exact ⟨Q,D,H,h⟩
end ParcelR
end YM.QCD.Raft
