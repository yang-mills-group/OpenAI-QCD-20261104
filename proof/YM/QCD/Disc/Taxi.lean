import YM.QCD.Raft.Roads
/-! # Cumulative budget using telescope on dovetailed station meshes. Prices before mesh size. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical InnerProductSpace ComplexConjugate
variable {j k N:ℕ}{E:Patch}{K:KernelChoices}{p:Clip}{η Ω Θ u v t r a b c C D s G α:ℝ}

open ParcelR
structure Spritely (E:Patch)(K:KernelChoices)(p:Clip)(u v η Ω Θ:ℝ)(j N:ℕ) where
 Periods : ℕ → ℕ→Side
 mats (i:ℕ): Train j
 station (i:ℕ)(_ : i<N): Back E K j j p u v
 engine (i:ℕ)(h:i<N): Avenue (station i h) η Ω Θ
 seek (i:ℕ): ℕ→ℕ
 pushed i (h:i<N):Tendsto (seek i) atTop atTop
 aligns i (h:i<N): (station i h).chain.n ∘ seek i= Periods (i+1)
 topUp i (h:i<N) : ∀ v,localG (station i h) (seek i v)=Periods i v
 inP i (h:i<N): (station i h).fly.wing=mats i
 outP i (h:i<N): (station i h).fly.land=mats (i+1)
 height (i:ℕ)(_ : i≤N): Tendsto (Periods i) atTop atTop

variable (P:Plan j) (Q: Spritely E K p u v η Ω Θ j N) (R: ParcelR) {X:ℕ→ SunR R} {Y: ℕ→ℝ}
def Bronze (P:Plan j)(Q: Spritely E K p u v η Ω Θ j N)(X:ℕ→SunR R)(A:su.Color)(i n:ℕ):ℝ := readP (rollG P (Q.mats i) (X i).powerG (Q.Periods i n)) A
section ember
variable (x: su.Color) (hx:‖x‖=1)(hR: Rates R η)(hv:0<η)(hp:∀ i (h:i<N),R.BirthR P (Q.station i h) (Q.engine i h) (X i) (X (i+1)) (Y i))
include hx hR hv hp
lemma go (i l:ℕ)(h:i+l ≤ N): Tendsto (fun n=> Bronze R P Q X x i n - Bronze R P Q X x (i+l) n) atTop (𝓝 (Tally i l Y)):=by
  induction l with
  | zero=> simp [Tally]
  | succ l ih=>
    have hh:i+l<N:=by omega
    have H:=(hp _ hh); let V:=Q.station (i+l) hh
    have ht:= deed P P V (Q.engine (i+l) hh) x (X (i+l)).X (X (i+l)).Y (X (i+l+1)).X (X (i+l+1)).Y (X (i+l)).Z (X (i+l+1)).Z hx hR.hr hR.hc hR.hs hR.hd hR.ht hR.fit hv H.limbs hR.hw hR.hl H.price -- order of hp. deed input O
    have heq : Tendsto (fun n=> Bronze R P Q X x (i+l) n-Bronze R P Q X x (i+l+1) n) atTop (𝓝 (Y (i+l))):=by
      apply (ht.comp (Q.pushed _ hh)).congr'; apply Eventually.of_forall; intro n; unfold Bronze; change readP (rollG P V.fly.wing (X _|>.powerG) (localG V (Q.seek _ n))) _-readP (rollG P V.fly.land (X _|>.powerG) (V.chain.n (Q.seek _ n))) _= _; unfold V; rw [Q.topUp,Q.outP,Q.inP,← Q.aligns _ hh]; rfl -- Q.inP?]
    rw [Tally,Finset.sum_range_succ]; refine ((ih hh.le).add heq).congr' (Eventually.of_forall fun p=> ?_)
    rw [← Nat.add_assoc]; ring
end ember
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent Extra Iteration QCD.Smoke
open Eyrie Stationary Quarry Work.F03 Matrix Kit Pine Orbit Birth Garden Transfer Revolve Sparks Lat
open YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Jacobi Fog Voyage Flume Exterior ParcelR
lemma gloom (i l:ℕ)(n:ℕ)(h: i+l ≤N): Real.log ((Q.Periods i n).val)=Real.log (Q.Periods (i+l) n).val+ l * Real.log E.L.val:=by
  induction l with
  | zero=> simp
  | succ l ih=>
    have hp:i+l<N:=by omega
    rw [ih hp.le,← Q.topUp (i+l) hp]; let B:= Q.station (i+l) hp
    have hm:(localG B (Q.seek (i+l) n)).val=(Q.Periods (i+l+1) n).val*E.L.val:=by rw [← Q.aligns (i+l) hp]; rw [show (localG B (Q.seek (i+l) n)).val=_ from (anchor B (Q.seek (i+l) n)).sizes]; change (B.chain.n (Q.seek (i+l) n)).val*B.fly.L.val= _; rw [B.has]; rfl
    rw [show (localG (Q.station (i+l) hp) (Q.seek (i+l) n)).val=_ from hm]; push_cast; rw [← Nat.add_assoc, Real.log_mul (by positivity) (by positivity)]; ring

def Custody (P:Plan j)(E:Patch)(K:KernelChoices)(p:Clip)(R:ParcelR)(u v η Ω Θ D:ℝ):Prop:= 0≤ D ∧∀ (N:ℕ)(Q:Spritely E K p u v η Ω Θ j N)(X:ℕ→SunR R)(Y:ℕ→ℝ),
    (∀ i (h:i<N), BirthR R P (Q.station i h) (Q.engine i h) (X i) (X (i+1)) (Y i)) → ∀ i l,i+l ≤ N→ |Tally i l Y-l*(Pearl.chargeF* Real.log E.L.val)|≤D

lemma portal (P:Plan j) (he:0<η)(hr:Rates R η)(E:Patch)(K:KernelChoices)(p:Clip)(u v Ω Θ:ℝ):∃ D,Custody P E K p R u v η Ω Θ D:=by
  let a:=EuclideanSpace.single Fog.lodging (1:ℝ)
  have hx:‖a‖=1:= lodging_st
  obtain ⟨b,h⟩:= Raft.calibrated P a hx hr.hr hr.hs R.c R.d
  refine ⟨|b|+|b|,by apply add_nonneg <;> apply abs_nonneg,fun n Q X Y H i l hp=>?_⟩
  have ht (j)(hk:j≤n):∀ᶠ t in atTop, |Bronze R P Q X a j t-Pearl.chargeF* Real.log (Q.Periods j t).val|≤ |b|:= ((Q.height j hk).eventually h).mono fun t hx=> le_trans (hx (X j).X (X j).Y _) (le_abs_self _)
  have he := go P Q R a hx hr he H i l hp
  let F:= Bronze R P Q X a; apply le_of_tendsto ((he.sub_const (l*(Pearl.chargeF*Real.log E.L.val))).abs)
  filter_upwards [ht i (by omega), ht (i+l) hp] with t hi hj
  change |F i t-F (i+l) t -_| ≤ _; refine le_trans (le_of_eq (show |_ - _|=|(F i t-Pearl.chargeF*Real.log (Q.Periods i t).val)-(F (i+l) t-Pearl.chargeF*Real.log (Q.Periods (i+l) t).val)| from ?_)) ((abs_sub _ _).trans (add_le_add hi hj))
  rw [gloom Q i l t hp]; ring_nf

lemma leavesG (h:ReadyR R P E K p u v η Ω Θ)(K₀: SunR R):∃ (X:ℕ→ SunR R)(Y:ℕ→ℝ), X 0 =K₀ ∧ ∀ i (H:i<N), BirthR R P (Q.station i H) (Q.engine i H) (X i) (X (i+1)) (Y i):=by
  have he(i:ℕ)(x:SunR R): ∃ y c,∀ H:i<N,BirthR R P (Q.station i H) (Q.engine i H) x y c:=by
    by_cases hi:i<N; · obtain ⟨y,c,h⟩:= h.2 (Q.station i hi) (Q.engine i hi) x; exact ⟨y,c,fun _=>h⟩ -- syntax
    exact ⟨x,0,fun h'=> False.elim (hi h')⟩
  choose M c H using he
  let X(i:ℕ):SunR R:= Nat.rec (motive:=fun _=> SunR R) K₀ (fun j x => M j x) i
  exact ⟨X,fun j=> c j (X j), rfl,fun i h=> H i (X i) h⟩
lemma pondG (h:ReadyR R P E K p u v η Ω Θ) :∃ (X :ℕ→SunR R)(Y:ℕ→ℝ), (X 0).X.lamp=0∧(X 0).Y.lamp=0∧ (∀ i,((X 0).Z.page i).coeff=0)∧∀ i (p:i<N), BirthR R P (Q.station i p) (Q.engine i p) (X i) (X (i+1)) (Y i):=by
  obtain ⟨u,hU⟩:=virgin 1 h.1.hr.le h.1.hc; obtain ⟨v,hV⟩:= virgin 2 h.1.hs.le h.1.hd; obtain ⟨w,hW⟩:=soil h.1.ht h.1.he; obtain ⟨X,Y,hp,H⟩:= leavesG P Q R h ⟨u,v,w⟩; refine ⟨X,Y,?_,?_,?_,H⟩ <;> rw [hp] <;> first | exact hU| exact hV| exact hW

lemma lift_hit (F:ℕ)(h:Custody P E K p R u v η Ω Θ D)(hs:∀ i (p:i<N), BirthR R P (Q.station i p) (Q.engine i p) (X i) (X (i+1)) (Y i)) (A:ℕ→ℝ)
    (n i)(p:n+i ≤ N)(B:ℝ)(hh:|Tally n i A+i*(su.slopeConstant*Real.log E.L.val)|≤B): |Tally n i (fun j=> A j+F*Y j)+i*(betaQ F*Real.log E.L.val)|≤ B+F*D:=by
  have hm:= h.2 N Q X Y hs n i p
  rw [show Tally n i (fun j=> A j+F*Y j)= Tally n i A+F*Tally n i Y by unfold Tally; rw [sum_add_distrib,Finset.mul_sum]]
  unfold betaQ; rw [show (_:ℝ)+_+_*(_*Real.log E.L.val)=Tally n i A+i*(su.slopeConstant*Real.log E.L.val)+ F*(Tally n i Y - i*(Pearl.chargeF*Real.log E.L.val)) from ?_]
  · apply (abs_add_le ..).trans; rw [abs_mul,abs_of_nonneg (show 0 ≤ (F:ℝ) by positivity)]; exact add_le_add hh (mul_le_mul_of_nonneg_left hm (by positivity))
  ring

end YM.QCD.Raft
#print axioms YM.QCD.Raft.lift_hit
