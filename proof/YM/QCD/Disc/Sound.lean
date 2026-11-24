import YM.QCD.Acre.Trail
import YM.QCD.Disc.Taxi
/-! # Engaging preliminary analysis over augmented gauges -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft
open Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D u v x y W:ℝ}{p:ChartRatio su}{M:ℕ→ Bed}{T:ℕ→Towers E.L}
variable {F L:Side→ℝ}{Λ Γ r c:ℝ}
structure PulseRide (K:KernelChoices)(q:Clip)(E:Patch)(u v:ℝ)(Y:ℕ→SparkMesh)(N:ℕ) where
 path : ℕ→PathData su
 costP : ℕ→ℝ
 place (i:ℕ) (_:i<N) : Place (Pike E i) K (Y i) (path i) q u v
variable {Y:ℕ→SparkMesh}
structure Invoice (R:PulseRide K q E u v Y N)(p:ChartRatio su)(M:ℕ→ Bed)(T:ℕ→Towers E.L)(u₁ Ω' ψ C Λ:ℝ):Prop where
 rootsP : R.path 0=Design.top su q
 he i : i ≤ N→ EnjoyCut M q u v Λ i (R.path i)
 grade i (h : i<N) : Grade (R.place i h) (R.path (i+1)) M T p (R.costP i) u₁ Ω' ψ C

lemma awoke (X:Soil K q E σ η Ω M T) (h : PreCut K q E.J η σ Ω u v γ D k F L) (hl : LocalRatio p)(hh:E.Branches K su)(hu:k ≤ E.L.val)(hη:0 < η)(hV:∀ (n:ℝ),0 ≤ n → (Design.top su q).Bounds q u v n):∃ c:ℝ,0<c∧∀ N (Y:ℕ→SparkMesh)(Λ Ω':ℝ),1 ≤ Λ → L E.L ≤ Λ → (∀ i,reachM E (Y i)) →F E.L ≤ Ω' → ∃ R:PulseRide K q E u v Y N, Invoice R p M T c Ω' γ D Λ:=by
  obtain ⟨U,hU,H⟩:= accompanying X h hl hh hu hη
  refine ⟨U,hU,fun N Y Λ X0 hΛ hx hm hp=>?_⟩
  let f i := Y i; let hol i := { R : PathData su // EnjoyCut M q u v Λ i R }
  have hj (i:ℕ) : reachM E (f i) := hm i
  have HE i (P:hol i):∃ R:hol (i+1),∃ (V:Place (Pike E i) K (f i) P.val q u v) (α:ℝ),Grade V R.val M T p α U X0 γ D:=by
    obtain ⟨V,α,E,h,hx⟩:= H i _ _ _ _ hΛ hx (hj i) hp P.property; exact ⟨⟨E,h⟩,V,α,hx⟩
  choose G W z H using HE
  let R₀:= Design.top su q
  let Z : hol 0 := ⟨R₀,hV Λ (zero_le_one.trans hΛ), X.top.symm ▸ Design.attached q⟩
  let u := fun i=> Nat.rec (motive:=hol) Z G i; refine ⟨⟨fun i=> (u i).val,fun i=> z i (u i),fun i _=> W i (u i)⟩,rfl,fun i hi=> (u i).property,fun i hi=>H i (u i)⟩
variable {Y:ℕ→SparkMesh}(R: PulseRide K q E u v Y N)(X:Soil K q E σ η Ω M T)(H: Invoice R p M T c Γ γ D Λ)(hp:0<η)
namespace PulseRide
def farm (i)(h:i<N): Back E K E.J E.J q u v := ⟨R.path i,Pike E i,rfl,Y i,R.place i h⟩
-- use harmonic
def fuel (i)(h:i<N):Avenue (R.farm i h) σ Ω Ω where
 D := M i
 D':= M (i+1)
 T:= T i
 s:= E.J - 2
 floorP (t):=⟨_,_,X.trace _ _⟩
 stays t := X.crosses i _ _ _
 sworn t := (H.grade i h).foresee t
 price := (X.fund i).2.2.2.2
 nextP:= (X.fund (i+1)).1
 begun:=by have he:=E.order_cut; omega
 coins:=X.pay i
 paidUp t := ⟨by have e:=E.order_cut; omega, (X.fund i).2.2.2.2,(X.fund (i+1)).1, X.pay i, by intro a b c d; rw [X.cell]; exact harmonic_column (Pike E i) _ K.penalty_pos E.order_cut a b c d,X.oath i _,⟨_,_,hp,X.trace i _⟩,X.crosses i _ _ _, ((R.place i h).admiss t).1⟩
 merits:= (X.fund (i+1)).2.1
 home:= (X.trace (i+1) 1).starts
 Sw:= fun i'=> X.oath _ _
abbrev nudges (S T:SparkMesh):Prop:= ∃ f:ℕ→ℕ,Tendsto f atTop atTop ∧ S.n ∘ f = T.n
def ark (S:SparkMesh)(Z :∀ i,nudges (Y i) (footM E S N (i+1))) : Spritely E K q u v σ Ω Ω E.J N where
 Periods i:= (footM E S N i).n
 mats i:= tile E i
 station:= farm R
 engine:= fuel R X H hp
 seek i := Classical.choose (Z i)
 pushed i _:= (Classical.choose_spec (Z i)).1
 aligns i _:= (Classical.choose_spec (Z i)).2
 topUp i h v:= by rw [foot_align S h]; have he:=congr_fun (Classical.choose_spec (Z i)).2 v; refine Eq.trans (show _=(Y i).n (Classical.choose (Z i) v) * E.L from rfl) (congr_arg (fun x=> x*E.L) he)
 inP:= fun _ _=>rfl
 outP:=fun _ _=>rfl
 height _ _:=tendsto_atTop.2 fun a=> SparkMesh.cofinal _|>.eventually_ge_atTop a.val
end PulseRide
open Flume PulseRide
include H
lemma plumZ i l (h:i+l≤ N): |Tally i l R.costP + l*(su.slopeConstant * Real.log E.L.val)|≤ l * D:=by
  induction l with
  | zero=> simp [Tally]
  | succ l ih=>
    let X:= (su.slopeConstant * Real.log E.L.val)
    have hp:i+l<N:=by omega
    have hh := (H.grade _ hp).receipts
    change |_ +_ * X| ≤_
    rw [Tally, Finset.sum_range_succ,Nat.cast_add,Nat.cast_one, show _+R.costP _+_=Tally i l R.costP+l *X+(R.costP (i+l)+X) by unfold Tally; ring]
    have hg := le_trans (abs_add_le ..) (add_le_add (ih hp.le) (show |R.costP (i+l)+X| ≤ D from by unfold X; linarith)); refine le_trans hg ?_; rw [add_mul,one_mul]
lemma sharp (P:Plan E.J)(Z:ParcelR)(h: ReadyR Z P E K q u v σ Ω Ω)(hY:Custody P E K q Z u v σ Ω Ω W) (S:SparkMesh) (hZ:∀ i,nudges (Y i) (footM E S N (i+1))): let Q:= PulseRide.ark R X H hp S hZ; ∃ (X:ℕ→ SunR Z)(Y:ℕ→ℝ), (X 0).X.lamp=0∧(X 0).Y.lamp=0∧ (∀ i,((X 0).Z.page i).coeff=0)∧ (∀ i (p:i<N), BirthR Z P (Q.station i p) (Q.engine i p) (X i) (X (i+1)) (Y i))∧∀ f i l:ℕ,i+l ≤N→ |Tally i l (fun j=> R.costP j+ f*Y j) + l*(betaQ f*Real.log E.L.val)| ≤ l*D+f*W:=by
  intro Q; obtain ⟨X,Y,h₁,h₂,h₃,Hᵤ⟩:= pondG P Q Z h
  exact ⟨X,Y,h₁,h₂,h₃,Hᵤ,fun f i l hp=> lift_hit P Q Z f hY Hᵤ R.costP i l hp _ (plumZ R H _ _ hp)⟩
end YM.QCD.Acre
