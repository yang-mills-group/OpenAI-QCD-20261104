import YM.VStages.Lumber
import YM.VStages.Municipal
import YM.Massive.Tuner.Budget
import YM.Massive.Tuner.Limits

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N) (hG: Stargate T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
namespace Reference
open IV
open NormedSpace
variable {u' τ₁ x₀ :ℝ}
open Nola Globe
lemma flatQ (κ t : ℝ) (U : ParcelR) (P : Plan j) (hw : 0 < t) (c L : Side) (h : FreeholdQ P N L c W) :
    ∀ᶠ y in atTop, ∀ (k : ℕ) (B : Side), B=c*L^k → ∀ (F : Voice B N) (p : BudgetPoint),
    Enn p b' L y t (1/8) (duo F.P F.K) → ∀ (Z : Pixel B N), Rain.realP Z → ∀ (G : Clip) (l : SunR U) (M : Train j)
      (N' : PathData su) (β v z : ℝ), 0 < z → |v| ≤ roofK L t κ y →
      Z=z • red F.P F.K l P M p N' G (haloK L y) β v 0 →
    z * Real.exp (Finch.scent l.Z.page p N' G β 0 N (1 : Grid B)) * Globe.expo W B ≤ (cBer Z 1).re:=by
   obtain ⟨w,H,hw',hh,hH⟩:=h.port
   have hN:0 < N:=by have := b'.isLt; omega
   let d : ℝ := (Fintype.card Fiber:ℝ)*N*H^2
   have hc : 0 < H:=by linarith
   have hd : 0 < d:=by unfold d; positivity
   filter_upwards [honey (L:=L) b' hc (show 0 < w/2 by positivity) hw,(beamsR L t κ).below (by norm_num) (w/2/d) (by positivity)] with y hy hY k B hf F p he Z hZ G l M N' β v z hv hz hE
   rw [flatR P F Z _ l _ _ M hZ hE hv,Port.oneC,add_assoc]
   apply mul_le_mul_of_nonneg_left _ (mul_pos hv (Real.exp_pos _)).le
   obtain ⟨hx,hV⟩:=hy p B F he 1
   apply hH k _ hf
   · obtain ⟨f,g,h,-⟩:= he; exact Cocoa.add ((Tempo.one.smul v).butter N) (appetite F.P F.K h.pan hx)
   have ht: |v| ≤ w/2/d:= hz.trans ((le_abs_self _).trans hY)
   have hp := band_mass v H hc B N 6
   apply (band_add _ (paleF N (v • (1:Sheet B))).val (Patron.total _ _ _).val hc).trans ((add_le_add hp hV).trans _)
   have hh:= (le_div_iff₀ hd).mp ht; unfold d at hh; simp only [←mul_add]
   gcongr; linarith only [hh]

end Reference
end Rails
end YM.QCD.Acre
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
open Rain PulseRide
variable {O:Patch} {P':ℕ→BudgetPoint}{X:ℕ→SunR Ω}{U V Wv Y:ℕ→ℝ}
variable {τ':Policy Q T'.top N}(B:SparkMesh){S':ℕ→SparkMesh}(b':Flavor N) (g:PulseRide T'.bind T'.top.clip O a d S' n)
variable {T₁:ℕ→Towers O.L}{V₁:ℕ→Bed}{b₀:ℕ→ℝ}
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)


/-!
Bpressure analogue. `K` a lower-margin expense (large positive), `A` majorant size.
uniform over the x (β) tail, *all* k on the M from the initial DomainF, *all* steps
in these positive-common-mass histories. Include actual lower and upper as used in E.
Use `#` exactly: spare = 3 v + 1, rich = 3 v - 3. In particular bounds may be used
without paying a `log(h)` in every volume degree. On passing to the large x gates,
the torus populations can also pay the last few powers when wanting bounds with matched
power `3v`; here state with the displayed actual powers. Never assume the precision
needed to do a stability argument on perturbing the *entire* mass ray has been achieved
just by this positive-common-mass lower.
-/
variable {n0 : ℕ} {B₀ : Side} {J : Patch}
variable (L : HaarBudget su)

local notation "Cₘ" => towerQ O B n i k
set_option quotPrecheck false
-- single-bound tuning preparation hypotheses
variable (Kt A'':ℝ) (Ω : ParcelR) (T : Teller su)
structure HeatQ (P₀:Plan j) (b:Flavor N)(T:Teller su)(O:Patch)(B₀:Side)(A Ωp:ℝ) (P:ParcelR)(κ η x a d s : ℝ) :Prop where
  enough : 2 ≤ run O.L x
  g_pos : 0< gaugeSize O.L x
  g_le : gaugeSize O.L x ≤ 1
  exact_ : run O.L x * gaugeSize O.L x ^ 2=1
  adjacent : run O.L (run O.L x) ≤ 2 * run O.L x
  range_ : roofK O.L η κ x ≤ 1
  fan_ : 1 ≤ fan O.L η x
  chip : |Jets.Touch.chip O.L x|≤1
  high (c : Side) (p : BudgetPoint) (hq : Now O.L p T.top x) (F : Voice c N) (he : Enn p b O.L x η (1/8) (duo F.P F.K)) (v:Train j) (E : SunR P) (D:PathData su) (β m:ℝ)
      (hL:D.Bounds T.top.clip a d s) (hm: |m|≤roofK O.L η κ x) (hb:run O.L x/2≤β) (hB:β≤2*run O.L x) (U:Grid c) : ‖red F.P F.K E (P₀) v p D T.top.clip (haloK O.L x) β m 0 U‖ ≤ Massive.Pressure.major su c A (2*gaugeSize O.L x / strength T.top.clip) U
  low (c : Side) (p : BudgetPoint) (F : Voice c N) (he : Enn p b O.L x η (1/8) (duo F.P F.K)) (v:Train j) (E : SunR P) (D:PathData su) (β m:ℝ) (hm:|m|≤roofK O.L η κ x) (k:ℕ) (hC:c=B₀*O.L^k) (z:ℝ) (Y: Pixel c N) (hz:0<z) (hY:Y=z • red F.P F.K E (P₀) v p D T.top.clip (haloK O.L x) β m 0) (h:Rain.realP Y) : z*Globe.expo Ωp c ≤ (cBer Y 1).re
  cap : 1+(Fintype.card PlaqAxes:ℝ) ≤ Ωp

-- unify J=4 proofs
lemma heatWave (T) (Ω:ParcelR) (O:Patch) (hk:0<κ) (hη:0<η) (hh:Ω.Rates σ)
    (hB:Globe.FreeholdQ P₀ N O.L B₀ H) (a d s:ℝ) : ∃ A D:ℝ, ∀ᶠ x in atTop, ∀ y,x ≤ y→ HeatQ P₀ b' T O B₀ A D Ω κ η y a d s:=by
  let J:= O.J; obtain ⟨Z,hU⟩:=unmarked (b':=b') -- args edit
       (P₀) T O.L Ω a d s κ η hh hη hk
  let K := max (1+(Fintype.card PlaqAxes:ℝ)) H
  obtain ⟨r,hr⟩:= eventually_atTop.mp (hU.and ((prices T.top O.L η κ hk hη).and (flatQ (U:=Ω) b' κ η P₀ hη _ _ hB))) -- args
  refine ⟨Z,K,?_⟩; filter_upwards [eventually_ge_atTop r] with x hx y hy; obtain ⟨hz,⟨ha,hb,hc,hd,he,hf,hg,hH,-⟩,h⟩:=hr _ (hx.trans hy)
  refine ⟨ha,hb,hc,hd,he,hf,hg,hH,fun c p h F he v E D β m hL hm hb hB U=>hz c p h F he U v E D hL β m hb hB hm,?_,le_max_left ..⟩
  intro c p F he v E D β m hm k hC z Y hZ hY hF
  apply le_trans (mul_le_mul_of_nonneg_left (Globe.earns (le_max_right ..)) hZ.le)
  simpa only [scent_one,mul_one,Real.exp_zero] using (h k _ hC F p he Y hF T.top.clip E v D β m z hZ hm hY)
end Reference
end Rails
end YM.QCD.Acre
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
namespace Cairn
open NormedSpace MeasureTheory Rails.Reference
open Finset
variable {t s t' ζv:ℝ}
-- Settlement
variable (P₀:Plan j) {Ω:ParcelR} {κ:ℝ} (F₀:Flavor N) {u':ℝ}
lemma broaden (T:Teller su)(he:HeatQ P₀ F₀ T J c A D Ω κ η x a d s)(hq:A≤Y)(ht:D≤t): HeatQ P₀ F₀ T J c Y t Ω κ η x a d s:=by
    refine { he with cap:=he.cap.trans ht, high:=?_, low:=?_ }
    · intro c P hp V hV b E P₀ β m hh hm hv he' U
      apply (he.high c P hp V hV b E P₀ β m hh hm hv he' U).trans; unfold Massive.Pressure.major; gcongr
    intro c P V hV b E P₀ β m hm k h' z Y hz hY h
    exact le_trans (mul_le_mul_of_nonneg_left (Globe.earns ht) hz.le) (he.low c P V hV b E P₀ β m hm k h' z Y hz hY h)

abbrev Digit (O:Patch):Prop := ∃ i:ℕ,O.L.val=3^i

def Day (T:Teller su)(O:Patch)(M:ParcelR)(ν θ x u v s A D:ℝ) :Prop := ∀ᶠ i:ℕ in atTop,∃ (B:Side)(k:ℕ), refrain i=B*O.L^k ∧ HeatQ P₀ F₀ T O B A D M ν θ x u v s

lemma periodics (T:Teller su) (Ω: ParcelR) (O:Patch)(hk:0<κ) (hη:0<η)(hh:Ω.Rates σ)
    (hB:∀ X:Side,m ≤ X.val →∃ M:ℝ,0 ≤ M ∧ Globe.FreeholdQ P₀ N O.L X M) (a d s:ℝ)(hf:Digit O): ∃ A D:ℝ,∀ᶠ x in atTop, Day P₀ F₀ T O Ω κ η x a d s A D:=by
    obtain ⟨n,h⟩:=hf; have hn:0<n:=by by_contra! hm; rw [show n=0 from by omega,pow_zero] at h; have H:=O.coarse; omega
    have ht: Tendsto (fun i=> (refrain i).val) atTop atTop:= by
        apply (accord 0).cofinal.congr'; filter_upwards with k; change (refrain (k+0)).val =_; rw [Nat.add_zero]
    obtain ⟨l,H⟩:= eventually_atTop.mp (ht.eventually_ge_atTop m)
    let X (i:Fin n):=refrain (l+i.val)
    choose M hM hX using fun i:Fin n=> hB (X i) (H _ (by omega))
    choose A D H using fun i=>heatWave P₀ F₀ T Ω O hk hη hh (hX i) a d s
    let p:=∑ i, |A i|; let q:= ∑ i,|D i|
    have hh(i:Fin n):A i ≤ p:= (le_abs_self _).trans (single_le_sum (f:=fun i=>|A i|) (fun _ _=> abs_nonneg _) (mem_univ i))
    have hD(i:Fin n): D i≤ q:= (le_abs_self _).trans (single_le_sum (f:=fun i=>|D i|) (fun _ _=> abs_nonneg _) (mem_univ i))
    refine ⟨p,q,?_⟩; filter_upwards [eventually_all.mpr H] with x hx; refine (eventually_ge_atTop l).mono fun k hk=>?_
    let i:Fin n:=⟨(k-l)%n,Nat.mod_lt _ hn⟩; let b:=(k-l)/n; have ht': i.val+n*b=k-l := Nat.mod_add_div ..; have he : k=l+i.val+n*b:=by omega
    have hL: O.L=(3:Side)^n:=by apply Subtype.ext; change O.L.val=((3:Side)^n).val; exact h.trans (by simp)
    refine ⟨X i,b,?_,broaden P₀ F₀ T (hx i x le_rfl) (hh i) (hD i)⟩; unfold X; rw [he,hL]; unfold refrain; -- rewrite issue b depends k!
    rw [pow_add,pow_mul,mul_assoc]
end Cairn
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Cairn.periodics
