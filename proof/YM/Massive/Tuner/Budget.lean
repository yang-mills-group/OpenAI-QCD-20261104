import YM.QCD.Reef.Crown
import YM.Massive.Tuner.Shoot
import YM.Massive.Pressure.Minor
import YM.Massive.Pressure.Smoothed
import YM.Massive.Tuner.Flat
import YM.Massive.Tuner.Empty
import YM.Massive.Tuner.Major
import YM.Massive.Pressure.Major
import YM.QCD.Tide.Palace
import YM.QCD.Corn.Green
import YM.QCD.Rain.Majesty
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
variable (A0:∀ i,Pixel (towerQ O B n i k) N)
namespace Reference
open Next.Rank IV
variable {s t A'' :ℝ}
open NormedSpace
open MeasureTheory
open YM.SectorNext.Vacuum (rich spare)
open YM.Massive.Pressure (scent_one)

lemma mud_pay (X : EvenA c N) : ‖mud X‖ ≤ ‖X‖:=by
   change ‖coef ∅ X.val‖ ≤ ‖X.val‖; rw [Grass.norm_def]
   exact single_le_sum (f:=fun i=>‖coef i X.val‖) (fun i _=>norm_nonneg _) (mem_univ _)

lemma size_start (L : HaarBudget su) (vi : ℝ) (hi : 0<vi) (he : vi≤1) (hb : 0 ≤ β) (hK : β*vi^2≤2)
    (he' : Even c.val) (hn : 4 ≤ c.val) (P : BudgetPoint)
    (A : Voice c N) (ht : 1≤fan J.L η x) (hr : Enn P b' J.L x η (1/8) (duo A.P A.K)) (ht' : |Jets.Touch.chip J.L x|≤1)
    (hs : P.B= highR J.L x) (S : SunR Ω) (q : PathData su) (t : Clip) (l : Train j)
    (Y : Pixel c N) (u k : ℝ) (hu : |u|≤1) (hk : 0<k) (hQ : Y = k • red A.P A.K S P₀ l P q t (haloK J.L x) β u 0) (hp:∀ y,Cove.light _ (Y y)=primalD c N β u y) :
    k*Globe.expo (1+Fintype.card PlaqAxes) c*(L.small*vi^su.lieDim)^spare c ≤ (Cvol Y).re:=by
   let v:ℝ := Fintype.card (Site c); let Z:=red A.P A.K S P₀ l P q t (haloK J.L x) β u 0
   have he y:Y y=k • Z y:=congr_fun hQ y
   let D:= Patron.total A.P P.threshold 1; have hh: Real.exp (-v) ≤ ‖mud (Z 1)‖:=by
        let B:= songT (c:=c) (N:=N) (fan J.L η x)⁻¹
        have hv:0 ≤ v:=Nat.cast_nonneg _
        have hD:‖D‖ ≤ v := (wordy b' A hr hs 1).2.trans (le_trans (b:= ‖B‖ * v) (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hv ((le_abs_self _).trans ht')) (norm_nonneg _)) (mul_le_of_le_one_left hv (Globe.cache ht)))
        unfold Z red; rw [flatP,scent_one,zero_add]; apply Real.exp_monotone; exact (abs_le.mp ((Complex.abs_re_le_norm (mud D)).trans ((mud_pay D).trans hD))).1
   have hz : k*Real.exp (-v)≤1:=by
        apply (mul_le_mul_of_nonneg_left hh hk.le).trans_eq
        rw [←Real.norm_of_nonneg hk.le,←norm_smul (α:=ℝ), ← show mud (k • Z 1)=k • mud (Z 1) from map_smul ((clay c N).restrictScalars ℝ) ..,← he]
        change ‖Grass.coef ∅ (Cove.light _ (Y 1))‖=1
        rw [hp]; unfold primalD
        have hf : Wilson.bare β (1:Grid c)=1:=by simp [Wilson.bare, Wilson.energy, WilsonStartup.face_one, su.price_one]
        rw [hf, one_smul, show coef ∅ (gauss _)=1 from mudB _ (N:=N), norm_one]
   let R:Massive.Regulator c N:=⟨β,0,fun _=>u⟩
   have hM : Cvol Y=R.Z:=by
        change (∫ i, _ ∂prior su c)=Massive.joint ⇑(R.density*1); rw [mul_one]; unfold Massive.joint; apply integral_congr_ae (ae_of_all _ fun i=>?_); change ber _ (Cove.light _ (Y i)) = _; rw [hp]; rfl
   rw [hM]; apply le_trans _ (Massive.Pressure.wilson L R hi ‹vi≤1› (fun j=>show -3 ≤ u from (by obtain ⟨h1,h2⟩:= abs_le.mp hu; linarith)) hb hK he' hn)
   have he : k*Globe.expo (1+Fintype.card PlaqAxes) c = k*Real.exp (-v)*Real.exp (-v*(Fintype.card PlaqAxes:ℝ)):=by rw [mul_assoc,← Real.exp_add]; unfold v Globe.expo; ring_nf
   rw [he]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (Real.exp_pos _).le hz) (by have := L.positive; positivity)

section other
variable (L : HaarBudget su) {θc : ℝ} (hG:Gated θc T' B b' g P' X Y κ x τ'.t D W' k V U Wv A0)
variable (hk:O.Branches T'.bind su)(hN:Even N)
include hG hk hN
lemma proper (i : ℕ)(hi : i≤n) : Continuous (A0 i) ∧ Rain.realP (A0 i) ∧ ProperF (A0 i):=by
   induction i with
   | zero=>
        let T:= (⟨V 0,0,U 0⟩:Cut (towerQ O B n 0 k) N); obtain ⟨hu,hv,-⟩:=dawning T rfl hG.begin hN; exact ⟨hu,hv,garbs hG.begin⟩
   | succ j ih=>
        obtain ⟨hp,hv,hM,h⟩:= hG.vocals j hi; obtain ⟨hq,hm,ht⟩:=ih (by omega)
        let S:=Pike O j; exact ⟨(Rain.marching S _ (A0 j) _ hk hq _ _ hp h).1,sunlight S _ _ _ _ (A0 j) _ hp hk hq h hm,marchP (S:=S) _ _ _ _ hk ht hq hp h⟩ -- S explicit

lemma minor (i : ℕ) (hi : i<n) (he : 1 < (towerQ O B n (i+1) k).val) (hβ : 0≤V i) :
    (((Pike O i).visit T'.bind (lift0 B (t:=k) hi)).penaltyZ (V i) su)^spare (towerQ O B n (i+1) k)*(cBer (A0 (i+1)) 1).re ≤ (Cvol (A0 (i+1))).re:=by
   obtain ⟨hp,hV,h⟩:= proper B b' g A0 hG hk hN i hi.le
   obtain ⟨hp',hV',h'⟩:= proper B b' g A0 hG hk hN (i+1) hi
   obtain ⟨hw,hx,hy,hj⟩:= hG.vocals i hi
   let P:= (Pike O i).visit T'.bind (lift0 B (t:=k) hi); let n':=towerQ O B n i k; let c:=towerQ O B n (i+1) k
   let p (j:Grid n'):= (cBer (A0 i) j); let q (x:Grid c) := cBer (A0 (i+1)) x; let K:=gain (Wv i)⁻¹ c N; let L : ℝ := (P.penaltyZ (V i) su)^spare c
   have hh (U:Grid c) : P.push (V i) (fun j=>(p j).re) U= K*(q U).re:=by
         have hv: (ber _ (advance (Pike O i) T'.bind (lift0 B (t:=k) hi) (A0 i) (V i) U)).re= _ := (IV.voicing (S:=Pike O i) (K:=T'.bind) (h:=lift0 B (t:=k) hi) hk _ hp hV _ U).2
         apply hv.symm.trans; rw [hj U]; change (ber _ (Cove.light _ (wearK c N _ _))).re=_; rw [Rain.crestP]; simp; rfl -- maybe
   have hI: Integrable p (prior su n'):= ((peakW n' N).continuous.comp hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hf : GaugeInvariant (P.push (V i) (fun j=>(p j).re)):=by
         intro k U; rw [hh,hh,show q (Lattice.gauge k U)=q U from ?_];
         change ber _ (Cove.light _ _) = _; rw [← no_jac N k, h'.gauges]; rfl
   have hv:=Massive.Pressure.Average.smooth he su (V i) P hβ hk (fun j => (p j).re) hI.re (fun j => (hV j).2) hf (1:Grid c)
   rw [hh 1,show (∫ j,(fun j=>(p j).re) j ∂prior su n') =(Cvol (A0 i)).re from integral_re hI,(Rain.marching (Pike O i) _ (A0 i) T'.bind hk hp (V i) _ hw hj).2, Complex.smul_re, smul_eq_mul] at hv
   change L * (q 1).re ≤ _; rw [mul_left_comm] at hv; exact le_of_mul_le_mul_left hv (show 0 < K from pow_pos (inv_pos.mpr hw) _)

end other
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.size_start
#print axioms YM.QCD.Acre.Rails.Reference.minor
