import YM.QCD.Cabin.Reach
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
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ: Policy Q T'.top N}
variable (F₀: Flavor N) {M':ℕ→SparkMesh}
variable {E:ℕ→SunR Ω}{X:ℕ→ℝ}{T:ℕ→Towers J.L}
lemma signing (B: SparkMesh)(g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:Passage τ D B M' F₀ χ g Ω E X T x κ s₀ 1 μ z 1 W' H A' 1 o){k:ℕ}(X':Grid (towerQ J B n 0 k))(hp:Pencil J.L P F₀ τ.t (delay J n 0 x) 1 (birthV (towerQ J B n 0 k) P N T'.top.clip β))(he:Decent T'.top.clip P): Cove.light _ (songBody (k:=k) (T':=T') (i:=0) B (birthV (towerQ J B n 0 k) P N T'.top.clip β) g P (E 0) x β b X')=primalD (towerQ J B n 0 k) N β b X':=by
    obtain ⟨hn,ht⟩:= hΓ.vaultUp
    unfold songBody quoteF red; rw [hΓ.gauge, vacT hΓ.start.2.2]; apply voiceBorn _ _ _ _ _ _ _ (defrost _ hn ht X') F₀ hp he -- args
-- public Sustained theorem no continuity. UV.Current.Ch.
variable (B:SparkMesh) (g: PulseRide T'.bind T'.top.clip J a d M' n)
noncomputable def hatG (E:Patch)(n i:ℕ)(x:ℝ):=run E.L (delay E n i x)
noncomputable def rangeG (J:Patch)(n i:ℕ)(κ θ x:ℝ):= roofK J.L θ κ (delay J n i x)
def Cashroom (E:Patch)(n i:ℕ)(x p:ℝ):Prop:= hatG E n i x/2 ≤ p ∧ p ≤2*hatG E n i x
lemma pointR (L:Side)(S:Stage) :∀ᶠ x in atTop,∃ p:BudgetPoint, Now L p S x:=by
   have hx:=Work.E09.betaF_growth su L
   filter_upwards [hx.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop 1), Delay.shift_pos su L, (Rate.flame (G:=su) (L:=L)).below (by norm_num) 1 zero_lt_one] with x ht hh hv
   let p:=betaF su x L; exact ⟨⟨S.power,S.order,S.supportExponent,radiusB p,fiery su x L,S.power_ge,S.order_ge,S.price_pos,ht,Work.E09.temp_pos hh,(le_abs_self _).trans hv⟩,⟨rfl,rfl,rfl⟩,rfl,rfl⟩
-- one late.RG property. indices actual M. 
set_option quotPrecheck false
structure Script (F₀:Flavor N)(B:SparkMesh)(g:PulseRide T'.bind T'.top.clip J a d M' n)(τ: Policy Q T'.top N)(Ω:ParcelR)(E:ℕ→SunR Ω)(x κ D W':ℝ)(P:ℕ→BudgetPoint)(Y:ℕ→ℝ):Prop where
  receipts (i l:ℕ)(h:i+l≤ n): |Raft.Tally i l Y+l*(betaQ N*Real.log J.L.val)| ≤ l*D+N*W'
  clock (i:ℕ): Now J.L (P i) T'.top (delay J n i x) -- syntax
  topG (k:ℕ)(p:ℝ): Cashroom J n 0 x p→
      let c:= towerQ J B n 0 k; ∃ W:Voice c N,Pencil J.L (P 0) F₀ τ.t (delay J n 0 x) 1 W ∧∀ (U:Grid c)(m:ℝ), Cove.light _ (songBody (T':=T') (i:=0) (k:=k) B W g (P 0) (E 0) x p m U)=primalD c N p m U
  warm (i k:ℕ)(hi:i < n)(A:Voice (towerQ J B n i k) N) : Pencil J.L (P i) F₀ τ.t (delay J n i x) 1 A →∀ σ p:ℝ,Cashroom J n i x p→|σ|≤ rangeG J n i κ τ.t x →
     ∃ (W:Voice (towerQ J B n (i+1) k) N)(m y w c':ℝ), Pencil J.L (P (i+1)) F₀ τ.t (delay J n (i+1) x) 1 W ∧0<w∧w≤2∧|y|≤1 ∧ForceMass σ (rangeG J n i κ τ.t x) m (rangeG J n (i+1) κ τ.t x)∧0 < c' ∧ ∀ (U:Grid (towerQ J B n (i+1) k)), advance (Pike J i) T'.bind (lift0 B hi) (songBody (T':=T') (k:=k) (i:=i) B A g (P i) (E i) x p σ) p U=c' • gBody (towerQ J B n (i+1) k) w (songBody (T':=T') (k:=k) (i:=i+1) B W g (P (i+1)) (E (i+1)) x (p+Y i+y) m U)
variable (S:Side) (θ:ℝ)
def Attain (L:Side) (T:Stage) (f:Flavor N)(x θ:ℝ):Prop:= ∀ y,x≤y→ (∃ p:BudgetPoint, Now L p T y) ∧∀ P:BudgetPoint,Now L P T y→∀ p, run L y/2 ≤ p→p≤2*run L y→∀ c:Side,Pencil L P f θ y 1 (birthV c P N T.clip p)∧Decent T.clip P
lemma attains (L:Side)(h:G.clip.direct≤1):∀ᶠ x in atTop, Attain L G F₀ x θ:=by
   obtain ⟨p,hp⟩:= eventually_atTop.mp ((pointR L G).and (savings _ _ F₀ h (Θ:=θ))) -- fix
   filter_upwards [eventually_ge_atTop p] with x hx y hy; exact hp y (hx.trans hy)
lemma nobleG (hΓ:Passage τ D B M' F₀ χ g Ω E X T x κ s₀ 1 μ z 1 W' H A' 1 o)(h:G=T'.top) (he:T'.top.supportExponent=2) (hL:Attain J.L T'.top F₀ x τ.t): ∃ (P:ℕ→BudgetPoint), Script F₀ B g τ Ω E x κ D W' P (fun j=>g.costP j+N*X j):=by
   have hm (i):= hL (delay J n i x) (matters ..); choose P H' using fun i=>(hm i).1
   refine ⟨P,hΓ.receipts,H',?_,?_⟩
   · intro k p hR c; obtain ⟨hp,hE⟩:= (hm 0).2 (P 0) (H' 0) p hR.1 hR.2 c; exact ⟨_,hp,fun U m=>signing F₀ B g hΓ U hp hE⟩
   intro i k hi A hA σ p hP hr; exact earthed F₀ B g hΓ he hi A (H' i) hA (H' (i+1)) hr hP.1 hP.2
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.nobleG
