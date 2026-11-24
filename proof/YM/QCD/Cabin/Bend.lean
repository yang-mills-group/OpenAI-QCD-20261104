import YM.QCD.Cabin.Fling
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
variable (A:Voice c N) (F₀: Flavor N) (B: SparkMesh) {M':ℕ→ SparkMesh}
abbrev towerQ (E:Patch)(S:SparkMesh)(n i j:ℕ):=(footM E S n i).n j
lemma lift0 {t:ℕ}(hv:i < n) : (towerQ J B n i t).val=(towerQ J B n (i+1) t).val*J.L.val:=by unfold towerQ; rw [foot_align B hv]; rfl
lemma legend (h:Pencil L P F₀ η w r A)(hb:r ≤ P.supportExponent)(hv:0≤r)(hp:P.B=highR L w):Enn P F₀ L w η r (duo A.P A.K):=by
    obtain ⟨hQ,hK,g,v,hG,hF,hU⟩:= promises A.P A.K _ L P r w hv hb hp h.portraitP -- binder order
    exact ⟨g,v,⟨hG,hF,hK,hQ⟩,hU⟩
-- n final; actual.Step.
variable {E:ℕ→SunR Ω}{X:ℕ→ℝ}{T:ℕ→Towers J.L}
variable (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:Passage τ D B M' F₀ χ g Ω E X T x κ s₀ 1 μ z 1 W' H A' 1 o)
noncomputable abbrev quoteF (c:Side)(Z:Voice c N)(K:Plan j)(w:Train j)(O:Clip)(T:PathData su)(P:BudgetPoint)(U:SunR Ω): ℝ→ ℝ→ℝ→Grid c→EvenA c N:=fun t v z=>red Z.P Z.K U K w P T O t v z 0
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
noncomputable abbrev songBody (B: SparkMesh)(Z:Voice (towerQ J B n i k) N)(g:PulseRide T'.bind T'.top.clip J a d M' n)(P:BudgetPoint)(U:SunR Ω)(x p v:ℝ):= quoteF (towerQ J B n i k) Z (passportM J.J J.order_cut) (tile J i) T'.top.clip (g.path i) P U (haloK J.L (delay J n i x)) p v
-- transport relation after.Less.C.Coordinate
include hΓ
lemma earthed (hy:T'.top.supportExponent=2)(hu:i < n)(A:Voice (towerQ J B n i k) N)(hP:Now J.L R T'.top (delay J n i x)) (hx:Pencil J.L R F₀ τ.t (delay J n i x) 1 A) (hR: Now J.L P T'.top (delay J n (i+1) x))(hm:|b| ≤ roofK J.L τ.t κ (delay J n i x))(hβ:run J.L (delay J n i x)/2 ≤ β)(hv:β ≤2*run J.L (delay J n i x)) : ∃ (E':Voice (towerQ J B n (i+1) k) N)(m β' w c':ℝ), Pencil J.L P F₀ τ.t (delay J n (i+1) x) 1 E' ∧ 0<w∧ w≤2 ∧ |β'|≤1 ∧ ForceMass b (roofK J.L τ.t κ (delay J n i x)) m (roofK J.L τ.t κ (delay J n (i+1) x))∧ 0 < c'∧ ∀ (U:Grid (towerQ J B n (i+1) k)), advance (Pike J i) T'.bind (lift0 B hu) (songBody (T':=T') (k:=k) (i:=i) B A g R (E i) x β b) β U=c' • gBody (towerQ J B n (i+1) k) w (songBody (T':=T') (k:=k) (i:=i+1) B E' g P (E (i+1)) x (β+(g.costP i + N* X i)+β') m U):=by
   let n':= delay J n (i+1) x; have hD:= next_delay J x hu
   have hg : Enn R F₀ J.L (delay J n i x) τ.t 1 (duo A.P A.K):= legend A F₀ hx (by rw [hP.era.2.2,hy]; norm_num) zero_le_one hP.ball
   rw [← hD] at hm hβ hv hP hg; obtain ⟨Z,Y,hZ⟩:= hΓ.posed i k hu P R hR hP b β hβ hv hm
   have hr:(towerQ J B n (i+1) k)=(M' i).n (k+5):=(hΓ.payment i k).symm
   let S:= Pike J i; have he: (towerQ J B n i k)=high S (M' i) (k+5):=Subtype.ext ((show (towerQ J B n i k).val=_ from (lift0 B hu).trans (by rw [hr]; exact (divides0 S (M' i) _).symm)))
   -- generalize
   let D:=g.costP i+N*(X i)
   have hx (f c:Side)(hv:f=high S (M' i) (k+5))(hp:c=(M' i).n (k+5))(hS:f.val=c.val*J.L.val)(A:Voice f N)(h:Enn R F₀ J.L (run J.L n') τ.t 1 (duo A.P A.K)): ∃ (E':Voice c N)(m v w c':ℝ), Pencil J.L P F₀ τ.t n' 1 E' ∧ 0<w∧ w≤2 ∧ |v|≤1∧ ForceMass b (roofK J.L τ.t κ (run J.L n')) m (roofK J.L τ.t κ n')∧0 < c'∧ ∀ (U:Grid c), advance S T'.bind hS (quoteF f A (passportM J.J J.order_cut) (tile J i) T'.top.clip (g.path i) R (E i) (haloK J.L (run J.L n')) β b) β U=c' • gBody c w (quoteF c E' (passportM J.J J.order_cut) (tile J (i+1)) T'.top.clip (g.path (i+1)) P (E (i+1)) (haloK J.L n') (β+D+v) m U):=by
       subst f c; exact release (P₀:=passportM J.J J.order_cut) _ A F₀ Z Y hZ rfl rfl h
   simp_rw [songBody,← hD]; exact hx _ _ he hr _ A hg
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.earthed
