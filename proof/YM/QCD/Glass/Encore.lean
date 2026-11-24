import YM.QCD.Glass.Slide
import YM.QCD.Sq.Axis
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
open High PrismT MeasureTheory
open High PrismT MeasureTheory Sq
open Grass
open Sq Stew.Project
variable {J:Patch}(T':Teller su)(B:SparkMesh) (b': Flavor N) {S':ℕ→SparkMesh}{Y:ℕ→ℝ}{P':ℕ→BudgetPoint}{E:ℕ→ SunR Ω}(D':PulseRide T'.bind T'.top.clip J a d S' n)
variable (O:PlaqAxes)(hD:Storyboard n k T' B b' D' P' E Y κ x r D W' O)(hPay:∀ i≤n,RightsT J n N x (run J.L x) W' Y i)(ht:J.Branches T'.bind su)
include hD ht hPay
lemma marchesC (l:ℕ)(hl:l ≤ n):∃ Z V U S F,ChartQ T' B b' D' l Z V U S F (P':=P') (k:=k) (Y:=Y) (E:=E) (κ:=κ) (x:=x) (r:=r):=by
     induction l with
     | succ j ih=>
          obtain ⟨Z,V,U,S,F,h⟩:=ih (by omega); exact ridesC _ _ _ _ _ hD hPay ht j V U S F h hl -- j
     | zero=>
          let x':= centerG Y (run J.L x) n 0; let u:= sideG n 0; let g:= rangeG J n 0 κ r x; let t (i:Twin):=x'+u*Sq.tail i; let s (i:Twin):= g* mast i; let P j i:= CodeG (towerQ J B n j k) N (t i) (s i)
          have hC : Continuous t:=by unfold t; fun_prop
          refine ⟨Set.univ,(fun _=>t),(fun _=>s),P,id,⟨isClosed_univ,continuous_id,(fun i hi=>(hi (Set.mem_univ _)).elim),fun i _=>⟨rfl,rfl⟩,fun i k _=> rfl⟩,hC.continuousOn,primeT hC (show Continuous s from (by unfold s; fun_prop)),fun _ _=>rfl,?_,fun _ _ i hi=>by omega,fun _ _ i hi=>by omega⟩
          intro v _ i hi; have hh:= side_p n 0; have hg:=hD.positive 0; have hp : Cashroom J n 0 x (t v):=by apply (hPay _ hl).le; unfold t; rw [show x'+u*Sq.tail v-centerG Y (run J.L x) n 0=u*Sq.tail v from (by unfold x'; ring),abs_mul,abs_of_nonneg hh.le]; exact mul_le_of_le_one_right hh.le (Sq.shore _).1 -- unfold x' hx
          rcases Nat.eq_zero_of_le_zero hi with rfl
          exact ⟨hp,(by rw [show |s v|= g*|mast v| by rw [show |s v|= _ from abs_mul _ _, abs_of_nonneg (show 0 ≤ g from hg.le)]]; exact mul_le_of_le_one_right hg.le (Sq.shore _).2),(hD.stars _ _ hp).1⟩
-- story.Ph.Mark
structure Stargate (T':Teller su)(B:SparkMesh)(b':Flavor N)(D':PulseRide T'.bind T'.top.clip J a d S' n)(P':ℕ→BudgetPoint)(E:ℕ→SunR Ω)(Y:ℕ→ℝ)(κ x r D W':ℝ)(k:ℕ)(V U W:ℕ→ℝ)(A0:∀ j,Pixel (towerQ J B n j k) N):Prop where
    receipts (i l:ℕ)(h:i+l ≤ n): |Raft.Tally i l Y+l*(betaQ N *Real.log J.L.val)|≤ l*D+N*W'
    clock (i:ℕ):Now J.L (P' i) T'.top (delay J n i x)
    begin (i:Grid (towerQ J B n 0 k)): Cove.light _ (A0 0 i)=primalD (towerQ J B n 0 k) N (V 0) (U 0) i
    finish: V n=run J.L x ∧ U n=0
    costs (i:ℕ)(h:i≤n): Cashroom J n i x (V i)∧0 < rangeG J n i κ r x ∧|U i| ≤ rangeG J n i κ r x ∧ Trek T' B b' D' (E i) (P' i) i k x r (V i) (U i) (A0 i)
    vocals (i:ℕ)(h:i<n): 0 < W i ∧ W i ≤4 ∧|V (i+1)-V i-Y i| ≤2 ∧ ∀ l: Grid (towerQ J B n (i+1) k), advance (Pike J i) T'.bind (lift0 B h) (A0 i) (V i) l=gBody _ (W i) (A0 (i+1) l)
    lawT (i:ℕ)(h:i<n): Litmus (ΞP Ω (E (i+1)) _ J (delay J n (i+1) x) (i+1)) b' (A0 (i+1)) (U (i+1))
lemma evoke :∃ V U W A,Stargate T' B b' D' P' E Y κ x r D W' k V U W A:=by
     obtain ⟨Z,V,U,S,F,h⟩:= marchesC T' B b' _ O hD hPay ht n le_rfl
     obtain ⟨y,hp,hV⟩:= Sq.beam F h.live.born h.live.chir; have hy:y∈Z:=by
           by_contra ht; obtain ⟨i,hx⟩:= h.live.goals y ht; unfold Sq.ray at hx; cases i <;> simp [hp,hV] at hx
     have hv(i)(hi:i≤n):= h.vogue y hy i hi; choose! f H using fun i hi=> h.cost y hy i hi hi
     refine ⟨(fun i=> V i y),(fun i=>U i y),f,(fun i=>S i y),hD.tale,hD.clock,fun i=>?_ ,?_,fun i hi=> ?_,?_, h.lawT y hy⟩
     · rw [h.birth y hy]; exact (hD.stars _ _ (hv 0 (by omega)).1).2 i
     · obtain ⟨hx,ht⟩:=h.live.site y hy; rw [hp,mul_zero,add_zero] at hx; rw [hV,mul_zero] at ht; exact ⟨hx.trans (by simp [centerG, Raft.Tally]),ht⟩
     · exact ⟨(hv i hi).1,hD.positive i,(hv i hi).2⟩
     intro i hi; exact ⟨(H i hi).1,(H i hi).2.1,(H i hi).2.2.1,(H i hi).2.2.2.2⟩
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.evoke
