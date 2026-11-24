import YM.QCD.Glass.Reins
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
open High PrismT MeasureTheory Grass
variable (b':Flavor N) (O:Clip)(K':PathData su)
lemma backB (W:Voice c N)(E:Patch)(b v x:ℝ)(U:SunR Ω)(i:ℕ): quoteF c W (passportM E.J E.order_cut) (tile E i) O K' P U (haloK E.L x) v b=bio P W K' O (FieldB Ω U c (haloK E.L x) (passportM E.J E.order_cut) (tile E i)) U.Z.page v b:=rfl
variable (T':Teller su){S':ℕ→SparkMesh}(B:SparkMesh)
section one
variable (F': Flavor N)(g:PulseRide T'.bind T'.top.clip J a d S' n) (E:ℕ→SunR Ω)
noncomputable def Trek (T':Teller su)(B:SparkMesh)(F':Flavor N)(g:PulseRide T'.bind T'.top.clip J a d S' n)(E:SunR Ω)(p:BudgetPoint)(i k:ℕ)(s t x σ:ℝ)(Y:Pixel (towerQ J B n i k) N):Prop:=∃ (A:Voice (towerQ J B n i k) N)(u:ℝ),0<u ∧ Enn p F' J.L (delay J n i s) t (1/8) (duo A.P A.K)∧ Y=u • songBody B A g p E s x σ (k:=k) (i:=i) (T':=T')
noncomputable abbrev ΞP (Ω:ParcelR)(U:SunR Ω)(c:Side)(J:Patch)(s:ℝ) (k:ℕ):=FieldB Ω U c (haloK J.L s) (passportM J.J J.order_cut) (tile J k)
variable (R)
noncomputable abbrev FortG (h:i<n)(t p:ℝ)(Y:Pixel (towerQ J B n i k) N): Pixel (towerQ J B n (i+1) k) N:= vest _ _ t (fort (Pike J i) T'.bind (lift0 B h) N p Y)
noncomputable abbrev billT (J:Patch)(i j:ℕ)(x D:ℝ):ℝ:= 2*|hatG J i j x|+ |D|+1
variable {T'} {δp: ℕ→ℝ} {T:ℕ→Towers J.L}{o:Target.Order su W}{Q:ConnectedActivityE6.Target su T'}{τ:Policy Q T'.top N}
variable (hΓ:PassageR τ D B S' F' χ g Ω E δp T x κ s₀ 1 μ z 1 W' H A' (1/8) o (T':=T')) -- potential `variable` different!
set_option quotPrecheck false
variable {w₅ w₆ d₁:ℝ} (Y':PlaqAxes)
structure Satyr (T':Teller su)(B:SparkMesh)(F':Flavor N)(g:PulseRide T'.bind T'.top.clip J a d S' n)(hi:i < n)(E:ℕ→SunR Ω)(P R:BudgetPoint)(k:ℕ)(x D α u v θ:ℝ)(j:PlaqAxes)(w₅ w₆ d₁:ℝ):Prop where -- u=κ? etc
 gift :0 < w₅
 positive: 0 < v
 entries (p m:ℝ)(Z:Pixel (towerQ J B n i k) N)(hp:Cashroom J n i x p)(hZ: Trek T' B F' g (E i) P i k x θ p m Z)(hM: |m|≤u):
     ∃ (t m' d:ℝ), let F:=FortG T' B hi t p Z; let c:= towerQ J B n (i+1) k; let l:=delay J n (i+1) x; let V:= E (i+1);let Q:=ΞP Ω V c J l (i+1);
     0<t∧t ≤ 4∧|d|≤2 ∧Trek T' B F' g V R (i+1) k x θ (p+α+d) m' F ∧ForceMass m u m' v∧ (∀ U:Grid c, advance (Pike J i) T'.bind (lift0 B hi) Z p U =gBody c t (F U))∧ 1/4 ≤ Stew.Project.unitF true c (Q 1) ∧ NormG Q F' F R (g.path (i+1)) T'.top.clip V.Z.page j w₅ w₆ d₁ (p+α+d) m'
include hΓ
lemma tracts (h:i<n)(hy: T'.top.supportExponent=2)(hp:Now J.L P T'.top (delay J n i x))(ht:Now J.L R T'.top (delay J n (i+1) x))(hj:0 < rangeG J n (i+1) κ τ.t x)
    (hM:KeysG (towerQ J B n (i+1) k) R (g.path (i+1)) T'.top.clip J.L (delay J n (i+1) x) τ.t s₀ (billT J n i x (g.costP i+N*δp i)) F' Y' (rangeG J n (i+1) κ τ.t x) w₅ w₆ d₁): Satyr T' B F' g h E P R k x D (g.costP i+N*δp i) (rangeG J n i κ τ.t x) (rangeG J n (i+1) κ τ.t x) τ.t Y' w₅ w₆ d₁:=by
   refine ⟨hM.gift,hj,?_⟩; intro p m Z hP hZ hL; obtain ⟨X,L,hF,hE,rfl⟩:= hZ
   obtain ⟨S,m',p',w,B',hW,hG,hVp,hα,hY,hM',hn,hB,h⟩:=earthedR F' B g hΓ hy h X hp hE ht hL hP.1 hP.2 -- don't shadow
   let d:=g.costP i+↑N*δp i; let u:=p+d+p'; let Y:= E (i+1); let C:= towerQ J B n (i+1) k
   have hu : |u|≤ billT J n i x d:=by
       have he: |p|≤2*|hatG J n i x| :=by
         have hx':=(abs_le.mp (le_refl |hatG J n i x|)).1; have hp:=hP.1; have hh:= hP.2; exact abs_le.mpr ⟨by linarith [abs_nonneg (hatG J n i x)],by linarith [le_abs_self (hatG J n i x)]⟩
       exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add_left he _)) hα)
   let q:= delay J n (i+1) x; let V:=ΞP Ω Y C J q (i+1);
   obtain ⟨X₀,r',w',D',h1,h2,h3,h4,h5,h6,h7,h8⟩ :=hM.immigrates S V hn hW u m' Y.Z.page hM' hu
   let Q₀:=songBody B X₀ g R Y x (u+D') r' (k:=k) (i:=i+1) (T':=T'); let X₁:=songBody B X g P (E i) x p m (k:=k) (i:=i) (T':=T')
   let U₁:=w'*w; have he : p+d+(p'+D')=u+D':=by unfold u; abel
   have hV : vest C N w' (songBody B S g R Y x u m' (k:=k) (i:=i+1) (T':=T'))=Q₀:=funext h6
   obtain ⟨hL',hY'⟩:= canonX w w' L B' hG h3 X₁ _ _ hV h
   refine ⟨U₁,r',p'+D',mul_pos h3 hG,(mul_le_mul h4 hVp hG.le (by positivity)).trans (by norm_num),(abs_add_le ..).trans ((add_le_add hα h5).trans_eq (by norm_num)),?_,forceζ hY hj h2,?_,h7,?_⟩ -- let-intros edit
   · refine ⟨X₀,L*B',mul_pos hF hB,h1,?_⟩; rw [he]; exact hL'
   · intro A; rw [← hL'] at hY'; exact hY' A -- rw funct
   rw [he]; change NormG V F' ((vest C N U₁ _)) _ _ _ _ _ _ _ _ _ _; rw [show vest C N U₁ _= _ from hL']; exact oasisP F' h8 (mul_pos hF hB)
end one
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.tracts
