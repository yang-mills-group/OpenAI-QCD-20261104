import YM.QCD.Glass.Tune
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
variable (g:ℕ→ℝ) (J)
def centerG (g:ℕ→ℝ)(p:ℝ)(N j:ℕ):= p-Raft.Tally j (N-j) g
noncomputable abbrev sideG (N j:ℕ):ℝ:= (N-j:ℕ)*3+1
structure RightsT (J:Patch)(N k:ℕ)(t σ w:ℝ)(g:ℕ→ℝ) (i:ℕ) :Prop where
    le (p:ℝ):|p-centerG g σ N i|≤ sideG N i → Cashroom J N i t p
lemma squares (J:Patch)(v:ℝ) (h:i<n):centerG g v n i+g i=centerG g v n (i+1):=by
    unfold centerG; rw [show n-i=n-(i+1)+1 by omega]; -- peel
    have h(n:ℕ)(i:ℕ): Raft.Tally i (n+1) g=Raft.Tally (i+1) n g+g i:=by
        induction n with | zero=> simp [Raft.Tally] | succ n ih=>rw [show Raft.Tally i (n+1+1) g=Raft.Tally i (n+1) g+g (i+(n+1)) from Finset.sum_range_succ ..,ih,show Raft.Tally (i+1) (n+1) g= _ from (show _=Raft.Tally (i+1) n g+g (i+1+n) from Finset.sum_range_succ ..)]; rw [show i+(n+1)=i+1+n from (by omega)]; abel
    rw [h]; ring
lemma side_p (N i:ℕ) : 0 <sideG N i:=by unfold sideG; positivity
lemma routeH (J:Patch)(h:i≤n) : hatG J n i x=x+su.slopeConstant*Real.log J.L.val+(n-i:ℕ)*(su.slopeConstant*Real.log J.L.val):=by
    let F:=J.L; let v:=su.slopeConstant* Real.log F.val; have he (l:ℕ): tallyK F x l=x+l*v:=by induction l with|zero=> simp [tallyK]|succ l ih=>rw [show tallyK F x (l+1)=run F (tallyK F x l) from Function.iterate_succ_apply' ..,ih]; change x+ l*_+v=_; push_cast; ring
    unfold hatG delay; rw [he]; change x+ _* _+_= _; ring
lemma asks (D s:ℝ) (H:D≥0)(hp:2*(D+3) ≤ subG N*Real.log J.L.val) :∀ᶠ x in atTop,∀ (n:ℕ)(g:ℕ→ℝ)(j:ℕ),j≤n →(∀ i l,i+l≤n→ |Raft.Tally i l g+l*(betaQ N * Real.log J.L.val)|≤ l*D+N*s)→ RightsT J n N x (run J.L x) s g j:=by
    let L:=Real.log J.L.val; have hL:0≤L:= Real.log_nonneg (by exact_mod_cast J.L.pos); let S:=su.slopeConstant*L; have hG:0≤S:=mul_nonneg (Gauge.slopeConstant_pos simple).le hL
    let p:=betaQ N* L; have hP:p≤S:=mul_le_mul_of_nonneg_right (by unfold betaQ Pearl.chargeF; exact sub_le_self _ (by positivity)) hL
    have hx: p-S/2≥2*(D+3):=by unfold subG at hp; unfold p S; linarith only [hp]
    filter_upwards [((Work.E09.betaF_growth su J.L).eventually_ge_atTop (max 1 (2*N*s+4):ℝ))] with x he n g j hJ hT
    constructor; intro t hv; let k:= n-j; let r:ℝ:=k; -- remove
    obtain ⟨h1,h2⟩:= abs_le.mp hv; obtain ⟨h3,h4⟩:=abs_le.mp (hT j k (by omega)); unfold centerG sideG at *; let y:=run J.L x; have h5:y≥ 2*N*s+4:= (le_max_right ..).trans he; have h6:y≥1:= (le_max_left ..).trans he
    unfold Cashroom; rw [routeH J hJ]; change (y+r*S)/2 ≤ t∧t≤2*(y+r*S); have hr:0≤r:=Nat.cast_nonneg _
    change -(r*3+1) ≤ t-(y-Raft.Tally j k g) at h1; change t-(y-Raft.Tally j k g) ≤ r*3+1 at h2; change y≥2*N*s+4 at h5; change -(r*D+_)≤ Raft.Tally j k _+r*p at h3; change Raft.Tally j k g+ r*p≤ _ at h4; constructor
    · linarith only [h1,h4,h6,h5, mul_le_mul_of_nonneg_left hx hr, mul_nonneg hr H,hr]
    linarith only [h6,h5,hP,h2,h3,h4,mul_le_mul_of_nonneg_left hP hr,mul_le_mul_of_nonneg_left hx hr,mul_nonneg hr H,hr]
end Rails
end YM.QCD.Acre
