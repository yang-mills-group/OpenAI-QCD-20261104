import YM.Parishes.Luxe
import YM.Parishes.Rebates
import YM.VStages.Predict
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
variable {K:KernelChoices}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R: BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P: SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
open Suburb Rails
namespace Tribute
open Massive.Poised Massive Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.Poised.Pipes
open Bank Hike Stative Stair -- Hike nested? open Bank before
variable {D U M A:Type}(Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0 Gn :ℕ)
variable {θ tol:ℝ}(Y:Metros P J θ F₀ χ)
-- same base.Cliff. Pre prices per node; Lois K-neighbor max in bootstrap of progress; simple sum bound†.
structure Fluke (d:ℕ) where
 (n k m s r:ℕ)
 (a b:ℝ)
   -- n=order, k power, m polynomial leg, s #band length. chosen prior
 award:Pilot Θ Uv d n k m s r a b
 high: d < n
 core :6  ≤  n
 hull : d+1 ≤  s
 wide : max 2 d ≤  k
 power : max 2 d ≤ m
noncomputable def maker (Gn:ℕ) : Fluke Θ Uv Gn:=Classical.choice <| show Nonempty .. from by
    let n:=6+Gn; let k:=max (max 2 Gn) (Gn*Gn); let m:=max (max 2 Gn) (Beacon.surface Gn); let s:= Gn+1+ Fintype.card (Palette.ZBand Gn)+1
    obtain ⟨r,a,b,hP⟩:= services Gn Θ Uv n k m s (by omega) (le_max_right ..) (by omega) (le_max_right ..)
    exact ⟨n,k,m,s,r,a,b,hP,(by omega),(by omega),(by omega),(le_max_left ..),le_max_left ..⟩
variable (b:ChangeQ)(f:Fluke Θ Uv Gn)
local notation "Z!"=>maker Θ Uv Gn
local notation "η"=>θ -- dangerous
structure PreLoan (Gn:ℕ)(f:Fluke Θ Uv Gn) where
   M :ChangeQ→ℝ
   g :ChangeQ→ℕ
   funds b : 1 ≤ M b
   major : ∀ (b:ChangeQ),Gn/2 ≤ b.lo→∀ (S:Flight b.old b.new), g b  ≤  S.L.val→ S.patch.Branches K su→∀ (σ τ Λ tol:ℝ)(p:ParcelR)(X:LedgerQ (Y b) tol S σ τ Λ p),∀ᶠ x in atTop,Cliffs Θ (J b.hi) (J b.lo) χ X.policy S.patch X.o p i0 Gn f.n f.k f.s f.m X.μ X.C (M b) (run S.L x)
lemma funded : Nonempty (PreLoan Θ Uv i0 Y Gn f):=by
   have hp (b:ChangeQ)(h:Gn/2 ≤ b.lo):= bridal Θ (Y b) i0 Gn f.n f.k f.s f.m f.core f.high h f.wide ((le_max_right ..).trans f.power)
   -- choose! caveat. for other b easy
   choose! M g hg hS using hp
   let V (b:ChangeQ):= if Gn/2 ≤ b.lo then M b else 1 -- type
   refine ⟨V,g,fun b=>?_,fun b hb S h hq α β γ tol p X=>?_⟩
   · unfold V; split; exact hg _ (by assumption); rfl
   unfold V; rw [if_pos hb]; exact hS _ hb S h hq α β γ tol p X
variable (V:PreLoan Θ Uv i0 Y Gn f)
-- `LW orientation`, rewards from C and β costs.Total tol.R.Up.Track.B
abbrev tabC (b:ChangeQ)(M:ℝ):=Stair.lootS Gn 4 (f.a* preS M f.b) -- loot with w ≤ 4, includes support etc
abbrev eps (b:ChangeQ):= (8*tabC Θ Uv Gn f b (V.M b))⁻¹
abbrev goldT (b:ChangeQ):ℝ:= supportC (V.M b) f.b f.a
abbrev ridgeT (b:ChangeQ):ℝ:= 2 * tabC Θ Uv Gn f b (V.M b)*(goldT Θ Uv i0 Gn Y f V b) -- args
abbrev coverT (b:ChangeQ):ℝ:= max (ridgeT Θ Uv i0 Gn Y f V (steady b.hi)) (ridgeT Θ Uv i0 Gn Y f V (enter b.hi))
local notation "Πr"=>tabC Θ Uv Gn f b (V.M b)
local notation "τq"=> goldT Θ Uv i0 Gn Y f V b
lemma guardT : 0< preS (V.M b) f.b:=by unfold preS; have he:= f.award.funds; have h1:=V.funds b; positivity
lemma tab_h : 1  ≤ Πr:= Stair.positiveS _ (by norm_num) (mul_nonneg (zero_le_one.trans f.award.light) (guardT ..|>.le))
lemma eps_h :0 < eps Θ Uv i0 Gn Y f V b:=by unfold eps; have h:= tab_h Θ Uv i0 Gn Y b f V; positivity
lemma scale_h : 1 ≤ goldT Θ Uv i0 Gn Y f V b:=by
    unfold goldT supportC; have h:= guardT Θ Uv i0 Gn Y b f V; have hF:=f.award.funds; have hG:= f.award.light; exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (by positivity)) (by linarith)
lemma stem_h :1 ≤  ridgeT Θ Uv i0 Gn Y f V b:=by unfold ridgeT; have ht:= tab_h Θ Uv i0 Gn Y b f V; exact one_le_mul_of_one_le_of_one_le (by linarith) (scale_h ..)
lemma feast_h :1  ≤ coverT Θ Uv i0 Gn Y f V b:= (stem_h ..).trans (le_max_left ..)
lemma next_pay (c:ChangeQ)(hc:c.lo=b.hi) : ridgeT Θ Uv i0 Gn Y f V c ≤  coverT Θ Uv i0 Gn Y f V b:=by
   obtain ⟨i,j,h⟩:=c; change i=b.hi at hc; rcases h with h|h <;> subst j; subst i; exact le_max_left ..; subst i; exact le_max_right .. -- syntax after <;> conflict
abbrev BranchPay (tol:ℝ) (b:ChangeQ)(S:Flight b.old b.new)(α β σ:ℝ)(p:ParcelR)(X:LedgerQ (Y b) tol S α β σ p)(x:ℝ):Prop :=
   Cliffs Θ (J b.hi) (J b.lo) χ X.policy S.patch X.o p i0 Gn f.n f.k f.s f.m X.μ X.C (V.M b) (run S.L x) ∧ BudgetH S.L (Y b).guide.halo i0 Gn f.n f.k f.r f.m f.s θ (V.M b) f.b f.a (coverT Θ Uv i0 Gn Y f V b) (eps Θ Uv i0 Gn Y f V b) x ∧ Rebater Uv S.L (r:=f.r) (d:=Gn) θ x -- order!
lemma permit_pay (tol:ℝ):∃ m:ℕ, Gn/2 ≤ b.lo→∀ (S:Flight b.old b.new),m ≤  S.L.val→ S.patch.Branches K su→∀ (A B F:ℝ)(p:ParcelR)(X:LedgerQ (Y b) tol S A B F p),∀ᶠ x in atTop,BranchPay Θ Uv i0 Gn Y f V tol b S A B F p X x:=by
    have hx:= (Y b).lead
    obtain ⟨m,hP⟩:=loanGate (Y b).guide.halo f.r i0 Gn f.n f.k f.m f.s θ (V.M b) f.a f.b _ _ (V.funds _) f.award.light f.award.funds (feast_h Θ Uv i0 Gn Y b f V) hx (eps_h Θ Uv i0 Gn Y b f V) -- args Q etc explicit later
    exact ⟨m+V.g b,fun h S hz hv A B F p X=> (V.major b h S (by omega) hv _ _ _ _ _ X).and ((hP S.patch (show m ≤  S.L.val by omega)).and (upCost Gn Uv S.L θ hx f.r))⟩ -- op.Ed
end Tribute
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.permit_pay
