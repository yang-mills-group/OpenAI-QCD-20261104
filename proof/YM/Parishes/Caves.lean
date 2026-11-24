import YM.Parishes.Trier
import YM.VStages.FullRun
import YM.VStages.MeltQ
import YM.Massive.Jasper.Source
import YM.Massive.Jasper.Fuse
import YM.VStages.WindowY
import YM.VStages.Lumens
import YM.VStages.SkawY
import YM.VStages.HazeY
import YM.Massive.Jasper.Food
import YM.VStages.Icicle
import YM.VStages.ExposureY
import YM.VStages.Thin
import YM.Massive.Sharp.Spectrum
import YM.VStages.Yarn
import YM.VStages.RegisterY
import YM.VStages.Wardpost
import YM.VStages.Foster
import YM.VStages.PonderY
import YM.VStages.VistaW
import YM.Massive.Aperture.Calendar
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor 6}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open MeasureTheory Rails.Reference Next.Rank IV Rain
open Finset NormedSpace Grass
open Cairn
open YM.Massive.Pressure (noiseZ)
open YM.SectorNext.Vacuum (rich spare)
variable {κ:ℝ}
open YM.Massive (transfer joint Density Regulator Stiffness.Window Scheme)
open Affair
namespace Melt
open Weft Fibre Sway OrbitG Conductor Conductor.Quant Struck Struck.Library Aperture -- Weft
open Glint Jasper
variable {Pt:ℕ→BudgetPoint}{Δ:PlaqAxes}
variable (B:SparkMesh) (T:Affair P₀ A X B x n)
set_option quotPrecheck false
local notation "Pq"=> J (A.level i)
local notation "S'"=> T.W.state
local notation "TZ"=> (P.stage (A.level i)).clip
local notation "Kz"=> K
open Massive (Sequence Scheme)
variable (E:RiseBook P₀) {O:Paved P₀ A X x} {Ht:Uptax P₀ A E x} (LL:HaarBudget su) {M₃:ℝ}
local notation "Φw"=>key P₀ A E

/-!
# One unequal-mass SU(3)-6 trajectory, in the coupling-and-spinor weight scheme,
with exact asymptotic slope, growing strides and mass-offset signal (positive & distinct)

Not the continuum theorem. See `tundra` for the existence result relating this
to the target `YM.Massive` quantities (the component `Sequence.searching`)
including tying the mass-offset signal to the Mark expansion and pressure assertions
(`Epitome`, `StormT` there). Statement for eventual βRef regime, no further
limit in reference β along the path.
-/
variable (ν:ℝ)
variable (stX:Supply P₀ A X E ν O Ht Pt) (ht:key P₀ A E σ)
variable (EM:Epitome P₀ A X B E fork ν Ht LL Pt Δ O a σ T k)
local notation "λ₀"=> clockQ P₀ A x 0
local notation "χm"=> SeasonR P₀ A E σ x
include stX ht
variable (Y: SeriesR P₀ A X E LL ν Pt Ht O Δ σ)
def KeptT (l:ℕ→ℕ):Prop:=(∀ i,l (Y.mark i)≤ (Y.outR P₀ A X E LL ν i).val) ∧ Nonempty ((i:ℕ)→ Trier P₀ A X (accord (Y.mesh i)) (Y.listed i) E fork ν Ht LL (Y.snap i))
omit stX ht -- check include context
variable (Δ:PlaqAxes) (hv:0<ν)(hTol:2*tol+tol^2≤1/2) (hw:2*tol+tol^2≤ν)(paid:ℝ)(paid_proof: Track.Staked A paid)(hR:K.penalty=1)
include hv hTol stX ht
lemma piled {Δ:PlaqAxes} (r:ℕ→ℝ)(he:∀ i, 0 < r i) (l:ℕ→ℕ) : ∃ Y:SeriesR P₀ A X E LL ν Pt Ht O Δ σ,
   (∀ i:ℕ, 0<Y.mark i) ∧ StrictMono Y.mark ∧ Y.quota=r ∧ KeptT P₀ A X E LL ν Y l ∧∀ i, i≤ (Y.outR P₀ A X E LL ν i).val :=by
   choose V hV hQ using Track.smoothWindow A
   let Q:=Nat.rec (motive:=fun _=>ℕ) 0 (fun _ d=> V d +1)
   have hvv:StrictMono Q:=strictMono_nat_of_lt_succ fun i=>lt_add_one _|>.trans_le (Nat.add_le_add_right (hV _) _) -- defeq?
   let M i:=V (Q i)+1
   have hm:StrictMono M:= fun i j h=> hvv (Nat.succ_lt_succ h)
   choose b hb using fun i:ℕ=> (stX.head.stock (M i) (fun l h=>by
         have ht: l=V (Q i):= Nat.succ_injective h.symm; subst l; exact hQ _)).exists
   let B i:= accord (b i); let Stb (i):= Classical.choice (hb i)
   have h(i:ℕ) : ∀ᶠ k:ℕ in atTop, ∃ T:Epitome P₀ A X (B i) E fork ν Ht LL Pt Δ O (r i) σ (Stb i) k, Nonempty (Trier P₀ A X (B i) (Stb i) E fork ν Ht LL T):= entities P₀ A X E fork ν Ht LL Δ stX (he i) hv hTol _ (Stb i) (by decide) (by decide) unmarkU ht
   choose k hk hK using fun i:ℕ=> ((h i).and ((B i).cofinal.eventually_ge_atTop (max i (l (M i))))).exists; choose Z hz using hk; exact ⟨⟨M,k,b,Stb,r,Z⟩,fun i=>Nat.zero_lt_succ _,hm,rfl,⟨fun i=>(le_max_right ..).trans (hK i),⟨fun i=> Classical.choice (hz i)⟩⟩,fun i=>(le_max_left ..).trans (hK i)⟩
variable (heG:Earlier P 6 gate)
include heG hw paid_proof hR
set_option maxHeartbeats 700000 in
theorem quay (l:ℕ→ℕ) : ∃ (u: Flavor 6→ℝ) (Y:SeriesR P₀ A X E LL ν Pt Ht O Δ σ), Ship P₀ A X E LL ν Δ u Y ∧ KeptT P₀ A X E LL ν Y l:=by
   let L:=Glint.Value (SeasonR P₀ A E σ x); let M:=2*StartM P₀ A x; let v:= SeasonR P₀ A E σ x; have hv':0< v:= Glint.money_pos (token P₀ A X E stX.views ht).1
   obtain ⟨r,hr,h⟩:= wait6 (by positivity : 0<v/256); obtain ⟨Y,hN,hY,hQ,hPk,hV⟩:= piled (Δ:=Δ) P₀ A X E LL ν stX ht hv hTol r (fun i=> (hr i).1) l
   let Q:=SeriesR.flagP P₀ A X E LL ν Y

   have hQ' (i:ℕ) :DensityS 6 (Q i) L M:= braved P₀ A X (accord (Y.mesh i)) (Y.listed i) E LL ν stX ht (Y.snap i) (hN i) (hQ.symm ▸ (hr i).2)
   let W: Set (Flavor 6→ℝ):=Set.univ.pi fun _=> Set.Icc L M; obtain ⟨u,hu,g,hg,H⟩:= (show IsCompact W from isCompact_univ_pi fun i=>isCompact_Icc).tendsto_subseq (x:=Q) (fun i b _=> (hQ' i).margin b); let Y':SeriesR P₀ A X E LL ν Pt Ht O Δ σ:=⟨Y.mark ∘ g,Y.floor ∘ g,Y.mesh ∘ g, (fun i=> Y.listed (g i)), Y.quota ∘ g, fun i=> Y.snap (g i)⟩ -- avoid notation d
   let G:= SeriesR.series P₀ A X E LL ν Y'
   have hτ:=StrictMono.tendsto_atTop hg; have hy : StrictMono Y'.mark:=hY.comp hg
   have he: Tendsto Y'.quota atTop (𝓝 0):=(hQ.symm ▸ h).comp hτ -- motive
   have hb (i:ℕ)(m:ℕ)(h:m ≤ Y'.mark i):= story P₀ A X (accord (Y'.mesh i)) (Y'.listed i) E fork ν Ht LL (Y'.snap i) stX splitU h
   obtain ⟨hhg,⟨Dg⟩⟩:=hPk; refine ⟨u,Y',⟨fun i=> hN _,?_,?_ ,fun i=> (hQ.symm ▸ hr) (g i),he,H⟩,fun i=>hhg (g i),Nonempty.intro (fun i=> Dg (g i))⟩
   · change G.Path x ν
     refine ⟨hR,rank_ge _,( (tendsto_atTop_mono (fun i=> hV i) tendsto_id).comp hτ), hy,(Suburb.ladder_time P₀ A).comp (StrictMono.tendsto_atTop hy),fun i=>(Y'.snap i).arrange.ready.2.1,fun i=>(Y'.snap i).arrange.ready.1,fun i=>(hb i 0 (by omega)).2.1,fun i=>(hb i 0 (by omega)).2.2.1,fun i=>(Y'.snap i).history.finish.1,fun {i m} h=> (hb i m h).1,fun {i m} h=>(hb i m h).2.2.2.2.2.1,fun m=>⟨2*A.scale x m,fun i h=>(hb i m h).2.2.2.2.2.2.1⟩,fun {i m} h=> ((Y'.snap i).history.relay m h).band.trans hw,?_⟩
     refine ⟨Reference.SIX.2,fun ε' hε'=>?_⟩
     filter_upwards [Track.slope_all A heG x ε' paid_proof hε'] with m hm i hi; rw [Reference.SIX.1]; change |_ / Real.log (((Suburb.ladder P₀ A).spacing m)⁻¹) - _|≤ ε'; rw [Suburb.ladder_cost]; exact hm _ _ (Y'.listed i).W (accord (Y'.mesh i)) ((Y'.snap i).spin m) hi (Y'.listed i).aligned (hb i m hi).2.2.2.2.2.2.2
   have hh (b:Flavor 6):Tendsto (fun i=> Q (g i) b) atTop (𝓝 (u b)):= tendsto_pi_nhds.1 H b
   refine ⟨div_pos hv' (by norm_num),fun i=>(hu i (Set.mem_univ _)).1, fun i j h=> ge_of_tendsto' (((hh i).sub (hh j)).abs) (fun k=> (hQ' _).apart i j h),fun b=>?_⟩
   apply ((Complex.continuous_ofReal.tendsto _).comp (hh b)).congr_dist
   refine squeeze_zero (fun i=>dist_nonneg) (fun i=>?_) he; rw [dist_comm,dist_eq_norm]; exact (scene P₀ A X _ (Y.listed (g i)) E fork ν Ht LL ht (Y.snap (g i)) stX (hN _) (by decide)).2 b


end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.quay
