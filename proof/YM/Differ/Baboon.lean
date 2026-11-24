import YM.Differ.Autumn
import YM.Differ.Chirp
import YM.Pods.Spear
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
namespace Nacre
open Bounce Ivy MeasureTheory
variable (f:Fluke Θ Uv Gn) (V:PreLoan Θ Uv i0 Y Gn f)
-- λ costs.Frame arbitrary.Prerange wear.S.Appointment.S tie inverse.
structure PilotW (b:ChangeQ)(a:ℝ):Prop where
     tall : 1≤ a
     top : (1+f.b*f.a)*preS (V.M b) f.b ≤ a
     element : (1+f.b*f.a)*(V.M b+1) ≤ a
     look : 2*tabC Θ Uv Gn f b (V.M b) ≤a
     base : ridgeT Θ Uv i0 Gn Y f V b ≤ a
lemma knocks (b:ChangeQ)(x:ℝ) :∃ m:ℝ, x ≤ m ∧ PilotW Θ Uv i0 Gn Y f V b m:=by
     obtain ⟨p,h1,h2,h3,h4,h5⟩ := (show ∃ m:ℝ,x ≤ m ∧ 1≤ m ∧ (1+f.b*f.a)*preS (V.M b) f.b ≤ m ∧ (1+f.b*f.a)*(V.M b+1) ≤ m∧2*tabC Θ Uv Gn f b (V.M b) ≤ m from by exact ⟨max (max (max (max (1:ℝ) x) ((1+f.b*f.a)*preS (V.M b) f.b)) ((1+f.b*f.a)*(V.M b+1))) (2*tabC Θ Uv Gn f b (V.M b)),by grind⟩); let q:= max p (ridgeT Θ Uv i0 Gn Y f V b); exact ⟨q,h1.trans (le_max_left ..),h2.trans (le_max_left ..),h3.trans (le_max_left ..),h4.trans (le_max_left ..),h5.trans (le_max_left ..),le_max_right ..⟩
lemma vertical (a b:ℝ)(ha:1 ≤ a)(hb:1 ≤ b) :∃ n:ℕ,∀ L:Side,n≤L.val→ Bounce.Ticket a b (Kit.slope L):=by
     let f:ℕ→ℝ:=fun i=>(Real.sqrt (i:ℝ))⁻¹; have h:Tendsto f atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
     let g:=fun i=> Real.sqrt (f i); have hp: Tendsto g atTop (𝓝 (0:ℝ)):= Real.sqrt_zero ▸ h.sqrt
     obtain ⟨i,hX⟩:= eventually_atTop.mp (((hp.const_mul (a^2+a)).eventually_le_const (show _<(1/32:ℝ) from (by norm_num : (a^2+a)*0<_))).and (((hp.const_mul a).mul_const (b^2)).eventually_le_const (show _<(1/32:ℝ) from (by norm_num : a*0*b^2<_)))) -- simplify
     refine ⟨i,fun L hx=> ⟨ha,hb,Kit.slope_pos L,?_,(hX _ hx).1,(hX _ hx).2⟩⟩; unfold Kit.slope; exact (inv_le_one₀ (by positivity)).mpr (Real.sqrt_one ▸ Real.sqrt_le_sqrt (by exact_mod_cast L.property))
-- gap purpose. Post K0 costs.C.Qx for occupancy repeated.St.Wrap.
variable (a:ChangeQ→ℝ)(hp:∀ b:ChangeQ,PilotW Θ Uv i0 Gn Y f V b (a b))
structure BodyUp (b:ChangeQ)(L:Side)(x e:ℝ) :Prop where
   loans : Ivy.Silo L ((Y b).guide.halo) i0 Gn f.n f.k f.r f.m f.s θ (V.M b) f.b f.a e x
   earns(c: ChangeQ):c.lo=b.hi→ Bounce.Ticket (a b) (a c) (Kit.slope L)
-- forall d & α pick heights prone.Don't fix higher d.W Outlook.
include hp
lemma chair (b:ChangeQ) : ∃ m:ℕ,∀ L:Side,m ≤ L.val →∀ (ε:ℝ),0<ε→∀ᶠ x in atTop, BodyUp Θ Uv i0 Gn Y f V a b L x ε:=by
    obtain ⟨s,hS⟩:=vertical (a b) (a (steady b.hi)) (hp b).tall (hp _).tall
    obtain ⟨t,hT⟩:= vertical (a b) (a (enter b.hi)) (hp b).tall (hp _).tall
    refine ⟨s+t,fun L h e he=>?_⟩; filter_upwards [Ivy.tidies L i0 ((Y b).guide.halo) Gn f.n f.k f.r f.m f.s θ (V.M b) f.b f.a e (Y b).lead (V.funds b) (f.award.funds) (f.award.light) he] with x hx; refine ⟨hx,?_⟩; intro c h; obtain ⟨i,j,hc⟩:= c; change i=b.hi at h; rcases hc with hp|hp <;> subst j <;> subst i; exact hS L (by omega); exact hT L (by omega)
end Nacre
end Tribute
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.Nacre.chair
