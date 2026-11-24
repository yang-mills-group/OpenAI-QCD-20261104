import YM.Infer.Packet
import YM.Differ.Covenant
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
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised.Sieve Orientation
open QCD
variable (p: Massive.UV.Label Gn)(W:Gallery.Knot p)(h:Requisite Θ p W)(ε:ℝ)
open Rails.Reference.Sharp Suburb.Melt Conductor Conductor.Quant
open MassiveQCD.Sample MassiveQCD.Sample.GreenCap.Works
variable (Φ:Capsule Θ Uv Gn f p W ε)(E: RiseBook Y)(b:ChangeQ)(L:Side)
local notation "α" x:arg => Pressure.fiery su x L -- Pressure ambiguity
local notation "Fc" x:arg => Φ.J*((Pressure.fiery su x L^W.g)⁻¹+(Pressure.fiery su x L^W.m)⁻¹)
structure FilmW (x V:ℝ) : Prop where
    pace : Pressure.fiery su x L < Φ.γ
    scale : 0 < run L x -- positivity
    threshold : (fan L θ x)^2/(Pressure.fiery su x L*(run L x/2)) ≤ Φ.Δ
    boxP : roofK L θ (halo₀ Y L b) x+ 5*Quant.crest L x (E.eps b) (1/4) ≤ Φ.Δ
    paid : Φ.M ≤ radiusB (run L x)
    labor : ∃ Z:ℝ,0 ≤ Z ∧ (Fc x+ 2*(Z*Φ.D))*Real.exp (4*81) ≤ Φ.D*V ∧ ∀ (c:Side)(P:BudgetPoint), P.threshold=Pressure.fiery su x L →∀ (y:Massive.UV.Label Gn)(F:Grid c)(o:Cover), Creek.load (fun _=>fan L θ x) (Orientation.graphs Gn Uv o y F)≤ Z*wealth y.val P.threshold (fan L θ x)
#check FilmW
lemma berth :∃ (π:ℝ→ℝ)(a:ℝ),Rate su L a π ∧∀ᶠ x in atTop,0 ≤π x ∧∀ Z≥π x,FilmW Θ Uv Gn Y f p W ε Φ E b L x Z:=by
    obtain ⟨K,t,hR,h⟩:= ballast L Uv Gn θ (Y b).lead
    let i : ℝ→ℝ:=fun x=>Pressure.fiery su x L
    let F:ℝ→ℝ:=fun x=>Fc x
    have hg (n:ℕ): Rate su L (1/2 *n) (fun x=>((i x)^n)⁻¹):=by simp_rw [← inv_pow]; exact (inverse_mist su L).pow n
    let z:=max ((1:ℝ)/2*W.g) (1/2*W.m); have hF:Rate su L z F:= (((hg W.g).weaken (le_max_left ..)).add ((hg W.m).weaken (le_max_right ..))).mul_left Φ.J
    let u:=max z t; let π:ℝ→ℝ:= fun x=>(F x+2*(K x*Φ.D))*Real.exp (4*81)
    have hP:Rate su L u π:= (((hF.weaken (le_max_left ..)).add ((hR.mul_right Φ.D|>.mul_left 2).weaken (le_max_right ..))).mul_right _)
    have hx : Rate su L (-(1/2)) (fun x=>fan L θ x^2/(i x*(run L x/2))):=by
        let T (x:ℝ):ℝ:= (fan L θ x)^2*(i x)⁻¹*(betaF su x L)^(-1:ℝ)*2
        have ha:Rate su L (0*2+1/2+-1) T:= (((Jets.Touch.Seat.ruled (L:=L) (f:=fan L θ) Jets.Touch.Seat.keeps).pow 2 |>.mul (inverse_mist su L)).mul (Rate.power (a:= -1)) |>.mul_right 2)
        norm_num at ha -- suspect transforms T or number
        refine (ha.weaken ?_).congr (Eventually.of_forall fun x=>?_); · norm_num
        unfold T; rw [Real.rpow_neg_one]; simp only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv]; ring -- edit
    have hB:Rate su L (-1) (fun x=> roofK L θ (halo₀ Y L b) x+5*Quant.crest L x (E.eps b) (1/4)):= (beamsR L θ _).add ((Jets.Touch.chip_rate L).mul_left (E.eps b)|>.mul_left ((1/4)^2) |>.mul_left 5)
    refine ⟨π,u,hP,?_⟩; filter_upwards [hx.below (by norm_num) Φ.Δ Φ.ball.1,hB.below (by norm_num) Φ.Δ Φ.ball.1, (Rate.flame (G:=su) (L:=L)).below (by norm_num) _ (half_pos Φ.age),Delay.shift_pos su L, (YM.Work.E01.radiusB_tendsto.comp (Work.E09.betaF_growth su L)).eventually_ge_atTop Φ.M,h] with x hx hv hQ hb ht hf
    have hh:0<Pressure.fiery su x L:=mul_pos (inv_pos.2 (Real.sqrt_pos.2 hb)) (Delay.monitor_pos ..); have hj: 0≤F x:= mul_nonneg Φ.sun (add_nonneg (by positivity) (by positivity)); have hJ: 0 ≤ π x:=by unfold π; positivity [hf.1,Φ.day]
    refine ⟨hJ, fun V he=> ⟨(le_abs_self ..).trans_lt (hQ.trans_lt (half_lt_self Φ.age)),hb,(le_abs_self ..).trans hx,(le_abs_self ..).trans hv,ht,K x,hf.1,?_,fun c P hp y F o=>hf.2 c P hp o y F⟩⟩; exact he.trans (le_mul_of_one_le_left (hJ.trans he) Φ.day)
end Nacre
end Tribute
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Tribute.Nacre.berth
