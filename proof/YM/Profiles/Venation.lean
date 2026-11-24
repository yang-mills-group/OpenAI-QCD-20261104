import YM.Profiles.Polar
import YM.Profiles.Holler
import YM.VStages.FullRun
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
-- pay any supplementary gate plus D masses from commitments. Startup tolerance funding paid at time >=, applied during actual trajectory. Expose all post schedule for simultaneous rank purchases from Source kernels. Geometry beta.beta.min large; exposure constants paid before L.
open Tribute Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp
-- default schedule.Sc purchase
namespace Blazar
open Lobby.LifeT Lobby Counter Counter.Economies
variable (Θ:Massive.SourceRead.TaperHol){Vb:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Vb)(i0:ℕ)(d:ℕ) (ξ:Fluke Θ Uv d)(Ξ:PreLoan Θ Uv i0 P₀ d ξ)
set_option quotPrecheck false
noncomputable abbrev bloom (b:ChangeQ):ℝ:=2*tabC Θ Uv d ξ b (Ξ.M b)
local notation "Bp"=>bloom P₀ Θ Uv i0 d ξ Ξ
lemma bigT (b:ChangeQ):1 ≤ Bp b:=one_le_mul_of_one_le_of_one_le (by norm_num) (tab_h ..)
local notation "Q"=> A.measure
local notation "N₁"=>A.spacing
local notation "wΓ"=>dimmer
noncomputable def ℓγ (b:ChangeQ):ℝ:=((b.lo:ℝ)+1)⁻¹
structure Wins (b:ChangeQ)(L:Side) : Prop where
    high : Real.log (bloom P₀ Θ Uv i0 d ξ Ξ b)≤ ℓγ b*Real.log (L.val:ℝ)
lemma fly (b:ChangeQ) :∃ i:ℕ, ∀ L:Side,i ≤ L.val → Wins P₀ Θ Uv i0 d ξ Ξ b L:=by
    have ht:Tendsto (fun i:ℕ=> ℓγ b*Real.log (i:ℝ)) atTop atTop:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by unfold ℓγ; positivity); obtain ⟨i,h⟩:= eventually_atTop.mp (ht.eventually_ge_atTop (Real.log (Bp b))); exact ⟨i,fun L hx=>⟨h _ hx⟩⟩
variable (Z:ℕ→Massive.UV.Label d)
-- η spending proof.L. Lower contract propagates only forecasts. Spectrum.E want local.Pr heights.R_l bound.
local notation "φ"=> FWealth P₀ A Θ Uv d ξ (Pt:=Pt) (x:=x) -- use d
variable (ε:ℝ)
local notation "ψ" t=>A.node t
noncomputable abbrev gross (i:ℕ):ℝ:=∑ j ∈ range i,Real.log (bloom P₀ Θ Uv i0 d ξ Ξ (A.node j))
local notation "Gq"=>gross P₀ A Θ Uv i0 d ξ Ξ
local notation "Fs" i:arg=>Kit.slope (A.spacing i)
local notation "PC"=> (d:ℝ)/2
variable {T:ℝ}
lemma gross_l (i:ℕ):0≤ Gq i:=sum_nonneg fun i _=>Real.log_nonneg (bigT ..)
lemma runway (i:ℕ): Fs i ^ d=Real.exp (- ((d:ℝ)/2)* Real.log ((A.spacing i).val:ℝ)):=by
    unfold Kit.slope; let L:ℝ:=(A.spacing i).val; have h:0<L:=by unfold L; positivity
    change (Real.sqrt L)⁻¹^d=Real.exp (- ((d:ℝ)/2)* Real.log L); rw [← Real.exp_log (show 0<(Real.sqrt L)⁻¹ from by positivity),← Real.exp_nat_mul, Real.log_inv,Real.log_sqrt h.le]; congr 1; ring
variable (m i :ℕ) -- m base i cap
lemma voyage_l (hZ:0 ≤ T)(hm:m ≤ i)(h:φ m (Z m) ≤T) (hF:∀ j:ℕ,m ≤ j→j < i→ (Kit.slope (A.spacing j))^d* FWealth P₀ A Θ Uv d ξ (Pt:=Pt) (x:=x) (j+1) (Z (j+1)) ≤ (bloom P₀ Θ Uv i0 d ξ Ξ (A.node j)) * FWealth P₀ A Θ Uv d ξ (Pt:=Pt) (x:=x) j (Z j)) : φ i (Z i) ≤ T * Real.exp (((d:ℝ)/2)*A.measure i+Gq i):=by
   induction hm with
   | refl=> exact h.trans (le_mul_of_one_le_right hZ (Real.one_le_exp (add_nonneg (mul_nonneg (by positivity) (A.measure_nn _)) (gross_l ..))))
   | @step j hj ih=>
       have h1:=ih (fun i hi hp=>hF i hi (by omega)); let t:= Gq j; let f:=Fs j; have hf:0<f:= Kit.slope_pos _; apply le_of_mul_le_mul_left _ (pow_pos hf d); apply (hF _ hj (by omega)).trans; let b:= Bp (ψ j); apply le_trans (mul_le_mul_of_nonneg_left h1 (show 0≤b from zero_le_one.trans (bigT ..))) (le_of_eq ?_); change b*_=Fs j^d*(T*_); rw [runway,show Gq (j+1) = t + Real.log b from Finset.sum_range_succ _ _, Track.era]; let L:=Real.log ((A.spacing j).val:ℝ); let v:= PC*Q j+t; change b*(T*Real.exp v) = Real.exp (- PC*L)*(T*Real.exp _); rw [show PC*(Q j+L) + (t+Real.log b)= v + Real.log b + PC*L from by unfold v; ring,mul_left_comm (Real.exp _), ← Real.exp_add,show -PC*L+(v+Real.log b+PC*L)=v+Real.log b from by ring,Real.exp_add v (Real.log b),Real.exp_log (zero_lt_one.trans_le (show 1≤b from bigT ..))]; ring
-- log.C sums dominated any epsilon.P carrying fixed trajectory
variable (he:0< ε)(hw:∀ᶠ m in atTop, Wins P₀ Θ Uv i0 d ξ Ξ (A.node m) (A.spacing m))
include he hw
lemma ahead :∀ᶠ i:ℕ in atTop, Gq i ≤ ε*A.measure i:=by
    have hX: Tendsto (fun i:ℕ=>ℓγ (A.node i)) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (1:ℝ) (tendsto_natCast_atTop_atTop.comp A.free))
    let f:=ε/2; have hf:0<f:=half_pos he; obtain ⟨n,hp⟩:= eventually_atTop.mp ((hX.eventually_le_const hf).and hw)
    have h(i:ℕ)(hk:n ≤ i): Gq i ≤ Gq n + f * Q i:=by
         induction hk with
         | refl=>exact le_add_of_nonneg_right (mul_nonneg hf.le (A.measure_nn _))
         | @step i hi ih=>
            let s:=Real.log ((A.spacing i).val:ℝ); have hS0:0 ≤ s:= by unfold s; exact Real.log_nonneg ((show 1 ≤ (2:ℝ) by norm_num).trans (A.per_len _))
            have hC:Real.log (Bp (ψ i)) ≤ f*s:= (hp _ hi).2.high.trans (mul_le_mul_of_nonneg_right (hp _ hi).1 hS0); rw [show Gq (i+1)=Gq i+Real.log (Bp (ψ i)) from sum_range_succ _ _,Track.era]; nlinarith only [ih,hC]
    filter_upwards [eventually_ge_atTop n, A.outlay (Gq n) 0 _ hf] with i hi hz; have h':= h i hi; change Gq _ ≤ _; unfold f at *; linarith only [h',hz]
omit he hw
-- money up.Agenda ephemeral scales.Leg.Pl.Price. Bound valuation inverse power along poses, given proof.Mark.Root Γ.
variable (hX:∀ i:ℕ,Counter.Cave (A.spacing i) (clockQ P₀ A x i) θ)
local notation "φh"=> salary P₀ A (x:=x)
include he hX
lemma lunar:∀ᶠ i:ℕ in atTop, (φh i)⁻¹ ≤ Real.exp (ε*Q i):=by
    let e:= ε/4; have he': 0<e:=by unfold e; positivity
    filter_upwards [Counter.Economies.futureBudget (x:=x) P₀ A e he'] with i h; have hx:= (hX i).shape.2.2; rw [show betaF _ _ _=A.scale x i from (augmented P₀ A i x)] at hx; apply hx.trans; rw [Real.rpow_two]; let p:= Real.sqrt (A.scale x i); have hP: p ≤ e* Q i:=Real.sqrt_eq_rpow ..|>.trans_le h
    have hD:0 < A.scale x i:= lt_of_lt_of_le (by norm_num) ((show 2 ≤ A.scale x i from (augmented P₀ A i x) ▸ (hX i).high)); have hg:0 < p:= Real.sqrt_pos.mpr hD; have hS:p^2=A.scale x i:= Real.sq_sqrt hD.le
    rw [← Real.exp_log (show 0<A.scale x i^2 from by positivity)]; apply Real.exp_monotone; rw [Real.log_pow, ← hS,Real.log_pow]; unfold e at hP; push_cast; nlinarith only [hP,Real.log_le_sub_one_of_pos hg,hP]
local notation "ΞT"=> Lobby.LifeT.luster P₀ A Θ Uv d ξ x Pt
-- parameter ξ may mismatch d. remove
end Blazar
end Melt
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Blazar.lunar
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.Melt.Blazar.voyage_l
