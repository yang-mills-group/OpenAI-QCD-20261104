import YM.Topaz.Meter
import YM.Differ.Humming
import YM.Oars.Mother
import YM.Affina.Rem
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
namespace Stratum.MarchQ
open Rails
open ChangeQ Fog.Mist YM.Massive.Stratum
variable {R:BudgetPoint}{χ:Chi}{F₀:Flavor N}{x W0:ℝ}{st ord:ℕ}
variable {P:SheetR K st ord}{J:(i:ℕ)→Plan (rank i)}
namespace Suburb
variable {gate:ChangeQ→ℕ} {μ tol θ:ℝ} (P₀:Metros P J θ F₀ χ)(A:TrackQ (gate:=gate) P₀)
open Spire.Client (Vows fallback ceilingL fall)
open Track Rails
variable (X:∀ i:ℕ,SlotQ P₀ tol A i) {b:ℝ}
open Track Depot
namespace MintV
open Finset Real
open Sapphire Dial
variable (L:Side)(V:Dial n)
lemma massΘ : ∀ᶠ x in atTop,PP L V x 0 ≤distV L (V.ν+1) x:=by filter_upwards [Dial.futureQ L V] with x hx; exact (formerA L V x 0 hx).2.2.2
lemma vintageP : ∀ᶠ x in atTop,vintage L V x 0 ≤ highR L x:=by filter_upwards [massΘ L V,smallerV L (V.ν+1) 1 zero_lt_one] with x hx hh; rw[one_mul] at hh; exact (le_trans (Nat.le_succ _) hx).trans (Nat.cast_le.mp hh)
lemma bootPrice (q:ℝ) : Rate su L 0 (fun x=> q^(vintage L V x 0)):=by
    let u:=max (|q|) 1; have hu: 0<u:=zero_lt_one.trans_le (le_max_right ..); let v:=Real.log u; have hv:0≤v:=Real.log_nonneg (le_max_right ..); refine Rate.compare (w:=fun x=> Real.exp ((distV L (V.ν+1) x :ℝ)*v)) ?_ ?_
    · intro a ha; let d:=a/(1+v); have h₁:0<1+v:=by linarith only [hv]
      have hh:0<d:=div_pos ha h₁; filter_upwards [savingsV L d (V.ν+1) hh,(Work.E09.betaF_growth su L).eventually_ge_atTop 1] with x hx hp
      rw [abs_of_nonneg (Real.exp_nonneg _)]; have hy:0< betaF su x L:=zero_lt_one.trans_le hp; apply (Real.log_le_log_iff (Real.exp_pos _) (Real.rpow_pos_of_pos hy _)).mp; rw [Real.log_exp,Real.log_rpow hy]; let X:=(distV L (V.ν+1) x:ℝ); change X*v ≤ _
      calc
           _ ≤ X*(1+v):= mul_le_mul_of_nonneg_left (by linarith) (by positivity)
           _ ≤ _:= (mul_le_mul_of_nonneg_right hx h₁.le).trans_eq (by unfold d; field_simp) -- indent fix
    filter_upwards [massΘ L V] with x hx
    let N:= vintage L V x 0; have hp:N ≤distV L (V.ν+1) x:=(Nat.le_succ _).trans hx
    change |q^N|≤ _; rw [abs_pow,abs_of_nonneg (by positivity : 0 ≤ Real.exp _)]; apply (pow_le_pow_left₀ (abs_nonneg q) (le_max_left ..) N).trans; exact (pow_le_pow_right₀ (le_max_right (abs q) (1:ℝ)) hp).trans_eq (by unfold v; rw [← Real.log_pow,Real.exp_log (pow_pos hu _)])
noncomputable def skimP (L:Side)(a x:ℝ):ℝ:= (run L x)^a
variable (F G:ℝ→ℝ)
lemma pocketF (A C':ℝ)(s:ℝ)(hp:Rate su L a G)(he:Rate su L s (fun x=>(F x)⁻¹))(hF:∀ᶠ x in atTop,0< F x) :∃ (b d:ℝ)(t:ℝ), Rate su L t (fun x=>(skimP L b x)⁻¹) ∧∀ᶠ x in atTop,0< skimP L d x ∧ 0<skimP L b x ∧ (Dial.rateB L 2 x+Dial.worthA L V x)*skimP L b x≤ skimP L d x ∧ C'*(A*((skimP L d x + skimP L d x)*G x)) ≤ F x :=by
    let d:=(-1:ℝ)-a-s; let b:= d-1; let k:= V.R; have hh: Rate su L 0 (Dial.worthA L V):=by refine (Rate.const 1).compare ?_; filter_upwards with x; have h:= uniformV L x k; unfold Dial.worthA; rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans h)),abs_one]; exact inv_le_one_of_one_le₀ h
    let p:=skimP L; have H (v):Rate su L (-v) (fun x=>(p v x)⁻¹):= Rate.power.congr ((Delay.shift_pos su L).mono fun x hx=>(Real.rpow_neg hx.le _).symm)
    have hd:Rate su L d (p d):= Rate.power
    have hv:= (( (rateMeasure L (2+9)).add hh).mul (show Rate su L b (p b) from Rate.power)).mul (H d); have hm:=((((hd.add hd).mul hp).mul_left A).mul_left C').mul he; refine ⟨b,d,-b,H b,?_⟩
    filter_upwards [hF,Delay.shift_pos su L,hm.below (by unfold d; linarith) 1 zero_lt_one,hv.below (by unfold b; ring_nf; norm_num) 1 zero_lt_one] with x hF hx hh hp; have hk:0<p d x:=Real.rpow_pos_of_pos hx _; refine ⟨hk, Real.rpow_pos_of_pos hx _,(_root_.div_le_one hk).mp ?_,(_root_.div_le_one hF).mp ?_⟩
    · rw[div_eq_mul_inv]; exact (le_abs_self _).trans hp
    rw [div_eq_mul_inv]; exact (le_abs_self _).trans hh
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.pocketF
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.bootPrice
