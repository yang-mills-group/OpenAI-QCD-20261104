import YM.QCD.Fall.Fling
import YM.Push.BETA_TRANSPORT.Noise
import YM.QCD.Fall.Clan
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
namespace Rails
open Finset Coat Grass
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q G N}
lemma atOrigin (p:Clip)(V:PathData su) (c:Side): secondTerm p V (1:Grid c)=0:=by
   unfold secondTerm; unfold Patch.average Precision.quadratic; have hh(x: Face (Per c)): faceValue (1:Grid c) x=1 :=by simp [faceValue,square,travel,Step.read]
   have hp(x: Face ℤ): faceValue (1:CoverConfig su) x=1 :=by simp [faceValue,square,travel,Step.read]
   have he (a:Slot)(i:Site c): Slot.eval a (expandAt i (1:Grid c))=0:=by apply norm_eq_zero.mp; rw [Slot.eval,su.norm_adjoint,show expandAt i (1:Grid c)=1 from rfl,hp,su.curvature_unit,norm_zero]
   simp [pull_one_field,hh,PathData.ell, PathData.ellTerms,Slot.atSite,he]
open Sector
lemma quotaLow (Y₀: StepData c f)(Ñ:ChartRatio su)(F':Forest Y₀.ratio) (h:LocalRatio Ñ) (hp:0<β) : ∃ C:ℝ, 0<C∧ ∀ u:ℝ, β ≤ u → u ≤ v → C ≤ Fare.solar F' Ñ u:=by
   by_cases hL:β ≤v
   · let S:=Set.Icc β v
     have hf:ContinuousOn (Fare.solar F' Ñ) S:=by
        intro i hi; unfold Fare.solar Sector.prefactor gStep
        have ht:ContinuousAt (fun t=> (Y₀.penaltyZ t su)⁻¹) i:=(Push.BetaTransport.penaltyZ_cont Y₀ su|>.continuousAt).inv₀ (Y₀.penaltyZ_pos i).ne'; have hp:ContinuousAt (fun t=> (Real.sqrt t)⁻¹) i:= ContinuousAt.inv₀ (by fun_prop) (Real.sqrt_pos.2 (hp.trans_le hi.1)).ne'; exact ContinuousAt.continuousWithinAt (by fun_prop)
     obtain ⟨w,hw,hz⟩:= isCompact_Icc.exists_isMinOn (show S.Nonempty from ⟨β,le_rfl,hL⟩) hf; exact ⟨_,sun _ _ _ (hp.trans_le hw.1) h,fun _ hb hx=>hz ⟨hb,hx⟩⟩
   exact ⟨1,one_pos,fun i hb hx=> False.elim (hL (hb.trans hx))⟩
-- no pay.R row viability extra. 
lemma ledger (B:Badge P₀ τ R P o χ T U b x r β μ z)(he:P.threshold=Pressure.temp x) (F': Tree.Forest (S.visit K h).ratio) : let X:= Greenbelt.prism T x χ o.K (1:Grid c) F'; let p:=trimP T R (lowK S.L x T'.top.supportExponent) β 0
     β>0→ Fare.solar F' Q.table β*Real.exp (-(Fintype.card (Tubular f su)*o.ample)/2) ≤ Matter.overhead X p Q.table:=by
    intro X V₀ hr; have ht:flags P.threshold X.V=∅:=UVNext.CouplingReset.flags_one ..; have hv:X.manifest:=by unfold Coat.manifest; change ∅=RG.flags (Pressure.temp x) (1:Grid c); rw [← he]; exact ht.symm
    have hp: Matter.overhead X V₀ Q.table=Matter.overhead X (Pane.virgin T R β) Q.table:=rfl
    rw [hp, Fare.overdraft F' T β R P X Q.table he ht, show secondTerm T.low T.down X.V= _ from atOrigin ..,mul_zero,zero_sub]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by linarith only [Fare.chairs F' T X β R B.virginP hv (show X.width=o.K from rfl)])) (sun F' Q.table β hr Q.table_exists).le
end Rails
end YM.QCD.Acre
