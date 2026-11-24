import YM.Affina.Donas
import YM.Affina.Rem
import YM.Tinus.WoodR
import YM.Tinus.Nim
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
open MassiveQCD.Sample YM.Intag YM.Intag.Receipt Basal Sail
open Rails.Bank.Hike
set_option quotPrecheck false
variable (L:Side)
local notation "W" x:arg=> (highR L x+1:ℕ)
local notation "Q" x:arg=> (↑(highR L x+1:ℕ):ℝ)
local notation "n1" x:arg=>riseV L x (W x)
local notation "B" x:arg=>highR L (n1 x)
local notation "v" x:arg=> fan L θ (n1 x)
variable (Wχ:ℕ→ℝ)(U S:ℝ)
local notation "G★" x:arg=> Wχ (B x)* (v x)^2
variable (S T E G Mv:ℝ→ℝ)
local notation "Cv" x:arg => W x
variable (αs Vs Wk Kπ Fs Dq WT Ht:ℝ)
local notation "L★" x:arg => Q x
local notation "yδ" m:arg x:arg=>T x +2*((αs+1)*m)
-- e1=eEta=E.M.G mass margin.Trajectory.
local notation "Jδ" m:arg e:arg x:arg =>((S x*Vs+Vs*e*(yδ m x))+(Wk*2*E x)*(yδ m x))
local notation "EΔ" m:arg e:arg x:arg => Q x*(Wk*Kπ*Fs^6*(Jδ m e x)+(Wk*2*E x)*(yδ m x)+E x*m)
variable (hs:Tendsto (fun x=>(↑(highR L x+1:ℕ):ℝ)*S x) atTop (𝓝 0)) (hE:Tendsto (fun x=>(↑(highR L x+1:ℕ):ℝ)*E x) atTop (𝓝 0)) (hM:Tendsto (fun x=> (↑(highR L x+1:ℕ):ℝ)*E x*T x) atTop (𝓝 0))
include hs hE hM
-- easier choose αξ after w.A continuity EVENTUALLY.D small.Effects Label drift E.V.
lemma debitsG (η:ℝ)(hp:0<η)(hv:Ht < WT)(V':ℝ→ℝ)(hV:∀ᶠ x in atTop,0<V' x):∀ᶠ x in atTop,∃ g:ℝ,0<g∧ Jδ WT g x+(EΔ WT g x+Ht) < WT∧ g*(yδ WT x) ≤ V' x ∧ Dq*(EΔ WT g x) ≤ η :=by
     let b:=2*((αs+1)*WT); let Δ:=Wk*Kπ*Fs^6; let J x:=Jδ WT 0 x; let H x:=EΔ WT 0 x; let X x:=Q x; have hJ :Tendsto (fun x=> X x* J x) atTop (𝓝 0):=by
         have h' : Tendsto (fun x=> X x*S x*Vs+ Wk*2*(X x*E x*T x+X x*E x*b)) atTop (𝓝 0):=by simpa only [zero_mul,mul_zero,add_zero] using (hs.mul_const Vs).add ((hM.add (hE.mul_const b)).const_mul (Wk*2))
         apply h'.congr; intro x; unfold J b; ring
     have hJ': Tendsto J atTop (𝓝 0):=by
         have h:Tendsto (fun x=> (X x)⁻¹* (X x*J x)) atTop (𝓝 0):=by simpa only [mul_zero,X,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (opusT L)).mul hJ
         exact h.congr fun x=>by rw [←mul_assoc,inv_mul_cancel₀ (by unfold X; positivity),one_mul]
     have hH: Tendsto H atTop (𝓝 0):=by
         have h: Tendsto (fun x=> Δ*(X x*J x)+Wk*2*(X x*E x*T x+X x*E x*b)+X x*E x*WT) atTop (𝓝 0):=by simpa only [zero_mul,mul_zero,add_zero] using (((hJ.const_mul Δ).add ((hM.add (hE.mul_const b)).const_mul (Wk*2))).add (hE.mul_const WT))
         refine h.congr fun x=>?_ ; unfold H b Δ J X; ring
     let Y x:= J x + (H x+Ht); have hr : Tendsto Y atTop (𝓝 Ht):=by simpa only [zero_add] using hJ'.add (hH.add_const Ht)
     filter_upwards [hV,hr.eventually (gt_mem_nhds hv),(hH.const_mul Dq).eventually (gt_mem_nhds (show Dq*0<η from by simpa only [mul_zero]))] with x hx hv hη; let t(g:ℝ):= (Jδ WT g x)+(EΔ WT g x+Ht); let u(g:ℝ):= Dq*(EΔ WT g x); let f(g:ℝ):= g*(yδ WT x); have hf:f 0<V' x:=by unfold f; simpa only [zero_mul] using hx
     have hb1:t 0 < WT:=hv; have hb2:u 0 < η:=hη
     have heA (y:ℝ→ℝ)(hY:Continuous y) (q:ℝ)(h:y 0<q): ∀ᶠ z:ℝ in 𝓝[>]0,y z <q:= ((hY.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h))
     obtain ⟨g,hg,hK₁,hK₂⟩:= (((show ∀ᶠ x:ℝ in 𝓝[>] (0:ℝ),0<x from self_mem_nhdsWithin).and (heA t (by unfold t; fun_prop) _ hb1)).and ((heA u (by unfold u; fun_prop) _ hb2).and (heA f (by unfold f; fun_prop) _ hf)))|>.exists
     exact ⟨g,hg.1,hg.2,hK₂.le,hK₁.le⟩ -- pattern
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.debitsG
