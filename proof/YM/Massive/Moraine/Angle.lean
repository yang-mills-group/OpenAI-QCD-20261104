import YM.Massive.Struck.Charts
import YM.Massive.Cairn.Backdrop
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
namespace Stratum.Spire
open Rails
/-!
# Mixed-stride analytic mass offset angles

In design, need SAME base marker in every history even in the later pressure
selection. But the marker costs from Filament on a step are calculated in a chart whose
radius is *not stationary* across the seams. We put registers `dial` on the
uses of those charts so as to enable keeping `α` (absolute marker) constant.
This file provides the primitive mechanism, not yet utilizing the sources at
this budget.
-/
namespace Moraine
open Fibre Struck Library Massive.Filament Client Terrace AtlasH
set_option quotPrecheck false
variable {Y':Side}{t y ε s t':ℝ}
section
variable (hscale:run L x=run Y' y)
include hscale
lemma diary (Z: Code c N)(F:Flavor N)(hw:Desk Z P F L x η): Desk Z P F Y' y η := {hw with base:=germSet hscale F Z.master hw.base}
lemma annual (Z: Code c N)(hw: Library.Fare Z P L x η A M): Library.Fare Z P Y' y η A M:=by
   obtain ⟨hp,hv,hc,hT⟩:=hw; rw [pitch_at hscale] at hp hv; rw [pitch_at hscale,flash hscale] at hc hT; exact ⟨hp,hv,hc,hT⟩
omit hscale in
lemma inflate (F:ℂ→Pixel c N)(s):Library.grow t (Library.grow s F)= Library.grow (s*t) F:=by
   funext i; unfold Library.grow; rw [Complex.ofReal_mul,mul_assoc]
local notation "H₀"=> Rotary.chartR
omit hscale in
lemma grew (F:ℂ→Pixel c N)(hw:t*(H₀ x)=s*(H₀ y)): Library.grow (H₀ x) (Library.grow t F)= Library.grow (H₀ y) (Library.grow s F):=by rw [inflate,inflate,hw]
omit hscale in
lemma wider (F:ℂ→Pixel c N)(hw:t*(Rotary.chartR x)=s*(Rotary.chartR y))(Z:Code c N)(G:Grid c→ℝ)(H:St c)(ht:Library.Wing (grow t F) Z P x G H): Library.Wing (grow s F) Z P y G H:=by
   obtain ⟨C,Hc,hX,h1,h2,h3⟩:= ht.launch; simp only [grow,mul_zero] at h2; rw [grew F hw] at h3;
   exact ⟨C,Hc,hX,h1,(by simpa [grow] using h2),h3⟩
lemma ident (F:ℂ→Pixel c N)(e:Flavor N) (hw:t*(Rotary.chartR x)=s*(Rotary.chartR y)): Library.Sens (Rotary.chartR x) (fan L η x) e (grow t F)=Library.Sens (Rotary.chartR y) (fan Y' η y) e (grow s F):=by unfold Library.Sens; rw [pitch_at hscale,grew F hw]
-- Avoid notation/lock ambiguity
lemma porter (F:ℂ→Pixel c N)(hw:t*(Rotary.chartR x)=s*(Rotary.chartR y))(A:Library.Arrow N)(b:Flavor N)(K:Grid c→ℝ)(U:St c)(ht:Ladder (grow t F) P L A b η x w D ε K U): Ladder (grow s F) P Y' A b η y w D ε K U:=by
   obtain ⟨Z,hz,hY,hp,φ,hφ,hV,hA⟩:=ht.owns -- rename below
   refine ⟨ht.upS,fun i=> (ident hscale F _ hw).symm.trans (ht.shape i),Z,diary hscale Z b hz, wider F hw Z K U hY,(fun i=> (by rw [← pitch_at hscale]; exact hp i)),φ,hφ, (by rw [← chip_at hscale]; exact hV),annual hscale _ hA⟩
end
variable {R:Rock 4}{F₀:Flavor N}{χ:Chi} (P₀: Client 4 R N F₀ χ) (Y:AtlasH R (passportM 4 P₀.good) P₀.guide.table)

-- Consume in step i at χ(fine offset input)*dial i.
def dial (Y:AtlasH R (passportM 4 P₀.good) P₀.guide.table)(x:ℝ):ℕ→ℝ
  | 0=>1
  | i+1=> dial Y x i * (Rotary.chartR (Y.scale x i)) / Rotary.chartR (precursor P₀ Y x (i+1))

lemma rayMono (hx: 0< x)(h:x≤y): Rotary.chartR x ≤ Rotary.chartR y:= by unfold Rotary.chartR; exact sub_le_sub_left (inv_anti₀ hx h) _
lemma precursor_mono_rev (x:ℝ) (i:ℕ) : precursor P₀ Y x (i+1) ≤ Y.scale x i:=by
   unfold precursor; rw [←second]; unfold Client.fallback run betaF
   have hh : Real.log ((Y.length i).val:ℝ)≤ Real.log ((Y.length (i+1)).val:ℝ):= Real.log_le_log (Bloch.side_pos _) (by exact_mod_cast Y.slopes i)
   linarith only [mul_le_mul_of_nonneg_left hh (Gauge.slopeConstant_pos simple).le]
variable (he:∀ i,1 ≤ precursor P₀ Y x i)
include he
lemma scaleRay (i:ℕ): 2<Rotary.chartR (precursor P₀ Y x i):= (Rotary.spring (Y.length i) ((show 1 < (Y.length i).val from (by have h:= (Y.path i).coarse; exact lt_of_lt_of_le (by norm_num) h))) _ (he i)).1
lemma scalePay (i:ℕ): 1≤ dial P₀ Y x i:=by
   induction i with
   | zero=>exact le_rfl
   | succ i ih=>
       rw [dial]; apply (le_div_iff₀ ((by linarith only [scaleRay P₀ Y he (i+1)]))).mpr; rw [one_mul]; have ht:= rayMono (zero_lt_one.trans_le (he (i+1))) (precursor_mono_rev P₀ Y x i); exact ht.trans (le_mul_of_one_le_left ((by linarith only [scaleRay P₀ Y he (i+1)] : 0 ≤ Rotary.chartR (precursor P₀ Y x (i+1))).trans ht) ih)
lemma scaleRay_eq (i:ℕ): dial P₀ Y x i * Rotary.chartR (run (Y.length i) (precursor P₀ Y x i)) = dial P₀ Y x (i+1) * Rotary.chartR (precursor P₀ Y x (i+1)):=by
   rw [season,dial, div_mul_cancel₀]; exact ne_of_gt (by linarith only [scaleRay P₀ Y he (i+1)])
end Moraine
end Stratum.Spire
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.Spire.Moraine.porter
#print axioms YM.QCD.Acre.Stratum.Spire.Moraine.scalePay
