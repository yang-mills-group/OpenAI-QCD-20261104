import YM.Affina.Donas
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
local notation "Y₁" x:arg=> fan L θ x
local notation "Y₂" x:arg=> fiery su x L
local notation "tt" x:arg=> run L x
-- Develop inverse ratios only because scale λ uses reverse. speedy diff from log
lemma lgrate (s:ℝ) (hS:0 ≤ s):∀ᶠ x in atTop, |Real.log (x+s)-Real.log x| ≤ s/x ∧ |Real.log (Real.log (x+s))^2-Real.log (Real.log x)^2|≤2*(s/x) :=by
       let g:=fun x:ℝ=> Real.log x^2; let f:=fun x:ℝ=>2*Real.log x/x
       have hf (x:ℝ)(hx:x∈ Set.Ici (1:ℝ)):HasDerivWithinAt g (f x) (Set.Ici 1) x:=by
           change 1≤x at hx
           simpa [f,g,div_eq_mul_inv] using! (((Real.hasDerivAt_log (show x ≠ 0 by linarith)).pow 2).hasDerivWithinAt (s := Set.Ici 1))
       have hb(x:ℝ)(hx:x∈Set.Ici (1:ℝ)):‖f x‖≤2:=by
           change 1≤x at hx; have h:0 < x:=zero_lt_one.trans_le hx
           unfold f; rw [Real.norm_of_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hx)) h.le),div_le_iff₀ h]; linarith only [Real.log_le_sub_one_of_pos h]
       filter_upwards [eventually_gt_atTop 0,Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hv
       have hp:x≤x+s:=le_add_of_nonneg_right hS; have hz:0 < x+s:=hx.trans_le hp; have hr: Real.log x ≤ Real.log (x+s):=Real.log_le_log hx hp
       have h:0 <(x+s)/x:= div_pos hz hx; have ht : |Real.log (x+s)-Real.log x| ≤ s/x:=by
            rw [abs_of_nonneg (sub_nonneg.mpr hr), ← Real.log_div hz.ne' hx.ne']; exact (Real.log_le_sub_one_of_pos h).trans_eq (by field_simp; ring)
       exact ⟨ht, ((convex_Ici (𝕜:=ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hf hb hv (hv.trans hr)).trans (mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤2 from by norm_num))⟩
lemma log_to_rate (f:ℝ→ℝ) (C:ℝ) (h:∀ᶠ x in atTop,0 < f x ∧ |Real.log (f x)|≤ C/(run L x)): Rate su L (-1) (fun x=> f x-1):=by
      have hp:Rate su L (-1) (fun x=>(run L x)⁻¹):= Rate.power.congr (Eventually.of_forall fun i=> (Real.rpow_neg_one _).symm)
      let F:=fun x=> C*(run L x)⁻¹; have ht:Rate su L (-1) F:= hp.mul_left C
      refine (ht.mul_left (Real.exp 1)).compare ?_; filter_upwards [ht.below (by norm_num) _ zero_lt_one,h] with x hx hf
      obtain ⟨h,hF⟩:=hf; rw [div_eq_mul_inv] at hF; let K:= Set.Iic (1:ℝ) 
      let t:= Real.log (f x); have hT:t≤ 1:= (le_abs_self _).trans (hF.trans ((le_abs_self (F x)).trans hx)); have hS: ‖Real.exp t-Real.exp 0‖ ≤ Real.exp 1 * ‖t-0‖ := (convex_Iic (𝕜:=ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le (fun x _=> (Real.hasDerivAt_exp x).hasDerivWithinAt) (fun x hx=>by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_monotone hx) (show (0:ℝ)∈ K from (show (0:ℝ) ≤ 1 from zero_le_one)) hT
      rw[ Real.exp_zero,Real.norm_eq_abs, Real.norm_eq_abs, show Real.exp t=f x from Real.exp_log h, sub_zero] at hS; exact hS.trans ((mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le).trans (le_abs_self _))
lemma welcomeQ : Rate su L (-1) (fun x=> Y₁ x/ Y₁ (tt x)-1) ∧ Rate su L (-1) (fun x=> Y₂ x/Y₂ (tt x)-1):=by
       let C :ℝ:=su.slopeConstant*Real.log L.val; have hC:0 ≤ C := Work.E04.shift_nonneg su L
       have h := (Work.E09.betaF_growth su L).eventually (lgrate C hC)
       let V:=fan L θ; let u:=fun x=> fiery su x L; constructor
       · refine log_to_rate L (fun x=>V x/V (tt x)) (2*|θ| *C) ?_; filter_upwards [h] with x hx
         let t:=tt x; let f:= fun x=> Real.log (Real.log x)^2
         have hv (x:ℝ): Real.log (V x)= θ*f (run L x):=by change Real.log ((Real.exp _)^θ)=_; rw[Real.log_rpow (Real.exp_pos _), Real.log_exp]
         have hp:run L t=t+C:=rfl
         refine ⟨div_pos (fan_pos ..) (fan_pos ..),?_⟩; change |Real.log (V x/V t)| ≤2*_ * C/t; rw [Real.log_div (fan_pos ..|>.ne') (fan_pos ..|>.ne'),hv,hv,hp,abs_sub_comm,←mul_sub,abs_mul]; exact (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)).trans_eq (by change |θ| *(2*(C/t))=_; ring)
       refine log_to_rate L (fun x=>u x/u (tt x)) (3*C) ?_; filter_upwards [h, Delay.shift_pos su L] with x hx hp
       let T:=tt x; let s:=T+C; have hS:run L T=s:=rfl; have hT:0 < s:=add_pos_of_pos_of_nonneg hp hC
       let g:=fun x=> Real.log (Real.log x)^2; have h (x:ℝ)(hx:0<x): 0<Pressure.temp x ∧ Real.log (Pressure.temp x)= g x-Real.log x/2:=by
           refine ⟨Work.E09.temp_pos hx,?_⟩; unfold g Pressure.temp; rw [Real.log_mul (by positivity) (by positivity),Real.log_inv, Real.log_sqrt hx.le,Real.log_exp]; ring
       refine ⟨div_pos (h T hp).1 (h s hT).1,?_⟩; change |Real.log (Pressure.temp T / Pressure.temp s)|≤ 3*C/T; rw[Real.log_div (h T hp).1.ne' (h s hT).1.ne',(h T hp).2,(h s hT).2]; rcases hx with ⟨hh,he⟩; change |g s-g T|≤ 2*(C/T) at he; change |Real.log s-Real.log T|≤ C/T at hh; obtain ⟨h₁,h₂⟩:= abs_le.mp hh; obtain ⟨h₃,h₄⟩:=abs_le.mp he; have hr:0≤C/T:= div_nonneg hC hp.le; rw[mul_div_assoc]; refine abs_le.mpr ⟨?_,?_⟩ <;>linarith only [h₁,h₂,h₃,h₄,hr]
end MintV
end Suburb
end Stratum.MarchQ
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Stratum.MarchQ.Suburb.MintV.welcomeQ
