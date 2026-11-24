import YM.Massive.Struck.Taper
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Struck
open Acre
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
open Stew Ursell
open Blaze Shells Sands Dust King Lapis Sienna Fare Octave Fount Grove Planned.JetPort Tidings Entr PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit -- Badge from Acre below
open Acre Rails
open Finset Coat Grass NormedSpace
open MeasureTheory Massive.Filament Pith Fibre Fused
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W r e:ℝ} {P T:BudgetPoint} {R:Pixel c N}
variable {I Ω ι β: Type}
namespace Library
variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (Y: Code c N) -- independent shape
set_option quotPrecheck false
namespace Carrier
variable {b:Flavor N} {y A':ℝ}{b':Bool}  (φ:ℝ)(D:ℝ)(A:Library.Arrow N) {ε κ θ η:ℝ}
local notation "ρ₁"=> (1/8:ℝ)
local notation "Q₁"=> Jets.Touch.chip L x
local notation "T₁"=> fan L θ x
-- amplify true Woven at current bank exposure, can pick already-calculated witness.Names
lemma amplitudeE (X:Gem c N I)(u:ℝ)(hx:0≤u)(hq:Bite X P t x r b')(ht:0<t)(H:CrossP X) : Bite (ampE X u) P t (u*x) r b':=by
     let G:=ampE X u; obtain ⟨g,hg,h⟩:= (Bite.law hq).zone; refine ⟨fun i=>u*g i,valued_mult X.addr g hg hx,fun i=>?_⟩
     have hv:= mudloan_pipe (X.addr i).site (X.view i) u (hq.mint X i); have hr:= (h i).byScalar u; rw [Real.norm_of_nonneg hx] at hr; exact ⟨hr,hv.1,fun hi=> puff _ (grip _ (Crisp X H i) u) hr hv ht hi (X.addr i).anchor⟩
lemma rental (m: Flavor N→ℝ) (hp:0<t) : Bite (rentGem (c:=c) m) P t (Real.exp ρ₁*∑ i, priceL m t i) ρ₁ false:=by
    let G:= Pith.rentGem (c:=c) m; refine ⟨priceL m t ∘ Prod.snd,rentPaid c m,fun i=>?_⟩; have hM:Mint false (G.view i) i.1 {i.1}:=⟨mudLoan .., fun _ h=>False.elim (Bool.noConfusion h)⟩; have hr:= moneyL i.2 i.1 (m i.2) P hp; exact ⟨hr,hM.1,fun hi=>puff _ (Crisp G (rentCross c m) i) hr hM hp hi (mem_singleton_self _)⟩ -- h level rite
lemma Bite.raise (G:Gem c N I)(hp:Bite G P t v w b')(h:v ≤ u): Bite G P t u w b':=by obtain ⟨f,hz,hq⟩:=hp; exact ⟨f,fun i=>budget_loosen (hz i) h,hq⟩
lemma Quits.scaleS (X:Rail c N I)(hp:Quits X n v w x y)(z:ℝ)(h:0≤z): Quits (ampK X z) n (z*v) w x y:=by
    have hh:= watt_price X (z:ℂ) hp; rw [Complex.norm_real,Real.norm_of_nonneg h] at hh; exact hh
lemma travelP (u:ℝ)(ht:0<u)(hp : κ= u^2*(ε * A')) : u⁻¹^2*(D*κ)= D*ε*A' ∧ u⁻¹^3*(u*D*κ)=D*ε*A':=by rw [hp]; field_simp; grind
-- rent ceiling C0 geometric Reissue without coupling runtime h.TravelC
abbrev Rental (N:ℕ): ℝ:= Real.exp ρ₁*(Fintype.card (Flavor N):ℝ)*priceP N*6
abbrev lowNeed (L:Side) (x ε D:ℝ):ℝ:= D*ε*Jets.Touch.chip L x
lemma budgetSense (hf: Desk Y P b L x θ)(hp: Fare Y P L x θ (D*κ) (φ*D*κ)) (hm:∀ i,|(fan L θ x)^2*Y.focus i- κ*A.tip i|≤ κ/2)(ht:0<φ)(hz:0 ≤ κ)(he : κ=φ^2*(ε* Q₁)): let p:=lowNeed L x ε D; let r:= lowNeed L x ε (Rental N); Budget Y P L x θ φ p p p ρ₁ r:=by
   intro p r; obtain ⟨hP,hM⟩:= travelP D φ ht he
   have hw : Library.wage Y (fan L θ x) ≤ Rental N*κ:=by
       have hh(i): T₁^2*‖Y.focus i‖≤ 6*κ:= by
          have ht(i): |κ*A.tip i|≤ κ*5:= by rw [abs_mul, abs_of_nonneg hz]; exact mul_le_mul_of_nonneg_left (A.bound i) hz
          rw [Real.norm_eq_abs, show T₁^2* |Y.focus i| =|(fan L θ x)^2*Y.focus i-κ*A.tip i+κ*A.tip i| from (by rw [sub_add_cancel,abs_mul,abs_of_nonneg (sq_nonneg T₁)])]; linarith only [(abs_add_le ..).trans (add_le_add (hm i) (ht i)), hz] -- placeholder
       unfold Library.wage Rental; let t:=priceP N; calc
         _ ≤ Real.exp ρ₁ * ((∑ i:Flavor N,t*(6*κ))) := by refine mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>?_)) (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_left (hh i) priceP_nonneg
         _ =_:= by simp only [sum_const,card_univ, nsmul_eq_mul]; unfold t; ring
   change φ⁻¹^2*_ = p at hP; change φ⁻¹^3*_ = p at hM
   refine ⟨hP ▸ ?_, hM ▸ ?_,?_,hP ▸ ?_, hM ▸?_⟩ -- orientation echanging D*ε*.. lhs inside goal defeq p might not work
   · exact amplitudeE _ _ (by positivity) hp.low (fan_pos ..) hf.arg
   · exact amplitudeE _ _ (by positivity) hp.high (fan_pos ..) hf.eve
   · have hg := Bite.raise (P:=P) Y.canonical (rental Y.focus (fan_pos L θ x)) hw
     have hv : φ⁻¹^2*(Rental N*κ)=r:= (travelP (Rental N) φ ht he).1
     exact hv ▸ (amplitudeE Y.canonical _ (by positivity) hg (fan_pos ..) (rentCross c Y.focus)) -- need fix msg
   · exact Quits.scaleS _ hp.near _ (by positivity)
   exact Quits.scaleS _ hp.top _ (by positivity)
-- Startup θ law.P.Current
-- Choose ε after T and P-count fixed but before L: μ rent constants independent L.
abbrev Enough (N k:ℕ)(D ε:ℝ):Prop:=
        Real.exp (-(ρ₁/2))*(1+(penny k*(2*(Rental N*ε))+2*(penny k*(2*(D*ε)))))≤ 1
lemma authorize (N k:ℕ)(D:ℝ): ∃ ε:ℝ, 0<ε∧ Enough N k D ε:=by
    let T:=Real.exp (-(ρ₁/2)); let f (ε:ℝ):= T*(1+(penny k*(2*(Rental N*ε))+2*(penny k*(2*(D*ε)))))
    have h:T<1:=Real.exp_lt_one_iff.mpr (by norm_num); have hf:Tendsto f (𝓝[>] (0:ℝ)) (𝓝 T):=(Continuous.tendsto' (f:=f) (by unfold f; fun_prop) _ _ (by unfold f; ring)).mono_left nhdsWithin_le_nhds; have hp:∀ᶠ x:ℝ in 𝓝[>] (0:ℝ), 0<x:= self_mem_nhdsWithin; obtain ⟨ε,he,hx⟩:=(hp.and (hf.eventually_le_const h)).exists; exact ⟨ε,he,hx⟩
-- after choosing and L. use Warm.Step same ε always per-level
lemma copper (L:Side)(D ε:ℝ)(N k:ℕ)(hx:Enough N k D ε) : ∀ᶠ x:ℝ in atTop, let p:=lowNeed L x ε D; let r:= lowNeed L x ε (Rental N); ∀ P:BudgetPoint,P.order=k→ mild P L p p x r p ∧ modulus P p r:=by
    let p x:= lowNeed L x ε D; let r x:= lowNeed L x ε (Rental N); have hp: Rate su L (-1) p:=(chip_rate L).mul_left (D*ε); have hr: Rate su L (-1) r:=(chip_rate L).mul_left (Rental N*ε)
    let u:= Real.exp (-(ρ₁/2)); have hW:0<u:=Real.exp_pos _; have hz:u<1:=Real.exp_lt_one_iff.mpr (by norm_num); have hY:0<1-u:=sub_pos.mpr hz; let K:=(2:ℝ)^k; have hK:0<K:=by positivity
    filter_upwards [hp.below (by norm_num) (1/8) (by norm_num),hr.below (by norm_num) (1/8) (by norm_num),(hp.mul_left K).below (by norm_num) (1/4) (by norm_num),(hr.mul_left K).below (by norm_num) (1/4) (by norm_num),( (hp.add hp).mul_left u).below (by norm_num) (1-u) hY, Delay.shift_pos su L] with x hA hB h₀ h₁ hₓ hΦ
    intro p' r' P hP; refine ⟨⟨?_,?_⟩, fun j h=>?_⟩
    · let Q:=Jets.Touch.chip L x; have h:=healthy_chip hΦ; unfold massPay snack; rw [hP]; have hz₁: p'= D*ε*Q:=rfl; have hz₂:r'=Rental N*ε*Q:=rfl; rw [hz₁,hz₂]; unfold Enough at hx; nlinarith only [mul_le_mul_of_nonneg_right hx h.le]
    · have h: u*(p'+p')≤1-u:=(le_abs_self _).trans hₓ; unfold u at h; linarith only [h]
    rcases h with h|h; · exact ⟨h.trans ((le_abs_self (p x)).trans hA), hP.symm ▸ (mul_le_mul_of_nonneg_left h hK.le).trans ((le_abs_self (K*p x)).trans h₀)⟩
    exact ⟨h.trans ((le_abs_self (r x)).trans hB),hP.symm ▸ (mul_le_mul_of_nonneg_left h hK.le).trans ((le_abs_self (K*r x)).trans h₁)⟩
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.budgetSense
#print axioms YM.QCD.Struck.Library.Carrier.copper
