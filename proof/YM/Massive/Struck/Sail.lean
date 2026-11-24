import YM.Massive.Struck.Parent
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
variable {b:Flavor N}(φ:ℝ) (z s:ℂ)
private lemma Same (G: Gem c N I)(X:Gem c N ι){a:I→ℝ}{d:ι→ℝ}(h:LowFare G P q t u a)(hx:LowFare X P q t r d):LowFare (weave G X) P q t (u+r) (Sum.elim a d):=by
     constructor
     · exact fun i=> budgetFuse _ (h.1 i) (hx.1 i)
     rintro (i|i); exact h.2 i; exact hx.2 i
lemma looser (G:Gem c N I)(α:I→ℝ)(h: LowFare G P q t u α)(hx:u≤v): LowFare G P q t v α:=⟨fun i=>budget_loosen (h.1 i) hx,h.2⟩
def rings (f:Y.master.ι→ℝ)(g: (Site c×Flavor N)→ℝ)(a:Y.A→ℝ)(b:Y.B→ℝ) (P:BudgetPoint): EIndex Y →ℝ:= Sum.elim f (Sum.elim (logBudget P g) (Sum.elim (logBudget P a) (logBudget P b)))
lemma flute (G: Gem c N I)(z s:ℂ)(p:I→Dye)(f:I→ℝ)(hz:‖z‖≤1)(hs:‖s‖≤1)(H:LowFare G P q t v f)(ht:0≤q)(hq:1≤t)(hh:v≤1/8)(hr:2^P.order*v≤1/4):LowFare (solvent G p z s) P q t (penny P.order*(2*v)) (logBudget P f):=logFare _ f (wakingL G f H (fun i=> Struck.pigment (p i) z s) (fun i=>upperPaint (p i) _ _ hz hs)) ht hq hh hr
-- compute help Sec.SMark and Duke.Europe: use LowPrice f.Tag x from Elsa.C.Yawn Booth
abbrev snack (P:BudgetPoint)(q:ℝ):=penny P.order*(2*q)
local notation "C!"=> Jets.Touch.chip L x
local notation "T!"=> fan L ρ x
abbrev modulus (P:BudgetPoint)(p r:ℝ) : Prop := ∀ u:ℝ, u≤p∨u≤r → u≤1/8 ∧ 2^P.order*u≤1/4
-- Bite input seats
structure SeatsE (φ:ℝ) (Y:Code c N)(P:BudgetPoint)(L:Side)(x θ q r p:ℝ)(b:Flavor N)(f:Y.master.ι→ℝ)(g:Site c × Flavor N→ℝ)(h:Y.A→ℝ)(k:Y.B→ℝ):Prop where
    master: LowFare Y.master.P P q (fan L θ x) (Jets.Touch.chip L x) f
    prime : ∀ i,Nonwrapping (Y.master.P.addr i).support (Y.master.P.addr i).site → Dust.Feast P (Y.master.P.addr i).support (Y.master.P.addr i).site b (Y.master.P.view i) (fan L θ x) (f i)
    cool : LowFare (ampE Y.low (φ⁻¹^2)) P q (fan L θ x) p h
    heat : LowFare (ampE Y.high (φ⁻¹^3)) P q (fan L θ x) p k
    rent : LowFare (ampE Y.canonical (φ⁻¹^2)) P q (fan L θ x) r g
abbrev massPay (P:BudgetPoint)(L:Side)(x r p:ℝ):ℝ:= Jets.Touch.chip L x+(snack P r+(snack P p+snack P p))
variable (f:Y.master.ι→ℝ)(g:Site c×Flavor N→ℝ)(t:Y.A→ℝ)(k:Y.B→ℝ)
lemma sails (hp:SeatsE φ Y P L x ρ q r p b f g t k)(h:modulus P p r)(hz:‖z‖≤1)(hs:‖s‖≤1)(he:0≤q)(ht:1≤ T!): LowFare (PackageE Y φ z s) P q T! (massPay P L x r p) (rings Y f g t k P):=by
    obtain ⟨r₀,r₁⟩:=h _ (Or.inr le_rfl); obtain ⟨p₀,p₁⟩:= h _ (Or.inl le_rfl)
    exact Same _ _ hp.master (Same _ _ (flute _ z s _ g hz hs hp.rent he ht r₀ r₁) (Same _ _ (flute _ z s _ t hz hs hp.cool he ht p₀ p₁) (flute _ z s _ k hz hs hp.heat he ht p₀ p₁)))
-- want LowFare expanded for parts too. caller flute.G.KE
local notation "q₁"=> (1/8:ℝ)
lemma table (hp:Budget Y P L x ρ φ ζ q p q₁ r) (hr: P.B=highR L x)(hd:Desk Y P b L x ρ): ∃ f g t k, SeatsE φ Y P L x ρ q₁ r p b f g t k:=by
    obtain ⟨f,g,hc,hf⟩:=hd.base
    obtain ⟨A,hA,hL⟩:=hp.low.law.zone; obtain ⟨H,hH,hP⟩:=hp.high.law.zone; obtain ⟨X,hX,hN⟩:=hp.rent.law.zone
    exact ⟨f,X,A,H,⟨hr.symm ▸ hc.fillP.χ,fun i=>(hf i).1⟩,fun i=>(hf i).2,⟨hA,hL⟩,⟨hH,hP⟩,⟨hX,hN⟩⟩
-- exponent gap receipt. use number of sites.cover true ≥1
lemma eroded (X:Gem c N I)(f:I→ℝ)(hX:LowFare X P q₁ u v f): LowFare X P (q₁/2) u (Real.exp (-(q₁/2))*v) f:=by
     let e:=q₁/2; obtain ⟨h,hp⟩:=hX; refine ⟨fun x=> budget_mono (budget_scale (Real.exp_pos (-e)).le (h x)) (fun i=> ?_) (fun i=>?_),hp⟩
     · split; exact mul_nonneg (hp _).travel (Real.exp_pos _).le; exact le_rfl
     · split; next hz=> have hx:=Real.exp_monotone (show e*coverNumber P.B (X.addr i).support≤ -e+q₁*coverNumber P.B (X.addr i).support from (by have hk: (1:ℝ) ≤ coverNumber P.B (X.addr i).support:= Nat.one_le_cast.mpr (Animals.price_pos (X:= (X.addr i).support) ..|>.2 ⟨_,(X.addr i).anchor⟩); unfold e; linarith)); rw [Real.exp_add] at hx; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hx (hp _).travel
       next hz=> rw [mul_zero]
lemma quitting (u':ℝ)(X:Rail c N I)(hX:Quits X P.B v u q₁ u')(hv:0≤u): Quits X P.B (Real.exp (-(q₁/2))*v) u (q₁/2) u':=by
     obtain ⟨f,h,hp⟩:=hX.cost; let e:=q₁/2
     refine ⟨f,fun x=> budget_mono (budget_scale (Real.exp_pos (-e)).le (h x)) (fun i=>?_) (fun i=>?_),hp⟩
     · split; exact mul_nonneg (mul_nonneg (pow_nonneg hv _) ((norm_nonneg _).trans (hp _ 1))) (Real.exp_pos _).le; exact le_rfl
     · split
       next hz=> have hx:=Real.exp_monotone (show e*coverNumber P.B (Ruby.home X i)≤ -e+q₁*coverNumber P.B (Ruby.home X i) from (by have hk: (1:ℝ) ≤ coverNumber P.B (Ruby.home X i):= Nat.one_le_cast.mpr (Animals.price_pos ..|>.2 ⟨_,hz⟩); unfold e; linarith)); rw [Real.exp_add] at hx; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hx (mul_nonneg (pow_nonneg hv _) ((norm_nonneg _).trans (hp _ 1)))
       next hz=> rw [mul_zero]
lemma kisses (z s:ℂ)(hp:Budget Y P L x ρ φ a u p q₁ r)(h:Desk Y P b L x ρ)(hr:P.B=highR L x)(hz:‖z‖ ≤1)(hs:‖s‖≤1): Quits (PackageK Y φ z s) P.B (1+(a+u)) (taxK L x 1) q₁ T!:=by
     let Z:= ampK Y.prime (φ⁻¹^2); obtain ⟨g,hg,hq⟩:=hp.loft.cost; have he:0≤a:=budget_nonneg (hg 0)
     exact quitsTie _ _ (Library.steady Y.master h.base hr).bill (quitsTie _ _ (wattsLoosen _ (watt_price Z _ hp.loft) (mul_le_of_le_one_left he (upperPaint pegE z s hz hs))) (one_mul u ▸ (quitsH _ _ (fun i=>upperPaint _ z s hz hs) hp.top zero_le_one))) -- risk one_mul direction
-- board reserve. used at Factory on same gamma,z p as common points.
def mild (P:BudgetPoint)(L:Side)(a u x r p:ℝ):Prop:= Real.exp (-(q₁/2))*massPay P L x r p ≤ Jets.Touch.chip L x ∧ Real.exp (-(q₁/2))*(1+(a+u))≤1
abbrev Hook (p:BudgetPoint) (Y:Gem c N I)(ξ:I→ℝ)(w e:ℝ) := LowFare Y p (q₁/2) w e ξ
private lemma order_tag (Z: Gem c N I)(T:Rail c N ι)(v:ℝ)(z:I→ℝ)(he:LowFare Z P (q₁/2) u e z)(hp: Quits T P.B 1 v (q₁/2) u)(hV:0<u)(hX:0≤v): ∃ g:ι→ℝ, Cents (duo Z T) z g u P.threshold ∧ Fill (duo Z T) z g (1/16) (1/16) v 1 e P.B:=by
     obtain ⟨g,hg,hq⟩:=hp.cost; have ht:q₁/2=1/16:=by norm_num
     refine ⟨g, ?_, ⟨by positivity,hX,?_,?_⟩⟩
     · refine ⟨fun i=>(he.2 i).travel, fun i=> (norm_nonneg _).trans (hq i 1), ?_, hq⟩
       intro i U; change Creek.load _ (Cove.light _ (masked P.threshold (Z.addr i).support (Z.view i) U))≤_; by_cases ht:Healthy P.threshold (Z.addr i).support U
       · rw [masked_eq _ _ _ _ ht]; exact (Stew.shot (lens (Z.addr i).site) _ u hV).trans ((he.2 i).sizeU U ht)
       rw [masked_ne _ _ _ _ ht,map_zero,Cove.load_zero]; exact (he.2 i).travel
     · exact ht ▸ he.1
     change Ac.Hit (Ruby.home T) P.B (fun i=>g i*v^(Ruby.oriD T i).card) (1/16) 1; rw [show (fun i=>g i*v^(Ruby.oriD T i).card)=GasP.taxed (Ruby.oriD T) g v from funext fun i=>mul_comm ..]; exact ht ▸ hg
lemma Ticket (hB:Budget Y P L x ρ φ a u p q₁ r)(hp:SeatsE φ Y P L x ρ q₁ r p b f g t k)(h:modulus P p r)(he:Desk Y P b L x ρ)(hr:P.B=highR L x)(hz:‖z‖≤1)(hs:‖s‖≤1)(ht:1 ≤ T!)(hm:mild P L a u x r p): ∃ G: KIndex Y→ℝ,
      Cents (Cane Y φ z s) (rings Y f g t k P) G T! P.threshold ∧ Fill (Cane Y φ z s) (rings Y f g t k P) G (1/16) (1/16) (taxK L x 1) 1 (Jets.Touch.chip L x) (highR L x):=by
     rw [← hr]; refine order_tag _ _ _ _ (looser _ _ (eroded _ _ (sails Y φ z s f g t k hp h hz hs (by norm_num) ht)) hm.1) ?_ (zero_lt_one.trans_le ht) (Real.exp_pos _).le; exact wattsLoosen _ (quitting (P:=P) _ _ (kisses Y φ z s hB he hr hz hs) (Real.exp_pos _).le) hm.2
-- note names collision pension.B.
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.quitting
#print axioms YM.QCD.Struck.Library.Carrier.table
#print axioms YM.QCD.Struck.Library.Carrier.Ticket
