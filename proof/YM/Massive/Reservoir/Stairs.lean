import YM.Massive.Reservoir.Laws
import YM.Massive.Jasper.Corpus
import YM.Massive.Reservoir.Pixels
/-! # Sup and integrated budgets across one split trajectory.

`station` gives volume exponent independent of depth for L¹(dU) norm of
normalized Pixel (not of Grass coefficient regularizing factors). Issue:
price has an extra `(gaugeSize x)⁻ᴺ` hopping factor from missing links,
so need growth in torus side **at moving cutoff**. We use only elementary
square-coordinate arithmetic plus the increase itself. Not sending physical
volume to infinity *per* history; lower valuation here works for all sites.
Sup estimate DOES cost additional scale factors (see `roof` formula arm).
-/
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
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Reference
-- one-step transfer along same stopping parameters. No growth frame of F along unchosen schemes.
variable {A3 tol:ℝ}{E:ℕ→SunR Ω}{Xb:ℕ→ℝ}{Ut:ℕ→Towers J.L}
variable (F₀:Flavor N)(M₀:Arrow N) (B:SparkMesh) {M':ℕ→ SparkMesh} (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E Xb Ut x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{D0 a3 Q₀ ξ:ℝ}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- implicit tol not from above? A3 variables namespace shadow from Bank; outside ended.Bank need declare. see compile.
local notation "xg"=> delay J n i x
local notation "xo"=> delay J n (i+1) x
open Conductor Conductor.Quant High Meridians Ruby High.PrismT Massive.Filament
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*Xb i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)
variable (F:∀ j,ℂ→Pixel (towerQ J B n j k) N)
open Aperture Conductor.Quant
open Kin Sway OrbitG MeasureTheory NormedSpace
variable (G₀: Gem c N I)(T: Patron.Rail c N J')
open Finset
namespace Sharp
open Price Next.Rank IV Rain
open Massive.Pressure
open YM.SectorNext.Vacuum (rich spare)
variable (X:HaarBudget su)
variable (Y:∀ j,LanternT (towerQ J B n 0 k) N (towerQ J B n j k)) (hj:J.Branches T'.bind su)(hE:Gallery T' J n k B N V1 W1 Q1 Y hj)
variable {R0 K₁ B₁ p:ℝ}
variable (hw:Fueled T' B F₀ M₀ V1 U1 g Pt E τ.t x ε D0 k Y p v) -- p type nb
local notation "sY"=> ShapeX B Y M₀.tip v
local notation "qX"=> gainsW B Y M₀ τ.t x
variable (hk:CarrierL J.L T'.top N ε D0 A3 a3 Q₀) (hP:Regular X t R0 K₁ T' Q B F₀ x κ τ g Pt E (fun i=> g.costP i+N*Xb i) D W' k V1 U1 W1 Q1)
open scoped ComplexOrder


namespace Reservoir
variable (T:Teller su)
local notation "ζd"=> (su.lieDim:ℝ)


variable {heJ:J.Branches T'.bind su}
local notation "βg"=> gaugeSize J.L x
lemma arches (i:ℕ) : tallyK J.L x i=x + i*Rotary.lamp J.L:=by
    induction i with
    | zero=> simp [tallyK]
    | succ i ih=> rw [tallyK, iterate_succ_apply',← tallyK, ih]; unfold run betaF Rotary.lamp; push_cast; ring
-- use $O(m+x)$ for the log (not sharp but no UV factor paid in exponent per site).
lemma scale_width (hL:1<J.L.val)(hx:1≤x)(i:ℕ) : - Real.log (gaugeSize J.L (tallyK J.L x i)) ≤ run J.L x + i*Rotary.lamp J.L:=by
    let b:=run J.L x+i*Rotary.lamp J.L; have hb:run J.L (tallyK J.L x i)=b:=by unfold b; rw [arches]; unfold run betaF; ring
    have he:= Rotary.bright J.L hL; have hK: 1 ≤ b:=by unfold b; change 1 ≤ (x+Rotary.lamp J.L)+_; linarith only [hx,he,(show 0≤ (i:ℝ)*Rotary.lamp J.L from by positivity)]
    unfold gaugeSize; rw [hb,Real.log_inv,neg_neg]; let s:= Real.sqrt b; have hp:0<s:=Real.sqrt_pos.2 (zero_lt_one.trans_le hK); have hs:1 ≤ s:=by have hh:= Real.sqrt_le_sqrt hK; rw [Real.sqrt_one] at hh; exact hh
    have hQ:=Real.sq_sqrt (show 0 ≤ b from zero_le_one.trans hK); have hc:=Real.log_le_sub_one_of_pos hp; nlinarith only [hc,hQ,hK,hs,mul_le_mul_of_nonneg_left hs hp.le] -- order
local notation "♯"=> (Fintype.card (Site c):ℝ)
local notation "gp"=> gaugeSize J.L y
local notation "S!"=> fixed J T'.bind heJ
lemma gradeL {hJ:J.Branches T'.bind su}(hL:1<J.L.val)(R:Side)(i:ℕ) : (i:ℕ)≤ Fintype.card (Site ((fixed J T'.bind hJ).side R i)):=by
   let S:=fixed J T'.bind hJ; let f:= S.side R i
   have he : i≤f.val:=by
        have hp: i <J.L.val^i:= Nat.lt_pow_self hL
        apply hp.le.trans; unfold f Massive.Scheme.side S; rw [ratio,PNat.mul_coe, PNat.pow_coe]; exact Nat.le_mul_of_pos_left _ R.property
   rw [site_card]; refine he.trans ?_; change f.val≤ f.val^4; exact le_self_pow₀ (show 1≤ f.val from f.property) (by norm_num)
-- growth budget independent of mass resolution and torus size. Depends on β.Ref and patch.
abbrev squad (P:Patch)(x a b:ℝ)(X:HaarBudget su)(T:Teller su):ℝ:=21*(shelfPrice X T a b+4*ζd*(run P.L x + Rotary.lamp P.L))
lemma ceiling (hL:1<J.L.val) (hx:1≤x) (R:Side)(i:ℕ){hJ:J.Branches T'.bind su} {Y:Pixel ((fixed J T'.bind hJ).side R i) N} (hg:0<gaugeSize J.L (tallyK J.L x i)) (h: plaza _ Y ≤ (ζMax X T ((fixed J T'.bind hJ).side R i) J.L (tallyK J.L x i) a / ζMin X T ((fixed J T'.bind hJ).side R i) J.L (tallyK J.L x i) (b+2))^21):
    plaza _ Y ≤ Globe.expo (- squad J x a b X T) ((fixed J T'.bind hJ).side R i):=by
     let f:= (fixed J T'.bind hJ).side R i; let v:ℝ:= Fintype.card (Site f); apply (totalCap X T f J (tallyK J.L x i) a b hg h).trans; apply Real.exp_le_exp.mpr; have hl:= scale_width hL hx i
     have hv:(i:ℝ) ≤ v:= by unfold v; exact_mod_cast gradeL (hJ:=hJ) hL R i
     have he:0 < Rotary.lamp J.L:= Rotary.bright _ hL; have h1: 1 ≤ v:=by unfold v; exact_mod_cast (Fintype.card_pos (α:=Site f) : 1 ≤ Fintype.card (Site f))
     have hp : - Real.log (gaugeSize J.L (tallyK J.L x i)) ≤ v*(run J.L x + Rotary.lamp J.L):=by apply hl.trans; rw [mul_add]; apply add_le_add _ (mul_le_mul_of_nonneg_right hv he.le); exact le_mul_of_one_le_left (by change 0 ≤ x+Rotary.lamp J.L; linarith only [hx,he]) h1
     unfold squad; nlinarith only [mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*ζd by positivity)]
-- Lens.Lheight at Screen. For all FuseS. hCab feeds θ positivity. `θ` price tag refers `tallyK` in estimate.
variable (R':Jasper.Grant X χ J F₀ M₀ Q a d D A3 a3 A' tol ε D0 Q₀ heJ ν)(Y':Massive.Run (fixed J T'.bind heJ) n (B.n k) N)(s:Flavor N→ℝ)
variable (hCab:Jasper.Cab F₀ M₀ X heJ R' x B)(hf:Jasper.FuseS F₀ M₀ X heJ R' n k B Y' s σ r x)
-- preserve shape major. note θL lamp. independent of Ω etc.
structure Ticket (P:Pixel c N)(J:Patch)(X:HaarBudget su)(T:Teller su)(a b x:ℝ): Prop where
   point(U:Grid c): ‖P U‖ * Audience c X T J x a b ≤ major su c a (2*gaugeSize J.L x/strength T.top.clip) U
   paid : plaza c P ≤ (ζMax X T c J.L x a/ζMin X T c J.L x (b+2))^21
-- cast equality.Carrier.L.
lemma across_card (a b K:ℝ)(T':Teller su)(h:c=f)(P:Pixel c N)(he:Ticket (Acre.Rails.money P) J X T' a b K): Ticket (Acre.Rails.money (Massive.Run.paper (transit h (light _∘ P)))) J X T' a b K:=by
     subst f; unfold transit; rw [Massive.Run.paper_back]; exact he
abbrev runway (i:ℕ)(x:ℝ)(P:Patch):= tallyK P.L x i
include hCab
private lemma tpos (h: i≤n): 0< gaugeSize J.L (tallyK J.L x i):=by
   have hx:=hCab.showT.pos (delay J n (n-i) x) (matters ..); change 0< _; unfold delay at hx; rw [show n-(n-i)=i from (by omega)] at hx; exact hx.1
include hf
lemma admits (hi:i≤n): Ticket (Y'.state i) J X T' R'.W₁ R'.K (tallyK J.L x i):=by
    obtain ⟨G,M,D,U,Z,hΓ,hI⟩:= hf.coil; obtain ⟨V,S,W,Q,y,v,L,h1,h2,h3,h4,h5,h6,h7,hF,h8⟩:=hI.studio
    let l:= n-i; let c:=towerQ J B n l k; let z:=delay J n l x; have hL:l+i=n:=Nat.sub_add_cancel hi; have he:z=tallyK J.L x i:=by unfold z delay; rw [show n-l=i from by omega]
    let F:=ShapeX B L M₀.tip y l; let A:=F (v:ℂ)
    obtain ⟨K,b,X0,H⟩:= h6.2 l (by omega)
    rw [← he]; unfold Massive.Run.state Massive.Run.stock; rw [hF l i hL (expand B heJ l i hL (k:=k))]; apply across_card; have hp:=hCab.showT.pos z (matters ..); obtain ⟨h',hr,hP,hH⟩:= H.look.clean (v:ℂ) (by rw [normS v (by linarith only [h6.1.1])]; linarith only [h6.1.2]); have hg:= sheer_mark X T' c J z _ _ hp.1 H.polish H.pays ⟨hP,hH⟩; exact ⟨hg.1,hg.2⟩
lemma station (hi:i≤n)(hL:1<J.L.val): let c:=(fixed J T'.bind heJ).side (B.n k) i; let z:= Y'.state i
    (∀ U:Grid c,‖z U‖ ≤ Globe.expo (- arm X T' J (tallyK J.L x i) R'.W₁ R'.K) c) ∧ plaza _ z ≤ Globe.expo (- squad J x R'.W₁ R'.K X T') c:=by
    intro c z; have hp:= admits F₀ M₀ B X R' Y' s hCab hf hi; have he:= tpos F₀ M₀ B X R' hCab hi
    exact ⟨rooftop X T' c J _ _ _ he z hp.point, ceiling X T' hL ((hCab.showT.pos x le_rfl).2.1) (B.n k) i he hp.paid⟩
end Reservoir
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Reservoir.station

