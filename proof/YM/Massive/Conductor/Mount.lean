import YM.Massive.Meridians.Clang
import YM.Massive.Struck.Creed
import YM.Massive.Lanescape.Transit
import YM.Massive.Weft.Value
/-! # Send an earned `E,K` planet to the structured outgoing snapshot with estimates
The incoming coupling, chart and budget are unchanged. All the marker controls align
per g with support paid cost. This is a building block, assumes strong sector-quits
& finances & family structure from migrations; no claim this gives iteration yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Conductor
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
open Struck Struck.Library
open Finch Carrier

variable {t p:ℝ}
open Sway Pith Strut Lime
open Massive.Log
variable (X:ℂ→ℂ→ Patron.Rail c N I)(Y:ℂ→ℂ→Ruby.Hue c N Ω)
open Ruby Weft High
set_option quotPrecheck false
local notation "Tz"=>P.threshold
variable {b Y₁: ℝ}{s z U:ℂ}
local notation "νT"=> (1/8:ℝ)
open Meridians Rails.Bank
-- E+K harmonics. finite count arguments vs existence of Budget.Meta.R
variable {b':Flavor N} {s0:ℂ}
variable (V: Gem c N ι) (Z:ι→ Dye) (E G:Gem c N Ω)(Q Q':Ruby.Hue c N Ω)(p':Ω→Dye)
variable (φ κ W₀ W₁:ℝ)
abbrev paidE (X:Gem c N Ω)(f:Ω→ℝ): Gem c N Ω:= Library.wind X (fun i=>(f i:ℂ))
abbrev pension (s a:ℝ)(e:Dye):ℝ:=s^e.2*a^e.1
abbrev compressL : Gem c N Ω:= paidE (dusting E) (fun _=>φ^2*κ)
abbrev compressH : Gem c N Ω:= paidE (shone G) (fun i=> pension φ κ (p' i))
abbrev moment :Flavor N→ℝ:=fun i=>φ^2*κ*(gaugeMass E i)
variable (D₀:Voice c N)
variable [aΩ:Countable Ω][aI:Countable I]
-- substitution at frozen step.
def mounted: Code c N := { master:=⟨D₀.ι, I,D₀.P,X 0 0⟩, focus:= moment E φ κ, A:=Ω,B:=Ω,E:=I,F:=ℕ×I, low:=compressL E φ κ, high:=compressH G p' φ κ, prime:= faint X 1 κ φ, top:=Fibre.tail X κ φ, ad:=fun i=>(p' i).1, up:= Harm.widthE} -- B macro! check
omit aΩ
lemma weighted (F: Dye→ℝ) (hp:Lurch E p'): Lurch (paidE E (fun i=> F (p' i))) p':=by
    refine ByGrit _ p' (fun i=> grip _ ⟨hp.1.gauge i,hp.1.num i,hp.1.real i⟩ (F (p' i))) (fun p k g hh=>?_);
    obtain ⟨d,hd⟩:=hp.2 p k g hh
    refine ⟨d,fun i=>⟨(hd i).1,(hd i).2.1,fun U=>?_⟩⟩; change Diode N p k g (F (p' i) • _) = F (p' (d i)) • _; rw [(hd i).1]; exact (eSM _ (OrbitG.phare _) (F (p' i)) _).trans (congr_arg ((F (p' i)) • ·) ((hd i).2.2 U))
variable {β₀:Bool}{K₀:ℝ}
lemma pensions (F:Ω→ℝ) (hF:∀ i,‖F i‖≤K₀) (hx:0≤K₀)(hp:Bite E P t x r β₀)(ht:0<t)(he:CrossP E): Bite (paidE E F) P t (K₀*x) r β₀:=by
     obtain ⟨f,hp0,h⟩:= hp.law.zone; refine ⟨fun i=>K₀*f i,valued_mult E.addr f hp0 hx,fun i=>?_⟩
     have hh:= mudloan_pipe (E.addr i).site (E.view i) (F i) (hp.mint E i); have hv:=((h i).byScalar (F i)).stretches (Finset.Subset.refl _) (mul_le_mul_of_nonneg_right (hF i) (h i).travel); exact ⟨hv,hh.1,fun hX=> puff _ (grip _ (Crisp E he i) (F i)) hv hh ht hX (E.addr i).anchor⟩
lemma dropE (hp:Bite E P t u v β₀)(h:A≤v): Bite E P t u A β₀:=by
    obtain ⟨f,hf,hA⟩:=hp; refine ⟨f,fun i=> budget_mono (hf i) (fun j=> ?_) (fun j=> ?_),hA⟩
    · split; exact mul_nonneg (hA _).1.travel (Real.exp_pos _).le; exact le_rfl
    split; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right h (by positivity))) (hA _).1.travel; exact le_rfl -- ambiguity `exp`
lemma normS (x:ℝ) (hx:0 ≤ x): ‖(x:ℂ)‖=x:=(Complex.norm_real x).trans (Real.norm_of_nonneg hx)
lemma near (κ:ℝ)(hx:0≤κ)(h:κ<1)(z:ℂ)(hp:‖z‖≤1):‖(κ:ℂ)*z‖<1:=by rw [norm_mul,normS _ hx]; exact lt_of_le_of_lt (mul_le_of_le_one_right hx hp) h
local notation "ζX"=> φ^2*κ
local notation "D₁"=>fan L η x
local notation "Xl"=> faint X 1 κ φ
local notation "Xh"=>Fibre.tail X κ φ
local notation "Ψ'"=>mounted X E G p' φ κ D₀
variable (he: Meridians.Seed X P (taxK L x 4) (3/16) (fan L η x) s0)
variable (hV: Cargo V Z E G Q Q' p' P (fan L η x) v A W₀ W₁ r q)
variable (hQ:0≤q)(hv:q+2≤A)(ht:1 ≤ fan L η x)(hφ:0≤φ)(hκ:0≤κ)(hs: Safe (φ:ℂ))(hx:κ<1)
variable (hr: P.B=highR L x)(hD: Enn P b' L x η νT (deckH D₀))
variable (hk:Quits (faint X 1 κ φ) P.B u (taxK L x 1) νT (fan L η x))(hK:Quits (Fibre.tail X κ φ) P.B w (taxK L x 1) νT (fan L η x))(hz:‖s0‖<1)
include aΩ -- `[ ]` always required for K I in X?
include he hV hQ hv ht hκ hs hx hr hD hk hK hz
lemma reboot : Desk (Ψ') P b' L x η:=by
    have h₁:= (tenorOne X he D₀ hD hr rfl hz).1; have h2:= tenureQ X κ P D₀ he hD hz hs (near κ hκ hx 0 (by simp)) (by simp) hr hk hK ht φ rfl
    let Y₀:=mounted X E G p' φ κ D₀; have hL:= Weft.cashable Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv; have hB:= h2.2.2.2.1; have hN:=weighted (shone G) p' (pension φ κ) hL.rise
    refine ⟨h₁,(lurkPin _ _ (φ^2*κ) hL.tilt).1,hN.1,h2.2.2.1,hB.1,h2.1,h2.2.1,fun i=>(hV.digest i).2,fun i=>(by exact Nat.le_add_left 2 (_:ℕ)), ?_,?_⟩
    · intro p k g he; obtain ⟨e,hh⟩:= hN.2 p k g he; exact ⟨e,fun i=>⟨congr_arg Prod.fst (hh i).1,(hh i).2⟩⟩
    intro p k g hy; obtain ⟨e,he,hh⟩:= hB.2 p k g hy; exact ⟨e,he,fun i=>congr_arg Prod.fst (hh i)⟩
omit he hr hD hz
include hφ
lemma rents (hq:φ^2*((2+Pith.jointFee N)*W₀)≤u)(hv₁:φ^3*(2*W₁) ≤ w): Struck.Library.Fare (Ψ') P L x η u w:=by
    have hL:= Weft.cashable Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv; have hN:= hL.rise; have hF: ‖(φ:ℂ)‖≤1:=(Fused.withinL hs).le
    have hu(i:Ω): ‖pension φ κ (p' i)‖ ≤ φ^3 :=by rw [← Complex.norm_real,Struck.qr (p' i)]; exact le_trans ((Struck.within_weight _ _ _ (by rw [normS κ hκ]; exact hx.le) (hV.digest i).1 hF).2 (hV.digest i).2) (le_of_eq (congr_arg (·^3) (normS φ hφ)))
    have hx' (_:Ω): ‖φ^2*κ‖ ≤ φ^2:= by rw [Real.norm_of_nonneg (by positivity)]; exact mul_le_of_le_one_right (sq_nonneg _) hx.le
    have hB : νT ≤ A :=by linarith
    have hZy:0<D₁:= by linarith
    exact ⟨dropE _ (Carrier.Bite.raise _ (pensions _ _ hx' (by positivity) hL.low hZy hL.tilt.1) hq) hB,dropE _ (Carrier.Bite.raise _ (pensions _ _ hu (by positivity) hL.high hZy hN.1) hv₁) hB,hk,hK⟩
omit hφ hκ hx hk hK ht hs hv hV hQ
omit aΩ
lemma pension_eq (x:Dye)(z:ℂ): z^x.1*(pension φ κ x:ℂ)=  Struck.pigment x ((κ:ℂ)*z) (φ:ℂ):=by unfold pension Struck.pigment; push_cast; rw [mul_pow]; ring
lemma engage (p:Ω→ℝ) (q r:Ω→ℂ)(hp:∀ i,q i*(p i:ℂ)= r i): Library.wind (paidE E p) q= Library.wind E r:=by
   unfold paidE Library.wind; congr! 1; funext i U; dsimp only; rw [smul_smul,hp]
lemma windH (z:ℂ): Library.wind (compressH G p' φ κ) (fun i=>z^(p' i).1)= Library.wind (shone G) (serving p' ((κ:ℂ)*z) φ):=engage _ _ _ _ (fun i=>pension_eq φ κ (p' i) z)
lemma windL (z:ℂ): Library.wind (paidE E (fun _=>φ^2*κ)) (fun _=>z)= Library.wind E (fun _=>Struck.pigment pegE ((κ:ℂ)*z) φ):=engage _ _ _ _ (fun i=> by unfold Struck.pigment pegE; push_cast; ring)
lemma clearsL (m:Flavor N→ℝ)(t:ℝ): Library.wind (Pith.rentGem (c:=c) m) (fun _=>(t:ℂ))= rentGem (fun i=> t*m i):=by
   unfold Library.wind rentGem; congr! 1; funext i U; dsimp only; rw [Lscale,Lscale,Complex.coe_smul, smul_smul] -- rhs simp progress
include aΩ
omit aΩ aI in
lemma scoreEq (K: Grid c→ℝ)(T₁:St c) (W:Gem c N Ω) (F':Patron.Rail c N ι) (D:Patron.Rail c N I)(U:Grid c)(hv:heartK F' r U= heartK D r U): scoreV W D r K T₁ U= scoreV W F' r K T₁ U:=by rw [scoreV,scoreV,hv]
include ht hκ hs hx he hD hr hz hk hK
lemma seats (K:Grid c→ℝ) (S:St c)(z:ℂ)(h:‖z‖≤1)(U:Grid c): scoreV (payWarp D₀ E G p' ((κ:ℂ)*z) φ) (X ((κ:ℂ)*z) φ) P.threshold K S U= Maternal (Ψ') P K S z U:=by
     have h1:= tenureQ X κ P D₀ he hD hz hs (near κ hκ hx z h) h hr hk hK ht φ rfl
     have he: (Ψ').EvalE z=payWarp D₀ E G p' ((κ:ℂ)*z) φ:=by
        refine congr_arg (weave D₀.P) (congr_arg₂ weave ?_ (congr_arg₂ weave (windL _ φ κ z) (windH G p' φ κ z)))
        change Library.wind (Pith.rentGem (c:=c) (fun i=> ζX*(gaugeMass E i))) _=_; rw [← clearsL]; exact windL _ φ κ z
     unfold Maternal; rw [he]; exact scoreEq K S _ _ _ _ (h1.2.2.2.2 U).symm
omit he hD hr hz hk hK hκ hx hs -- retain ht
include hV hQ hv
lemma arrival (U:Grid c): sting (Ψ') P U=(φ^2*κ) • Weft.leaves E P U:=by
     have hZ:= Weft.cashable Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv
     change Patron.total (Pith.rentGem (fun i=>ζX*(gaugeMass E i))) Tz U+Patron.total (compressL E φ κ) Tz U=_; unfold Weft.leaves; rw [smul_add, ← clearsL]; refine congr_arg₂ HAdd.hAdd ?_ ?_
     · exact (Library.spar _ ((φ^2*κ:ℝ):ℂ) U Summable.of_finite).tsum_eq
     exact (Library.spar _ ((φ^2*κ:ℝ):ℂ) U (Stew.permits _ hZ.low.law (by linarith) (by linarith) U)).tsum_eq
end YM.QCD.Conductor
#print axioms YM.QCD.Conductor.rents
#print axioms YM.QCD.Conductor.reboot
#print axioms YM.QCD.Conductor.seats
#print axioms YM.QCD.Conductor.arrival
