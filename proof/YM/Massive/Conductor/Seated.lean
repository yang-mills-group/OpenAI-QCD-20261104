import YM.Massive.Lanescape.Quill
import YM.Massive.Conductor.Mount
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
def PositiveCharm (G:ℂ→ℂ):Prop := Holo G ∧ (G 0).im=0 ∧ 0<(G 0).re ∧∀ z:ℂ, ‖z‖<1→ G z≠0
structure Credits (F:ℂ→Pixel c N)(X:ℂ→ℂ→Pixel c N)(x κ φ v:ℝ) : Prop where
    ready : ∃ G:ℂ→ℂ, PositiveCharm G ∧ ∀ z:ℂ, ‖z‖<1 → grow (Rotary.chartR x) F z= G z • vest c N v (X ((κ:ℂ)*z) φ) -- rela K. note bare path F transported.BodyFort.
variable (D₀:Voice c N)
local notation "Ψ'"=>mounted X E G p' φ κ D₀
variable [Countable Ω][Countable I]
variable (he: Meridians.Seed X P (taxK L x 4) (3/16) (fan L η x) s0)
variable (hV: Cargo V Z E G Q Q' p' P (fan L η x) v A W₀ W₁ r q)
variable (hQ:0≤q)(hv:q+2≤A)(ht:1 ≤ fan L η x)(hφ:0≤φ)(hκ:0≤κ)(hs: Safe (φ:ℂ))(hx:κ<1)
variable (hr: P.B=highR L x)(hD: Enn P b' L x η νT (deckH D₀))
variable (hk:Quits (faint X 1 κ φ) P.B u (taxK L x 1) νT (fan L η x))(hK:Quits (Fibre.tail X κ φ) P.B w (taxK L x 1) νT (fan L η x))(hz:‖s0‖<1)
local notation "D₁"=>fan L η x
lemma climb (G:ℂ→ℂ)(H:ℂ→ℂ→ℂ)(h:PositiveCharm G)(hK:0≤κ)(hκ:κ<1)(hs:‖(φ:ℂ)‖<1)(hp:Fused H)(hv:H 0 φ=0)(hx:0<r): PositiveCharm (fun z=> (G z*(r:ℂ))*Complex.exp (H ((κ:ℂ)*z) φ)):=by
    let M(z:ℂ):= H (κ*z) φ; let P (z:ℂ):= G z*(r:ℂ); let C (z:ℂ):=P z*Complex.exp (M z);
    have ht: Holo (fun z:ℂ=>(κ:ℂ)*z):=by unfold Holo; fun_prop
    have hH:Holo M:=(hp.wire φ hs).comp ht (fun z hz=>mem_ball_zero_iff.mpr (near κ hK hκ z (mem_ball_zero_iff.mp hz).le))
    change PositiveCharm C; have hp: C 0= G 0*(r:ℂ):= by unfold C P M; simp only [mul_zero,hv,Complex.exp_zero, mul_one]
    refine ⟨DifferentiableOn.mul (h.1.mul (differentiableOn_const (r:ℂ))) (Complex.differentiable_exp.comp_differentiableOn hH), ?_, ?_,fun z hz=>?_⟩ -- g binder
    · rw [hp,Complex.mul_im,Complex.ofReal_im,h.2.1]; ring
    · rw [hp,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,h.2.1,zero_mul,sub_zero]; exact mul_pos (h.2.2.1) hx
    exact mul_ne_zero (mul_ne_zero (h.2.2.2 z hz) (by exact_mod_cast hx.ne')) (Complex.exp_ne_zero _)
variable (F:ℂ→Pixel c N) (K:Grid c→ℝ) (S:St c)(XX:ℂ→ℂ→Pixel c N)
include he hV hQ hv ht hκ hs hx hr hD hk hK hz
include hφ
lemma owns (hW:Credits F XX x κ φ v) (hs₀:0<w₀)(hq:φ^2*((2+Pith.jointFee N)*W₀)≤u)(hv₁:φ^3*(2*W₁) ≤ w)(hA:∀ z' s:ℂ,∀ U:Grid c, ‖z'‖ ≤1 → ‖s‖≤1→ wearK c N v (XX z' s U)= w₀ • (Complex.exp (Weft.moneyL p' E G z' s) • (scoreV (payWarp D₀ E G p' z' s) (X z' s) P.threshold K S U))) : Desk (Ψ') P b' L x η ∧ Wing F (Ψ') P x K S ∧ Struck.Library.Fare (Ψ') P L x η u w:=by
    have hy:= Fused.withinL hs; obtain ⟨H,hH,hB⟩:= hW.ready; obtain ⟨hG,hG0⟩:= Weft.cargoGlow Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv; have hf := climb φ κ H (Weft.moneyL p' E G) hH hκ hx hy hG (hG0 _) hs₀; have hd:= reboot X V Z E G Q Q' p' φ κ W₀ W₁ D₀ he hV hQ hv ht hκ hs hx hr hD hk hK hz; have hc:= rents X V Z E G Q Q' p' φ κ W₀ W₁ D₀ hV hQ hv ht hφ hκ hs hx hk hK hq hv₁
    let C:ℂ→ℂ:= fun z=> (H z*(w₀:ℂ))*Complex.exp (Weft.moneyL p' E G ((κ:ℂ)*z) φ); have hj (z:ℂ)(h:‖z‖<1) : grow (Rotary.chartR x) F z=C z • Maternal Ψ' P K S z:=by
       rw [hB z h]; funext U; rw [Pi.smul_apply, Pi.smul_apply,show vest c N v _ U=_ from (hA _ _ U ((near κ hκ hx z h.le).le) hy.le),show scoreV ..=Maternal .. from seats X E G p' φ κ D₀ he ht hκ hs hx hr hD hk hK hz K S z h.le U]; unfold C; simp only [mul_smul,Complex.coe_smul]
    refine ⟨hd,⟨C,hf.1,hf.2.1,hf.2.2.1, ?_,fun z h=>⟨hf.2.2.2 z h,hj z h⟩⟩,hc⟩
    rw [← escape Ψ' hr hd hc ht]; simpa [grow] using hj 0 (by simp)
omit he hφ hs hx hD hk hK hz -- keep hr and needed
variable (V₁:Gem c N ι)
abbrev hear (L:Side)(F:ℂ→Pixel c N) (θ x:ℝ)(b:Flavor N):ℝ:= Sens (Rotary.chartR x) (fan L θ x) b F
structure Destination (L:Side)(Y:Code c N)(P:BudgetPoint)(K:Grid c→ℝ)(S:St c)(x θ u w:ℝ)(F:ℂ→Pixel c N)(b:Flavor N) :Prop where
  desk : Desk Y P b L x θ
  purse : Struck.Library.Fare Y P L x θ u w
  wing : Wing F Y P x K S
omit ht hV hκ hv hr hQ in
lemma feesC (b:Flavor N)(v:EvenA c N) (W t:ℝ): flagRead b t (W • v)=W*flagRead b t v:=by unfold flagRead; rw [map_smul,smul_eq_mul,mul_div_assoc] -- include vars omit
variable {S0 S1 R0 p0 q0 v0:ℝ}{m₀:Flavor N→ℝ}
variable (hd:Destination L (mounted X E G p' φ κ D₀) P K S x η u w F b')
include hd
omit hκ in
lemma targeted (b:Flavor N): hear L F η x b=φ^2*κ*flagRead b D₁ (Weft.leaves E P 1):=by
     rw [hear,fore _ _ _ K S hr hd.desk hd.purse F hd.wing, arrival X V Z E G Q Q' p' φ κ W₀ W₁ D₀ hV hQ hv ht 1,feesC]
lemma closest (b:Flavor N): (c.val:ℝ)*|hear L F η x b-D₁^2*((Ψ').focus b)|≤ φ^2*κ*(Finch.fare A P.B*W₀):=by
    have h: 0<A:=by linarith
    rw [targeted X V Z E G Q Q' p' φ κ W₀ W₁ D₀ hV hQ hv ht hr F K S hd,← Weft.vibe Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv b D₁]
    obtain ⟨f,hp,hx⟩:= hV.mass.cost.zone; have he := totalFare b E hp h.le hx (zero_lt_one.trans_le ht) h hV.mass.pupil.1
    let z:= Patron.total E P.threshold 1; let s:= φ^2*κ; have hM: hear L F η x b=hear L F η x b:=rfl; let p:= flagW (feeF b z); rw [Finch.flagP]; change (c.val:ℝ)* |s*(D₁^2*p)-D₁^2*(s*(gaugeMass E b))| ≤ s*_
    rw [show s*(_*p)- _ = (s*D₁^2)*(p-gaugeMass E b) from (by ring),abs_mul,abs_of_nonneg (show 0 ≤ s*D₁^2 by unfold s; positivity)]
    calc
      _ = s*(D₁^2*((c.val:ℝ)*|p-gaugeMass E b|)):=by ring
      _ ≤ _:= mul_le_mul_of_nonneg_left he (by unfold s; positivity)
omit hd hκ ht hV hr hv hQ in
lemma invertSense (v W:ℝ)(U:EvenA c N)(b:Flavor N)(hp:0<W): flagRead b v U=(v/W)^2*flagRead b W U:=by rw [Finch.flagP,Finch.flagP]; field_simp
variable (hB: Breath P V V₁ Z n m₀ S0 S1 t R0 p0 q0) (ht₀:0<t)
include hB ht₀
lemma essential (b:Flavor N): ‖hear L F η x b-φ^2*κ*v^2*(D₁^2*(m₀ b*S0))‖ ≤ φ^2*κ*v^2*(D₁/t)^2*R0:=by
    let Y₀:=Patron.total (LowSection V₁ Z) P.threshold 1; let M:=φ^2*κ; have h:= hB.sugar b; have ht':0≤ M*v^2*(D₁/t)^2:=by unfold M; positivity
    rw [targeted X V Z E G Q Q' p' φ κ W₀ W₁ D₀ hV hQ hv ht hr F K S hd, Weft.leaseRead Q q Z p' V W₁ W₀ E G Q' hV hQ ht hv D₁ b V₁ hB.bump.view.symm,invertSense D₁ t Y₀ b ht₀]
    change ‖ M*(v^2*((D₁/t)^2* flagRead b t Y₀)) - M*v^2*(D₁^2*(m₀ b*S0))‖ ≤ _
    suffices hl:M*(v^2*((D₁/t)^2* flagRead b t Y₀)) - _ = (M*v^2*(D₁/t)^2)*(flagRead b t Y₀-t^2*(m₀ b*S0)) by rw [hl,norm_mul,Real.norm_of_nonneg ht']; exact mul_le_mul_of_nonneg_left h ht'
    field_simp
-- package route.Does not depend on hZ or hk now!
structure Pend (L:Side)(F:ℂ→Pixel c N)(P:BudgetPoint)(K:Grid c→ℝ)(S:St c)(x θ a q u v φ κ w t R U:ℝ)(M:Flavor N→ℝ)(b:Flavor N) :Prop where
    -- a support exponent, q = first W; u|v Fare.B. s=Aux η=φ. M = Source.Sector magnitudes. w Grassmann wear value. t raw height. R = LS Low sector read cost. U= λ expected.
    push : ∃ Y:Code c N, Destination L Y P K S x θ u v F b ∧ ∀ i:Flavor N, (c.val:ℝ)* |hear L F θ x i-(fan L θ x)^2*Y.focus i|≤ φ^2*κ*(Finch.fare a P.B *q) ∧ ‖hear L F θ x i-φ^2*κ*w^2*((fan L θ x)^2*(M i*U))‖ ≤ φ^2*κ*w^2*((fan L θ x)/t)^2*R
omit hd
-- instance support P.L.
variable {Gg:ParcelR} {V':SunR Gg}(S':PathData su)(O':Clip)(E':St c)
omit hV
include hs hx hz hφ
structure Afford (c L:Side)(P:BudgetPoint)(N:ℕ)(x θ φ κ u u' p₁ p₂:ℝ)(s₀:ℂ) : Prop where
   left : φ^2*((2+Pith.jointFee N)*p₁) ≤ u
   right : φ^3*(2*p₂) ≤ u'
   rent : ∀ (I:Type)[Countable I], ∀ (X:ℂ→ℂ→Patron.Rail c N I), Meridians.Seed X P (taxK L x 4) (3/16) (fan L θ x) s₀→ Quits (faint X 1 κ φ) P.B u (taxK L x 1) νT (fan L θ x) ∧ Quits (Fibre.tail X κ φ) P.B u' (taxK L x 1) νT (fan L θ x)
lemma sheltered (h:Bank.Joint XX V Z S' O' E' b' V' v A p d W₀ W₁ r q η x w₁ w₂ s0 L P)(hw: Credits F XX x κ φ v)(hAf:Afford c L P N x η φ κ u w W₀ W₁ s0): Pend L F P (scent V'.Z.page P S' O' w₁ 0 N) (E'+w₂ • 1) x η A W₀ u w φ κ v t R0 S0 m₀ b':=by
    obtain ⟨D,I,hI,X,Ω,hΩ,Zx,G,Q,Q',p',p₀,h0,hD,he,hV,hN⟩:= h.leg; obtain ⟨hk,hK⟩:= hAf.rent I X he; obtain ⟨H,hq,hA⟩:= owns X V Z Zx G Q Q' p' φ κ W₀ W₁ D he hV hQ hv ht hφ hκ hs hx hr hD hk hK hz F _ _ XX hw h0 hAf.left hAf.right hN; have h: Destination L _ P _ _ x η u w F b':=⟨H,hA,hq⟩
    exact ⟨_,h,fun i=>⟨closest X V Z Zx G Q Q' p' φ κ W₀ W₁ D hV hQ hv ht hκ hr F _ _ h i,essential X V Z Zx G Q Q' p' φ κ W₀ W₁ D hV hQ hv ht hκ hr F _ _ V₁ h hB ht₀ i⟩⟩
end YM.QCD.Conductor
#print axioms YM.QCD.Conductor.sheltered
