import YM.Massive.Struck.Twinkle
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
abbrev evaluated (t:ℝ)(s:ℂ)(p:ℂ) (P:BudgetPoint)(K: Grid c→ℝ)(U:St c):= scoreV (PackageE Y t s p) (PackageK Y t s p) P.threshold K U
-- normalize flags still. projection proof from `Eval(state)` exactly when $s=φ$.
lemma ampTransport (hp:0<φ)(p:Dye): Struck.pigment p z φ*((φ⁻¹:ℝ):ℂ)^p.2=z^p.1:=by unfold Struck.pigment; push_cast; rw [mul_right_comm, ←mul_pow,mul_inv_cancel₀ (by exact_mod_cast hp.ne'),one_pow,one_mul]
lemma coinEta (hp:0<φ)(p:Dye)(v:EvenA c N) : Struck.pigment p z φ • ((φ⁻¹^p.2:ℝ) • v) = z^p.1 •v:=by
    change Struck.pigment p z _ • ((↑(φ⁻¹^p.2:ℝ):ℂ) • v)=_; rw [smul_smul,Complex.ofReal_pow, ampTransport _ _ hp]
-- generic Gem ampκ.Power total identities
lemma liftE (hp:0<φ)(X:Gem c N I)(p:I→ Dye)(j:ℕ)(hx:∀ i,(p i).2=j) (w:I→ℂ)(hw:∀ i,w i=z^(p i).1): wind (ampE X (φ⁻¹^j)) (fun i=>Struck.pigment (p i) z φ)=wind X w:=by
    unfold wind ampE; unfold wind; congr! 1; funext i U; rw [hw,← hx i]; exact coinEta φ z hp (p i) _
lemma liftK (hp:0<φ)(X:Rail c N I)(p:I→ Dye)(j:ℕ)(hx:∀ i,(p i).2=j)(w:I→ℂ)(hw:∀ i,w i=z^(p i).1): hueW (ampK X (φ⁻¹^j)) (fun i=> Struck.pigment (p i) z φ)=hueW X w :=by
    unfold hueW ampK watt; congr! 1; funext i U; rw [hw,← hx i]; exact coinEta φ z hp (p i) _
lemma awakenK (hp:0<φ) : PackageK Y φ z φ=Y.EvalK z:=by
   let A:=ampK Y.prime (φ⁻¹^2); let C:= ampK Y.top (φ⁻¹^3);
   refine congr_arg (tie Y.master.K) (congr_arg₂ tie ?left ?right)
   case left=> exact liftK _ _ hp Y.prime (fun _=>pegE) 2 (fun _=>rfl) (fun _=>z) (fun i=> (pow_one z).symm)
   exact liftK _ _ hp Y.top _ 3 (fun _=>rfl) _ (fun _=>rfl) -- metavariable drama
variable {G X: Gem c N I}{F:Type}(f:I→Dye)
lemma liftBook (hb:Budget Y P L x ρ φ a u p q r)(hq:0≤q)(hp:0<φ)(hl:φ ≤ 1)(ht:1≤fan L ρ x) (hR: Desk Y P b L x ρ)(hr:P.B=highR L x) (he:modulus P p r)(hz:‖z‖≤1)(K: Grid c→ℝ) (U:St c)(V:Grid c) : evaluated Y φ z φ P K U V= Maternal Y P K U z V:=by
   unfold evaluated Maternal scoreV; rw [awakenK Y _ z hp]; apply congr_arg₂ (HMul.hMul (α:=EvenA c N)) _ rfl; apply congr_arg NormedSpace.exp; unfold heartS; apply congr_arg
   let t:=fan L ρ x; let v:=P.threshold; let VV := V; have hE: Summable (letters Y.master.P v V):= Stew.permits _ (Library.steady _ hR.base hr).shelf (fan_pos ..) (by norm_num) _
   have hS :∀ {I I' J J':Type}(G':Gem c N I)(H':Gem c N I')(G:Gem c N J)(H:Gem c N J')(p q:EvenA c N), (HasSum (letters G' v V) p ∧ HasSum (letters H' v V) p)→ (HasSum (letters G v V) q∧ HasSum (letters H v V) q) →(HasSum (letters (weave G' G) v V) (p+q) ∧ HasSum (letters (weave H' H) v V) (p+q)):= fun {_ _ _ _} G' H' G H p q h hS=> ⟨weaved _ _ _ h.1 hS.1,weaved _ _ _ h.2 hS.2⟩ -- differing index types needed
   have hφ : ‖(φ:ℂ)‖≤1:= (Complex.norm_real _).trans_le ((Real.norm_of_nonneg hp.le).trans_le hl)
   have paid (K:Type) (G:Gem c N K)(Q: K→ Dye)(n:ℕ)(hQ:∀ i,(Q i).2=n)(w:K→ℂ)(hW:∀ i,w i=z^(Q i).1) {Z:ℝ}{b:Bool} (h: Bite (ampE G (φ⁻¹^n)) P t Z q b)(he:Z ≤ 1/8)(hf:2^P.order*Z≤1/4): let X:=wind G w; let V' := Patron.total X v V; let T:= solvent (ampE G (φ⁻¹^n)) Q z φ; HasSum (letters T v V) V' ∧ HasSum (letters X v V) V' := by
         intro X V' T; obtain ⟨f,hf',hh⟩:=h.law.zone; let C:= ampE G (φ⁻¹^n); have hχ:= wakingL C f (show LowFare C P q t Z f from ⟨hf',hh⟩) (fun i=>Struck.pigment (Q i) z φ) (fun i=> upperPaint (Q i) z φ hz hφ); have hW:= liftE φ z hp G Q n hQ w hW
         unfold V' T solvent X; rw [← hW]; refine ⟨soma _ f hχ hq ht he hf _, (Stew.permits _ (show Licence P q Z t _ from ⟨f,hχ⟩) (fan_pos ..) hq _).hasSum⟩ -- rfl
   obtain ⟨a,b⟩:=he _ (Or.inl le_rfl); obtain ⟨u,w⟩:=he _ (Or.inr le_rfl)
   obtain ⟨hX,hZ⟩:= hS Y.master.P Y.master.P _ _ _ _ ⟨hE.hasSum,hE.hasSum⟩ (hS _ _ _ _ _ _ (paid _ Y.canonical (fun _=>pegE) 2 (fun _=>rfl) (fun _=>z) (fun i=> (pow_one z).symm) hb.rent u w) (hS _ _ _ _ _ _ (paid _ Y.low (fun _=>pegE) 2 (fun _=>rfl) (fun _=>z) (fun i=> (pow_one z).symm) hb.low a b) (paid _ Y.high (fun i=>knot (Y.ad i)) 3 (fun _=> rfl) (fun i=>z^Y.ad i) (fun _ =>rfl) hb.high a b)))
   exact hX.tsum_eq.trans hZ.tsum_eq.symm
end Carrier
end Library
end YM.QCD.Struck
#print axioms YM.QCD.Struck.Library.Carrier.liftBook
