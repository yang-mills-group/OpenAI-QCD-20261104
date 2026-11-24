import YM.Massive.Reservoir.Stairs
import YM.Massive.Brush.Width

/-! # E-bias first term. Pressure certificate into required quartic reader.

We KEEP marked mass leases. All these bounds per root with no sign-preservation
assumption on determinant. Related momentum kernel lemma `HaloM` reprises the
very same row estimates as in unmarked step family.
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
open Next.Rank IV Rain
namespace Glint
open High.PrismT Globe Massive.Reading
variable (L1:HaarBudget su)(D:PathData su) (F':ℂ→Pixel c N)


namespace Brush -- extend from certificate `ShapeX`
open Massive.PCAC Brave
open Massive (Density)
open Nola
open Grass.Ward Loft
open Sharp
local notation "♯"=> Fintype.card (Site c)
lemma charged (x:EvenA c N)(V K:ℝ)(he:0<V)(hv: GrassA x V 0 K): ‖panel 4 x.val‖ ≤ (♯:ℝ)*(K/V^4):=by
    rw [← mul_div_assoc, le_div_iff₀ (pow_pos he 4), Grass.norm_def,sum_mul]; apply le_trans _ hv; unfold band; apply sum_le_sum; intro i _
    rw [Stew.angel]; split
    next hs=> unfold grainH Nola.tell; rw [hs,pow_zero,mul_one]
    next h=> rw [norm_zero,zero_mul]; exact grains locationP _ he i

-- Layer projection in density and in its log. Use `Phases` for equality.
lemma phase_oil (x:EvenA c N)(he:Pith.Phases x): Pith.Phases (oilD x):=by
    unfold oilD; apply Pith.phase_sub he; rw [show Stew.stage 0 x= coef ∅ x.val • (1:EvenA c N) from Subtype.ext (Stew.bush x.val)]; exact Pith.phase_c _ _ Pith.phase_id
lemma grade_oil (x:EvenA c N)(n:ℕ)(he:n ≠ 0): Stew.panel n (oilD x).val= panel n x.val:=by
    change panel n (x.val-panel 0 x.val)=_; rw [map_sub, past (n:=0) _ (Stew.chamber 0 _), if_neg he,sub_zero]
lemma fine_oil (x:EvenA c N): feeF F₀ (oilD x)= feeF F₀ x:=by
    unfold feeF; rw [←breast,grade_oil x 2 (by norm_num), breast]; -- argument
-- Plus + no body
lemma parts_oil (x:EvenA c N) : (oilD x).val ∈ Loft.floor (Pairs (Modes c N)) 2:=Loft.test.mpr fun s h=>by
    by_cases hs:s.card=0; · rw [Finset.card_eq_zero.mp hs]; exact oil₀ x
    exact Stew.measured s (by omega) (oilD x)
lemma first_shelf (x:EvenA c N) : traceP (exp (oilD x).val)=traceP (oilD x).val:=by
    let H:= (oilD x).val; have hv: traceP (exp H)=traceP (1+H):= by
         apply unquote; rw [←sub_sub]; exact reduce (exhaust (parts_oil x)) (by decide)
    rw [show _=traceP (1+H) from hv, Loft.trace_add, show traceP (1:Fields c N)=0 by ext i j; simp [traceP,pairD,vary_one],zero_add]

lemma paid (V:Density c N)(x:EvenA c N)(z:ℂ)(hz:z≠0)(h:V 1=z • exp x.val) (hp:Pith.Phases x)(hx:‖panel 4 x.val‖ ≤ (♯:ℝ)*w)(he:∀ i, Tempo (feeF i x) ∧ Beam (feeF i x) 6 t): LocalPrice V w t:=by
    let Y:=oilD x; let z':=z*Complex.exp (UPr x); have h': V 1=z' • exp Y.val:=by rw [h,ring_of]; unfold z'; rw [mul_smul] -- unfold z'
    have hZ: z'≠0:=mul_ne_zero hz (Complex.exp_ne_zero _)
    have ht:Stew.panel 2 Y.val=form (Matrix.blockDiagonal fun i=> feeF i x):=by rw [grade_oil x 2 (by norm_num),Pith.clean x hp, Pith.fibers x hp]
    refine ⟨Y,z', (fun i:Flavor N=>feeF i x),h',hZ,oil₀ x,ht,?_, ?_,he⟩
    · intro i; unfold Massive.Stiffness.body; rw [h',map_smul,basic,first_shelf x, Loft.traceT (oilD x).val, pack_scale, body_exp ?_,smul_eq_mul,mul_one, inv_smul_smul₀ hZ]; exact (fine_oil i x).symm; exact Loft.reduce (parts_oil x) (by omega)
    rw [grade_oil x 4 (by norm_num)]; exact hx


end Brush
end Glint
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Glint.Brush.paid
