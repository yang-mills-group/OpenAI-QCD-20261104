import YM.Massive.Sharp.Apply
import YM.Massive.Sharp.Joint
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
variable (Y₀:LanternT f N c)(u:Flavor N→ℝ)
abbrev inspect (z:ℂ):ℂ:=Cvol (experimental Y₀ u v z)
private lemma earns (X:Lanes c N): Integrable (cBer X) (prior su c):= ((peakW _ _).continuous.comp X.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
noncomputable def presentL :EvenA f N →L[ℂ]ℂ:= LinearMap.toContinuousLinearMap {
    toFun:=fun x=>Cvol (Y₀ x)
    map_add':= by
         intro i k; unfold Cvol; simp only [cBer,map_add,ContinuousMap.add_apply]; exact integral_add (earns (Y₀ i)) (earns (Y₀ k))
    map_smul':=fun z y=> by unfold Cvol; simp only [cBer,map_smul,ContinuousMap.smul_apply,RingHom.id_apply]; exact integral_smul .. }
lemma inspects : Differentiable ℂ (Sharp.inspect Y₀ u (v:=v)):=by
    let T:= presentL Y₀; let H:= ingredient f u; change Differentiable _ (fun z:ℂ=> T (exp (((v:ℂ)*z) • H))); apply T.differentiable.comp; exact (differentiable_exp_smul_const ℂ H).comp (by fun_prop) -- inference conflicts.S.z
lemma peak (X:Lanes c N): ‖Cvol X‖ ≤ ∫ U, ‖X U‖ ∂prior su c := (norm_integral_le_integral_norm _).trans (by exact integral_mono (earns X).norm (X.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun x=> Grass.price ..))
-- complex integral for all i.Stop.Gauge. Use variable hZ.
include hj hE
lemma lit (hi:i<n)(u:Flavor N→ℝ)(v:ℝ)(z:ℂ): Cvol (ShapeX B Y u v (i+1) z)= (↑(gain (W1 i) (towerQ J B n (i+1) k) N):ℂ)*Cvol (ShapeX B Y u v i z):=by
    have he : Massive.Transfer.growth (towerQ J B n (i+1) k) N (W1 i)=(↑(Rain.gain (W1 i) (towerQ J B n (i+1) k) N):ℂ):=(Complex.ofReal_pow ..).symm
    have hk:= circuit B hj Y hE u v hi z; change Massive.joint (Cove.light _ ∘(ShapeX B Y u v (i+1) z))=_; rw [← hk,Massive.Transfer.conserves _ _ _ _ _ (show (Pike J i).patch.Branches T'.bind su from hj) _ (Massive.Transfer.soften_pay _ _ ((Cove.lightC _).comp ((show Continuous (ShapeX B Y u v i z) from (Y i _).continuous)))) , he]; rfl
include hP
lemma relative (hi:i≤n):∃ p:ℝ,0<p∧∀ z:ℂ,Cvol (sY i z)=(p:ℂ)*Cvol (sY 0 z):=by
    induction i with
    | zero=> exact ⟨1,zero_lt_one, by simp⟩
    | succ i ih=> obtain ⟨p,hp,h⟩:= ih (by omega); let P:=Rain.gain (W1 i) (towerQ J B n (i+1) k) N ; refine ⟨P*p,mul_pos (pow_pos (hP.vocals i hi).1 _) hp,fun z=>?_⟩; rw [lit B Y hj hE hi,h z, Complex.ofReal_mul,mul_assoc] -- defeq
-- bare nonnegative sign. derive not assuming hZ.Morph.L are.Nonconstant.Leg.Rep.Frame`. regular from Paper.
omit hP hj hE
open scoped ComplexOrder
lemma shown (R:Massive.Regulator c N)(hf:0≤R.β)(hc:4 ≤ c.val)(he: Even (c.val)): 0 ≤ R.Z:=by
    refine le_trans ?_ (Massive.Checker.lower R hf he hc); apply Complex.zero_le_real.mpr; exact mul_nonneg (partition_pos _).le (prod_nonneg fun _ _=>Even.pow_nonneg ((by decide : Even 12).mul_right _) _)
lemma massC {R0:Massive.Regulator c N}(G:Pixel c N)(hf:Cove.light _∘ G= ⇑(R0.density)): Cvol G= R0.Z:=by
    change Massive.joint (Cove.light _ ∘ G) = Massive.joint ⇑(R0.density*1); rw [hf,mul_one]
include hj hP hE hZ
-- omit hZ? ordered requires!
lemma active (s:ℝ)(hi:i≤n)(he:Even (B.n k).val) (hn:4≤(B.n k).val): 0≤ Cvol (sY i s):=by
    obtain ⟨p,hp,hV⟩:= relative F₀ M₀ B g X Y hj hE hP hi; rw [hV (s:ℂ)]; apply mul_nonneg (Complex.zero_le_real.mpr hp.le); rw [massC _ (ordered F₀ B g hZ hj Y hE _ _ s)]
    have hh: ∀ i, towerQ J B n i k=B.n k* J.L^(n-i):=fun i=>feetM ..; apply shown _ (zero_le_one.trans (hP.beta _ (Nat.zero_le _))); · rw [hh,PNat.mul_coe]; exact hn.trans (Nat.le_mul_of_pos_right _ (by positivity))
    rw [hh,PNat.mul_coe]; exact he.mul_right _
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.active
