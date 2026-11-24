import YM.MassiveQCD.Tangent.Reach
import YM.MassiveQCD.Cabaret.Hydra
import YM.QCD.Finch.Dad
import YM.QCD.Moss.Muse
/-!
 # Aisle for the marked cluster assembly
 Actual sum layout. Costs on **all** with arbitrary marker support and generation preserved. Separate locator `seat` by supported true and coerces for repaint. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Shells
open ConnectedActivityE6 ConnectedActivityE6.Blaze Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation
open QCD.Beam QCD.Loom Fleet QCD.Patron QCD.Cove PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L : Side}{j n l k : ℕ} {S : StepData c f} {T : Tube su S} {F : Forest S.ratio} {P : Teller su}
variable {O R : BudgetPoint} {X : Coat T F} {I : Finset (Tubular f su)} {η r q a W d C' A b s μ C v B t t' w y u: ℝ}
variable {δ β B₀:ℝ}{Q : YM.ConnectedActivityE6.Target su P}{o :Target.Order su W}{H : Cash W s μ L Q o C T (trimP T R δ β B₀)}
variable {χ:Chi}{ι:Type}{N:ℕ}(Y:Fleet H ι N)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage
open Ursell QCD.GasP Stained March Graph AnalyticBridge.LocalGaussianLaws
open WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open Spice Lat Multi Multi.Puff Kit Jets Port Fork Sands Fj
variable {N':Libretto su j}
open Garden Stew Dust Brick YM.Next.Free Jets.Touch Orbit Further Leaf Tee Flume Quarry Pine
open Planned.AtomRegular
open Run Jets Jets.Sun
open Ac Trees Labels Animals Further.ShellBirth49.Fusing Collide
open Trees Ac Further.ShellBirth49.Fusing Collide
open Labels
variable {p i j' m m':ℕ}
-- Anchor dictionary only needs single B. Y estimator equality of register. 
variable {E J: Type}[Countable E][Countable J]{D:Type}[Fintype D]
open King Moss Calm
variable (H) (P': Send S.ratio N D) (Y':Rise f N E J)
set_option quotPrecheck false
local notation "ζ"=> radiusB s
local notation "Y!"=> deckHue H P' Y' (roof P' Y' 30 ζ)
local notation "Z!"=> united (Y!) Y
local notation "A⁔"=> Warmlet H Y P' Y'
local notation "C₀"=> Clusters (Z!).Bright
namespace Warmlet
variable (V:Cash W s μ L Q o C T (lore (trimP T R δ β B₀))) (G:Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→RegularAddress c)
-- prepare budget for ANY supported shops
variable (sparse:E→Prop)(gain:E→Bool)(x:Warmlet H Y P' Y'→ℝ) -- replace
local notation "Kp"=> Duke H Y P' Y'
local notation "q*"=> col H Y P' Y'
local notation "W⁔"=> trunkP H Y P' Y' V
noncomputable def beat (p:A⁔):ℝ:= if h:prince H Y P' Y' p then if sparse (q* ⟨p,h⟩) then x p else 0 else 0
variable {ξ ρ τ Y₀:ℝ}{χ:Chi} (f₁ f₂:Warmlet H Y P' Y'→ℝ)(k: Clusters (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y).Bright→Prop) -- replace
variable (hG : Valued (trunkP H Y P' Y' V) t f₁ (radiusB s) ξ)(hM: Valued (trunkP H Y P' Y' V) t (beat H Y P' Y' sparse f₁) (radiusB s) ρ) (h₂: Valued (trunkP H Y P' Y' V) t f₂ (radiusB s) τ) (hW:∀ i,Woven (trunkP H Y P' Y' V i).site (trunkP H Y P' Y' V i).support O r ((crude (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y) χ G).view (callV H Y P' Y' i)) (f₂ i + factorP H Y P' Y' gain i * f₁ i))
omit [Countable E] [Countable J] in
lemma beatSmall {t:Bool}(h: (t=true→ w ≥ L.val) ∧ (t=false→ w ≥(L.val:ℝ)^2)): rampFee t L ≤ w:=by cases t <;> first | exact h.1 rfl| exact h.2 rfl
-- Common fee T chosen up front, split coarse
local notation "T0"=> callV H Y P' Y'
local notation "w!"=> beat H Y P' Y' sparse f₁
include hG hM h₂ hW
lemma takeR (z:ℝ)(hL:1 ≤ z)(v:ℝ)(hv:0≤ v)(hr: O.B=ζ)(htag:∀ i:(Kp), k (T0 i.val)→let u:= q* i; rampFee (gain u) L ≤ if sparse u then z+v else z): ∃ f: A⁔→ℝ, Valued (W⁔) t f O.B (τ+(z*ξ+v*ρ)) ∧∀ (i:A⁔),k (T0 i)→ Woven ((trunkP H Y P' Y' V i).site) ((trunkP H Y P' Y' V i).support) O r ((crude (united (deckHue H P' Y' (roof P' Y' 30 (radiusB s))) Y) χ G).view (T0 i)) (f i):=by
   let A:= Warmlet H Y P' Y'; let f(i:A):=z*f₁ i+v*w! i; have hF: Valued (W⁔) t f ζ (z*ξ+v*ρ):= advance _ _ _ (reserve_sum _ (zero_le_one.trans hL) hG) (reserve_sum _ hv hM)
   refine ⟨fun i=> f₂ i+f i,hr.symm ▸ advance (W⁔) f₂ f h₂ hF,fun i hk=> (hW i).stretches (Subset.refl _) (add_le_add (by rfl) ?_)⟩ -- order
   unfold f beat factorP; have hx:=vex _ _ hG i; split
   next he=> have h := htag ⟨i,he⟩ hk; dsimp only at h; split
             next hs=> rw [if_pos hs] at h; rw [← add_mul]; exact mul_le_mul_of_nonneg_right h hx
             next hs=> rw [if_neg hs] at h; rw [mul_zero,add_zero]; exact mul_le_mul_of_nonneg_right h hx
   next _=> rw [mul_zero,add_zero]; exact mul_le_mul_of_nonneg_right hL hx
where reserve_sum {v u:ℝ}(T:A⁔→ℝ)(h:0≤v)(P:Valued (W⁔) t T ζ u) : Valued (W⁔) t (fun i=>v*T i) ζ (v*u):= by
         intro i; convert budget_scale h (P i) using 1; ext j; dsimp only; split<;>simp [*, mul_assoc]
end Warmlet
end YM.QCD.Shells
