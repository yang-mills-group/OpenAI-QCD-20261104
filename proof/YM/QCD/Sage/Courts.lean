import YM.QCD.Sage.Well
/-!
 # Ξ.T discrepancy tested even when CHAR.V6 compact vs V9.Q.Bounds.Consume after 
  proof of acquisition at all x heights. continuity budgets Book.Small.Old μ remain.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sage
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Baffle Prism Brim Lotus Peak
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (h : Intake P T X.x R) (hp : Scrim X a) (hP : Room P S T X.x)
variable (U: Eth R i)
variable (L' : Config G f→ℝ)(hL': LocalOn (R.activities.reg i).support L')(hm:U.ingredient= masked R.p.threshold (R.activities.reg i).support L')
variable {ζ d A t : ℝ} (ht : Canary G d A)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Z : E→ Config G c} {p : E} {n : ℕ} {v N Q K δ τ L M m m' : ℝ}
variable (A' : Anthem n) (hs : ∀ (u:Prices G I), ‖u‖≤ L→ Score X i R a q κ b D u K d ζ δ N Q A' Z p)
variable (hr : Ranks X i R a q κ b D Z d ζ p n) (hf : 0 < ζ*X.t) (hy : Tendsto Z (𝓝 p) (𝓝 X.V))
variable (hK : ∀ y, dotProduct y ((lamp6 X a X.V) *ᵥ y) ≤ M * dotProduct y y)
variable (hv : 0≤ v) (he : gStep R.beta*(Fintype.card G.ColorIndex:ℝ)*(v+δ)<(D.ε*R.p.threshold)/8) {Bt : BudgetPoint} {Ct : Libretto G n}

abbrev coin₀ (A : Anthem n) (N Q:ℝ) := incomeB A N Q * Q * (1+(1+1):ℝ)^n
def Eth.out (U H: Eth R i): Eth R i := ⟨(fun i=> U.ingredient i-H.ingredient i), fun a b h=> congr_arg₂ (·-·) (U.specific _ _ h) (H.specific _ _ h), _,fun x=>(norm_sub_le ..).trans (add_le_add (U.earn x) (H.earn x)), U.borel.sub H.borel⟩
include h hp ht hr hK A' hs hf hy hP hv he U hm hL'
lemma waves (hc : Plays Ct D Bt R.p P T X.x) (hz : Healthy Bt.threshold Y X.V) (hh : ∀ᶠ x in 𝓝 p, (vary X (Z x)).relating.PosDef ∧ Drivable X d A (Z x))
    (hA : ∀ i, Tendsto (volume9 X a q 1 b i ∘ Z) (𝓝 p) (𝓝 (volume9 X a q 1 b i X.V)))
    (he' : ∀ i, ‖volume9 X a q 1 b i X.V‖ ≤ m*X.t) (hw : m*X.t+D.ε*R.p.threshold ≤ ζ*X.t) (hb : 8*ζ*X.t ≤ d/2)
    (hvol : ∀ i,‖volume6 X a i X.V‖ ≤ m'*X.t) (hB : Baffle.screen ζ X.t m' (gStep R.beta) ≤ L) (hL : 0≤L) (h₁ : 0 ≤ K) (l : ℕ) (W : ℝ) (Ñ : ChartRatio G) (H:Eth R i) (c: ℝ)(hC:∀ z:Prices G I,‖z‖≤ L → ‖golf X i R a H z-golf X i R a U z‖ ≤ c):
    let y x:= cinema i R H (vary X (Z x)) ζ (podium S G Y X.B)
    let u:= a.hymn T (gStep R.beta) q b X.k L' (magic D R.p R.beta κ) 1
    Brush n (c*coin₀ A' N Q+U.weight * (2*Prism.blend A' N Q δ K v M)) 1 (fun x=> y x - u (Z x)) p := by
    intro y u; have hV:= wickets X i R a q κ b D h hp hP U L' hL' hm ht A' hs hr hf hy hK hv he hc hz hh hA he' hw hb hvol hB hL h₁ l W Ñ
    let P':Eth R i:= Eth.out i R H U
    let B:=lamp6 X a X.V; let μ:= cloud B
    have hP1 := hs 0 (by rwa [norm_zero]); have hp₀ : (lamp6 X a X.V).PosDef := hP1.at_z ▸ (show (lamp6 X a (Z p)).PosDef from hP1.commits.sane)
    let J:= T6 X i R a P' d ζ Z; let C x:= ∫ z,J x z ∂μ
    let g x:= cinema i R U (vary X (Z x)) ζ (podium S G Y X.B)
    have hT:= liveIn X a ht h.positive hc hz hp q κ b hy hA hf he' hw
    have hH:∀ᶠ x in 𝓝 p, ∀ s, veil X a q κ b D R.p d R.beta s (Z x)≠0 → coin X i R a d R.beta ζ (Z x) s=1:= hT.mono fun _ hh s hv=> (hh s hv).1
    have ha : Meristem J p μ n:= (corridors X i R a q κ b D h ht P' hf hy μ hr hvol hH).1
    let w:=c*coin₀ A' N Q; have hw:Brush n w 1 C p:=by
       apply ha.buds (fun _=>w) (integrable_const _) zero_le_one (by simp) (ae_of_all _ ?_)
       intro z; let r:=golf X i R a P' z; by_cases hv':‖z‖≤ L
       · have he:= hs z hv'; have hF:= (arrows X i R a q κ b D h ht z A' he).1; have hb : ‖r‖≤ c:=hC z hv'
         apply (hF.paints ((he.cover.smul r).climb (mul_le_mul_of_nonneg_right hb he.basis) le_rfl)).trim.climb ?_ le_rfl |>.shimmy _
         · unfold w coin₀; exact le_of_eq (by ring)
         exact Eventually.of_forall fun s=> congr_arg (fun y=> tax6 X i R a d R.beta (Z s) z*y) (mul_comm (coin X i R a d R.beta ζ (Z s) z) r)
       have hw : 0 ≤ w:= by
          have he:=hP1.basis; have hc:0≤c:=(norm_nonneg _).trans (hC 0 (by rwa [norm_zero])); have hv:= (arrows X i R a q κ b D h ht 0 A' hP1).1.nonneg
          unfold w coin₀; positivity
       apply zi _ hw zero_le_one
       filter_upwards [silence X i R a h ht hy hf hvol hB hL] with t ht; change box6 ..=0; rw [box6,ht z (lt_of_not_ge hv'),zero_mul,mul_zero]
    have h₁ := (corridors X i R a q κ b D h ht U hf hy μ hr hvol hH).2.2; have h₂:= (corridors X i R a q κ b D h ht H hf hy μ hr hvol hH).2.2
    apply (hw.gathering hV).shimmy
    filter_upwards [hh,h₁,h₂] with z ht' H1 H2; change _=C z+(g z-u (Z z))
    have he(X₁ : Eth R i): cinema i R X₁ (vary X (Z z)) ζ (podium S G Y X.B)=∫ w,T6 X i R a X₁ d ζ Z z w ∂μ:=pop6 X i R a h hp (by assumption) ht ht'.2 X₁ hf hb l Ñ W hp₀ ht'.1
    have hh:g z= _:=he U
    rw [show y z=_ from he H,hh]; dsimp only [C]; rw [show J z=fun w=> T6 X i R a H d ζ Z z w-T6 X i R a U d ζ Z z w from funext fun i₀=>?_ ,integral_sub H2.1 H1.1]; swap
    · unfold J T6 Function.comp box6; rw [show golf X i R a P' i₀=golf X i R a H i₀-golf X i R a U i₀ from rfl]; ring
    abel
end YM.PhysicalNext.Repeat.Sage
