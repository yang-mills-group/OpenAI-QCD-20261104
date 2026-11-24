import YM.Rebus.Coda
import YM.Rebus.Shoe
import YM.Rebus.Ruler
/-! # Payload pricing projections. One-vertex estimate for common-tile.Id.Loan.Pν normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot Apron Apron.Grove
open Play.Camp Stitch
open scoped Topology Matrix InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{P:Teller su}{β τ C μ W s v κ' κ₁ p₀ q₁ q₂ r' r t t' A₀ A₁ B' u u' s' σ θ η η₁ h' x x' a a' w w' z b v' Ω' φ ε :ℝ}
variable {O:BudgetPoint}{ι κ I E J D: Type}[Fintype I]
variable {N i j n k m l B Q t₀: ℕ}
-- exported accounting for scripts.
variable (L':Flight i j)(h:f.val=c.val*L'.L.val)(K: KernelChoices)
variable {X: Run.St f}{T:Tube su (Flight.visit L' K h)}{F:Tree.Forest (Flight.visit L' K h).ratio}
local notation "Sⁱ"=> Flight.visit L' K h
local notation "R"=> sliceL L' h
variable {Q': Target su P}{o:Target.Order su W}
variable (H:Cash W τ μ L'.L Q' o C T (trimP T O r' β b))
variable (G:Sun L' c f h η h' z a a' m X)
set_option quotPrecheck false
variable (Z:Rise f N E J) (A: Stitch.Tablet Z I) (V₀: Finset (Finset I))(S': Finset E)(p:I→ Site f)(q:I→Bool)
local notation "xp"=> (sliceL L' h).parent∘ p
variable (Φ : Quince f N I)
local notation "Ap"=> spineP p N (majorT l*O.B)
local notation "Aw"=> can p (majorT l*O.B)
variable (Xz: Finset I)
variable {w0 w1:Clip}(J₀ J₁:Bed)(Tx:Towers (Flight.visit L' K h).patch.L) (AxP:Striation (T:=T) J₀ J₁ Tx w0 w1 s s')
variable {M₂ M₃ κz Vp tZ:ℝ}
variable (M₀:Myth su (Flight.visit L' K h) J₀ J₁ Tx (radiusB τ) Vp tZ)
local notation "B0"=>radiusB τ
local notation "Q0"=> (raw L' h K J₀ J₁ Tx B0)
local notation "QZ"=> (sineP L' h K J₀ J₁ Tx (solace J₀ J₁ Tx AxP) B0)
local notation "p₁"=> parties Φ Xz
local notation "KV"=> kpit L' h N B0 I
local notation "KZ"=> sfan L' h N B0 I
local notation "Xp"=> Play.Chamber.switch Φ Q0 QZ KV KZ
variable (hv: SetL p V₀ O.B l k t₀ Φ)(he:∀ i∈V₀,i.card ≤ l)(ht:∀ i∈V₀,∀ j:Finset I,j⊆i → j∈V₀)
-- growth unit height α. Frost only right; Tic point.Power.
structure RateV (V:Finset (Finset I)) (Q:Quince f N I) (C:ℝ): Prop where
    base : 1≤ C
    book i : i∈V → i.Nonempty → cents (Q i) ≤ C^i.card
variable (hC:RateV V₀ Φ C)
variable (hS: Spins L' h N (radiusB τ) M₂)
variable (hp:1 ≤ Vp)(hp2:Vp ≤M₃)(hz:M₂ ≤ M₃)
lemma sageMoney (l:ℕ):1 ≤ moneyN l:=by induction l with |zero=> simp [moneyN]|succ l h=> rw [moneyN]; apply one_le_mul_of_one_le_of_one_le h; exact le_add_of_nonneg_right (by unfold age; positivity)
include hC he ht
lemma specksP (i:Finset I)(h:i∈ V₀) : cents (parties Φ i) ≤ age l*C^l:=by
    have hv:=money_fast Φ (probate (Kh f)) C (fun j hj hh=>hC.book _ (ht i h _ (mem_powerset.mp hj)) hh) hC.base (he i h)
    exact hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC.base (he i h)) (by unfold age; positivity)) -- η?
noncomputable def groat (l k m:ℕ)(C:ℝ):ℝ:= emmet C C C C (l*k) (l*m)*age l*moneyN l
local notation "Go"=>groat l k t₀ M₃
include hv hS M₀ hp hp2 hz AxP
lemma kettle : RateV V₀ Xp (C*Go):=by
    have h3:= hS.pos.trans hz
    have he':1 ≤groat l k t₀ M₃:=by unfold groat; refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (em_pos h3) (one_le_pow₀ (by norm_num))) ?_; exact sageMoney ..
    refine ⟨one_le_mul_of_one_le_of_one_le hC.base he',fun i hi hh=>?_⟩
    have hp:= upbeat L' h K (O:=O) (l:=l) p tZ J₀ J₁ Tx AxP M₀ hS hp hp2 hz i i
    have hx v (he:v⊆ i)(hq:v.Nonempty):= hv.scope _ (ht i hi _ he) hq
    apply Play.Chamber.growth Φ Aw Ap Q0 QZ KV KZ hx C (Bera.emmet M₃ M₃ M₃ M₃ (l*k) (l*t₀)) hC.base (fun j hj hh=> hC.book _ (ht i hi _ hj) hh) (he i hi) (em_pos h3) (fun x he=>Bera.tolled _ _ _ _ _ he hp)
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.kettle
