import YM.MassiveQCD.Lyre.Speed
import YM.Poised.Lira
import YM.MassiveQCD.Lyre.Elevator
import YM.MassiveQCD.Lyre.Harmony
import YM.QCD.Purse.Debit
/-! # Bridge Cupola and Siege.Tower: paid on ONE trajectory -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Lyre
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote N loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c N ⊕ Ribbon.Spine I
open Cupola Plate Spice Shells Sands Phased -- inspect
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "V₁"=> withdraw N loc φ
local notation "HU"=> VarnC H U N
local notation "HP"=> united (VarnC H U N) (sailP H Γ N)
local notation "Vⁱ"=> Wound (roof (G.equip N (radiusB τ)) P₀ 30 B)
-- width invariance on shapes.prove for any spent∅ POD
variable {D':ℕ} -- shadows
variable (Z:Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ))) (hF: spent Z.val=∅)
include hF
local notation "sξ"=> Y.markers Z.val
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀:ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (hp: Peak (G.equip N (radiusB τ)) O.threshold x₀ x x₁ μ') (he:Y.Coins σ Φ x₀ O.threshold)(htB:0<radiusB τ)
variable (D₁:ℕ) (hx: ( (lore (trimP T O δ β b)).activities.reg D₁).support= brimW (G.equip N (radiusB τ)) P₀ Z.val) (hs:x₂ ≤ x)(hv:0≤ x₂) (hρ:0<ρ)(hZ:0 < κ')(hf:0 < φ)
variable {O₁:BudgetPoint} (F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b)))
local notation "X₁"=> Brim.plate F₁ D₁
include F' hp hv he hw htB hx hρ hs hf
lemma strideR (ha:coverNumber (radiusB τ) (Brim.plate F₁ D₁).support ≤radiusB τ):
    let P!:=∏ j∈Z.val, paidSet (G.equip N (radiusB τ)) P₀ μ' σ Φ x₁ ρ κ' 1 j
    Indicia Tx B' N₀ F₁ χ E₀ g₀ (Sum.inl Z) D₁ 0 (arid τ*((ρ⁻¹)^(leftE Z.val).card*P!)) 0 x₂ (prescription L' d K A φ (Y.markers Z.val) q'):=by
    intro Pk; constructor; intro FΩ η V GV _hp hB hV W PPv hW; let A₁:=G.equip N (radiusB τ); let W₁:=brimW A₁ P₀ Z.val; refine ⟨fun _=>0,fun _ _ _=>rfl,measurable_const,fun _ _=> (norm_zero).le,fun VQ hu hx'=>?_,spareG _ rfl χ B' _ _ V η⟩
    -- Direct rough Many pays without even healthy (but Ward compares only within its test).
    let o':=(X₁).site; let Pt: Finset I:=Y.markers Z.val; let WP:= Y.hue O.threshold A₁ Z.val VQ; let Wₖ:= pluck (Keys c N) (burst q' Pt) WP; let z₁:= Z.val.biUnion (QCD.Jets.Touch.roof A₁ P₀ 30 (radiusB τ)); have hX:=Y.lights_hue A₁ hw ((roofs A₁ P₀ 30 B le_rfl htB).1) Z.val VQ -- Y.l... resolution
    let QQ:=(X₁).support; have hh:z₁⊆ QQ:= (sageT L' d K H G U Γ Y A φ F' Z hF hx).pays -- VQ shadow.Ed
    have hc:Wₖ ∈ region (limits QQ):= regionMon (limitsMon _ _ hh) (hX.2 _)
    have hz:load (fun _=>x) Wₖ ≤ x₁^(kappa (A₁.trim+1) N * invSize P₀ Z.val)*priceSet Z.val μ' σ Φ:= ((Stitch.Tablet.polite_bill Pt WP (hX.1) hp.cup).symm).trans_le (Stitch.Tablet.wage Y A₁ hw he hp Z.val VQ)
    rw [tire L' d K H G U Γ Y A φ Z hF,sub_zero]; change ‖GV (pluck _ _ (withdraw N _ φ _))‖ ≤ _; rw [Cupola.home N _ _ hf]; apply (hB _).trans; apply (QCD.Stew.future _ hv hs _).trans; apply (Elevator.shutter QQ o' (Malachite.radiusD τ) (fun i hi=> (Corona.extent _ (radiusB τ) hi (X₁).anchor).trans ?cost) Wₖ hp.cup hc).trans
    case cost => unfold Malachite.radiusD; gcongr
    unfold Pk; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); rw [expensesW,← mul_assoc, ← mul_assoc,← mul_assoc, hF, Finset.card_empty, Nat.add_zero, pow_zero,mul_one,← mul_pow,inv_mul_cancel₀ (by linarith),one_pow,one_mul,invSize,hF,sum_empty,pow_zero,one_mul]; rw [invSize,hF,sum_empty] at hz; exact hz -- kappa filter. check.
end YM.MassiveQCD.Lyre
