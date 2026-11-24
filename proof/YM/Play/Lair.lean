import YM.Play.Firs
import YM.Play.Quiet
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
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
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
open Anomaly Play Chamber Camp Cupola
open Stitch Stitch.Tablet
local notation "Ip"=> Wound Zⁱ
local notation "X0"=> Keys f N ⊕ Spine I
local notation "X1"=> Keys c N ⊕ Spine I
local notation "K0"=> Keys f N
local notation "K1"=> Keys c N
variable {m₁:ℕ}
namespace Grove
-- degree on arbitrary subsets.D
set_option quotPrecheck false
local notation "Pe" e=> Fj.pin (picksV f m (radiusB τ)) e (∅:Finset J)
local notation "lk"=> (S').ratio.parent∘ A
local notation "T0"=> (withdraw N ((S').ratio.parent ∘ A) φ)
local notation "Oi"=> omegaE Zⁱ Y (fun (_:Varn f c ⊕ Gaze c)=> ∅)
local notation "inH" => (united U' X')
local notation "sM"=> (swingE N (Tx) (Oi))
variable (e:Finset E)(Z:Finset I)
variable {q₀:I→Bool} {θ α:ℝ}
variable (χ:Chi)(V:Grid c)(p':Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ)) ⊕ Varn f c⊕Gaze c →ℝ)
variable (hF:Registry L' d K H G U Γ Y A φ p' θ α q₀ χ)
variable (hR: Fleet.Regal N ((Flight.visit L' K d).ratio.parent ∘ A) φ q₀ (vantage L' d K H G U Γ Y A φ) (Sum.elim (fun w=>Y.markers w.val) (fun _=>∅))) -- Aura bargain
variable (hE:∀ i∈ e,(Y.spine i).Nonempty)
-- projection into Z pre & after. Mint
local notation "F!"=> mage L' d K H G U Γ Y A φ e χ
local notation "Pf"=> Pe (fled Y e Z)
local notation "ι+"=> ↥(TabletV.plume P₀ Z' Zⁱ Pf)
local notation "At" e=> (Play.Camp.port H Z' Zⁱ Y A φ inH (Pe e))
open PhysicalNext.Repeat.Greenbelt
local notation "PS" r=> (prism T τ χ o.K V (allot r))
local notation "PS'" r=> (planted (prism T τ χ o.K V (allot r)) (∅:Finset (Head (Flight.visit L' K d))))
open PhysicalNext.Repeat.Greenbelt Hypnos
include hF hR hE
open Bera
local notation "ζ0"=> T0
-- occurrence Lens for ANY input.E.
lemma aurea (i:Clusters (Tx).Bright) (he: game L' d K H G U Γ Y A φ e χ Z V i ≠ 0): Z.Nonempty ∧ Z.image lk⊆ seatP (Tx).lightF i∧ Mint N lk φ q₀ Z (game L' d K H G U Γ Y A φ e χ Z V i)∧ game L' d K H G U Γ Y A φ e χ Z V i=(Tx).honest χ V i:=by
    let S:=Tx; unfold game Play.Camp.port at he ⊢; split_ifs at he with h₁ h₂; rotate_left; · exact (he rfl).elim
    · exact (he rfl).elim
    rw [if_pos h₁, if_pos h₂]; change Z.Nonempty ∧ _ ∧ Mint _ _ _ _ _ ((Tx).honest χ V i) ∧ _
    refine ⟨h₁.1, ?_,?_,rfl⟩
    · rw [← h₁.2]; choose f h hf using h₂; have hu:= swingD L' d K H G U Γ Y A φ _ f hf
      intro j hj; obtain ⟨b,hb,rfl⟩:= mem_image.mp hj; rw [hu] at hb; obtain ⟨x,hx,hb⟩:=mem_biUnion.mp hb; have he: Y.markers (f x).val |> fun i=>b∈i:=hb; refine mem_biUnion.mpr ⟨x,hx,?_⟩; change _ ∈ (Tx).lightF _; unfold Fleet.lightF; rw [hf]; rw [show (Tx).fullA _=(f x).val.biUnion Zⁱ from (partV H Z' Zⁱ Y A φ inH (f x))]; exact Y.endowment Z' hF.property ((roofs Z' P₀ 30 B le_rfl hF.room.2).1) _ (mem_image_of_mem _ he)
    unfold honest; by_cases hz :Healthy (Pressure.temp τ) (seatP (Tx).lightF i) V; · rw [masked_eq _ _ _ _ hz,←h₁.2]; exact Fleet.swingM N lk φ q₀ _ _ hR (zero_lt_one.trans_le hF.strength) χ V i
    rw [masked_ne _ _ _ _ hz]; exact Mint.none _
private lemma viewMint (x:EvenA c M) (hp:Mint N lk φ q₀ Z x): ‖T0 x‖ ≤ ‖token c M φ x‖:=by
    have hφ:=zero_lt_one.trans_le hF.strength; let p:= burst q₀ Z; let y:= T0 x
    have h :∀ i:X1,1 ≤Stitch.Tablet.chip φ K1 (Spine I) i:=by rintro (i|i); exact hF.strength; exact le_rfl
    refine (Stitch.Tablet.minimal _ _ h _).trans (?_); change Stitch.Tablet.credits φ y ≤ _; exact (Stitch.Tablet.polite_bill Z _ hp.shows hφ).trans_le (Cupola.Well.pin p hφ hp.launch)
lemma gleam : ‖F! Z V‖ ≤ 1:=by
    obtain ⟨f,h,hX⟩:= earnestV L' d K H G U Γ Y A φ p' hF; rcases Z.eq_empty_or_nonempty with hZ|⟨x,hx⟩; · rw [hZ]; rw [absent L' d K H G U Γ Y A φ e χ V p' hF,norm_zero]; exact zero_le_one
    let k:=(lk) x -- macro
    let γ i:= game L' d K H G U Γ Y A φ e χ Z V i; let T:= (Tx); have hI:Summable γ:= gate_sum L' d K H G U Γ Y A φ e χ V p' hF Z
    let Ω:=(T0).toLinearMap.toContinuousLinearMap; have hv := hX k; have hB i:0 ≤ f i:= (norm_nonneg _).trans (h V i)
    unfold mage; change ‖Ω (∑' i,γ i)‖ ≤ 1; rw [Ω.map_tsum hI]; refine (norm_tsum_le_tsum_norm ((Ω.hasSum hI.hasSum).summable.norm)).trans ?_ -- root
    refine le_trans (Summable.tsum_le_tsum (?_) ((Ω.hasSum hI.hasSum).summable.norm) hv.2.1) hv.2.2; intro i; by_cases he:γ i=0; · change ‖Ω (γ i)‖ ≤_; rw [he,map_zero,norm_zero]; exact hv.1 i
    obtain ⟨hp,hk,hM,hg⟩:= aurea L' d K H G U Γ Y A φ e Z χ V p' hF hR hE i he
    let η:= lantern L'.L τ; let p:= T.stipendP p' η; change ‖Ω (γ i)‖ ≤ if k ∈seatP T.lightF i then p i * f i * currency B (α+1) _ else 0; rw [if_pos (hk (mem_image_of_mem _ hx))]; refine (viewMint L' d K H G U Γ Y A φ e Z χ p' hF hR hE _ hM).trans (?_) -- names
    rw [hg]; exact (h V i).trans (le_trans (le_mul_of_one_le_left (hB _) (stipendP_one T p' hF.haze hF.stout i)) (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans (stipendP_one T p' hF.haze hF.stout i)) (hB _)) (Real.one_le_exp (mul_nonneg (add_nonneg hF.bays.1.exp zero_le_one) (Nat.cast_nonneg _)))))
lemma ore (hv:∀ j∈e,∀ U:Grid f,Y.read O.threshold U j∈ QCD.Bera.vaultS univ ((Y.spine j).card*n))(j:Clusters (Tx).Bright): T0 (game L' d K H G U Γ Y A φ e χ Z V j) ∈vaultS univ (Z.card*n):=by
    unfold game; have hp(m:Finset E)(hm:m⊆e):=(bitterV L' d K H G U Γ Y A φ m (fun i hi'=>hv _ (hm hi')) hF.property (fun i hi'=>hE _ (hm hi')) j V χ (zero_lt_one.trans_le hF.strength) hF.favorable hR)
    split
    next he=>
        rw [← he.2]
        exact hp _ (filter_subset ..)
    rw [map_zero]; exact Submodule.zero_mem _
lemma lore (hv:∀ j∈e,∀ U:Grid f,Y.read O.threshold U j∈ QCD.Bera.vaultS univ ((Y.spine j).card*n)): F! Z V∈vaultS univ (Z.card*n):=by
   unfold mage; let L:= (T0).toLinearMap.toContinuousLinearMap; have hs:= gate_sum L' d K H G U Γ Y A φ e χ V p' hF Z; change L _∈ _; rw [L.map_tsum hs]; let Xv:= Bera.vaultS (univ:Finset X1) (Z.card*n)
   apply (Submodule.closed_of_finiteDimensional Xv).mem_of_tendsto (L.hasSum hs.hasSum|>.summable.hasSum)
   exact Eventually.of_forall (fun s=> Submodule.sum_mem Xv fun j _=> ore L' d K H G U Γ Y A φ e Z χ V p' hF hR hE hv j)

end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.lore
#print axioms YM.MassiveQCD.Apron.Grove.gleam
