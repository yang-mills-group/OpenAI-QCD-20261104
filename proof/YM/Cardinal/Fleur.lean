import YM.Cardinal.Pockets
import YM.MassiveQCD.Cupola.Garden
/-! # Footprints on every mark of a Root-Fleet with monotone projection.
 Each E letter retains full angular orientation in hue space.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom.Fleet
open ConnectedActivityE6 Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets Horticulture Mixed Reserves Trees Beam Cove Leaf Lat PhysicalNext.Repeat.Greenbelt MassiveQCD MassiveQCD.Cupola MassiveQCD.Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical PhysicalNext.Repeat.Greenbelt
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β τ μ W C:ℝ} {R:Rep su f}{F Z:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι I:Type}{N:ℕ}
local notation "W'"=> Pipe.Clump S ι
variable (N)[Fintype I](p:I→Site c)(φ:ℝ)(q:I→Bool)(Y:Fleet H ι (ample N I))
local notation "M"=> Ribbon.ample N I
local notation "mk"=> Mint N p φ q
local notation "wk"=> Well N p φ q
set_option quotPrecheck false
open Art Blaze Polar Shield Frond
open Grass Cove Lat GasP Filter Ursell Graph
open Sway OrbitG Villa Loom Bay Strut Patron
open MassiveQCD.Cupola
variable (D:ι→Finset I)
variable (h:Regal N p φ q Y D) (hp:0<φ)
open MassiveQCD.Plate MassiveQCD.Plate.Card
variable (Pᵢ:I→Support c)(ht:∀ i,D i⊆ atlas Pᵢ (Y.ground i))
include ht
lemma scentP (s:Pipe.Clump S ι) : deathT D s ⊆ atlas Pᵢ (Y.fullA s):=by
   intro i hi; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp hi; exact atlasNear Pᵢ (subset_biUnion_of_mem (Sum.elim H.supportP Y.ground) (mem_toRight.mp hj)) (ht _ hi)
lemma scentAll (s:Clusters Y.Bright) : swingE N Y D s ⊆ atlas Pᵢ (seatP Y.lightF s):=by
   intro i hi; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp hi; exact atlasNear Pᵢ (subset_biUnion_of_mem (Y.lightF ∘ s.2) hj) (scentP N Y D Pᵢ ht _ hi)
variable (he:Y.Famous)
include he hp h
lemma blossom (χ:Chi) : Gully N p q φ Pᵢ (claim Y χ):=by
    refine ⟨fun i V=>?_⟩; let F:= claim Y χ; let w:= (F.addr i).place; let a:= atlas Pᵢ w; let v:= ValidPieces (Keys c N) q a; let X:= Y.broad; let u:= withdraw N p φ; change v (u (mission Y χ V i.val)); unfold mission motto; split; swap; · rw [map_zero]; exact ValidPieces.noneV
    rw [map_prod]; -- apply
    rcases i with ⟨i,hi⟩; apply Subalgebra.prod_mem (ValidPieces.course q a) -- dependency i local let
    intro j hj; have hz:facesP Y.broad j⊆w:= subset_biUnion_of_mem (facesP Y.broad) hj; rcases j with j|j
    · exact ValidPieces.role _ (markets N p φ q Y D h hp j.val χ V).shows ((scentP N Y D Pᵢ ht j.val).trans (atlasNear Pᵢ hz))
    change v (u (NormedSpace.exp (-portion ..)-1)); let d :Clusters Y.Bright→ EvenA c M:= fun s=> if seatP Y.lightF s=j then Y.honest χ V s else 0; have hS(s:Clusters Y.Bright): v (u (d s)):=by
        unfold d honest; split
        next hh=> by_cases he:Healthy (Pressure.temp τ) (seatP Y.lightF s) V; · rw [masked_eq _ _ _ _ he]; exact ValidPieces.role _ ((swingM N p φ q Y D h hp χ V s).shows) ((scentAll N Y D Pᵢ ht _).trans (atlasNear Pᵢ (hh.symm ▸ hz))) -- `facesP` reducible? 
                  rw [masked_ne _ _ _ _ he,map_zero]; exact ValidPieces.noneV
        next _=> rw [map_zero]; exact ValidPieces.noneV
    rw [map_sub,NormedSpace.map_exp u u.toLinearMap.toContinuousLinearMap.continuous,map_one,map_neg,sub_eq_add_neg]; apply ValidPieces.plus _ ValidPieces.oneV.minus; apply ValidPieces.exponent; apply ValidPieces.minus; rw [show portion Y.lightF (Y.dawnV χ V) j=∑' s,d s from (by unfold portion d; simp_rw [phoenix Y χ V he]; rfl)]
    by_cases hf:Summable d; swap; · rw [tsum_eq_zero_of_not_summable hf,map_zero]; exact ValidPieces.noneV
    exact ValidPieces.tab (u.toLinearMap.toContinuousLinearMap.hasSum hf.hasSum) hS
end YM.QCD.Loom.Fleet
set_option autoImplicit false
namespace YM.MassiveQCD.Cupola
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
local notation "d!"=> (vacR I' (Keys c N)).comp (withdraw N loc φ)
local notation "Fuel"=> Pipe.Clump S' (Wound (Zⁱ)⊕ Varn f c⊕ Gaze c)
variable (q':I→Bool)
local notation "R₁"=> Sum.elim (fun (u:Wound (Zⁱ)) => Y.markers u.val) (fun _:Varn f c ⊕ Gaze c=>∅)
variable {χ:Chi}{θ t:ℝ}{m₁ m₂:ℕ}
variable (hx:Neat Y)(he:Supplies L' d K H G U Γ Y A φ χ q' θ t m₁ m₂)
open MassiveQCD.Plate MassiveQCD.Plate.Card
local notation "S²"=> Wound Zⁱ ⊕ Varn f c ⊕ Gaze c
-- guaranteed common halos
noncomputable def budAtlas (a:I→Site c)(k:ℕ)(i:I): Support c:=halo k ({a i})
local notation "Xz"=> budAtlas loc (30*radiusB τ)
include he
lemma twisted (u:S²) : (R₁) u ⊆ atlas Xz ((Tx).ground u):=by
   rcases u with u|u; swap; · exact empty_subset _
   intro i hi; refine mem_filter.mpr ⟨mem_univ _,?_⟩; intro j hj; have hx: A i ∈ brimW Z' P₀ u.val:= native_sub _ _ _ ((Y.extent (G.equip N B) he.property u.val) (mem_image_of_mem A hi)); obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hx
   change j∈ u.val.biUnion Zⁱ; refine mem_biUnion.mpr ⟨_,hk, Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr (mem_image_of_mem _ (mem_union_left _ hz))) hj⟩
lemma wingSpan (s:Clusters (Tx).Bright): swingE N (Tx) R₁ s ⊆ atlas Xz (seatP (Tx).lightF s):= scentAll N (Tx) R₁ Xz (twisted L' d K H G U Γ Y A φ q' he) _
lemma flex : Gully N loc q' φ Xz (claim Tx χ):=blossom N loc φ q' Tx R₁ (intent L' d K H G U Γ Y A φ q' he) (zero_lt_one.trans_le he.strength) Xz (twisted L' d K H G U Γ Y A φ q' he) he.title.favorable χ
end YM.MassiveQCD.Cupola
#print axioms YM.MassiveQCD.Cupola.flex
