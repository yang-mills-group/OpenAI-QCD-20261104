import YM.MassiveQCD.Lyre.Affair
import YM.MassiveQCD.Lyre.Revenue
import YM.Poised.Laurel
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
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ w mm :ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ w mm f))
variable (G:Sun L' c f d η h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ w mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ w mm f)) W' P' h η a u v i)
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
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim Warmlet
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
local notation "Tz"=> fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i
variable (hp: Peak (G.equip N (radiusB τ)) O.threshold x₀ x x₁ (fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i))
open Filter Ac Cupola Elevator
variable {O₁:BudgetPoint}(F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b))) (hO₁:O.threshold=O₁.threshold)(hO:O.B=O₁.B)
variable (hB:B'.B=radiusB τ)(hL:Works P L'.L τ (L'.visit K d) T)(hP:Plays N₀ E₀ B' O₁ P T τ)
variable {g'' θ kal α v₂ p₁ p₂ g W₀ W₁ ψ Y₂ θ':ℝ}
variable (hW:News P L'.L τ W Q o μ C n N₀ E₀ χ B'.power p₁ p₂ g₀ (L'.visit K d).patch)
variable (hΓ:Seats H χ)
variable (Ω:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c)
variable (hC: Coins B' O₁ P L'.L E₀ Q.halo N₀ H' τ β x₀ x η h a z₀ z a' h p₁ g₀ θ' mm p₂ x₁ x₀ θ P₁ N m) (hY:Y.Coins σ Φ x₀ O.threshold)
variable (hk: Trees.Ready (QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ Q.halo (radiusB τ)) (radiusB τ) (paidSet (G.equip N (radiusB τ)) P₀ (fun i=> Real.exp 1*terra G N (radiusB τ) x₀ x i) σ Φ x₁ (cashM L'.L θ τ) W₀ 1) α v₂ 1 W₁)(hD:1 ≤ cashM L'.L θ τ)
local notation "ψ₁"=> cashM L'.L θ τ
local notation "p!"=> paidSet (G.equip N (radiusB τ)) P₀ (Tz) σ Φ x₁ ψ₁ W₀ 1
open QCD.Brick
variable (e:E)
variable (hι:∀ i, σ i ≤ chip L'.L τ)
variable (hπ:x*fingers N*z≤ x₁*x₀)(hQ:∀ i,terra G N (radiusB τ) x₀ x i≤1)
variable (hS: Sea L' d (radiusB τ) η ρ z O.threshold G.Z G.V 2)(hhρ:4*((fingers N*ρ)*x) ≤ x₀/8)
open QCD.Dust
variable (G':Sun L' c f d η h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ w 0 f)))
local notation "F§"=> Warmlet H HP (Z') P₀
local notation "X§" p=> perch H HP (Z') P₀ F' p
local notation "G§" p=> trunkP H HP (Z') P₀ F' p
local notation "f0"=> fern L'.L ^ 5
local notation "I§" p=> Elevator.tap (q:=q') P₀ Y p
local notation "u§" p=> (P₀.row p).support
local notation "s§" p=> (P₀.row p).site
local notation "Y?" p=> prince H HP (Z') P₀ p
local notation "X?" p=> Small H HP (Z') P₀ p F'
local notation "x§" p=> col H HP (Z') P₀ p
-- Semantic task Hand as k predictor ANY marked aperture.
structure Patrol (χ:Chi)(P:BudgetPoint)(x α k:ℝ)(q':I→Bool)(f:E→ℝ):Prop where
  earn : ∃ g:F§→ℝ,Ac.Hit (fun i:F§=> (trunkP H HP (Z') P₀ F' i).support) (radiusB τ) g α k ∧ ∀ (Z:F§)(p:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c), (∀ i,(p i).support=GasP.seatP (Tx).lightF i) → (Y.markers Z.label.val).Nonempty → Small H HP (Z') P₀ Z F'→
     let v:=(perch H HP (Z') P₀ F' Z); let f':= (prescription L' d K A φ (Y.markers Z.label.val) q') ∘ (crude Tx χ p).view (individual Z.code)
     (∀ e:E,leftE Z.label.val={e}→Sight (P₀.row e).support (P₀.row e).site 2 O₁ x (Elevator.tap (q:=q') P₀ Y e) (f e)) → ¬ prince H HP (Z') P₀ Z → Sight v.support v.site 2 P φ f' (g Z)
local notation "Φ₁"=> tiltPot L'.L
local notation "Υ"=> wageP H HP (Z') P₀ F' (ψ₁) (caseT N₀ H' B' L'.L τ) (p!)
-- binder text common χ flags
variable {Ξ ο u₀ Y₁:ℝ}(hΞ:Warp L'.L (P₀.row e).site ((sliceL L' d).parent (P₀.row e).site) (ply L' d) N x₀ x ψ Ξ) (hΦ:Coins B' O₁ P L'.L E₀ Q.halo N₀ H' τ β x₀ x η h a z₀ z a' h p₁ g₀ θ' mm p₂ x₁ x₀ θ P₁ N m)
variable (hε:0 ≤ α)(ht':2*W₁<1)(hV: (caseT N₀ H' B' L'.L τ*(cashM L'.L θ τ)⁻¹)*(2*v₂*(2*W₁)^1*(1-2*W₁)⁻¹) ≤ kal)
variable {t ν:ℝ}(hSup:Supplies L' d K H G U Γ Y A φ χ q' t ν B'.order B'.power)
variable (hr':1 ≤ φ)(ht:φ ≤ x)(he:0≤ρ)(ha:0<a)(hF:fareG 1 φ N ≤ x)(hm:|mm|≤haloK L'.L τ)(hJ:5 ≤ n)(hς: (radiusB τ)+1 ≤ O.B+O.B)
include hp hB hL hP hΓ hC hY hk hD hι hπ hQ hS hhρ
include F₁ hO₁ hO hW hε ht' hV hSup ht ha
-- CASH.
set_option maxRecDepth 2600 in
set_option maxHeartbeats 690000 in
lemma windowP : Patrol (O₁:=O₁) L' d K H G U Γ Y A φ F' χ B' x₀ α kal q' σ:=by
    have hx:= hSup.room.2; have hw:= hSup.property; have hχ:= hSup.title; have h'A:=hχ.favorable; have h'H:= hχ.color; have hσ:=zero_lt_one.trans_le hSup.strength
    refine ⟨Υ, fun i=>budget_loosen ((getsWage H HP (Z') P₀ F' hk ht' (zero_lt_one.trans_le hD) ((by norm_num : (0:ℝ)≤2).trans (caseN ..)) hε) i) hV,?_⟩; intro Z p hψ hZ hY' v' f'; let r:= Z.label; let o':=oath H HP (Z') P₀ Z; obtain ⟨hT,hF',-⟩:=Classical.choose_spec (oak H HP (Z') P₀ Z)
    have hU : spent (Z.label.val)=∅:=Warmlet.stop H HP (Z') P₀ Z
    obtain ⟨Λ,hX⟩:= littered L' d K H G U Γ Y A φ F' hB p Z hSup hP.rehearsed.temp_eq hψ -- order
    intro hΞ hψ; let u:= (Z.label.val); have hv' : (leftE (Z.label.val)).Nonempty:=by
       apply Finset.nonempty_iff_ne_empty.mpr; intro h
       simp only [Stitch.Tablet.markers,h,hU,biUnion_empty, union_empty, Finset.not_nonempty_empty] at hZ
    have hδ : 1 ≤ (leftE (Z.label.val)).card:= Finset.card_pos.mpr hv'; have hM:= congr_arg Finset.card (pinch u); unfold pin at hM; rw [card_disjSum,card_disjSum] at hM
    by_cases hp' : 2 ≤ (leftE (Z.label.val)).card
    · rw [wageP,if_pos ⟨hY', by change 2 ≤ u.card; change 2 ≤ (leftE u).card at hp'; omega⟩]; exact laurelsA L' d K H G U Γ Y A φ F' Z.label hU hw hx H' o' hT ht hσ hσ hp F₁ hO₁ hB hL hP hW hΓ hY' p h'A h'H Z.earns hX hC hY hk hD hp'
    obtain ⟨i,hΨ⟩:= Finset.card_eq_one.mp (show (leftE (Z.label.val)).card=1 by omega); have hy:ops u≠∅:= fun h=>hψ ⟨_,(slate H HP (Z') P₀ Z i).mpr ⟨hΨ,h⟩⟩
    rw [wageP,if_pos ⟨hY',by change 2 ≤ u.card; have hr:1 ≤ (ops u).card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hy); change 1≤ (leftE u).card at hδ; omega⟩]; exact pulseTwo L' d K H G U Γ Y A φ F' Z.label hU hw H' o' hT ht hσ hσ hp F₁ hO₁ hO hB hL hP hW hΓ hY' p h'A h'H Z.earns hX hC hk hD _ hΨ (hF' i hΨ) hZ (hΞ i hΨ) (hι _) ha.le hπ hQ hS hhρ hy le_rfl
end YM.MassiveQCD.Lyre
