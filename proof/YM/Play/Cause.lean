import YM.Play.Lair
import YM.Play.Hug
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
open Bera Oce Rot
local notation "QP"=> ((ContinuousLinearMap.restrictScalars ℝ) ((Cupola.pick K1 q₀ Z).comp (T0).toLinearMap.toContinuousLinearMap)) -- syntax
local notation "Sd" r=>skyM H Z' Zⁱ Y A φ inH Pf (allot r)
local notation "Ps" r:arg k:arg=> ((PS' r).taggedL k)
variable {u' v' a'c m₀:ℝ}{l t':ℕ}
set_option maxHeartbeats 500000 in
lemma reportsV (x:Patio (Keys c N⊕Spine I)) (he: ∀ i:ι+, Healthy (Pressure.temp τ) (i.val.biUnion Zⁱ) V)(h:∀ (r:Reserve (S')) (k: (Flight.visit L' K d).Choices), ‖QP (call (Ps r k) (Sd r))-x‖ ≤ v') : ‖parties (fun z=> F! z V) Z-x‖ ≤ v':=by
    let f r (k:(S').Choices):= call (Ps r k) (Sd r); rw [quilting L' d K H G U Γ Y A φ e Z χ V p' hF hR hE he]; let L:=QP; let g r:= choiceS (fun k=>f r k)
    change ‖L (choiceS (fun r=>g r))-x‖ ≤ _; rw [choiceS,map_smul,map_sum]; letI : Nonempty (Tree.Forest (S').ratio) := Tree.select (Flight.visit L' K d).ratio L'.odd -- notation
    apply choo; intro r; unfold g choiceS; rw [map_smul,map_sum]; apply choo; exact fun i=> h _ _

variable {A' G₀ J₁:Type}[Fintype G₀][Fintype J₁]
variable (Xv:Matrix G₀ J₁ ℂ)(Qv: YM.Next.Rank.Normal.Symmetric G₀) (Mx:Matrix (Keys f N⊕Spine I) (Keys c N⊕Spine I) ℂ)(Vp : Matrix (Keys f N⊕Spine I) (Keys f N⊕Spine I) ℂ)
variable (P0:Finset I→ Papers G₀ (Patio (Keys f N⊕Spine I)))(b₀:J₁→ℝ)
local notation "Φ"=>Chamber.switch P0 Xv Qv Mx Vp
local notation "Zq"=> Oce.rose X1 b₀
local notation "Φ*"=> Zq ∘ Φ
variable (g v':ℝ)
-- close to unscaled W.Weight.gappa.x. Then resize titles with σ∇. No mask is rebased here. 
lemma sinksV (h:∀ W⊆Z, W.Nonempty→ ‖parties (fun z=> F! z V) W - (Oce.rose X1 b₀ (shootsW Xv Qv Mx Vp (parties P0 W)))‖ ≤ v') (hp:∀ j∈e,∀ U:Grid f,Y.read O.threshold U j ∈ Bera.vaultS univ ((Y.spine j).card*n))(hZ:1 ≤ g)(hV:∀ i⊆ Z,i.Nonempty→ ‖(Φ*) i‖ ≤ g) (hz:‖u'-1‖ ≤ m₀)(he:0 ≤ v')(hx:Z.card ≤ l)(ht:‖u'‖ ≤ 2):
    ‖Plate.turn I u' (F! Z V)- (Φ*) Z‖ ≤ ((Z.card*n:ℕ)*m₀*(2:ℝ)^(Z.card*n)) + (Chamber.face l g+1)^l*v':=by
      let T V Z:= F! Z V; let W:= T V; have hp' := gleam L' d K H G U Γ Y A φ e Z χ V p' hF hR hE; have hs := (turnBills u' m₀ (Z.card*n) (W Z) (lore L' d K H G U Γ Y A φ e Z χ V p' hF hR hE hp) hz ht).2
      have hU:0 ≤ m₀:= (norm_nonneg _).trans hz; refine (norm_sub_le_norm_sub_add_norm_sub _ (W Z) _).trans (add_le_add (hs.trans (mul_le_of_le_one_right (?_) hp')) (?_)); · positivity
      let Ylam:= Φ* -- macro shadow
      have hT(c:Finset I):parties (Φ*) c= (Zq) (shootsW Xv Qv Mx Vp (parties P0 c)):=by
           let g i:= shootsW Xv Qv Mx Vp (parties P0 i); rw [show shootsW Xv Qv Mx Vp (parties P0 c)= parties (Φ) c from (carries g c (by unfold g; rw [hollow,alights])).symm]; unfold parties; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_prod]; rfl
      let Ak:=parties W; let Bk:=parties (Φ*) -- syntax B macro
      have hW : W=cetacea Ak:= funext fun i=> Chamber.only Ak W i (fun i _=>rfl) (absent L' d K H G U Γ Y A φ e χ V p' hF) i (Subset.refl i)
      have hK : Ylam = cetacea Bk:=by
          apply funext; intro i; apply Chamber.only Bk (Φ*) i (fun i _=> rfl) (?_) i (Subset.refl i); unfold Function.comp Chamber.switch; rw [cet]; simp
      have hS i (hi:i⊆Z) (hh:i.Nonempty): ‖Ak i - Bk i‖ ≤ v':=by unfold Bk; rw [hT]; exact h i hi hh
      change ‖W Z - Ylam Z‖ ≤ _; rw [hW,hK]; exact spentX (marksV _) _ _ Z hx hZ he (fun i hi hv=> by rw [←hW]; exact (gleam L' d K H G U Γ Y _ φ e i χ V p' hF hR hE).trans hZ) (fun i hi hv=> by rw [←hK]; exact hV i hi hv) hS -- later
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.sinksV
