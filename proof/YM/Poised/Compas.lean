import YM.Poised.Stride
import YM.MassiveQCD.Lyre.Solace
import YM.MassiveQCD.Lyre.Speed
import YM.MassiveQCD.Lyre.Gleam
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
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
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
variable (Z:Wound (roof (G.equip N (radiusB τ)) P₀ 30 (radiusB τ))) (hF: spent Z.val=∅)
include hF
local notation "sξ"=> (Y.markers Z.val)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
variable (D₁:ℕ) (hx: ( (lore (trimP T O δ β b)).activities.reg D₁).support= brimW (G.equip N (radiusB τ)) P₀ Z.val) (hs:x₂ ≤ x)(hv:0<x₂)(hf:0 < φ)
local notation "X₁"=> Brim.plate F' D₁
local notation "Tz"=> fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i
local notation "Ωv"=>prescription L' d K A φ (Y.markers Z.val) q'
variable (hp: Peak (G.equip N (radiusB τ)) O.threshold x₀ x x₁ (fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i))
variable (e:E)(hE:leftE Z.val={e})(hK:((lore (trimP T O δ β b)).activities.reg D₁).site = (P₀.row e).site) (hh:(Y.markers Z.val).Nonempty)
include hF hE hw hh hf
open Elevator
local notation "Φ₁"=> Elevator.tap (q:=q') (P:=P₀) Y e
variable {O₁:BudgetPoint} (F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b))) (hO₁:O.threshold=O₁.threshold)
variable (he:Sight (P₀.row e).support (P₀.row e).site 2 O₁ x₀ (Elevator.tap (q:=q') P₀ Y e) ι')
variable (hr:0≤a)(hπ:x*fingers N*z ≤ x₁*x₀)(hQ:∀ i,terra G N (radiusB τ) x₀ x i≤1)
variable (hy:coverNumber (radiusB τ) (Brim.plate F' D₁).support ≤radiusB τ) (hΩ:∀ U V, BeamRaw (brimW (G.equip N (radiusB τ)) P₀ Z.val) U V g₀ → beamAt (brimW (G.equip N (radiusB τ)) P₀ Z.val) U V z₀)(hz:0≤z₀)(hm:z₀<η/2) (hS: Sea L' d (radiusB τ) η ρ z O.threshold G.Z G.V 2) (hu:4*((fingers N*ρ)*x)≤ x₀/4) (hP:Plays N₀ E₀ B' O₁ P T τ)
local notation "φ₀"=>∏ i ∈ops Z.val,Tz i
include hO₁ hΩ hz hm hS hu hs hv H' hr hπ hy hP hx hp hQ hK he
set_option maxHeartbeats 500000 in
lemma compassA : let χ' := z₀/(η/2); let BI:= ∏ i∈ops Z.val,Real.exp 1*terra G N (radiusB τ) x₀ x i; let C:= ι'*BI; let t':= if ops Z.val=∅ then ι' else arid τ*C
    Indicia Tx B' N₀ F₁ χ E₀ g₀ (Sum.inl Z) D₁ t' (arid τ*C*((((hooks (F:=N) ((S').ratio) (coreW (G.equip N (radiusB τ)) P₀ Z.val)).card:ℝ)*(x₁*χ')+(ops Z.val).card*χ'))) (Hera.grandFee H'*t') x₂ (prescription L' d K A φ (Y.markers Z.val) q'):=by
    intro d' Wp Ck t'; constructor; intro fQ g VP Qt he' hV hZ v W₀ hW -- z₀ shadow.Erase. cup
    let Y₀:= G.equip N (radiusB τ); let p:= brimW Y₀ P₀ Z.val; let o' := (P₀.row e).site
    have hv':Healthy O₁.threshold p v:=by
       unfold p; unfold Y₀; exact hx ▸ hW
    let vK:=Stitch.Tablet.tunnel Y₀ Z.val; let Qz:= Qt.comp ((vK v).restrictScalars ℝ); let r:= Qz ∘ (Φ₁)
    have hsite: (X₁).site = (sliceL L' d).parent o':=by change (sliceL L' d).parent _ = (sliceL L' d).parent _; rw [hK]
    have hh':Tone Vx (G.equip N (radiusB τ)) P₀ Z.val (.inl Z):=sameT L' d K H G U Γ _ hF; have hw':rootBill ((sliceL L' d).parent o') x Qt:=fun i=> by rw [←hsite]; exact (hV i).trans (QCD.Stew.future _ hv.le hs _)
    have ht' UF HG VG:= bore G P₀ O₁ Z.val e (hO₁ ▸ hp) hE Φ₁ he Qt hw' v hv' (Malachite.radiusD τ) hr hπ hQ UF HG VG hz hm (aboard (Vx) P₀ G Z.val D₁ hh' F' hx e hK hy)
    obtain ⟨hz,hW,hSet,hV'⟩:= ht' v hv' (hΩ v v (fun i _ _=> by rw [mul_inv_cancel,su.chord_one]; exact he')) -- ht' hV etc shadow
    have hN:O₁.supBounds o' p r t':=by
       unfold t'; split; next hQ=> exact grand G P₀ O₁ Z.val _ (hO₁ ▸ hp) hE Φ₁ he Qt hw' v hv' ρ (hO₁ ▸ hS) hQ hu -- argument order
       have hx:arid τ * Ck=((arid τ)*Wp)*ι':=by unfold Ck; ring
       rw [hx]; exact hW
    refine ⟨r,hx.symm ▸ hz.sites,hSet,?_,?_,?_⟩
    · intro U hU; exact hN.2 U (by unfold p Y₀; exact hx ▸ hU) [] (by simp) (by simp)
    · intro i hi hv
      rw [exposedAt L' d K H G U Γ Y A φ Z hF hw hf e hE hh _ _  (hO₁.symm ▸ hx ▸ hi)]; apply le_trans ((ht' i (hx ▸ hi) (hΩ i v (hx ▸ hv))).2.2.2); unfold Ck Wp d'; rw [show (S').ratio=sliceL L' d from rfl]; apply le_of_eq; ring
    have hg:0< gStep β:= inv_pos.mpr (Real.sqrt_pos.mpr (F'.laws.intake.positive)); exact Hera.guise H' (mapcase F₁ D₁ fQ) _ (hx.symm ▸ hz) (hK.symm ▸ hx.symm ▸ hN) W₀.anchor hP hZ hg.le _ (guard_silent χ hg (mul_pos E₀.guards O₁.threshold_pos)) _ _ _ _
end YM.MassiveQCD.Lyre
