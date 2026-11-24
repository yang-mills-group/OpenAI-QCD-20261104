import YM.MassiveQCD.Lyre.Solace
import YM.MassiveQCD.Charter.Plural
import YM.QCD.Purse.Debit
import YM.MassiveQCD.Plate.Slip
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

local notation "sξ"=> (Y.markers Z.val)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
variable (D₁:ℕ) (hx: ( (lore (trimP T O δ β b)).activities.reg D₁).support= brimW (G.equip N (radiusB τ)) P₀ Z.val) (hs:x₂ ≤ x)(hv:0<x₂)(hf:0 < φ)
local notation "X₁"=> Brim.plate F' D₁
local notation "Tz"=> fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i
local notation "Ωv"=>prescription L' d K A φ (Y.markers Z.val) q'
variable (hp: Peak (G.equip N (radiusB τ)) O.threshold x₀ x x₁ (fun i=>Real.exp 1*terra G N (radiusB τ) x₀ x i))
open Filter Ac Cupola Elevator
variable (hB:B'.B=radiusB τ)(hL:Works P L'.L τ (L'.visit K d) T)(hP:Plays N₀ E₀ B' O P T τ)
variable {g'' θ kal α v₂ p₁ p₂ g W₀ W₁ ψ Y₂ θ' mm:ℝ}
-- price tags before using SMART tilt signal.Front Ω political. Monic receipts.
variable (hW:News P L'.L τ W Q o μ C n N₀ E₀ χ B'.power p₁ p₂ g₀ (L'.visit K d).patch)
variable (hΓ:Seats H χ)(hy:coverNumber (radiusB τ) (Brim.plate F' D₁).support ≤radiusB τ)
variable (Ω:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c)
variable (hxP:(vantage L' d K H G U Γ Y A φ).Famous)(hzQ:Colored (vantage L' d K H G U Γ Y A φ))
local notation "J!"=>(vantage L' d K H G U Γ Y A φ).Bright
variable {qc:(vantage L' d K H G U Γ Y A φ).Bright}
variable (hN:Sands.Aliased (vantage L' d K H G U Γ Y A φ) qc (.inl Z))
variable (hV:Sight ((vantage L' d K H G U Γ Y A φ).fullA qc.val) (Brim.plate F' D₁).site 2 B' x₂ ((prescription L' d K A φ (Y.markers Z.val) q') ∘ (crude (vantage L' d K H G U Γ Y A φ) χ Ω).view (individual qc)) Y₂)
local notation "H★"=> (prescription L' d K A φ (Y.markers Z.val) q') ∘ (crude Tx χ Ω).view (individual qc)
variable {P₁:Plan j}
variable (hC: Coins B' O P L'.L E₀ Q.halo N₀ H' τ β x₀ x η h a z₀ z a' h p₁ g₀ θ' mm p₂ x₁ x₀ θ P₁ N m) (hY:Y.Coins σ Φ x₀ O.threshold)
variable (hk: Trees.Ready (QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ Q.halo (radiusB τ)) (radiusB τ) (paidSet (G.equip N (radiusB τ)) P₀ (fun i=> Real.exp 1*terra G N (radiusB τ) x₀ x i) σ Φ x₁ (cashM L'.L θ τ) W₀ 1) α v₂ p W₁)(hD:1 ≤ cashM L'.L θ τ)
local notation "ψ₁"=> cashM L'.L θ τ
local notation "p!"=> paidSet (G.equip N (radiusB τ)) P₀ (Tz) σ Φ x₁ ψ₁ W₀ 1
open Warmlet
local notation "D§"=> Sum.elim (fun u:Vⁱ=> Y.markers u.val) (fun _:Varn f c⊕ Gaze c=> ∅)
local notation "F§"=> Warmlet H HP (Z') P₀
local notation "Q§"=> QCD.Jets.Touch.roof (G.equip N (radiusB τ)) P₀ Q.halo (radiusB τ)
variable (Z: Warmlet H (united (VarnC H U N) (sailP H Γ N)) (G.equip N (radiusB τ)) P₀)
local notation "F★"=> perch H HP (Z') P₀ F' Z
local notation "Z★"=> Z.label
local notation "m0"=> Y.markers (Z.label.val)
local notation "l0"=> Z.code
omit [Countable E][Countable J] in
lemma area_stamp : (Tx).fullA Z.code.val=past H HP (Z') P₀ Z:= (cottage Tx Z.code (.inl Z.label) Z.earns).2
section general
variable {βx:Type}
local notation "E'!"=> (Ribbon.ample N I)
variable (F:Fleet H βx (Ribbon.ample N I)) (kx:βx→Finset I)
omit [Countable E][Countable J] in
lemma stamp_one (x:F.Bright)(i:βx)(hx: Aliased F x i):swingE N F kx (individual x)=kx i:=by
    change univ.biUnion (fun _:Option (Fin 0)=> deathT kx x.val)=_
    have hz:x.val.toRight={i}:=by rw [show x.val=_ from hx]; ext; simp
    simp only [deathT,hz,Finset.singleton_biUnion]; apply Finset.ext; intro i; constructor; exact fun h=>by obtain ⟨i,-,hd⟩:=Finset.mem_biUnion.mp h; exact hd
    intro hd; exact Finset.mem_biUnion.mpr ⟨none,mem_univ _,hd⟩
end general
omit [Countable E][Countable J] in
lemma name_stamp : swingE N Tx D§ (individual l0)= Y.markers Z.label.val:=stamp_one L' d K H Tx D§ Z.code (.inl Z.label) Z.earns
lemma vFare (x:Lat.Fields c N): Kites.engine 1 (Keys c N) x=x:=by apply poster; intro i; rw [Kites.fundW]; simp
local notation "rⁱ"=> individual Z.code
local notation "x§"=> prescription L' d K A φ m0 q'
variable {tΦ:ℝ}(hSup: Supplies L' d K H G U Γ Y A φ χ q' tΦ s B'.order B'.power)
include hSup hB
open Kites
set_option maxHeartbeats 350000 in
lemma littered (hr: B'.threshold=Pressure.temp τ)(hΩ:∀ i,(Ω i).support=GasP.seatP (Tx).lightF i): ∃ D:ℝ,Sight ((vantage L' d K H G U Γ Y A φ).fullA Z.code.val) (F★).site 2 B' φ (x§ ∘ (crude Tx χ Ω).view rⁱ) D:=by
     have hs:=zero_lt_one.trans_le hSup.strength; let o' :=(F★).site; let Q':=(Tx).fullA Z.code.val; have he: o'∈ past H HP (Z') P₀ Z:= (plateK H HP (Z') P₀ F' Z).2.1; have hg:=area_stamp L' d K H G U Γ Y A φ Z
     obtain ⟨h,h'⟩:=cottage Tx Z.code (.inl Z.label) Z.earns; have hX:(Ω (rⁱ)).support=Q':=(hΩ rⁱ).trans (h.trans h'.symm); have hv:o'∈ Q':=by unfold Q'; rw [hg]; exact he
     obtain ⟨g,hg,hP⟩:= mint_title N φ Tx χ Ω hΩ hs hSup.sharp hB hr; let X:RegularAddress c:=⟨o',Q',hv⟩; have hc := hg rⁱ o' (hX.symm ▸ hv); rw [hX] at hc
     let fΩ:=(crude Tx χ Ω).view rⁱ; have hw m : Mint N loc φ q' m0 (fΩ m):= (name_stamp L' d K H G U Γ Y A φ Z) ▸ crudeM N loc φ q' Tx D§ (Cupola.intent L' d K H G U Γ Y A φ q' hSup) hs χ m rⁱ Ω
     have hj:= invoice m0 loc q' φ fΩ X hs hc hw zero_lt_one hs (by rw [one_mul]) 2; simp_rw [Plate.turned,vFare] at hj; exact ⟨_,hj⟩
end YM.MassiveQCD.Lyre
