import YM.Poised.Agate
import YM.Poised.Vaults
import YM.Poised.Harp
import YM.Poised.Watch
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
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f 6 E J} [Countable E][Countable J]
variable {P₁:Plan j}{a₀ b₀ a₁ b₁ w mm vP:ℝ}{E₁:Offer 1 a₀ a₁}{E₂:Offer 2 b₀ b₁}
local notation "Xγ"=> (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))
variable (G:Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f))) (U :Swathe L' d (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) mm f)) W' P' h (coneK L'.L vP τ) a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample 6 I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip 6 (radiusB τ)
local notation "Zⁱ"=> roof (G.equip 6 (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip 6 (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U 6)
local notation "X'" => loommark I (sailP H Γ 6)
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Vx"=> tableau L' d K P₀ H G U Γ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
set_option quotPrecheck false
local notation "loc"=> ((S').ratio.parent ∘ A)
local notation "Β" => Ribbon.banknote 6 loc φ
local notation "I'"=> Ribbon.Spine I
local notation "mx"=> Keys c 6 ⊕ Ribbon.Spine I
open Cupola Plate Spice Shells Sands Phased -- inspect
variable (F':Cash W τ μ L'.L Q o C T (lore (trimP T O δ β b)))
local notation "V₁"=> withdraw 6 loc φ
local notation "HU"=> VarnC H U 6
local notation "HP"=> united (VarnC H U 6) (sailP H Γ 6)
local notation "Vⁱ"=> Wound (roof (G.equip 6 (radiusB τ)) P₀ 30 B)
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim Warmlet
variable {N₀:Libretto su n}{E₀:Heir.Record}{μ':Tr f→ℝ}{σ: E→ℝ}{Φ:J→ℝ}{x x₀ x₁ x₂ z₀ κ' ρ g₀ ι':ℝ}{χ:Chi}{B':BudgetPoint}{q':I→Bool}
variable (hw:Y.Wave O.threshold q' A) (htB:0<radiusB τ) (H': Hera.Rights su n)
local notation "Tz"=> fun i=>Real.exp 1*terra G 6 (radiusB τ) x₀ x i
open Cupola Elevator Massive.Poised Massive.Poised.Pipes Ac Cove.Send
variable {O₁:BudgetPoint}(F₁:Cash W τ μ L'.L Q o C T (lore (trimP T O₁ δ β b))) (hO₁:O.threshold=O₁.threshold)(hO:O.B=O₁.B)
variable (hB:B'.B=radiusB τ)(hL:Works P L'.L τ (L'.visit K d) T)(hP:Plays N₀ E₀ B' O₁ P T τ)
variable {Kq Φ₁ U₂ Dd Gd Gh Gn:ℕ}
variable (G':Sun L' c f d (coneK L'.L vP τ) h z a a' m (pesto P₁ L' d (trunkM E₁ E₂ (haloK L'.L τ) 0 f)))
variable (A₀ A₁ A₂ :ℝ)(hH:1≤A₀)(hα:B'.power=Kq)(hg:O₁.power=Gh)
variable (hr: Diary N₀ P j k Gh Gd Dd A₀ A₁ A₂)
variable (hn:6 ≤ n)(hD:Gn≤O₁.order)(hG:Gd≤Gn+1)(hW:Gd ≤ 2*n)(hk:2 ≤ Dd)(hQx:Gd ≤ U₂)
variable (hξ : O₁.threshold = fiery su τ L'.L)(hOc:O₁.B= highR L'.L τ)(hT:betaF su τ L'.L/2 ≤ β) (hX:2*(radiusB τ+1)< f.val)(ha:0<a)(hh':|mm| ≤ haloK L'.L τ)
variable {t ν:ℝ}(hSup:Supplies L' d K H G U Γ Y A φ χ q' t ν B'.order B'.power)
local notation "F§"=> Warmlet H HP (Z') P₀
variable (Z: Warmlet H (united (VarnC H U 6) (sailP H Γ 6)) (G.equip 6 (radiusB τ)) P₀)
variable (w:Clusters (vantage L' d K H G U Γ Y A φ).Bright → RegularAddress c)(hw':∀ i,(w i).support=GasP.seatP (vantage L' d K H G U Γ Y A φ).lightF i)
variable (e:E)(hE:leftE Z.label.val={e})(hq: ops Z.label.val=∅)(hp:(Y.markers Z.label.val).Nonempty)(h'Q: Seats H χ)
variable (Xb: Cover)(hY:wrap f Xb=(P₀.row e).site)(hU:φ ≤ A₀*x₀)(hΦ:0 < x₀)(hΘ: Flame (Elevator.tap (q:=q') P₀ Y e) O₁ (P₀.row e).support (P₀.row e).site x₀ Dd U₂ κ')
variable (S0:ℕ)(t0:ℝ)
variable (hV': Menus P₁ N₀ E₀ Kq Gh Dd U₂ k A₀ (pup Gd A₁+pup Gd A₂) H' Q (Flight.visit L' K d).patch L'.L W o μ C a vP h z a' m χ τ S0 t0)
variable (ht': O₁.B ≤ 2*radiusB τ)(hτ: coverNumber O₁.B (brimW (G.equip 6 (radiusB τ)) P₀ Z.label.val)≤ S0)
-- preserve price via porch
local notation "Sγ"=> Warmlet.perch H HP (Z') P₀ F' Z
local notation "nv"=> coverNumber O₁.B (brimW (G.equip 6 (radiusB τ)) P₀ Z.label.val)
include G' H' hO₁ hP hB hL F₁ hH hα hg hr hV' hn ht' hτ hξ hT hX ha hh' hp hSup hw' hE hq hΦ h'Q hΘ hY hU
local notation "Xm"=> Tx
-- pays.Scalar equality Mark.P.Act.
set_option maxHeartbeats 880000 in
lemma powerQ (hSmall:Warmlet.Small H HP (Z') P₀ Z F')(α:Directions su c)(j' d0:ℕ) (hr':j'<n)(htd:d0<U₂)(hP0:B'.dirBound (Sγ).site α)(hα':‖α‖ ≤ Brim.canopyW su L'.L B'.power τ) :
    let p₀:=List.replicate j' α; let Q:=(Massive.Poised.Pipes.mantel d0) ∘ Elevator.tap (q:=q') P₀ Y e; let Ft:=Massive.Poised.Pipes.framesF (purseX (Sγ).site Dd φ); let T₀:= (prescription L' d K A φ (Y.markers Z.label.val) q') ∘ (crude Tx χ w).view (individual Z.code)
    ‖leftDerivs (Ft ∘ (Massive.Poised.Pipes.mantel d0) ∘ T₀) p₀ 1-leftDerivs (Ft ∘ Fountain.cherub T (flareV (proton L' d)) Q) p₀ 1‖ ≤ t0*κ':=by
    intro l fQ Ft T₀
    have htP:B'.threshold ≤ 2 * O₁.threshold:= by rw [hP.rehearsed.temp_eq]; exact hP.rehearsed.tensions.coarse
    let p:= Warmlet.oath H HP (Z') P₀ Z; have hstop:= Warmlet.stop H HP (Z') P₀ Z
    obtain ⟨hZ,hZ',hv⟩:=Classical.choose_spec (Warmlet.oak H HP (Z') P₀ Z)
    let s:=(P₀.row e).site; let F:= Elevator.tap (q:=q') P₀ Y e; let S:= (P₀.row e).support; let X:= (lore (trimP T O₁ δ β b)).activities.reg p
    have he:X.site=s:= hZ' _ hE; have hr':X.support=brimW (Z') P₀ Z.label.val:= hZ; let g:= prescription (N:=6) L' d K A φ (Y.markers Z.label.val) q'; have ht : 0 < φ:= zero_lt_one.trans_le hSup.strength; have hw:= hSup.property
    have hφ (k:Frame f)(Uw:Grid f): slots 6 k (F (Lattice.gauge k Uw))=F Uw:=by
       have hp:= hw.turnsE e Uw k
       let i:= burst q' (Y.spine e); change slots 6 k (scrape _ i _)= scrape _ i _; exact (wing _ _ _ _).symm.trans (congr_arg _ hp)
    have hGK (f':Grid f) (X:Lat.Fields f 6): Stitch.Tablet.tunnel (Z') Z.label.val f' X=changeVars ((Z').shortP f') X:= by rw [Stitch.Tablet.tunnel,show axle (Z') f' Z.label.val=1 from by simp [Cove.axle,hq]]; exact Spice.echo (sliceL L' d) _ _
    have hδ(Uw: Grid f)(hx : Healthy O₁.threshold X.support Uw)(V:Grid c): g ((Tx).works (.inl Z.label) Uw V)=changeVars ((Z').shortP Uw) (F Uw):=by
        rw [← hGK]; exact exposedAt L' d K H G U Γ Y A φ Z.label hstop hw ht e hE hp V Uw (hO₁.symm ▸ hZ ▸ hx)
    have hC (W:Grid f)(k:Frame c) (_ : Healthy O₁.threshold X.support W): let J:= k ∘ (sliceL L' d).parent; let V:= Lattice.gauge J W; slots 6 k (changeVars ((Z').shortP V) (F V))=changeVars ((Z').shortP W) (F W):=by
       intro J V; have hk:J ∘ (sliceL L' d).embed=k:= funext fun x=>congr_arg k ((sliceL L' d).embed_parent x); rw [← hGK,← hGK]; exact ((congr_arg (fun J=> slots 6 J (Stitch.Tablet.tunnel (Z') Z.label.val V (F V))) hk).symm.trans (Stitch.Tablet.drivesAtG (Z') W J (Stitch.Tablet.tonal G 6 B) Z.label.val (F V))).trans (congr_arg _ (hφ J W))
    have hZs: halo (radiusB τ+1) S ⊆ X.support:=by rw [hr',brim_eq]; exact Corona.halo_mono le_rfl (Spice.leafSub G P₀ Z.label.val _ hE)
    let p':=Sγ; let Xq:= g ∘ (crude Tx χ w).view (individual Z.code); have hxI:wrap f Xb=X.site:=hY.trans he.symm; have hg0:p'.site=(sliceL L' d).parent X.site:=rfl
    obtain ⟨D,hD0⟩:= littered L' d K H G U Γ Y A φ F' hB w Z hSup hP.rehearsed.temp_eq hw'; have hS':(Xm).fullA Z.code.val⊆p'.support:=by rw [area_stamp L' d K H G U Γ Y A φ Z]; have hK:= (Warmlet.groom H HP (Z') P₀ F' Z).2.1; simpa only [trunkP, if_pos hSmall] using hK
    have hD': Sight p'.support p'.site 2 B' φ Xq D:=by refine ⟨fun i j h=> hD0.room _ _ (agrees_mono h hS'),fun U=> regionMon (limitsMon _ _ hS') (hD0.gate _),fun V h=> hD0.use _ (h.mono_left hS'),fun i h=> hD0.pole i (h.mono_left hS'),hD0.borel,hD0.travels⟩
    obtain ⟨C0,W₀,N₁,W₁,W₂,σ,f5,g0,h1,h2,h3,h4⟩:= hV'.poses
    have hX:S0 ≥ coverNumber O₁.B X.support:= by rw [hr']; exact hτ
    obtain ⟨k1,k2,k3,k4,k5,k6,k7,k8,k9,k0,K0⟩:= h4 f X.support B' O₁ hX ht' hξ hg hP.rehearsed.temp_eq hα htP β hT
    have hX':=K0 c L' d _ _ _ _ E₁ E₂ mm G rfl (by assumption) hh'
    let f₀:= trimP T O₁ δ β b
    rw [← hα] at h3; have hGx:WardBin.Lies.Germ n Xq 1:=hP.rehearsed.test ▸ hD'.use 1 (Next.Foundations.one_healthy _ _ B'.threshold_pos.le)
    have hI0: (wrap f Xb)∈ X.support:= by rw [hxI]; exact X.anchor
    have hA:=hSup.title; refine le_trans ?_ (k0 d0 htd κ' hΘ.sight.travels)
    exact piloting (Rx:=f₀) Tx F₁ hP hB H' p F' hO₁ rfl hL h3 (.inl Z.label) (sageT L' d K H G U Γ Y A φ F' Z.label hstop hZ) w h'Q hA.favorable hA.color _ Z.earns (hB.symm ▸ hSmall) S G G' F g U₂ Dd (he.symm ▸ hΘ) hφ hδ A₀ A₁ A₂ hH rfl rfl rfl hZs hh' hU hΦ ht ha hX' σ f5 k5 hr h2 hL.funds hg Xb hxI hGx W₀ N₁ C0 k3 k4 (k9 _ hI0) h1 k6 k1 k2 k7 k8 α j' d0 (by assumption) htd hP0 hα' (by omega)
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.powerQ
