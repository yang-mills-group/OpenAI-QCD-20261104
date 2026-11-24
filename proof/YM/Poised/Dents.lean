import YM.Poised.Meritus
import YM.Poised.Treks
import YM.Poised.Cruise
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
open Massive.Poised.Chute Planned.PrimaryIntegral295.Carrier Massive.SourceRead
variable (XB:Cover) (q0 p0 v0:ℕ)(d0:ℝ)(Θ: TaperHol)
local notation "Yg"=> (Sγ).support
local notation "Xg"=> (P₀.row e).support
local notation "Fp"=> Elevator.tap (q:=q') P₀ Y e
local notation "Fₓ"=> (prescription L' d K A φ (Y.markers Z.label.val) q') ∘ (crude Tx χ w).view (individual Z.code)
-- actual supports; expose intrinsic X→Yg. Price support reach explicit.M.Point. Extra toll.T.B'
variable (hSize:coverNumber O₁.B (P₀.row e).support≤ q0)(hRe:Laurent.size (cellar L'.L Xb-XB) ≤ p0)
include G' H' hO₁ hP hB hL F₁ hH hα hg hr hV' hn ht' hτ hξ hT hX ha hh' hp hSup hw' hE hq hΦ h'Q hΘ hY hU
include hSize hRe
-- A.Auth prize. cite cone x bits.
structure WindowG (o' : Side)(p':BudgetPoint)(p m u v:ℕ)(x:ℝ):Prop where
    room : 4*(m*(4*p'.B+2)+2*p'.B)+p ≤ v
    valid:100 ≤ o'.val
    late: 10*(radiusB x*(4*radiusB x+2)+2*radiusB x+p) < o'.val
    germ:2*(v+u)<o'.val
    pilot:10*(m*(4*p'.B+2)+2*p'.B) < o'.val -- paid.O.B.B.OK by f monotone
variable (hSκ:WindowG c O₁ p0 q0 (radiusB τ) v0 τ)
include hSκ
-- structural telescope.Use grant. K_frame
set_option maxHeartbeats 980000 in
lemma moonlight (hSmall:Small H HP (Z') P₀ Z F')(hD0:Gn<n)(hq0:Fintype.card (Palette.ZBand Gn)< U₂)(hy0:Gn*Gn≤Kq)(hw0:Beacon.surface Gn≤Dd)(σ C:ℝ)(hk:4 ≤ k)(hT':T.R.A0.strip σ C)(hV:∀ (u v:Pipes.Shell)(x:Cover),Laurent.Width σ C (Steed.arch L' u v x)) :
    Harbor Xg Yg Xb XB T O₁ σ C A₀ x₀ φ B'.threshold (radiusB τ) v0 ∧ LocalOn Yg Fₓ ∧ ContDiffAt ℝ Gn (Fₓ∘increment 1) 0 ∧ (separation (Sγ).site (wrap c XB) ≤ p0) ∧ Flame Fp O₁ Xg (wrap f Xb) x₀ Dd U₂ κ' ∧ B'.threshold≤ 2*fiery su τ L'.L ∧ 0<φ ∧ (∀ k U,slots 6 k (Fp (Lattice.gauge k U))=Fp U) ∧ ∀ d₁:Chute.Λ Gn,∀ i≤Gn,∀ α:Directions su c, B'.dirBound (Sγ).site α→‖α‖ ≤ canopyW su L'.L B'.power τ → ‖leftDerivs (framesF (purseX (Sγ).site Dd φ)∘ mantel d₁.val ∘ Fₓ) (List.replicate i α) 1-leftDerivs (framesF (purseX (Sγ).site Dd φ)∘ Fountain.cherub T (flareV (proton L' d)) (mantel d₁.val∘ Fp)) (List.replicate i α) 1‖ ≤ t0*κ':=by
    let X:= Xg; let Yfo:= Yg; let R:=sliceL L' d; have ho:(Sγ).site= R.parent (wrap f Xb):=by rw [hY]; exact (plateK H HP (Z') P₀ F' Z).2.2 e hE
    have hφ:=zero_lt_one.trans_le hSup.strength
    have hm: B'.threshold ≤ 2 * O₁.threshold:= by rw [hP.rehearsed.temp_eq]; exact hP.rehearsed.tensions.coarse
    have hx':wrap f Xb∈ X:= hY ▸ (P₀.row e).anchor
    have hI : Cruising R X Yfo Xb XB (radiusB τ) v0:=by
        apply Massive.Poised.Landing.passport R Xb XB X Yfo _ (radiusB τ) q0 _ v0 hx' hRe hSize hSmall ((ho ▸ (Sγ).anchor)) _ hSκ.valid hSκ.room hSκ.late hSκ.germ (lt_of_lt_of_le hSκ.pilot _); swap
        · rw [d]; exact Nat.le_mul_of_pos_right _ L'.L.property
        intro i hi k hk; unfold Yfo; rw [(plateK H HP (Z') P₀ F' Z).1, (slate H HP (Z') P₀ Z e).2 ⟨hE,hq⟩, Finset.singleton_biUnion]; unfold QCD.Jets.Touch.roof; apply halo_spec.mpr; obtain ⟨p,hp,h⟩:=halo_spec.mp hk; rw [Finset.mem_singleton.mp hp] at h; refine ⟨_,Finset.mem_image_of_mem _ (mem_union_left _ (show i∈_ from Lattice.halo_subset _ X hi)),?_⟩; refine h.trans ?_; have hg:0<B:=hSup.room.2; nlinarith [Q.buys]
    obtain ⟨A4,hA4⟩:= littered L' d K H G U Γ Y A φ F' hB w Z hSup hP.rehearsed.temp_eq hw'; have hS':(Tx).fullA Z.code.val⊆Yfo:=by rw [area_stamp L' d K H G U Γ Y A φ Z]; have hK:= (Warmlet.groom H HP (Z') P₀ F' Z).2.1; simpa only [trunkP, if_pos hSmall] using hK
    refine ⟨⟨hI,hT',fun t i j=>hV i j t,hφ.le,hΦ,hU,B'.threshold_pos.le,hm,B'.threshold_le,?_,hk⟩,(Massive.Poised.Counting.Terrain.shelf_out hS' hA4).room,(hA4.use 1 (Next.Foundations.one_healthy _ _ B'.threshold_pos.le)).of_le (by rw [hP.rehearsed.test]; exact_mod_cast hD0.le),?_ ,hY.symm ▸ hΘ, hξ ▸ hm,hφ,?_,fun i j hj α hα' hq0'=>?_⟩
    · let p:= Warmlet.oath H HP (Z') P₀ Z; obtain ⟨hZ,hZ',hv⟩:=Classical.choose_spec (Warmlet.oak H HP (Z') P₀ Z); obtain ⟨C0,W₀,N₁,W₁,W₂,σ,f5,g,h1,h2,h3,h4⟩:= hV'.poses; obtain ⟨k1,k2,k3,k4,k5,k6,k7,k8,k9,_⟩:= h4 f (brimW (Z') P₀ Z.label.val) B' O₁ hτ ht' hξ hg hP.rehearsed.temp_eq hα hm β hT; intro i hi
      have hc: (P₀.row e).support ⊆ brimW (Z') P₀ Z.label.val:= Subset.trans (Spice.leafSub G P₀ Z.label.val _ hE) (native_sub ..)
      exact k9 _ (hc hx') i ⟨hc hi.1,hc hi.2⟩
    · rw [ho, Planned.PrimaryIntegral295.Streets.owner R]; exact (Chute.cost_p c (cellar L'.L Xb) XB).trans hRe
    · intro k U; have he:= hSup.property.turnsE e U k; change slots 6 k (scrape _ _ _)= scrape _ _ _; exact (wing _ _ _ _).symm.trans (congr_arg _ he)
    exact powerQ L' d K H G U Γ Y A φ F' H' F₁ hO₁ hB hL hP G' A₀ A₁ A₂ hH hα hg hr hn hξ hT hX ha hh' hSup Z w hw' e hE hq hp h'Q Xb hY hU hΦ hΘ S0 t0 hV' ht' hτ hSmall α j i.val (hj.trans_lt hD0) (lt_of_lt_of_le i.isLt hq0) hα' hq0' -- args order check
end YM.MassiveQCD.Lyre
#print axioms YM.MassiveQCD.Lyre.moonlight
