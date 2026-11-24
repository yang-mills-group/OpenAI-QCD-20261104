import YM.Rebus.Pie
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
local notation "S"=> Flight.visit L' K h
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
local notation "βg"=> gStep β
variable (gT:Hypnos.State su)(u t:ℝ) (V: Directions su c) (Y:Coat T F) (Jz: Air f su)
local notation "HX"=> βg
local notation "B0"=> radiusB τ
local notation "Vv"=> increment 1 V
local notation "Y1"=> karm κ₁ Vv
variable (hV:Vitae p Z A S' V₀ r O.threshold (gStep β) ε O.B l Φ)(hF:SetL p V₀ O.B l k t₀ Φ)
variable {Vp d mξ D' A₂ ιp h₈ :ℝ}
variable (Xz:Finset I)
local notation "Xy"=> shock Xz (Ap)
local notation "Xw"=> shock Xz (Aw)
local notation "Wx"=> heather xp (radiusB τ) Xz
variable {w0 w1:Clip}(J₀ J₁:Bed)(Tx:Towers (Flight.visit L' K h).patch.L) (AxP:Striation (T:=T) J₀ J₁ Tx w0 w1 s s')
variable (M₀:Myth su (Flight.visit L' K h) J₀ J₁ Tx (radiusB τ) Vp t)
variable (hL:20*majorT l ≤ L'.L.val)(h0:O.B ≤2*radiusB τ)
local notation "X0"=> Dh f N I
local notation "X1"=> Dh c N I
variable (hT:SliceRows.Stamp T) (he:A.Wave O.threshold q p)
variable (ht:Xz∈V₀) (hx: Xz.card ≤ l)(hl:∀ i⊆Xz,i∈V₀)
variable (hV₁ : Y.manifest)(hV₂:Y.x=τ)(hV₃:Y.width=o.K)
local notation "YP"=> Y.input (Y.liftA β Jz)
variable (hh:Hypnos.Calm Y (heather ((sliceL L' h).parent∘p) (radiusB τ) Xz) o.ξ β Jz) (hc:∀ i∈heather ((sliceL L' h).parent∘p) (radiusB τ) Xz, ¬Inside i Y.seeds (30*Y.B))
variable (hy: HaloV Y (heather ((sliceL L' h).parent∘p) (radiusB τ) Xz) β φ D' V Jz)(hp: HaloV Y (heather ((sliceL L' h).parent∘p) (radiusB τ) Xz) β r D' V Jz)
-- `φ` is max radius actual V reachable. `r`: tile schedule previous, may be smaller; use either. 
local notation "Yk"=> karm βg YP
local notation "Kw"=> Fruit.cones su (Flight.visit L' K h) J₀ J₁ Tx (radiusB τ)
local notation "Qw"=> Oce.surge (dove F) (Kw  *ᵥ Y1) Jz
-- v threshold parent. `A₂` comparison budget post-L t from StepPrice. Match.W.C.Public
set_option quotPrecheck false
local notation "ST"=> swapV v φ |D'| mξ d gT.web.scale Vp t
variable (hε:0≤ ε)(hε':ε ≤ 1)(hg:∀ i⊆ Xz,i.Nonempty→ cents (Φ i) ≤ h₈)
local notation "Zr"=> Cape.cups p (majorT l*O.B) Xz
variable (hW:φ ≤ gT.r) (hz:‖(gStep β)⁻¹‖ ≤ mξ) (hK:|κ₁⁻¹| ≤ mξ)
variable (hVk : ‖V‖≤ v) (hd:‖(gStep β)⁻¹-κ₁⁻¹‖ ≤ d)(hK': Y.V=increment 1 V)(htg:v≤ gT.r)
variable (hA : chant φ mξ gT.web.scale + swapV v φ |D'| mξ d gT.web.scale Vp t ≤ A₂)
-- Step numerical once V radius paid 
include hh hc hV₂ hV₃ hV₁ H h0 hL hT
private lemma awakeD : Healthy O.threshold (Cape.cups p (majorT l*O.B) Xz) (Y.input (Y.liftA β Jz)) :=by
    have htB:0<B0:=(by have h:= H.laws.data.room.sight; omega)
    refine safe_H Y Wx (hV₂.symm ▸ H.laws.data) hV₃ hV₁ hT hh H.laws.intake.positive hc Zr (fun i hi=> hardy R p h0 hL htB (Finset.Subset.refl Zr) i hi) ?_
    have ht':= H.laws.intake.received.temp; change O.threshold =_ at ht'; change Pressure.fiery _ _ _ / 4 ≤ _; rw [hV₂, ht']; linarith [H.laws.data.room.fiery]
omit hc hV₂ hV₃ hV₁ hh h0 hL H hT
include hL h0 H hy hW
lemma yellowK (hw: gT.m*φ ≤ w)(i:Keys f N)(hi:Sum.inl i∈shock Xz Ap): Spice.BeamRaw (halo B0 {locationP i}) (Y.input (Y.liftA β Jz)) 1 w:=by
    have htB:0<B0:=(by have h:= H.laws.data.room.sight; omega); obtain ⟨u,hb,h,hp⟩:=hy.chosen; intro j hj h'
    have hf:= h j (spinFt (sliceL L' ‹_›) p h0 hL htB Xz i hi (mem_image_of_mem _ hj)); rw [Pi.one_apply,inv_one, mul_one,hf,increment, Pi.one_apply,mul_one]; exact (gT.cost _ (((norm_le_pi_norm u j).trans hb).trans hW)).trans ((mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hb) gT.m_pos.le).trans hw)
omit hy hW
include hh hc hV₁ hV₂ hV₃ hV hF hε hε' hg hx hp hT he hl
variable (hφ:0 ≤ h₈)(hρ:1 ≤ A₂)
local notation "ζ"=> A₂^(l*k)*h₈
local notation "F1"=> puddle A S' (Y.input (Y.liftA β Jz)) (O:=O)
local notation "F0"=> Oce.rose X0 Yk
lemma mush (hφ:0≤ h₈)(hhv:Oce.bill Yk (shock Xz Aw) A₂)(hρ:1≤ A₂): ‖parties F1 Xz- F0 (parties Φ Xz)‖ ≤ Chamber.face l (ζ+1)*ε:=by
    have htB:0<B0:=(by have h:=H.laws.data.room.sight; omega); have h':= awakeD L' h K H p Y Jz Xz hL h0 hT hV₁ hV₂ hV₃ hh hc
    have hz:0≤A₂:= zero_le_one.trans hρ
    obtain ⟨u₀,hu,hb,hJ⟩:= hp.chosen
    have hk (i)(hi:i⊆Xz)(hm:i.Nonempty): ‖F1 i-F0 (Φ i)‖≤ε:= awoken p q V₀ R Φ Z A S' i O.threshold _ hF h0 hL htB hV O rfl he YP u₀ Xz (hl i hi) hm hi hu hb h'
    have hc (i)(hi:i⊆Xz)(hm:i.Nonempty): ‖F0 (Φ i)‖≤ζ:=by
       have he:= hF.scope _ (hl i hi) hm; have hp:Oce.bill Yk (shock i Aw) A₂:=by intro j hj; obtain ⟨v,hv,hj⟩:=biDU.mp hj; exact hhv _ (biDU.mpr ⟨v,hi hv,hj⟩)
       exact (Oce.cares he.2 hp hρ).trans (mul_le_mul (pow_le_pow_right₀ hρ (Nat.mul_le_mul_right _ ((card_le_card hi).trans hx))) (hg _ hi hm) (cent _) (pow_nonneg hz _))
    refine Play.Chamber.parcelP F1 Φ (le_add_of_nonneg_left (mul_nonneg (pow_nonneg hz _) hφ)) Yk hε (?_) (fun i hi hh=> (hc i hi hh).trans (le_add_of_nonneg_right zero_le_one)) hk hx
    intro i hi hh; apply le_trans ?_ (add_le_add (hc i hi hh) ((hk i hi hh).trans hε')); rw [add_comm]; simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (F1 i) (F0 (Φ i)) 0
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.mush
