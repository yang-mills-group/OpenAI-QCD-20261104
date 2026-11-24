import YM.Poised.Watch
import YM.QCD.Calm.Dyn
import YM.VStages.Dense
import YM.Massive.Horizon.Cabin
/-! Any *one* witness with BOTH the common-flavor pantry and the shifted/marker grades. The constants V,A₃ quoted pre-side; thus can now demand S.L arbitrarily large compared to them. The constant pure-root estimate in Bank3 flatRange is truncation-free; used at canonical insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {P:Teller su}(Q:Target su P) -- edit
variable {N m l i j k:ℕ}{C A D η p h z a b t v u u' q θ:ℝ}
variable (P₁:Plan j)(P₂:Plan k)
open Blaze King March GasP Ursell Stew Patron
open Shells Sands

open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Dust Brick
open MassiveQCD MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Lyre
-- Auxiliary high data called on one fixed flight. Payment here also on unmarked normal
-- bill shelves (original Rep budget O and Casa), while comparison at any O'.
variable (χ:Chi)
set_option maxRecDepth 2800 in
set_option maxHeartbeats 730000 in
lemma reward (N:ℕ)(h K α u η:ℝ)(hj:4≤j)(hk:4≤k)(hx:0<h)(hr:0<η)(he:0<u)(hK:1≤K)(hα:0≤α) : ∃ n:ℕ,∀ L:Side,n≤L.val→∀ (W μ:ℝ)(o:Target.Order su W) (C d t q a:ℝ)(l:ℕ),0<d →∀ (D':RG.Patch), D'.Branches P.bind su → D'.L=L →∀ (D:Heir.Record)(n:ℕ)(H₁:Libretto su n)(H₂:Hera.Rights su n)(Kq:ℕ),D.ε≤1/4→2 ≤ n→ ∀ᶠ x:ℝ in atTop, ∀ (c f:Side)(S:Flight j k)(H:f.val=c.val*S.L.val)(Z: KernelChoices)(T:Tube su (S.visit Z H)), (S.visit Z H).patch=D' → S.L=L→ Works P L x (Flight.visit S Z H) T → 2*(radiusB x+1)<f.val →∀ (R R' O:BudgetPoint) (β δ β' mm a₀ b₀ a₁ b₁:ℝ)(E₁:Offer 1 a₀ a₁)(E₂:Offer 2 b₀ b₁) (G:Sun S c f H (coneK L d x) t q η a l (pesto P₁ S H (trunkM E₁ E₂ (haloK L x) mm f)))
   (W':ℕ→Atom su 2)(v y:ℝ)(p':ℕ)(V:Swathe S H (pesto P₁ S H (trunkM E₁ E₂ (haloK L x) mm f)) W' P₂ t (coneK L d x) η v y p') (Q₀:Land c (Site c) (Site c))(B₀:Cash W x μ S.L Q o C T (trimP T R δ β β'))(B₁: Cash W x μ S.L Q o C T (lore (trimP T R δ β β')))(B₂:Cash W x μ S.L Q o C T (lore (trimP T R' δ β β'))),|mm|≤haloK L x → betaF su x L/2≤ β → R.threshold= fiery su x L → R.threshold=R'.threshold →R.B=highR L x→ R'.B=R.B→ Seats B₀ χ → Plays H₁ D O R' P T x→ O.B=radiusB x → O.power=Kq →
   ∀{I E J:Type}[Fintype I][Countable E][Countable J] (Y:Rise f N E J)(A:I→Site f)(p:I→Bool)(φ:ℝ)(V₁:MassiveQCD.Stitch.Tablet Y I) (σ:E→ℝ)(ζ:J→ℝ), let T':= fan L h x; φ≤K*T' → Cents Y σ ζ T' R.threshold → Fill Y σ ζ u u (taxK L x 1) 1 (chip L x) (highR L x)→ V₁.Coins σ ζ T' R.threshold → (∀ e, σ e≤ chip L x)→∀ (a b:ℝ), MassiveQCD.Apron.Grove.Supplies S H Z B₀ G V Q₀ V₁ A φ χ p a b O.order O.power → Patrol (O₁:=R') S H Z B₀ G V Q₀ V₁ A φ B₁ χ O T' α (fan L (-h/4) x*chip L x) p σ :=by
    obtain ⟨n,H⟩:= billing P₁ N k Q.halo hj hk K α u η h hK hα he hr hx
    refine ⟨n,fun L hp W μ o C d t q a l hd F H' hf D m U U' Kq hD hm=>?_⟩; obtain ⟨T,hT,hΦ⟩:= H L hp d q t a l hd
    obtain ⟨Λ,Ω,z,hΛ,hΩ,hz',hA⟩:= spirit L (Q:=Q) (C:=C) (μ:=μ) (o:=o) U D χ F H' hD hm Kq 0
    obtain ⟨φ,ν,hφ,hν,h₀⟩:= tenderR P₁ N l Kq L U D U' t η q a t q d K h hr hd hK z hz'
    filter_upwards [hΦ.pays,hA,h₀,pluckZ L N d h T K _ _ _ _ hd hφ hν hΛ hΩ,plents U D L (Q.halo+5) Kq (by omega),nails L,versionBooths L U U' Kq h hx, Fees.horizons su L 4 (ε:=1) (a:=α) (by norm_num) hα (by norm_num :2*(1:ℝ)<3)] with x HΦ hA hΩ' hE hL hZ hb hG
    intro c f S H K' T' hGx hX hw hK' R R' O β δ β' mm a₀ b₀ a₁ b₁ V₁ V₂ G B v y p' V Z U₀ U₁ U₂ hy hβ hR he hB hB' hv hh hU hQ I E J _ _ _ Y A p Φ X σ ζ W hW ht hF hH hX₂ a' b' hY
    obtain ⟨R₀,hS,hS',hSH,HR⟩ := HΦ f c hK' a₀ b₀ a₁ b₁ t V₁ V₂ mm S H hX hy G
    obtain ⟨h1,h2,h3,-,h4,h5⟩:= HR Y σ ζ (hR ▸ ht) hF
    have hW₁:0<W:=fan_pos ..; let g:=coneK L d x
    have hαO:O.threshold≤ 2*fiery su x L:=by rw [hh.rehearsed.temp_eq,← hX,← U₀.laws.data.funds.length_eq]; exact U₀.laws.data.room.temperatures
    have hΓ: Coins O R' P L D Q.halo U U' x β W (K*W) g t η (φ x) q a t (Λ x) (z x) (ν x) mm (Ω x) T W h P₁ N l:=by
       have hϰ:R'.B≤2*radiusB x:=hB'.symm ▸ hB.symm ▸ hG.2.1
       have htemp:R'.threshold=fiery su x L:=by rw [← he,hR]
       exact ⟨(hL β hβ).2 O R' htemp hQ,hϰ,htemp.symm ▸ hαO, ⟨(hΩ' O hQ hαO).purse⟩,⟨hE.dawn,hE.swift⟩⟩
    clear hf -- L= S
    subst L
    have hτ : K*W*fingers N*q ≤ T*W :=by nlinarith only [mul_le_mul_of_nonneg_right h1 hW₁.le] -- nlin
    have htG:4*((fingers N*R₀)*(K*W))≤ W/8:=by nlinarith only [mul_le_mul_of_nonneg_right hSH hW₁.le] -- kk
    apply windowP S H K' U₀ G V Z X A Φ U₁ U' (hR.symm ▸ h2) U₂ he hB'.symm hU hw hh ?_ hv hΓ hH h4 h3 hX₂ hτ h5 (hR.symm ▸ hS) htG hα hb.1 (hb.2 O hQ) hY hW hr
    rw [hGx,hQ]; exact hA
end YM.QCD.Loom
