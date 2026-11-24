import YM.QCD.Purse.Grant
import YM.QCD.Purse.Silo
/-! # Pre-reset integration for any issued turning bank. -/
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
-- Standalone theorem purchase at ANY Φ clock supplies & rank. Need caller projectors and repeats. Population η not promised. No E log over μ averaged here; exactly Crude scope. Block scalar from Toll. λ extensions later.
set_option maxRecDepth 3400 in
set_option maxHeartbeats 900000 in
theorem contractE (α:ℝ)(hq:Q.rate ≤ -(3/8:ℝ))(Jq Kq:ℕ)(χ:Chi)(hα:0≤α)(hQe:(α+1)+1+1≤Q.exp) (hP:4≤j)(hQ:4≤k)(N:ℕ)(h η v u e:ℝ) (D:Heir.Record) (U₀: Libretto su Jq) (U₂:Hera.Rights su Jq) (hU:5 ≤ Jq)(hD:D.ε≤1/4)(hx:0<h)(hz:h<1/8)(hr:0<η)(he:0<u)(ht:1≤v)(h₀:0<e): ∃ n:ℕ,∀ s:Side,n ≤ s.val → ∀ᶠ W in atTop, 0<W ∧ ∃ μ:ℝ,0< μ ∧∀ D':RG.Patch, D'.Branches P.bind su → D'.L=s→ D'.J=k → ∃ (o:Target.Order su W)(C:ℝ), ∀ (a b t q U A:ℝ),0<a→0<b→0<t→0≤q→0≤U→
   ∃ (r z σ D₁ Y B:ℝ)(p p':ℕ), 0<r ∧∀ᶠ x:ℝ in atTop,
    let δ:=lowK s x P.top.supportExponent; let Z:=highW s v h x; let g:=coneK s r x
    0<δ ∧ ∀ (E:Garden.Offer 1 a q)(E': Garden.Offer 2 b U)(X:ℕ→Atom su 2),Extra.Iteration.Charged X t A → Extra.Iteration.SymmetricAtoms X → ∀ (c f: Side)(G:Flight j k)(H:f.val=c.val*G.L.val)(K:KernelChoices)(R:BudgetPoint) (m β w:ℝ) (T:Tube su (Flight.visit G K H)), G.L=s→ (G.visit K H).patch=D' →2*(radiusB x+1)< f.val→ Works P s x (Flight.visit G K H) T → SliceRows.Stamp T → R.threshold =fiery su x s → R.B=highR s x →R.supportExponent=P.top.supportExponent →T.up.Bounds T.high P.top.width P.top.paths (loopBill su s x) → betaF su x s/2 ≤β→β≤2* betaF su x s→|m|≤ wink s x→
    let T':=park G H P₁ E E' (haloK s x) m
    Nonempty {V:Jets.Sun G c f H g z σ η D₁ p T' // Bay.Sacred V} ∧ Nonempty (Swathe G H T' X P₂ z g η Y B p') ∧ ∃ (p₀ : Cash W x μ G.L Q o C T (trimP T R δ β w)) (ζ:Cash W x μ G.L Q o C T (Sands.lore (trimP T R δ β w))),∀ (G₁:Sun G c f H g z σ η D₁ p T') (V':Swathe G H T' X P₂ z g η Y B p'), Bay.Sacred G₁→ ∃ Γ,∀ {E J:Type}[Countable E][Countable J] (f': Rise f N E J),∀ (w:E→ℝ) (g:J→ℝ), Cents f' w g (fan s h x) R.threshold → Fill f' w g u u (taxK s x 1) 1 (chip s x) (highR s x) → f'.Wave R.threshold→ Villa.Pant f N R.threshold f' → Villa.PortD G K H p₀ G₁ V' f' Γ h Z (α+1) ∧ Gosh (tableau G H K f' p₀ G₁ V' Γ) χ (α+1) Z Jq Kq ∧ ∀ (O:BudgetPoint), O.B=radiusB x → O.power=Kq→ Plays U₀ D O R P T x→∀ (i:Flavor N), (∀ j, Spice.Worth f' j R (fan s h x) (w j) ∧ (Nonwrapping (f'.row j).support (f'.row j).site → Feast R (f'.row j).support (f'.row j).site i (f'.main j) (fan s h x) (w j))) → Warmlet.Aspen G H K G₁ p₀ f' (united (VarnC p₀ V' N) (sailP p₀ Γ N)) ζ χ O Z α (e*chip s x):=by
   have hz1 :0 ≤α+1:=by linarith
   obtain ⟨n,Hn⟩:= granted Q P₁ P₂ (α+1) hq Jq Kq χ hz1 hQe hP hQ N h η v u hx hz hr he ht
   let p:= max 1 (max v (fareG 1 v N)); have hp:1≤ p:=le_max_left ..
   let ε:=e/3; have hε:0<ε:=by unfold ε; positivity
   obtain ⟨C,hC,D₁,h₁⟩:= blooms hP hQ p hp N
   obtain ⟨M,hM⟩:= throne u α C ε Kq (Q.halo+8) U₀ U₂ he hα hε
   obtain ⟨B,hB⟩:= billing P₁ N k Q.halo hP hQ p α u η h hp hα he hr hx
   refine ⟨n+D₁+M+B,fun L hl=>?_⟩
   filter_upwards [Hn L (by omega)] with W hW; obtain ⟨hW,μ,hμ,hN⟩:=hW; refine ⟨hW,μ,hμ,?_⟩; intro D' hd hL hK
   obtain ⟨o,C',hN⟩:=hN D' hd hL hK; obtain ⟨Λ,Ω,z,hΛ,hΩ,hz',hA⟩:= spirit L (Q:=Q) (C:=C') (μ:=μ) (o:=o) U₀ D χ D' hd hD (by omega) Kq 0
   refine ⟨o,C',?_⟩; intro a b t q U A ha hb hw hu hu'
   obtain ⟨r,m,σ,d,Y,B',K,K',hx₁,hX⟩:= hN a b t q U A ha hb hw hu hu'
   obtain ⟨X',hZ,hZ'⟩:= hB L (by omega) r σ m d K hx₁
   obtain ⟨φ,ν,hφ,hν,hΦ⟩:= tenderR P₁ N K Kq L U₀ D U₂ m η σ d m σ r p h hr hx₁ hp z hz'
   refine ⟨r,m,σ,d,Y,B',K,K',hx₁,?_⟩
   filter_upwards [hA,hX,hZ'.pays,hΦ,pluckZ L N r h X' p _ _ _ _ hx₁ hφ hν hΛ hΩ,plents U₀ D L (Q.halo+5) Kq (by omega), pops L r 1 zero_lt_one,nails L,booths L U₀ U₂ Kq h ε hx hε,Warmlet.frosty L Q.halo ε 0 hε, Fees.horizons su L 4 (ε:=1) (a:=α) (by norm_num) hα (by norm_num :2*(1:ℝ)<3)] with x hΨ hX hZ' hT h' hz₀ hy hn' ht' hb₀ hg
   intro δ Z g; refine ⟨hX.1,?_⟩
   intro V₁ V₂ A' hA hV c f S H K'₀ R y β w T hS hL₁ hF hW hR htemp hb' hx hc ht₀ hQ hX₀ Z'
   obtain ⟨hN,hK',Q₀,⟨G⟩,hM'⟩:= hX.2 V₁ V₂ A' hA hV c f S H K'₀ R y β w T hS hL₁ hF hW hR htemp hb' hx hc ht₀ hQ hX₀
   have he0 : |(0:ℝ)|≤wink L x:=(by rw [abs_zero]; exact (abs_nonneg y).trans hX₀)
   obtain ⟨⟨E',-⟩⟩:= (hX.2 V₁ V₂ A' hA hV c f S H K'₀ R 0 β w T hS hL₁ hF hW hR htemp hb' hx hc ht₀ hQ he0).1
   refine ⟨hN,hK',Q₀,G,?_⟩; intro G₁ Z₁ he₂; obtain ⟨Γ,hN⟩:=hM' G₁ Z₁ he₂; refine ⟨Γ,?_⟩; intro E J _ _ f' w' ζ hw hP hF' hC
   obtain ⟨hr',hS',hc⟩:= hN f' w' ζ hw hP hF' hC; refine ⟨hr',hc,?_⟩
   intro O ho hv hψ i Hi
   obtain ⟨R',hJ,hZ,hI,HZ'⟩:=hZ' f c hF a b q U m V₁ V₂ y S H hS (hX₀.trans hy.1) G₁
   let t:=fan L h x; obtain ⟨hX',H',hC0,hZ0,hR₀,hQ⟩:=HZ' f' w' ζ (htemp ▸ hw) hP
   obtain ⟨b,hp',hG,_⟩:=hc.bills
   have hV:=Villa.tenet S K'₀ H Q₀ G₁ Z₁ f' χ hr' hg.1
   have hh:S.L=L:=hS
   clear hL
   subst L
   have hx₀ := Q₀.laws.data.room.temperatures
   have hv₀:=hψ.rehearsed.temp_eq
   have hΦO: O.threshold ≤2*fiery su x S.L := hv₀.symm ▸ hx₀
   let x':=p*t
   have hh : Coins O R P S.L D Q.halo U₀ U₂ x β t x' g m η (φ x) σ d m (Λ x) (z x) (ν x) y (Ω x) X' t h P₁ N K :=by
      have hV':= (hz₀ β ht₀).2 O R htemp hv
      exact ⟨hV', hb'.symm ▸ hg.2.1,htemp.symm ▸ hΦO,⟨(hT O hv hΦO).purse⟩, ⟨h'.dawn,h'.swift⟩⟩
   let Y':= united (VarnC Q₀ Z₁ N) (sailP Q₀ Γ N)
   have hΦ':Peak (G₁.equip N (radiusB x)) R.threshold t x' X' (fun i=>Real.exp 1*terra G₁ N _ t x' i) := htemp.symm ▸ H'
   have hhJ: O.order=Jq:=hψ.rehearsed.test
   have hI':0<t:=fan_pos ..
   have hK₀ : v≤p:= (le_max_left ..).trans (le_max_right ..)
   have hP₀:1 ≤ p:= hp
   have hδ:=hI
   refine Warmlet.holds S H K'₀ G₁ E' Q₀ f' Y' G U₂ w' ζ R' _ _ i hW ho ?news hψ hh (hX₀.trans hy.1) hΦ' (htemp.symm ▸ hJ) hZ ?sea ?wick hQ hF' hC.refr hr hS' hV.famous hV.graph ?target ?pos ?fare hU (fun i=> h₁ _ (by omega) _ rfl _ _ H i _ _ hI' (mul_pos (by linarith) hI') le_rfl) Hi (fun i=> anchored_each _ _ _ hP.χ hP.bud hw.pos i) hR₀ hZ0 hC0 hw (f₁:=b) (fun i hi=> hp' O i hi hhJ hv ho hv₀) hG ?cap (hb'.symm ▸ hP.χ) hε.le ht'.1 hα (hb'.symm ▸ hn') hg.1 ?cost
   case news => rw [hv,hL₁]; exact hΨ
   case sea=> unfold x'; nlinarith only [mul_le_mul_of_nonneg_right hδ hI'.le]
   case wick=> unfold x'; nlinarith only [mul_le_mul_of_nonneg_right hX' hI'.le]
   case target => exact mul_le_mul_of_nonneg_right hK₀ hI'.le
   case pos=> exact mul_pos (zero_lt_one.trans_le ht) hI'
   case fare=> have hv':fareG 1 v N≤p:= (le_max_right ..).trans (le_max_right ..); exact (le_of_eq (show fareG 1 Z N=fareG 1 v N*t by unfold Z highW t fareG; ring)).trans (mul_le_mul_of_nonneg_right hv' hI'.le)
   case cap => rw [hv]; exact hM _ (by omega)
   case cost => exact (add_le_add (add_le_add_left (ht'.2 O hv) _) hb₀).trans_eq (by unfold ε; ring)
end YM.QCD.Loom
