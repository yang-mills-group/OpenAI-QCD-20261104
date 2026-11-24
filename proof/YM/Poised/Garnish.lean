import YM.Poised.Riverbank
import YM.Poised.Review
import YM.Poised.Doves
/-!
# Accounts at all apertures. Covers actually Y^+ when using these. Bound with polynomial factor in length of input support (allows NOTshort in same currency).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG MassiveQCD.Plate MassiveQCD.Apron MassiveQCD.Elevator
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y:ℝ}{H:Cash W τ μ L Q o C T (trimP T O δ β y)}{ι κ I E J D:Type}{N:ℕ}
variable (Y:Fleet H ι N)(Γ :Cash W τ μ L Q o C T (lore Rx)) {X:Support f} {B:BudgetPoint}{n p d k l:ℕ}
local notation "Y?"=> Lat.Fields c 6
local notation "Y'"=> Lat.Fields f 6
variable {N': Libretto su n}{D:Heir.Record}{v u t M w W₁ W₂ Ω' ν r θ x x' x₀ Y₂ R₀ A₀:ℝ}{χ:Chi}
variable (hP:Plays N' D B Rx.p P T τ)(hB:B.B=radiusB τ)(Vb:Hera.Rights su n)(i:ℕ)
set_option quotPrecheck false
local notation "Z"=> (Brim.plate Γ i)
variable {U:Config su c}{Λ ψ gWay Z₀ ζ :ℝ}(F₀:Cash W τ μ L Q o C T (Sands.lore (trimP T O δ β y)))(hB₀:O.threshold=Rx.p.threshold)(hxZ:β=Rx.beta)
variable (hV':Works P L τ S T)(he:News P L τ W Q o μ C n N' D χ B.power W₁ W₂ gWay S.patch)
variable (r':ι)(hc: Choker Y r' F₀ i)(M₁: Clusters Y.Bright → RegularAddress c)(hO:Seats H χ)(hZ:Y.Famous)(hQ: Colored Y)(p':Y.Bright)(hY:Aliased Y p' r')(hx:coverNumber B.B (Brim.plate Γ i).support≤B.B)
include hP hV' hB₀ hxZ hB hc hO he hZ hQ hY hx
local notation "R₁"=>(crude Y χ M₁).view (individual p')
variable (ht : Lute.Plented N' D B Rx.p L (Q.halo+5) τ (gStep Rx.beta)) (hRx:Rx.p.B ≤2*radiusB τ) -- need ht'
local notation "nv"=> coverNumber Rx.p.B ((Sands.lore Rx).activities.reg i).support
local notation "A₁"=> Hera.dueFee N' B nv
include ht hRx
local notation "ro"=> (Brim.plate Γ i).site
local notation "Xo"=>((lore Rx).activities.reg i)
local notation "Y₀"=>(Xo).site

-- B.power fixed.pre-L ok.
variable (V:Support f)
variable {a i₁ u₁ v₁ η q m b₁ b₂ g₁ g₂:ℝ}
variable {V₁:Offer 1 b₁ b₂}{V₂:Offer 2 g₁ g₂}{P':Flight p k} {H':f.val=c.val*P'.L.val}{P₁:Plan p}
variable (Zt:Sun P' c f H' (coneK L v τ) t q u a l (pesto P₁ P' H' (trunkM V₁ V₂ (haloK L τ) m f)))(Zv:Sun P' c f H' (coneK L v τ) t q u a l (pesto P₁ P' H' (trunkM V₁ V₂ (haloK L τ) 0 f)))
variable (F:Grid f→ Lat.Fields f 6)(Ψ: EvenA c N→L[ℝ]Lat.Fields c 6)
variable (hV:V ⊆ ((lore Rx).activities.reg i).support) (hXXX:∃ x, Sight V ((lore Rx).activities.reg i).site 2 Rx.p w F x) -- don't use
-- R'.Ψ all output.Info
variable (U':ℕ)(D':ℕ) -- U' spill, D' endpoint power
variable (hW: Pipes.Flame F Rx.p V ((lore Rx).activities.reg i).site w D' U' R₀)(hG:∀ k U, Lat.slots 6 k (F (Lattice.gauge k U))=F U)
-- X=old test.Use input R0.Caract.A root & value.Tensor.Engine.
variable (hs:∀ A:Grid f, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support A →∀ V:Grid c, Ψ (Y.works r' A V)= changeVars (((Zt.equip 6 (radiusB τ)).shortP) A) (F A)) (hY':∀ U:Grid f,∀ g:Frame c, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → let W:=Lattice.gauge (g∘ S.ratio.parent) U; slots 6 g (changeVars (((Zt.equip 6 (radiusB τ)).shortP) W) (F W))=changeVars (((Zt.equip 6 (radiusB τ)).shortP) U) (F U))
variable (b:Cover)(G₁ G₂ D₂:ℕ)(hI:wrap f b=((lore Rx).activities.reg i).site) (Θ: SourceRead.TaperHol) (hα:∀ (J:Labels.Jet su)(j:ℕ), j<G₂→ WardBin.leading j (Beacon.moment (d:=D₂) Θ b J F)=0)
-- earnings given.Branches
omit hP hV' hB₀ hxZ hB hc hO he hZ hQ hY hx ht hRx
variable {Ux:Grid f→Sheet f}
structure Consider (D':ℕ)(K:ℝ)(G:Sun P' c f H' η t q u a l Ux) (i:ℕ)(δ':ℝ) : Prop where
   seaP : ∃ η' :ℝ,Sea P' H' i η η' q δ' G.Z G.V D' ∧ K*fingers 6*η' ≤ Kit.slope P'.L
lemma sealP (d:ℕ){γ t':ℝ}(p: Sun P' c f H' η t q u a l Ux)(h:Sea P' H' i η γ q t' p.Z p.V d) : 0 ≤ γ ∧ 0≤ q:=by
   obtain ⟨W,hW,h',_⟩:= (h 0).1.leases; obtain ⟨X,hX,hx,_⟩:= (h 0).1.stocks
   exact ⟨(sum_nonneg (fun i _=>mul_nonneg (meets_nn ..) (hW i))).trans h', (sum_nonneg (fun i _=>hX i)).trans hx⟩ -- variables
include hP hV' hB₀ hxZ hB hc hO he hZ hQ hY hx ht hRx hW hG hs hY' hI Θ hα
variable (K A K₁ K₂ K₃ σ₁ σ₂ σ₃ σ₄ g' g:ℝ)(hK:1≤K)(hr:1≤K₁)(hσ:1 ≤ K₂)
-- ratio charging includes K
variable (hE: Consider D' (K*(2^D':ℝ)) Zt (radiusB τ) Rx.p.threshold) (hM:Consider 2 (16*K) Zt (radiusB τ) Rx.p.threshold)
variable (h: FairT P₁ D N' 2 l L τ u v q a gWay σ₁ σ₄ B) (hp: FairT P₁ D N' D' l L τ u v q a gWay σ₂ σ₃ B)(hD:GramT N' D G₂ A K₂ B Rx.p τ L)
local notation "Γ₁"=> ((16*σ₁)*K)
local notation "Γ₂"=> (K*2^D'*(σ₂+σ₃))
variable (hX: (U':ℝ)*(K*2^D'*(σ₂+σ₃))*|W₁|+|W₂| ≤ Kit.slope L ^G₂)(hC':16*σ₁*K*|W₁|+|W₂| ≤ Kit.slope L ^G₂)(hp₁:0≤σ₁)(hp₂:0≤σ₂)(hp₃:0≤σ₃)
variable (hx':Ω' ≤ K*w) (hu: 0<u)(hv:0<Ω')(hw:0<w)(hm:|m| ≤ haloK L τ)(hV'': halo (radiusB τ+1) V ⊆ ((lore Rx).activities.reg i).support)
variable (hT:S.ratio=sliceL P' H')(hΓ:P'.L=L)(hn:1≤n)(hD':D₂ ≤ Rx.p.order)(hU:G₂ ≤ U')(hR:G₂ ≤ D₂ +1)(hn':G₂≤2*n)(hhD:2≤D')
variable (hA:Fountain.ScrollX N' g' K₁ G₂ G₁ P)(hg:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A)(hQ':Rx.p.power=G₁) (hhP:P.Funds S T)
variable (hF:Pipes.Heritage Rx.p ((lore Rx).activities.reg i).support b (purseX ((lore Rx).activities.reg i).site D' w) (purseX (Brim.plate Γ i).site D' Ω') G₂ (0,flareV (proton P' H')) (Kit.slope L) K₂)
variable (hΩ: Sight (Brim.plate Γ i).support (Brim.plate Γ i).site 2 B Ω' (Ψ ∘ (crude Y χ M₁).view (individual p')) g)
include hE hM h hp hΩ hF hA hQ' hg hhP hσ hK hr hD hx' hp₁ hp₂ hp₃ hu hv hw hm hT hΓ hn hX hC' hV'' hD' hU hR hn' hhD Zv Vb
set_option maxHeartbeats 550000 in
lemma sortedT : Flame (Ψ ∘ R₁) B (Z).support ro Ω' D' U' (((Kit.slope L)^G₂*badgeQ N' B G₂ nv)*tipW N' Vb U' G₂ K₁ K₂ (pup G₂ K₂)*R₀):=by
    let M:=pup G₂ K₂; have hmM:1≤ M:= pup_pos hσ _
    have hZ': S.patch.L=L:= ((show S.patch.L=P'.L from congr_arg Ratio.count hT)).trans hΓ
    let SR:=Kit.slope L; obtain ⟨η,hη,hξ⟩:=hE.seaP; obtain ⟨φ,hφ,hγ⟩:=hM.seaP
    rw [hΓ] at hξ hγ; have hb:=hM.seaP; obtain ⟨hy,hY⟩:=sealP (radiusB τ) D' Zt hη; have hxP0: 0 ≤ φ:= (sealP (radiusB τ) 2 Zt hφ).1
    let σ₀:=Γ₂ ; have hs₀: 0 ≤ σ₀:=by unfold σ₀; positivity
    have hUM: SR ≤ 1:= (boxed1 L).2
    have hV:= (halo_subset _ _).trans hV''
    have hVi : 0 ≤ fingers 6:=by unfold fingers; positivity
    let H1 (U:Grid f)(hx:Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U):= paths_b Zt U hη (hx.mono_left hV'') -- args
    have hx₁:4*((fingers 6*φ)*Ω') ≤ SR/2*w:=by
      calc _≤ 4*((fingers 6*φ)*(K*w)):=by gcongr
           _≤ SR/2*w:=by have ht:= mul_le_mul_of_nonneg_right hγ hw.le; have hx:= (boxed1 L).1; unfold SR; change 0< Kit.slope L at hx; nlinarith only [ht,mul_nonneg hx.le hw.le]
    have hx₂:4*((fingers 6*φ)*Ω') ≤ w/4:=by
      calc _≤ 4*((fingers 6*φ)*(K*w)):=by gcongr
           _≤ w/4:=by nlinarith only [mul_le_mul_of_nonneg_right (hγ.trans hUM) hw.le]
    have hh:L=S.patch.L:= hZ'.symm -- shadow

    rw [show Kit.slope L=Kit.slope S.patch.L from by rw [hh]]
    refine released Y Γ hP hB Vb i F₀ hB₀ hxZ hV' he r' hc M₁ hO hZ hQ p' (by assumption) hx ht hRx V ((Zt.equip 6 (radiusB τ)).shortP) F Ψ hV U' D' hW hG hs hY' b G₁ G₂ D₂ hI Θ hα K₁ g' A M σ₀ (fingers 6*η) σ₂ K₂ hr hσ hhP hQ' hA hg hw hv (flareV (proton P' H')) (by rw [hZ']; exact hF) (hh ▸ hD.pressure) (hh ▸ hD.spin) hD.posh hD' hR hn' ?_ ?_ (by positivity) hmM ?_ hp₂ ?_ ?_ hs₀ ?_ (hv₃:=by rw [hZ']; exact hx₁) hx₂ (hw₃:= show 0 ≤ (16*σ₁)*K by positivity) (σ₂:=σ₁) ?_ ?_ ?_ hU (hh ▸ hC') (hh ▸ hX) hhD g hΩ -- see #check
    · apply mul_le_of_le_one_right (zero_le_one.trans hmM); rw [hZ']; exact pow_le_one₀ (boxed1 L).1.le (boxed1 L).2
    · apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (by positivity : 0 ≤ (2:ℝ)^D')) (by positivity : 0≤fingers 6*η)).trans; change _ ≤ M*w; nlinarith only [mul_le_mul_of_nonneg_right (hξ.trans hUM) hw.le, mul_le_mul_of_nonneg_right hmM hw.le]
    · apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (by positivity : 0≤ (2:ℝ)^D')) hp₂).trans; unfold σ₀; nlinarith only [mul_nonneg (by positivity : 0 ≤ K*2^D'*w) hp₃]
    · intro U' hU; change Stanch V S.ratio _ _ _; rw [hT]; exact H1 U' hU
    · intro U₀ U' hx hU0 hX; exact streak Zt hp Γ i hT hV'' hu U₀ U' hX
    · intro hL K' y X g0 _ hGx U' _ hW X' ia hia
      rw [hI]
      exact divisor Ω' w hv hw Y₀ D' (leaps Zt Zv hp Γ hP i hT hΓ hn hV'' hu hm hY hL K' y X g0 hGx _ hW) σ₀ hp₃ (by
        apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (by positivity : 0≤ (2:ℝ)^D')) hp₃).trans; unfold σ₀; nlinarith only [mul_nonneg (by positivity : 0≤K*2^D'*w) hp₂]) ia hia
    · nlinarith only [mul_le_mul_of_nonneg_left hx' hp₁]
    · intro U hU; change Stanch V S.ratio _ _ _; rw [hT]; exact paths_b Zt U hφ (hU.mono_left hV'')
    intro U₀ U' hx hU0 hX; exact streak Zt h Γ i hT hV'' hu U₀ U' hX
end YM.Massive.Poised
#print axioms YM.Massive.Poised.sortedT
