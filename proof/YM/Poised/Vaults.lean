import YM.Poised.Vicinity
import YM.Poised.Argo
import YM.Poised.Wreath
import YM.Poised.Harp
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
variable (hTx : Lute.Plented N' D B Rx.p L (Q.halo+5) τ (gStep Rx.beta)) (hRx:Rx.p.B ≤2*radiusB τ) -- need ht'
local notation "nv"=> coverNumber Rx.p.B ((Sands.lore Rx).activities.reg i).support
local notation "A₁"=> Hera.dueFee N' B nv
include hTx hRx
local notation "ro"=> (Brim.plate Γ i).site
local notation "Xo"=>((lore Rx).activities.reg i)
local notation "Y₀"=>(Xo).site

-- B.power fixed.pre-L ok.
variable (V:Support f)
variable {a i₁ u₁ v₁ η q m b₁ b₂ g₁ g₂:ℝ}
variable {V₁:Offer 1 b₁ b₂}{V₂:Offer 2 g₁ g₂}{P':Flight p k} {H':f.val=c.val*P'.L.val}{P₁:Plan p}
variable (Zt:Sun P' c f H' (coneK L v τ) t q u a l (pesto P₁ P' H' (trunkM V₁ V₂ (haloK L τ) m f)))(Zv:Sun P' c f H' (coneK L v τ) t q u a l (pesto P₁ P' H' (trunkM V₁ V₂ (haloK L τ) 0 f)))
variable (F:Grid f→ Lat.Fields f 6)(Ψ: EvenA c N→L[ℝ]Lat.Fields c 6)
variable (hVVV:V ⊆ ((lore Rx).activities.reg i).support) (hXXX:∃ x, Sight V ((lore Rx).activities.reg i).site 2 Rx.p w F x) -- don't use
-- R'.Ψ all output.Info
variable (U':ℕ)(D':ℕ) -- U' spill, D' endpoint power
variable (hW: Pipes.Flame F Rx.p V ((lore Rx).activities.reg i).site w D' U' R₀)(hG:∀ k U, Lat.slots 6 k (F (Lattice.gauge k U))=F U)
-- X=old test.Use input R0.Caract.A root & value.Tensor.Engine.
variable (hs:∀ A:Grid f, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support A →∀ V:Grid c, Ψ (Y.works r' A V)= changeVars (((Zt.equip 6 (radiusB τ)).shortP) A) (F A)) (hY':∀ U:Grid f,∀ g:Frame c, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → let W:=Lattice.gauge (g∘ S.ratio.parent) U; slots 6 g (changeVars (((Zt.equip 6 (radiusB τ)).shortP) W) (F W))=changeVars (((Zt.equip 6 (radiusB τ)).shortP) U) (F U))
-- Inputs movement metric.F.Seat certified.AN.
omit hTx hRx
variable (K K₁ K₂ :ℝ){G₁ G₂:ℕ}(hK:1≤K)(hp':S.patch.L=L)(hR:P'.L=L)(h:S.ratio=sliceL P' H')(hV:halo (radiusB τ+1) V⊆ ((lore Rx).activities.reg i).support)(hm:|m|≤haloK L τ)(ht:Ω'≤K*w)
variable (hw:0<w)(hy:0<Ω')(hu:0 < u)
variable (hD':B.threshold=temp τ)
variable (hE:Consider D' (K*2^D') Zt (radiusB τ) Rx.p.threshold) (σ f5:ℝ)(hF : FairT P₁ D N' D' l L τ u v q a gWay f5 σ B)(hr:Diary N' P p k G₁ G₂ D' K K₁ K₂)(hσ:0 ≤ σ) (hG':P.Funds S T)(hQ0:Rx.p.power=G₁)
open WardBin.Lies
variable (b:Cover) (hI:wrap f b=((lore Rx).activities.reg i).site)(hQ':Germ n (Ψ ∘ (crude Y χ M₁).view (individual p')) 1)
local notation "T₀"=> Ψ∘ R₁
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
local notation "hzz"=>pup G₂ K₁+pup G₂ K₂
variable (W₀ N₁ A:ℝ) (hN:1≤N₁) (hT:Brim.canopyW su L B.power τ ≤ N₁*Heir.loom B (Heir.reach τ) N'.C)(hKx: ∀ i',Mom.needed (((lore Rx).activities.reg i).support) i'→Lyre.width Rx.p (wrap f b) i'≤1) (hP1:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A)(hL:N'.M * (N₁*Heir.loom B (Heir.reach τ) N'.C) ≤1)(hAL: 0< W₀)(hC:W₀≤1)(hN': (1+patterns n)*(A*(N'.M*(N₁*Heir.loom B (Heir.reach τ) N'.C)))*((Fintype.card Pipes.Shell:ℝ)*(pup G₂ K₁ + pup G₂ K₂)) ≤ W₀)(hJ:Cub.opal N' D B Rx.p L ((lore Rx).activities.reg i).support (Q.halo+5) τ (gStep Rx.beta)*N₁^n ≤ W₀)
include hW hG hs hB hE hF hr hu hp' hR h hG' hQ' hK hσ hAL hC hV hw hy hQ0 ht hm hL hN hP1 hKx hJ hN' hT hI Vb Zv
local notation "Ft"=>purseX ro D' Ω'
local notation "Pf"=>purseX Y₀ D' w
local notation "mΩ"=> AnalyticBridge.LocalGaussian.Moments.meter (Heir.Lute.heads su Rx.p L ((Sands.lore Rx).activities.reg i).support (Q.halo+5) τ) 0 D.K (2*((n+1)+(n+1)))
-- stack.V comparator all.Body.For horizon
set_option maxHeartbeats 480000 in
lemma piloting (α: Directions su c)(j d0:ℕ) (hj:j<n)(htd:d0<U')(hP0:B.dirBound ro α)(hα:‖α‖ ≤ Brim.canopyW su L B.power τ)(hn:2 ≤ n) : let p₀:= List.replicate j α; let Q:= (Pipes.mantel d0)∘ F
   ‖leftDerivs (framesF Ft ∘ Pipes.mantel d0 ∘ T₀) p₀ 1-leftDerivs (framesF Ft ∘ Fountain.cherub T (flareV (proton P' H')) Q) p₀ 1‖ ≤ ((d0:ℝ)*(K*2^D'*σ)*hzz^d0*R₀)*|W₁|+hzz^d0*R₀*|W₂| + Fountain.sheen d0 Vb W₀ hzz*R₀*mΩ:=by
    intro l f'; let p:= hzz; let X:= flareV (proton P' H'); have hYp':1≤ pup G₂ K₁:=pup_pos hr.warm _; have hYp'':1≤ pup G₂ K₂:=pup_pos hr.stellar _; have hYp:1≤ p:=by unfold p; linarith
    obtain ⟨η,hη,hζ⟩:= hE.seaP; obtain ⟨h₀,hq⟩:=sealP (radiusB τ) D' Zt hη; have hf:0≤ fingers 6:=by unfold fingers; positivity
    have htP: ro=(sliceL P' H').parent Y₀:= by change S.ratio.parent _ = (sliceL P' H').parent _; rw [h]
    let g:= Kit.slope P'.L; obtain ⟨hg,hp⟩:= boxed1 P'.L
    have hH : SeatD (purseX (wrap f b) D' w) Ft X p:=by
        have ht':= hr.spirit P' c f H' Rx.p w Ω' (Xo).support hw hy ht b; rw [hI] at ht' -- changes b? hI fine
        rw [hI,htP]; apply SeatD.less _ _ _ _ _ (Heritage.purse Rx.p ((lore Rx).activities.reg i).support b (0,X) _ _ hg hp hr.stellar ?_ |>.2)
        · unfold p; exact (mul_le_of_le_one_right (by positivity) (pow_le_one₀ hg.le hp)).trans (le_add_of_nonneg_left (by positivity))
        -- goal
        exact ht'
    let s:= hW.sight; have hSc : Ease.Charm Rx.p V f':= (show Ease.Charm Rx.p V F from ⟨s.room,s.use⟩).scales _
    have hx : coverNumber B.B (Z).support≤B.B :=by assumption
    rw [show mΩ=AnalyticBridge.LocalGaussian.Moments.meter (Heir.Lute.heads su Rx.p S.patch.L _ (Q.halo+5) τ) 0 D.K _ from (by rw [hp'])] -- holes
    refine bounties Y Γ hP hB Vb i F₀ hB₀ hxZ hV' he r' hc M₁ hO hZ hQ p' hY hx V (Zt.equip 6 (radiusB τ)).shortP ((Pipes.mantel d0).comp Ψ) ((halo_subset _ V).trans hV) b d0 D' α W₀ _ (inherent _ hG _) hSc (fun U=> region_mantel _ _ _ (s.gate _)) (fun U=> QCD.Stew.chamber ..) ?_ N₁ p A _ hH hYp hw hy ?_ ?_ ?_ ((Pipes.mantel _).measurable.comp s.borel) hI hN (hα.trans hT) ?_ hKx hP1 hL hAL hC hN' (hp'.symm ▸ hJ) ((Pipes.mantel _).contDiff.contDiffAt.comp _ hQ') j hj hP0 hα hn
    · rw [hI]; exact hW.issues d0 htd
    · intro V hV X; change (Pipes.mantel _) (Ψ _)=_; rw [hs V hV X,Pika]; rfl
    · intro F y V₀ hv hx
      have hA: Stanch V S.ratio ((Zt.equip 6 (radiusB τ)).shortP V₀) D' (fingers 6*η):=by rw [h]; exact Spice.paths_b Zt V₀ hη (hv.mono_left hV)
      have hzz':Ω'*2^D'*(fingers 6*η) ≤ p*w:=calc
           _≤(K*w)*2^D'*(fingers 6*η):=by gcongr
           _≤_:=by nlinarith only [mul_le_mul_of_nonneg_right (hζ.trans hp) hw.le,mul_le_mul_of_nonneg_right hYp hw.le]
      have hQ1:= slotsPrice Zt Zv hF Γ hP i h hR (by omega) hV hu hm hq F y V₀ hx
      rw [hI]; exact ⟨divisor Ω' w hy hw Y₀ D' hA p (by positivity) hzz',divisor Ω' w hy hw Y₀ D' hQ1 _ hσ ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (by positivity : 0≤ (2:ℝ)^D')) hσ).trans_eq (by ring))⟩
    · positivity
    have hφ: Limb Rx.p.power (S.ratio.parent (wrap f b)) α (2*N'.C*Rx.p.threshold):=by
        intro i'; let X' (n):= spine n i'.1 ((Brim.plate Γ i).site); rw [hI]; exact (hP0 _).trans ((mul_le_mul (show B.threshold ≤2 * N'.C * Rx.p.threshold from ((by rw [hP.rehearsed.temp_eq]; exact hP.rehearsed.tensions.coarse : B.threshold≤2*Rx.p.threshold)).trans (by nlinarith only [mul_le_mul_of_nonneg_right N'.C_one Rx.p.threshold_pos.le])) (pow_le_pow_right₀ (by simp :1≤ (1+(separation i'.1 ro:ℝ))) hP.rehearsed.powers) (by positivity) (by positivity [N'.C_one,Rx.p.threshold_pos])))
    have hG' := hr.gauge.flow S Rx.p T (Xo).support b α (by assumption) hQ0 S.patch.odd_side hφ Pf Ft
    obtain ⟨hp,hY⟩:=boxed1 S.patch.L
    exact Cub.higher (Heritage.purse Rx.p _ _ (route T α,0) _ _ hp hY hr.warm hG'|>.1) ((mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp.le hY)).trans (le_add_of_nonneg_right (by positivity)))
end YM.Massive.Poised
#print axioms YM.Massive.Poised.piloting
