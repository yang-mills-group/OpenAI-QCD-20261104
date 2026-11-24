import YM.Poised.Northern
import YM.Poised.Vicinity
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
variable (T₀:Grid f→ VectorD (Site f) (Faces (Site c)))(F:Grid f→ Lat.Fields f 6)(Ψ: EvenA c N→L[ℝ]Lat.Fields c 6)
variable (hV:V ⊆ ((lore Rx).activities.reg i).support) (hX:∃ x, Sight V ((lore Rx).activities.reg i).site 2 Rx.p w F x) -- don't use
-- R'.Ψ all output.Info
open Fountain WardBin.Lies
variable (b0:Cover) (d0 k0:ℕ)(α:Directions su c) (W0:ℝ)
variable (f':Grid f→Lat.Fields f 6)(hG : ∀ k U,slots 6 k (f' (Lattice.gauge k U))=f' U) (heV:Charm Rx.p V f') (hS:∀ U,f' U∈ Creek.region (limits V)) (hB':∀ V,f' V ∈ layer (Faces (Site f)) d0)
local notation "Xq"=> (Xo).support
local notation "Yq"=> (Z).support
local notation "Xr"=>purseX (wrap f b0) k0 w
local notation "Yr"=> purseX ro k0 Ω'
variable {τ':ℝ}
variable (hh:Rx.p.supBounds (wrap f b0) V (framesF (purseX (wrap f b0) k0 w)∘f') τ') -- τ' variable
variable (N0 Yp A₀ :ℝ)(Zq:VectorD (Site f) (Faces (Site c)))(hZ':SeatD (purseX (wrap f b0) k0 w) (purseX (Brim.plate Γ i).site k0 Ω') Zq Yp)(htT:1≤Yp)(hw:0<w)(hy:0<Ω')
variable (hs:∀ A:Grid f, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support A →∀ V:Grid c, Ψ (Y.works r' A V)= changeVars (T₀ A) (f' A))
variable (hP0 : ∀ (F:Tree.Forest S.ratio)(k:S.Choices)(U:Grid f), Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → BeamRaw ((lore Rx).activities.reg i).support U (Sands.homeQ F Γ χ 1 i k D) gWay →
   (∀ l∈limits V,(∑ j:Faces (Site c),purseX (Brim.plate Γ i).site k0 Ω' j* ‖T₀ U l j‖) ≤Yp*purseX (wrap f b0) k0 w l) ∧
   ∀ l∈limits V,(∑ j:Faces (Site c),purseX (Brim.plate Γ i).site k0 Ω' j* ‖T₀ U l j-Zq l j‖) ≤t*purseX (wrap f b0) k0 w l)
variable (hM:0 ≤ t)(hz:Measurable f')
local notation "T0" =>framesF Yr ∘ (Ψ ∘ R₁)
local notation "Tz"=> framesF Yr ∘ cherub T Zq f'
-- promises re.Powers.Xq and α dir.
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (hI:wrap f b0=((lore Rx).activities.reg i).site)(h0:1 ≤ N0) (hα: ‖α‖ ≤ N0 * loom B (Heir.reach τ) N'.C)(hf:Sized Yp (route T α) Rx.p (wrap f b0)) (hK:∀ i',Mom.needed (((lore Rx).activities.reg i).support) i'→Lyre.width Rx.p (wrap f b0) i' ≤1)
variable (hP1:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A₀)(hL:N'.M * (N0* loom B (Heir.reach τ) N'.C) ≤1) (hL':0<W0)(hD:W0≤1)(hN:(1+patterns n)*(A₀*(N'.M*(N0* Heir.loom B (Heir.reach τ) N'.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W0)(hJ:Cub.opal N' D B Rx.p S.patch.L ((lore Rx).activities.reg i).support (Q.halo+5) τ (gStep Rx.beta)*N0^n ≤ W0)
variable (hΨ:Germ n (Ψ ∘ (crude Y χ M₁).view (individual p')) (1:Grid c))

omit ht hRx
include Vb hw hM hf hG heV hS hB' hh hP0 hQ hx hZ' htT hV hΨ hs hI hz h0 hP1 hL hL' hK hD hN hJ hy hα
local notation "meterR"=> AnalyticBridge.LocalGaussian.Moments.meter (Heir.Lute.heads su Rx.p S.patch.L Xq (Q.halo+5) τ) 0 D.K (2*((n+1)+(n+1)))
set_option maxHeartbeats 360000 in
lemma bounties (j:ℕ)(hj:j<n)(hr:B.dirBound ro α)(hh':‖α‖≤ Brim.canopyW su L B.power τ)(hn:2 ≤ n) : let p₀:= List.replicate j α
    ‖leftDerivs T0 p₀ 1-leftDerivs Tz p₀ 1‖ ≤ (((d0:ℝ)*t*Yp^d0*τ')*|W₁| +(Yp^d0*τ')*|W₂| + sheen d0 Vb W0 Yp *τ'*meterR):=by
     intro l; let T' := Tz; let Ff0:= Xq; let fQ:= fun A=> framesF Yr (changeVars Zq (f' A)); let YrA:=Ψ∘R₁; let p'':=T0
     have hZs:Charm Rx.p Xq f':=⟨fun i j hh=>heV.sites _ _ (fun i hi hj=>hh i (hV hi) (hV hj)),fun i hi=>heV.smooth _ (hi.mono_left hV)⟩
     have hVc:Germ n Tz (1:Grid c):=(framesF Yr).contDiff.contDiffAt.comp _ (nest (T:=T) Zq f' heV hP.rehearsed.orders); have hx:Germ n p'' (1:Grid c):=(framesF Yr).contDiff.contDiffAt.comp _ hΨ
     obtain ⟨L0,hL0,hG0⟩:=QCD.Dust.commune (X:=leftDerivs p'' l 1-leftDerivs Tz l 1) -- order eq
     have hQ0:l.length≤ n:=by simp [l,hj.le]
     change ‖leftDerivs p'' _ _-leftDerivs Tz _ _‖≤_; rw [hG0,map_sub, ← Push.Local.left_linear L0 l (show Push.Local.Chart n p'' 1 from hx) hQ0, ← Push.Local.left_linear L0 l (show Push.Local.Chart n Tz 1 from hVc) hQ0]
     obtain ⟨_,_,_,_,_,_,_,_,_,Ψ',hQ',hs'⟩:=hO; have hZy:0 < gStep Rx.beta:= inv_pos.mpr (Real.sqrt_pos.mpr Γ.laws.intake.positive)
     let fQ':=L0 ∘ fQ; have he(L:Faces (Site f)) (hL:L∈limits V): (∑ j:Faces (Site c), Yr j*‖Zq L j‖) ≤ Yp*Xr L:= ((SeatD.from_weights _ _ _ _ (purse_pos _ _ _ hw) (fun i=> (purse_pos _ _ _ hy i).le)).1 hZ').2 L
     let τ0:=(Yp^d0*τ'); let U := (L0.comp (framesF Yr)).comp (vat Zq); have hz':0≤τ0:=mul_nonneg (by positivity) hh.1; have h : Charm Rx.p V fQ':=heV.scales U
     let hΓ(U:Grid f)(hu:Healthy Rx.p.threshold V U)(X:List (Directions su f))(hl:X.length≤Rx.p.order)(hk:∀ i∈X,Rx.p.dirBound (wrap f b0) i):= hh.2 U hu X hl hk
     have hX: Rx.p.supBounds (wrap f b0) Xq fQ' τ0:=by
         refine ⟨hz',fun A H L hL hK=>?_⟩; let z:= leftDerivs f' L A; have hA:= H.mono_left hV; have hA':= heV.smooth A hA
         change ‖leftDerivs (U ∘ f') L A‖≤_; rw [Push.Local.left_linear _ _ hA' hL]; change ‖L0 (framesF _ (changeVars Zq z))‖ ≤ _; apply (L0.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL0).trans _); have hL'(i):=hK i; have hx:= hΓ A hA _ hL hK; rw [Push.Local.left_linear _ _ hA' hL] at hx
         have hS': z∈region (limits V):= stays_left (Submodule.restrictScalars ℝ ((region (limits (F:=6) V)).toSubmodule)) _ hS _ _
         exact (lane Zq _ _ _ (purse_pos _ _ _ hw) (purse_pos _ _ _ hy) (zero_le_one.trans htT) he z hS' (show z∈ layer (Faces (Site f)) d0 from stays_left (Submodule.restrictScalars ℝ (layer (Faces (Site f)) d0)) _ hB' _ _)).trans (mul_le_mul_of_nonneg_left hx (pow_nonneg (zero_le_one.trans htT) _))
     have hx':=hh.1
     refine sunlit Y F₀ (R:=trimP T O δ β y) (P':=B) (hB₀:=hB₀) hxZ hV' (by assumption) hP hB r' i hc M₁ hQ' hs' hZ hQ p' hY ((L0.comp (framesF Yr)).comp Ψ) _ fQ' (L0∘T') l (hZs.scales U).1 (U.measurable.comp hz) (fun i hi=> hX.2 i hi [] (by simp) (by simp)) ?_ ?_ (L0.contDiff.contDiffAt.comp _ hx) (L0.contDiff.contDiffAt.comp _ hVc) (by assumption) hz' (by positivity) hQ0 (fun i hi=> (List.eq_of_mem_replicate hi).symm ▸ hr) (fun i=> (List.eq_of_mem_replicate (List.get_mem l i)).symm ▸ hh')
     · intro Fq k _ A HA HB; change ‖L0 (framesF _ (Ψ _))-L0 (framesF _ (changeVars Zq (f' A)))‖≤ _; rw [hs A HA,←map_sub,← map_sub]; obtain ⟨h,h'⟩:=hP0 Fq k A HA HB; apply (L0.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hL0).trans _)
       apply (tenderV _ _ _ _ _ (purse_pos _ _ _ hw) (purse_pos _ _ _ hy) (zero_le_one.trans htT) t hM htT h he h' (f' A) (hS _) (hB' _)).trans (mul_le_mul_of_nonneg_left (show load Xr _ ≤ _ from hΓ A (HA.mono_left hV) [] (by simp) (by simp)) (by positivity))
     intro F yq; let a:= mapcase Γ i F
     have hxI:wrap f b0∈((lore Rx).activities.reg i).support:=by rw [hI]; exact ((lore Rx).activities.reg i).anchor
     have hr' : B.dirBound (S.ratio.parent (wrap f b0)) α:=by rw [hI]; exact hr
     exact blanket (k:=yq) a hP b0 hxI hn 1 α N0 Yp hα h0 _ Yr Zq w A₀ hZ' htT (purse_pos _ _ _ hy) hw hP1 hL W0 hN f' d0 hG hZs hB' ⟨hh.1,fun V hv=> hh.2 V (hv.mono_left hV)⟩ Vb hf hK L0 hL0 χ hr' hL' hD (billboard Γ le_rfl i) hJ hZy hX _ hj -- syntax
end YM.Massive.Poised
#print axioms YM.Massive.Poised.bounties
