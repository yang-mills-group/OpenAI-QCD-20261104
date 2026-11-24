import YM.Poised.Caliph
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
variable (U':ℕ)(D':ℕ) -- U' spill, D' endpoint power
variable (hW: Pipes.Flame F Rx.p V ((lore Rx).activities.reg i).site w D' U' R₀)(hG:∀ k U, Lat.slots 6 k (F (Lattice.gauge k U))=F U)
-- X=old test.Use input R0.Caract.A root & value.Tensor.Engine.
variable (hs:∀ A:Grid f, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support A →∀ V:Grid c, Ψ (Y.works r' A V)= changeVars (T₀ A) (F A)) (hY':∀ U:Grid f,∀ g:Frame c, Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → let W:=Lattice.gauge (g∘ S.ratio.parent) U; slots 6 g (changeVars (T₀ W) (F W))=changeVars (T₀ U) (F U))
variable (b:Cover)(G₁ G₂ D₂:ℕ)(hI:wrap f b=((lore Rx).activities.reg i).site) (Θ: SourceRead.TaperHol) (hα:∀ (J:Labels.Jet su)(j:ℕ), j<G₂→ WardBin.leading j (Beacon.moment (d:=D₂) Θ b J F)=0)
-- parameters.
variable (K ζ' α A ψ M σ w₀ w'₀ V':ℝ)(hK:1≤K)(hK':1≤V') -- M outputC'.Equation accounting
variable (hp:P.Funds S T)(hr:Rx.p.power=G₁)(hA:Fountain.ScrollX N' α K G₂ G₁ P)(hA':∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→Through n (yaw i j) x A)(hw:0<w)(hv:0 < Ω')
variable (S₀ : VectorD (Site f) (Faces (Site c))) (hS₀: Pipes.Heritage Rx.p ((lore Rx).activities.reg i).support b (purseX ((lore Rx).activities.reg i).site D' w) (purseX (Brim.plate Γ i).site D' Ω') G₂ (0,S₀) (Kit.slope S.patch.L) V')
variable (hν: Heir.clinicFee n D.Q*(Heir.loom B (Heir.reach τ) N'.C)^2 + D.ε*Rx.p.threshold ≤ (Kit.slope S.patch.L)^max G₂ 2 * Rx.p.threshold) (hb: (1+patterns n)*(A*(N'.M*Heir.loom B (Heir.reach τ) N'.C))*((Fintype.card Pipes.Shell:ℝ)*pup G₂ V' * (Kit.slope S.patch.L)^2) ≤ (Kit.slope S.patch.L)^max G₂ 2) (hm:N'.M*Heir.loom B (Heir.reach τ) N'.C ≤1)
variable (hq0:D₂ ≤ Rx.p.order)(hq1:G₂≤D₂+1)(hq2:G₂≤2*n)
variable (hM₁ : pup G₂ V' * (Kit.slope S.patch.L)^2 ≤ M) (hM: Ω'*2^D'*w₀ ≤ M*w)(hw₁:0 ≤w₀)(hL:1≤ M)
variable (hD : Ω'*2^D'*w'₀ ≤ σ*w)(hC:0≤w'₀)
variable (H1:∀ U,Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → Stanch V S.ratio (T₀ U) D' w₀) (h2:∀ U U',Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U' →Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → BeamRaw ((lore Rx).activities.reg i).support U U' gWay → Stanch V S.ratio (T₀ U - T₀ U') D' w'₀)
variable (hσ:0 ≤ σ)(h₁:Short S Rx.p ((lore Rx).activities.reg i).support→∀ (F0: Tree.Forest S.ratio)(k:S.Choices) (V' : Grid c) (g:Frame c),Healthy B.threshold (Brim.plate Γ i).support V' →Heir.Canvas B (Brim.plate Γ i).site (Heir.reach τ) V' g n N'.C → ∀ U:Grid f,Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → BeamRaw ((lore Rx).activities.reg i).support U (Sands.homeQ F0 Γ χ V' i k D) gWay→ let B':=Lattice.gauge (g∘ S.ratio.parent) U; ∀ i': Faces (Site f), i' ∈ limits V→ (∑ j: Faces (Site c),purseX (Brim.plate Γ i).site D' Ω' j* ‖T₀ B' i' j - S₀ i' j‖) ≤ σ*purseX (wrap f b) D' w i')
local notation "xK"=> badgeQ N' B G₂ nv
variable (hΩ: Charm B (Brim.plate Γ i).support (Ψ ∘ (crude Y χ M₁).view (individual p')))
omit ht hRx
include ht hRx hΩ hV hw hx hw hs hW hv Vb
-- large. Choose (slope)^ζ ≤ enough.
variable {σ₁ σ₂ v' :ℝ}
variable (hv' : 0 ≤ v')(hv₃ : 4*(v'*Ω') ≤ Kit.slope S.patch.L/2*w)(hL₃: 4*(v'*Ω') ≤ w/4)
variable (p₂:ℝ)(hw₃:0≤ σ₁)(hu₃:4*(σ₂*Ω') ≤ σ₁*(w/4)) (hh1:∀ U,Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → Stanch V S.ratio (T₀ U) 2 v') (hh2:∀ U U',Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U' →Healthy Rx.p.threshold ((lore Rx).activities.reg i).support U → BeamRaw ((lore Rx).activities.reg i).support U U' gWay → Stanch V S.ratio (T₀ U - T₀ U') 2 σ₂)
variable (hu4: G₂ ≤ U')(hΨ: σ₁*|W₁|+|W₂| ≤ Kit.slope S.patch.L ^ G₂)
include hv₃ hL₃ hu₃ hw₃ hΨ hh1 hh2 hu4
set_option maxHeartbeats 400000 in
theorem echoes : B.supBounds ro (Brim.plate Γ i).support ((capSpill U' Ω' ro) ∘ (Ψ ∘ R₁)) ((Kit.slope S.patch.L^G₂*xK)*(1+Hera.grandFee Vb)*R₀):=by
    let v:= Kit.slope S.patch.L; let a:= Hera.grandFee Vb; let K:= (bias (g:= Stew.lens (N:=6) ro) Ω').restrictScalars ℝ -- check args
    have hx':=hW.sight; have hR:= hx'.travels; have hg:0≤a:= sinR Vb; obtain ⟨h₀,h₃⟩:=boxed1 S.patch.L; have ho:0≤A₁:=alert N' ..; let x:= xK; let c:=v^U'*R₀; have hX:1 ≤ x:=by unfold x badgeQ; apply one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp));
    have htX : 0 ≤ c:=by unfold c; positivity
    have hf:v^U' ≤ v^G₂:=pow_le_pow_of_le_one h₀.le h₃ hu4
    let L' := capSpill U' Ω' ro; -- high.Emphas
    refine covered Y Γ hP hB i F₀ hB₀ hxZ hV' he r' hc M₁ hO hZ hQ p' hY hx ht hRx (L'.comp Ψ) (hΩ.scales L') (x:=c) (t:=σ₁*R₀) (u:=a*c) htX (by positivity) (by positivity) ?_ ?_ (fun X hX=> ?_)
    · change 0 ≤ (v^_*x)*(1+a)*_; positivity
    · have hM : σ₁*R₀*|W₁|+c*|W₂| ≤ v^G₂*R₀:= calc
         _≤ (σ₁*|W₁|+|W₂|)*R₀:=by rw [add_mul]; unfold c; have hx:v^U'*R₀≤R₀:=mul_le_of_le_one_left hR (pow_le_one₀ h₀.le h₃); exact add_le_add (le_of_eq (by ring)) ((mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans_eq (mul_comm ..))
         _≤_:=mul_le_mul_of_nonneg_right hΨ hR
      have hA : A₁ ≤ xK:= by unfold badgeQ; exact (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (by positivity : 0≤1+A₁) (one_le_pow₀ (by simp)))
      apply (add_le_add hM (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf hR) hg) hA ho (by positivity))).trans
      calc v^G₂*R₀+a*(v^G₂*R₀)*x ≤ v^G₂*R₀*x+a*(v^G₂*R₀)*x:=by have h:= le_mul_of_one_le_right (show 0 ≤ v^G₂ * R₀ by positivity) hX; linarith only [h]
           _= _:=by unfold v a x; ring
    · let Q:= X.comp K; have hK : Spice.rootBill ro Ω' Q:=fun i=>(X.le_opNorm (K i)).trans (mul_le_of_le_one_left (norm_nonneg _) hX)
      have hy: Rooted V F:=⟨hx'.room,hx'.gate⟩; let H':=panel_courier (χ:=χ) Y Γ hP Vb i T₀ F Ψ r' hs hx'.borel gWay V hV hw hv ⟨hx'.room,hx'.use⟩ hy 2 hh1 hh2 U' Q hK h₀.le h₃ hx' rfl hv₃ hL₃ hw₃ hu₃
      exact H'
end YM.Massive.Poised
