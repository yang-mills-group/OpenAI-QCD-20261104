import YM.Poised.Revenues
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
abbrev badgeQ (N':Libretto su n)(B:BudgetPoint)(G:ℕ)(s:ℕ):= (1+Hera.dueFee N' B s)*(1+(s:ℝ))^(3*G)
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
-- universal inequality
variable (hZ': (U':ℝ)*σ*|W₁|+|W₂| ≤ (Kit.slope S.patch.L)^G₂)
local notation "xK"=> badgeQ N' B G₂ nv
variable (hΩ: Charm B (Brim.plate Γ i).support (Ψ ∘ (crude Y χ M₁).view (individual p'))) -- hygiene
include hV hW hs hY' hS₀ hp hA he hr hA' hM₁ hI hK hK' hL hν hb hm hw hv hM hD hσ hZ' hw₁ hC H1 h2 h₁ hG Θ hα hq0 hq1 hq2 Vb
include hΩ
set_option maxHeartbeats 430000 in
lemma worthP (k:ℕ)(hk:k < U') :
   B.supBounds ro (Brim.plate Γ i).support ((framesF (purseX ro D' Ω')) ∘ (mantel k) ∘ (Ψ ∘ (crude Y χ M₁).view (individual p'))) (((Kit.slope S.patch.L)^G₂*xK) * fareK N' Vb K V' k G₂ M *R₀):=by
   let p:= (Xo).support; let L:= S.patch.L; let K':= framesF (purseX ro D' Ω'); let L':= K'.comp ((mantel k).comp Ψ); let s:= nv
   let X:=badgeQ N' B G₂ s; let N:= fareK N' Vb K V' k G₂ M; let v:= (Kit.slope L)^G₂
   have hg:= sinR Vb; have ho:0≤ A₁:=alert N' ..; have ht₀:= (boxed1 S.patch.L).1; have hp0:0≤ v:= pow_nonneg ht₀.le _
   have hhx:1 ≤(1+(s:ℝ))^(3*G₂):=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)); have hpX:= one_le_mul_of_one_le_of_one_le (show 1 ≤1+A₁ from le_add_of_nonneg_right ho) hhx
   have hmP:=senior (N':=N') Vb k G₂ K V' M hK hK' hL
   have hx':= hW.sight
   have hR:= hx'.travels
   have hT0:0≤ (v*X)*N*R₀:=by change 1≤ N at hmP; change 1≤ X at hpX; positivity
   let Tt:Charm B (Brim.plate Γ i).support (L' ∘ R₁):= (hΩ.scales (K'.comp (mantel k)))
   let Ha:Charm Rx.p V F:=⟨hx'.room,hx'.use⟩
   have hφ:Rooted V F:=⟨Ha.sites,hx'.gate⟩
   have hh:(k:ℝ)*σ*|W₁|+|W₂|≤v:= by apply le_trans _ hZ'; gcongr
   have hWv : ((k:ℝ)*σ*M^k*R₀)*|W₁|+(M^k*R₀)*|W₂| ≤ v*M^k*R₀:= calc
       _=((k:ℝ)*σ*|W₁|+|W₂|)*(M^k*R₀):=by ring
       _≤_:=(mul_le_mul_of_nonneg_right hh (by positivity : 0≤ M^k*R₀)).trans_eq (mul_assoc ..).symm
   change B.supBounds ro (Z).support (L' ∘ R₁) ((v*X)*N*R₀)
   by_cases hδ: Short S Rx.p p
   · let f:= plaque^k; have hf:1 ≤ f:= one_le_pow₀ plaque_pos; let a:= Fountain.tithy k K V' Vb G₂; have ha:0≤a:= tithy_nn Vb _ _ hK hK' k G₂
     refine covered Y Γ hP hB i F₀ hB₀ hxZ hV' he r' hc M₁ hO hZ hQ p' hY hx ht hRx L' Tt (x:=f*(M^k*R₀)) (t:= f*((k:ℝ)*σ*M^k*R₀)) (u:= f*(a*R₀*v)) (by positivity) (by positivity) (by positivity) hT0 ?_ (fun U hU=>?_)
     · have he : f*(M^k+a) ≤ N:= by unfold N fareK; apply le_add_of_nonneg_left; positivity
       let A:= A₁; change _+ f*(a*R₀*v)*A ≤ _; have hX : 1 ≤ X:= hpX; have hYA : A ≤ X:= by unfold X badgeQ; exact le_trans (le_add_of_nonneg_left zero_le_one) (le_mul_of_one_le_right (by linarith only [ho]) hhx)
       calc
          _= f*(((k:ℝ)*σ*M^k*R₀)*|W₁|+(M^k*R₀)*|W₂|)+ f*(a*R₀*v)*A:=by ring
          _≤ f*(v*M^k*R₀)*X+f*(a*R₀*v)*X:=add_le_add ((mul_le_mul_of_nonneg_left hWv (zero_le_one.trans hf)).trans (le_mul_of_one_le_right (by positivity) hX)) (mul_le_mul_of_nonneg_left hYA (by positivity))
          _=(v*X)*(f*(M^k+a))*R₀:=by ring
          _≤_:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hR
     exact payP Y Γ b hP Vb i T₀ F Ψ r' hs hx'.borel gWay U V hV w₀ hw hv Ha hφ hM hL hw₁ H1 (hW.issues _ hk) α G₁ hp D₂ G₂ hr K V' A hA hA' S₀ hS₀ hK' hν hb hm Θ hα hI hδ hq0 hq1 hq2 hY' hG hM₁ hσ (h₁ hδ) hU
   let TQ:= Hera.grandFee Vb
   refine covered Y Γ hP hB i F₀ hB₀ hxZ hV' he r' hc M₁ hO hZ hQ p' hY hx ht hRx L' Tt (x:=M^k*R₀) (t:= (k:ℝ)*σ*M^k*R₀) (u:= TQ*(M^k*R₀)) (by positivity) (by positivity) (by positivity) hT0 ?_ (fun U hU=> blemish Y Γ hP Vb i T₀ F Ψ r' hs hx'.borel gWay V hV hw hv Ha hφ D' H1 h2 hx' (hW.issues k hk) U hU hw₁ hC hL hM hσ hD) -- order
   apply (add_le_add hWv (le_refl _)).trans
   let D0:= (1+(s:ℝ))^(3*G₂)
   have hcA: A₁≤v*X:=by
       unfold X badgeQ; apply le_trans (b:=(1+(A₁))*(v*D0)) ; swap; · exact le_of_eq (by unfold D0; ring)
       exact (le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (by positivity) (weighted_gain p G₂ hδ))
   have hA:(1+TQ)*M^k ≤ N:=by unfold N fareK; have ha:=tithy_nn Vb K V' hK hK' k G₂; linarith [mul_nonneg (pow_nonneg (zero_le_one.trans plaque_pos) k) (show 0 ≤ M^k+Fountain.tithy k K V' Vb G₂ by positivity)]
   refine le_trans (add_le_add (show v*M^k*R₀ ≤ (v*X)*M^k*R₀ from mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hp0 hpX) (by positivity)) hR) (mul_le_mul_of_nonneg_left hcA (by positivity : 0≤ TQ*(M^k*R₀)))) ?_
   exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (mul_nonneg hp0 (zero_le_one.trans hpX))) hR)
end YM.Massive.Poised
#print axioms YM.Massive.Poised.worthP
