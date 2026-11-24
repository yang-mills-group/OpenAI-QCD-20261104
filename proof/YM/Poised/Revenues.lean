import YM.Poised.Crest
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
-- grant packet all.L∀. normal.Act.
theorem covered (X:EvenA c N→L[ℝ] Lat.Fields c 6) (h: Charm B (Brim.plate Γ i).support (X ∘ R₁))(hp0:0≤x)(hp1:0≤t)(hp2:0≤u)(hp:0≤v) (hK:t*|W₁|+x*|W₂|+u*A₁ ≤ v) (hL:∀ U:Lat.Fields c 6→L[ℝ]ℝ, ‖U‖≤1→ Private Y B N' Γ χ D gWay r' i x t u (U.comp X)) :
 B.supBounds (Z).site (Z).support (X ∘ R₁) v:=by
    refine ⟨hp,?_⟩; intro U hU l hl hΘ; obtain ⟨g,hg,hg'⟩:=commune (X:=leftDerivs (X ∘ R₁) l U)
    have hc': B.threshold ≤ 2*Rx.p.threshold:= by rw [hP.rehearsed.temp_eq]; exact hP.rehearsed.tensions.coarse
    obtain ⟨f0,f1,v1,w1,w2,w3,w4,w5,w6,u₁,h1,h2⟩:=hO
    have he' := Hera.tern ht hRx hc' (show 0 ≤ gStep Rx.beta from by unfold gStep; positivity) hp2 nv (le_refl (coverNumber Rx.p.B ((Sands.lore Rx).activities.reg i).support)) -- remove
    have hA : t*|W₁|+x*|W₂|+ Hera.lyreFee N' u D B Rx.p L ((lore Rx).activities.reg i).support (Q.halo+5) τ (gStep Rx.beta) ≤ v:= (add_le_add le_rfl he').trans hK
    have hM:= grantsP (F':=Γ) Y F₀ hB₀ hxZ hV' he hP hB r' i hc M₁ h1 h2 hZ hQ p' hY (g.comp X) u (h.scales g) hx (hL _ hg) hp0 hp1 hp2 hp hA
    rw [hg', ← Push.Local.left_linear _ _ (h.smooth _ hU) hl]; exact hM.2 U hU l hl hΘ
-- act budget aggregation container
structure Headroom (N': Libretto su n)(Vb:Hera.Rights su n)(q j d:ℕ)(X₂ X₃ C:ℝ)(P:Teller su) where -- pre-L only, export bound after.Buyer.Q ratio.
   pos: 1 ≤ X₂
   large:1 ≤ X₃
   filled:1 ≤ C
-- statement cost independent high influence.Pay.V.Type.Current.Y
abbrev fareK (N': Libretto su n)(Vb:Hera.Rights su n)(γ ε:ℝ)(d m:ℕ) (C:ℝ):ℝ:=1+(1+Hera.grandFee Vb)*C^d+ plaque^d*(C^d+Fountain.tithy d γ ε Vb m)
-- include poly nonshort. q for projection engineering weight; λ for spin.Works per k.
-- ** small from Private additive such costs. branch Z support equal etc. **
omit hP hV' hB₀ hxZ hB hc hO he hZ hQ hY hx ht hRx
lemma weighted_gain (X:Support f) (k:ℕ)(h:¬ Short S B X):
 let L:=S.patch.L; let Q:=coverNumber B.B X; 1≤ (Kit.slope L)^k*(1+(Q:ℝ))^(3*k):=by
   intro L Q; have he:(L.val:ℝ)≤(Q:ℝ)^3:= by exact_mod_cast le_of_not_gt h -- neg form
   rw [pow_mul, ← mul_pow]; apply one_le_pow₀; unfold Kit.slope; rw [one_le_inv_mul₀ (by positivity)]; have hQ:1 ≤ (L.val:ℝ):= by exact_mod_cast L.property
   have hh:= Real.sq_sqrt (show 0≤ (L.val:ℝ) by positivity); refine le_trans (show Real.sqrt (L.val:ℝ) ≤ (Q:ℝ)^3 from ?_) (pow_le_pow_left₀ (by positivity) (le_add_of_nonneg_left zero_le_one) _); nlinarith only [Real.sqrt_nonneg (L.val:ℝ),he,hQ,hh]
lemma tithy_nn (Vb:Hera.Rights su n)(γ ε:ℝ)(hγ:1 ≤ γ)(hε:1 ≤ ε)(d m:ℕ) : 0 ≤ Fountain.tithy d γ ε Vb m:=by
   have hc:=Pipes.central_one Vb (by linarith:1 ≤ 1+γ+(1+ε)) d m; unfold Fountain.tithy; positivity [patterns_nonneg n]
-- unify `covered` at any Case using context. Dated assembly after. Need compare scalar factor powers γ,η. Use same η.Sensor.
lemma senior (Vb:Hera.Rights su n)(k d:ℕ)(A B' C:ℝ)(hp:1 ≤ A)(hB:1 ≤ B')(hC:1 ≤ C): 1 ≤ fareK N' Vb A B' k d C:=by
    unfold fareK; have h0:= tithy_nn Vb _ _ hp hB k d; have hr:= plaque_pos; have hh:= sinR Vb; linarith [pow_nonneg (zero_le_one.trans hr) k,mul_nonneg (pow_nonneg (zero_le_one.trans hr) k) (show 0≤C^k+Fountain.tithy k A B' Vb d by positivity),show 0≤(1+ Hera.grandFee Vb)*C^k by positivity]
end YM.Massive.Poised
