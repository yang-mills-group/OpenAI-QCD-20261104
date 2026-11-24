import YM.MassiveQCD.Apron.Awake
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (R':Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "Gm"=> deckHue H G P₀ R'
local notation "M"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
/-- spectral-work costs all on encoded guest tape. use right-sided markers; orientation
 on labels in Fleet of **any** dimension M compatible with these concrete encode calls -/
noncomputable def closet :Fleet H (Wound R') (Ribbon.ample N I) where
 limit i:= typo (P₀.wish (spent i.1))
 ground i:=i.1.biUnion R'
 fine i:=petal G P₀ i.1
 window i:=radio G P₀ i.1
 compat i j:= Disjoint (i.1.biUnion R') (j.1.biUnion R')
 works i U _:=δ⁻¹^budget P₀ i.1 • banknote N (S.ratio.parent ∘ z) a (X.hue O.threshold G i.1 U)
variable [Fintype D][Countable E][Countable J]
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ R')
local notation "Ξ"=> closet H G R' X z a
include hw
lemma flowing (i:Finset (Fj D E J)): Measurable (fun U=>Β (X.hue t G i U)):= ((Β).toLinearMap.continuous_of_finiteDimensional.measurable).comp (X.glory G hw i)
lemma floorsT : (Ξ).speaking:= fun i=>(measurable_const.smul (flowing G X z a hw i.1)).comp measurable_fst
include hk in
lemma residentG :(Ξ).gator:=by
    intro i U V; apply mixT; change pen N z' a (X.hue t G i.1 U).val ∈_; obtain ⟨hp,hZ⟩:=X.lights_hue G hw hk _ U
    have he:=hp.exact; rw [← he]; apply Ribbon.entitled; · exact hZ _
    intro j hj; exact X.endowment G hw hk _ (mem_image_of_mem _ (Ribbon.located q' _ _ hj))
lemma scout (u:Lat.Frame f)(V:Grid f)(i:Finset (Fj D E J))(hT:Stitch.Tablet.Toned G)(he:Cove.Count G P₀ R') : (trade (Lat.rotates M (u∘ S.ratio.embed))).passL (Β (X.hue t G i (Lattice.gauge u V)))= Β (X.hue t G i V):=by
    apply Subtype.ext; rw [← X.insulated G hw V u hT i]; let s:= X.markers i; let A:=z'; let W:=(burst q' s)
    let Y:= X.hue t G i (Lattice.gauge u V); let x:= (scrape (Keys c N) W Y.val); let g:=S.ratio; let p:Tine c N I:=Stitch.Tablet.dance I (u∘g.embed) N Y
    change slots M _ (pen N z' a Y.val)= pen N z' a (carry _ _ Y.val); rw [show (Y.val)= Ribbon.stake (Keys c N) W x from (X.lights_hue G hw he i _).1.exact.symm, Ribbon.speaks]; exact Ribbon.signal N A _ q' _ a x
include hk
lemma flaps (hT: Stitch.Tablet.Toned G) : Colored (Ξ):=by
    let Y:= Ξ; refine ⟨fun w=>⟨phare _,fun i x y=>?_⟩⟩; let U:=constantGauge w S.ratio; change (trade _).passL (δ⁻¹^budget P₀ i.1 • (Β (X.hue t G i.1 (Lattice.gauge U x))))= δ⁻¹^_ • _; let K:= trade (Lat.rotates M w)
    rw [eSM K.passL K.phare]; apply congr_arg; let F:= (scout G R' X z a hw U x i.1 hT hk); have he: U ∘ S.ratio.embed=w:= funext fun i=> congr_arg w (S.ratio.embed_parent _); rw [he] at F; exact F
variable {p₁:E→ℝ}{p₂:J→ℝ}{m:D→ℝ}{r s u η h γ:ℝ}
variable (hh:X.Coins p₁ p₂ h O.threshold)(hc:Peak G O.threshold h a r m)
-- h ≤ storage? important, no noise. price actual.
omit hk
include hh hc
local notation "b!"=> mintD H G P₀ R' m p₁ p₂ r
lemma cap (hd:0<δ)(i:Wound R')(U: Grid f)(V: Grid c): ‖token c M a ((Ξ).works i U V)‖ ≤ mintD H G P₀ R' m p₁ p₂ r i:=by
   -- need hk for polite_bill! omit? Wave.P.marker output polite can derive without hk for dye.
   let X' := X.hue t G i.1 U; let y:= X.markers i.1; have hp:Polite q' y X':= by
       unfold X' Stitch.Tablet.hue; split; · exact politeStep _ (X.lights_made G hw _ U).1 rfl
       exact polite_nil ..
   have hr: load (fun _=>a) (pen N z' a X'.val)= Stitch.Tablet.credits a X':=by rw [← hp.exact, Ribbon.penkin N z' a _ hc.cup, Stitch.Tablet.polite_bill y _ hp hc.cup]
   change ‖token _ _ a (δ⁻¹ ^ budget P₀ i.1 • Β X')‖ ≤ _; rw [map_smul,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ δ⁻¹ ^ budget P₀ i.1)]; exact mul_le_mul_of_nonneg_left (hr.trans_le (Stitch.Tablet.pinch_new X G hw hh hc U i.2)) (by positivity)
omit hc hh
include hk
set_option maxHeartbeats 500000 in
lemma ensembleX (_he:R'=roof G P₀ 30 (radiusB τ)) (hp:Stitch.Tablet.Toned G) (Yv:(Gm).Famous)(ha:1≤a)(hh:X.Coins p₁ p₂ h O.threshold)(hc:Peak G O.threshold h a r m)(hδ:0<δ): (Ξ).Famous:=by
    refine ⟨Yv.horizons,Yv.boot,?_,fun _ _ _ _ _=>rfl,?_,?_,Yv.signs,Yv.issued⟩
    · intro i V U Y hv; let p:=i.1; let ψ x:= δ⁻¹^budget P₀ p • Β x; exact congr_arg ψ (RG.UsesFinal.allReads O.threshold _ _ (X.ears G hw p) U Y hv)
    · intro i V; refine ⟨measurable_const.smul (flowing G X z a hw i.1),mintD H G P₀ R' m p₁ p₂ r i,fun u=> (tore _ ha).trans (cap H G R' X z a hw hh hc hδ i u V)⟩
    intro i V g hhg u; let T:=trade (Lat.rotates M (g ∘ S.ratio.embed)); let p:= (scout G R' X z a hw g u i.1 hp hk); have hz := Loom.flower H _ (funext hhg) (Β (X.hue t G i.1 (gauge g u))) -- reorder
    exact congr_arg (δ⁻¹^budget P₀ i.1 • ·) (hz.symm.trans p)
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.cap
