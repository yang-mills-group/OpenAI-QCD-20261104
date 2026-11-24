import YM.Poised.Incident
import YM.Poised.Dents
/-! # projected coordinate pricing on every bracelet. paid post-L.Uniform.B.Focus.Capture -/
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
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Sage PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Brim
open AnalyticBridge.SectorAffine.Offset Planned.AtomRegular
open QCD.Dust QCD.Brick Pipes Spice MassiveQCD.Lyre Shells Sands MultiNext.SignedSource.Ease
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ σ η μ W:ℝ}
variable {R Rx:Rep su f}{O O₁:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {δ y h t u :ℝ}{q p n m j k α:ℕ}
namespace TrainG
open Stative Steed Chute Planned.PrimaryIntegral295.Carrier UV SourceRead
structure LinksT (τ σ A:ℝ)(H:TaperHol)(V:Hera.Rights su n)(L:Side)(j k E Pk d D':ℕ)(K:KernelChoices)(v:ℕ)(x t1:ℝ) :Prop where
    pays (P:Flight j k) (hp: P.L=L) : (∀ (u v:Pipes.Shell)(x:Cover),Width σ τ (arch (P:Flight j k) u v x)) ∧ (linesOf P K.penalty).strip σ τ -- fix binder
    bridge (P:Flight j k)(h:f.val=c.val*P.L.val) (T:Tube su (Flight.visit P K h))(O':BudgetPoint)(F:Grid f→Lat.Fields f 6)(Z:Grid c→ Lat.Fields c 6)(Y:Support c)(o:Site c)(b:Cover)(t' κ:ℝ)(A Q:UV.Pol d):P.L=L→Q∈UV.cap d→A∈UV.cap d→ Beacon.ActionTest H b (kite P h T F Y) Q → Beacon.ActionTest H b Z A → LocalOn Y Z → ContDiffAt ℝ d (Z∘increment 1) 0 → ContDiffAt ℝ d (F∘increment 1) 0 → o∈Y → coverNumber (radiusB x) Y≤ radiusB x → separation o (wrap c b) ≤ E → O'.threshold ≤ 2*fiery su x L → O'.power=Pk → Beacon.surface d ≤ D' → d*d≤Pk →0<t' →0≤ κ → (∀ j:Chute.Λ d,∀ i:ℕ,i≤d→∀ α:Directions su c,O'.dirBound o α→ ‖α‖ ≤ canopyW su L O'.power x→ ‖leftDerivs (framesF (purseX o D' t') ∘mantel j.val∘ Z) (List.replicate i α) 1-leftDerivs (framesF (purseX o D' t') ∘ Fountain.cherub T (flareV (proton P h)) (mantel j.val ∘F)) (List.replicate i α) 1‖ ≤ fan L (-1/2) x*κ)→∀ i:Rings d, ‖Stative.fare i A O'.threshold t' - Stative.fare i Q O'.threshold t'‖ ≤ t1*κ
    honored (P:Flight j k)(h:f.val=c.val*P.L.val)(T: Tube su (Flight.visit P K h))(R:BudgetPoint)(X:Support f)(Y:Support c)(b b':Cover)(vi vo t κ:ℝ)(z:ℕ):P.L=L→ T.R.A0=linesOf P K.penalty → n ≤ R.order → Fintype.card (Palette.ZBand d) < z → Harbor X Y b b' T R σ τ A vi vo t (radiusB x) v →∀ (F:Grid f→ Lat.Fields f 6) (U₀ U₁:UV.Pol d), Flame F R X (wrap f b) vi D' z κ → U₀∈UV.cap d→U₁∈UV.cap d → Beacon.ActionTest H b F U₀→ Beacon.ActionTest H b' (kite P h T F Y) U₁→ d/2≤j→(∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)→∀ i:Rings d, (∀ (J:Labels.Jet su)(k:ℕ), k<UV.weight i.val→ WardBin.leading k (Beacon.moment (d:=d) H b J F)=0)→ ‖Stative.fare i U₁ t vo - (Kit.slope P.L:ℂ)^(UV.weight i.val) * Stative.fare i U₀ t vo‖ ≤ t1*κ
-- stake all A.Call.
abbrev relief (L:Side)(x:ℝ) := fan L (-1/3) x
lemma draft (H:TaperHol)(V:Hera.Rights su n)(L:Side)(j k E Pk d D':ℕ)(K:KernelChoices)(A:ℝ)(ha:0 ≤ A)(hD:d<n)(hj:4≤j)(hk:4≤k)(v:ℝ→ℕ)(hv:Seat L 0 (fun x=>(v x:ℝ))):
    ∃ τ σ:ℝ,0 ≤ τ∧0 < σ∧∀ᶠ x in atTop,∀ (c f:Side),LinksT (c:=c) (f:=f) τ σ A H V L j k E Pk d D' K (v x) x (relief L x):=by
    obtain ⟨σ,τ,hσ,hτ,h⟩:= gold j k K L hj hk
    choose C hC H0 using fun i:Rings d=> restored E d Pk D' i
    choose b hb H' using fun i:Rings d=> pastL i H j k D' V σ τ A ha hσ hτ hD
    have hX:= sunset L hσ ((-1/2)); have hY:= herring hv d (n+1); have hS (i:Rings d):Seat L ((-1/2)) (fun x=>b i*tar σ (radiusB x)*ratioP d (n+1) (v x)):=by simpa using! ((hX.timesL _).ponies hY)
    have hz(i:Rings d): Seat L ((-1/2)) (fun x=> C i*fan L (-1/2) x):= Seat.timesL (L:=L) (a:=(-1/2)) Seat.keeps (C i) -- implicit
    refine ⟨τ,σ,hτ,hσ,?_⟩; filter_upwards [eventually_all.mpr (fun i=> hz i (-1/3) (by norm_num)), eventually_all.mpr (fun i=> hS i (-1/3) (by norm_num))] with x hx hy c f
    constructor
    · intro P hp; exact ⟨(h P hp).2,(h P hp).1⟩
    · intro P D T O F Z Y o b t κ A Q hp hQ hAr hT hSΦ hYu hZ hF ho hCh hE hx' hPK hβ hDi ht hK he i
      subst L; apply (H0 i P D K T O F Z Y o H b x (fan P.L (-1/2) x*κ) t A Q hQ hAr hT hSΦ hYu hZ hF ho hCh hE hx' hPK hβ (hPK.symm ▸ hDi) ht (mul_nonneg (fan_pos ..).le hK) he).trans; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hx i)) hK
    intro P D T O X Y a a' vy vo t κ z hp hP hN hV hΛ F U₀ U₁ he hf hg hF hE hD hA i hG; apply ((H' i P K c f D T O (v x) (radiusB x) X Y a a' vy vo t κ z hN hV hΛ F U₁ he hg hE).2 K.penalty K.penalty_pos hP hD hA hG U₀ hf hF).trans; exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hy i)) he.sight.travels
end TrainG
end YM.Massive.Poised
#print axioms YM.Massive.Poised.TrainG.draft
