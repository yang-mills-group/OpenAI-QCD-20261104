import YM.Poised.Barr
import YM.Poised.Intone
/-! # ap strings post.P.Full Price -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) (R:BudgetPoint)
variable (X:Support l)(Y:Support c)(b b':Cover) {u v w L:ℕ} {τ σ t vo vi A C :ℝ}
-- key readers. adapt crop
section Spin
variable [Fintype B]
def peel (V:Support l) : VectorD (Site l) B →L[ℝ] VectorD (Site l) B:= ContinuousLinearMap.pi fun i=> if i ∈ Cove.limits (F:=6) V then ContinuousLinearMap.proj i else 0
lemma peelB (V:Support l)(Z:VectorD (Site l) B)(i:Site l) : asks (peel V Z) i=if i∈V then asks Z i else 0:=by funext j; by_cases h:i∈V<;> simp only [h,↓reduceIte]; all_goals unfold asks peel; rw [ContinuousLinearMap.pi_apply]; simp only [life_mem,h,↓reduceIte]; rfl
lemma screen_glazed (x:Pipes.Path l B)(V:Support l): Glazed ((Mom.screen V).prodMap (peel V) x) x V:=by
    refine ⟨fun i hi=>?_,fun i hi=>?_⟩; · change Mom.screen V _ _=_; rw [Mom.screen_at,if_pos hi]; rfl
    change asks (peel V x.2) i=_; rw [peelB,if_pos hi]
abbrev hiddenS (X: Support l)(b:Cover)(F:Cover→Flet B):VectorD (Site l) B:=flats fun x:Site l=> if x∈X then ap l (plinth b x) • F (plinth b x) else 0
lemma revealedS(x:VectorD (Site l) B) :peel X x= hiddenS X b (transitS x):=by
    apply flat_ext; intro i; unfold hiddenS; rw [invers,peelB]; split; swap; · rfl
    rw [transitS,pl_sq,smul_smul,ap_sq,one_smul]
end Spin
variable {X Y b b'} -- b now
variable (hΩ:Cruising (sliceL P h) X Y b b' u v)(H:TaperHol)(J:Labels.Jet su)
abbrev forwardG (X:Support l)(b:Cover)(f:Carrier.Window su.Color): Directions su l:= Mom.screen X fun i=> f (plinth b i.1) i.2
lemma meetsG (hT : Whole T.R.A0) (q:Directions su c) : Mom.screen X (Heir.route T q)=forwardG X b (applyLine T.R.A0 (transitL q)):=by
    apply congr_arg; rw [← leans P h T q hT]; funext i; unfold transitL; rw [pl_sq]
lemma mintedB (x:Site l)(hx:x∈X) :x=wrap l (plinth b x):=(pl_sq b x).symm
variable (d n) (vo t :ℝ)
abbrev actionT : Pipes.Path l (ZBand d):= (Mom.screen X (Heir.route T (visionL b' H Y (t • J) n d)),peel X (acting P h (visionS (c:=c) d n H.T b' vo)))
abbrev craftT : Pipes.Path l (ZBand d):= (forwardG X b (applyLine T.R.A0 (verdict (paintL b' (t • J) n d))),hiddenS X b (serve P (fun i=> paintS b' vo n d (Place.seat i))))
end Chute
end YM.Massive.Poised
