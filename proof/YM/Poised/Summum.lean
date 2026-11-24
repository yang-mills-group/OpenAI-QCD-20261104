import YM.Poised.Pearls
import YM.Poised.Sheets
/-! # Exact identity comparator of prince projected panels.P.Book. uses buffered Y+ *in projection of the actual* using Small. Does not claim support or local Gauge for the approximate quantity. -/
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
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h))
variable {X:Support l}{Y:Support c}{b b':Cover} {u v L:ℕ} {τ t vo A C a :ℝ}
open Display Kites Fountain
abbrev splitF (Y:Support c)(W:Grid c):Grid c:=fun i=> if Mom.needed Y i then W i else 1
lemma split_inc (q:Directions su c): splitF Y (increment 1 q)=increment 1 (Mom.screen Y q):=by
   funext i; unfold splitF; unfold increment; rw [Mom.screen_at]; split; rfl
   simp
variable (F:Grid l→Lat.Fields l 6)
abbrev kite (Y:Support c): Grid c→Lat.Fields c 6:= cherub T (flareV (proton P h)) F ∘ splitF Y
lemma powered : kite P h T F Y ∘ increment 1=ᶠ[𝓝 0] fun y=>changeVars (flareV (proton P h)) (F (increment (1:Grid l) (Heir.route T (Mom.screen Y y)))):=by
   let L:=Mom.screen (G:=su) Y; have he : Tendsto L (𝓝 0) (𝓝 0):=by simpa only [map_zero] using L.continuous.tendsto (0:Directions su c)
   filter_upwards [he.eventually (lofts (T:=T) (flareV (proton P h)) F)] with y hy; change cherub _ _ _ (splitF _ (increment _ y))=_; rw [split_inc]; exact hy
variable (he:Rooted X F)(hf:ContDiffAt ℝ d (F∘increment 1) 0)
local notation "Fs"=>flareV (proton P h)
include hf
lemma powered_germ :ContDiffAt ℝ d (kite P h T F Y∘increment 1) 0:=by
   refine ContDiffAt.congr_of_eventuallyEq ?_ (powered ..); let L:= ((changeVars Fs).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; let A:= (Heir.route T).comp (Mom.screen Y); exact L.contDiff.contDiffAt.comp (f:=(F∘increment 1)∘A) _ (( (show A 0=0 from map_zero _).symm ▸ hf).comp (f:=A) _ A.contDiff.contDiffAt)
variable (H:TaperHol)(J:Labels.Jet su)
-- framing for actual chart
variable (d)
private def revelation : Pipes.Path c (ZBand d) →L[ℝ] Pipes.Path l (ZBand d) :=
    ((Heir.route T).comp (Mom.screen Y)).prodMap (LinearMap.toContinuousLinearMap {
       toFun:= acting P h,map_add':=fun x y=> Matrix.mul_add _ _ _,map_smul':=fun r x=> Matrix.mul_smul _ r _ })
variable {d}
include he
local notation "JT"=> t • J
local notation "f!"=> fun i:ℕ=> actionT d i (X:=X) (b':=b') (Y:=Y) P h T H J vo t
lemma legendary (hn:n≤d) : iteratedDeriv n (engine vo (ZBand d) ∘ Beacon.moment H b' JT (kite P h T F Y)) 0=∑ i : OrderedFinpartition n, iteratedFDeriv ℝ i.length (lotsF F) 0 (fun j => f! (i.partSize j)):=by
    let U:= kite P h T F Y; let Z:= revelation (Y:=Y) (d:=d) P h T; let v:=recital d JT c b' H vo; have hV:v 0=0:=Prod.ext (inPlace JT d H c b') (woe_nil (c:=c) H.T b' vo d); have hG:(Z∘ v) 0=0:=by rw [Function.comp_apply,hV,map_zero]
    have hv:ContDiffAt ℝ (d:WithTop ℕ∞) v 0:=(lode_smooth JT d H c b').prodMk (woe_smooth H.T b' vo d)
    have hp:lotsF U ∘ v=ᶠ[𝓝 0] lotsF F∘Z∘v:=by
       have hy:Tendsto (lode d JT c b' H) (𝓝 0) (𝓝 0):= (inPlace JT d H c b') ▸ (lode_smooth JT d H c b').continuousAt
       filter_upwards [hy.eventually (powered P h T F (Y:=Y))] with y hy; let α:= (lode d JT c b' H) y; let β:= F (increment (1:Grid l) (Heir.route T (Mom.screen Y α))); change changeVars _ (kite P h T F Y (increment _ α))= changeVars _ β; change (kite P h T F Y) (increment _ α)=changeVars Fs β at hy; rw [hy]; exact (AlgHom.congr_fun (change_mul Fs (woe H.T b' vo y d (c:=c))) β).symm
    rw [(dressedT U H JT b' vo d |>.trans hp).iteratedDeriv_eq,iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ (d:WithTop ℕ∞) _ ((Z∘ v) 0) from hG.symm ▸ lots_alive F hf) (Z.contDiff.contDiffAt.comp (0:ℝ) hv) (Nat.cast_le.mpr hn),hG]
    refine Finset.sum_congr rfl fun i _=> (melody X F he _ _ (fun j=>?_) (hf.of_le (Nat.cast_le.mpr (i.length_le.trans hn)))).symm
    have hj: i.partSize j ≤ d:= (i.partSize_le j).trans hn; let ζ:=Z (echoG c b' H JT vo d (i.partSize j))
    have he : iteratedDeriv (i.partSize j) (Z ∘ v) 0=ζ:= (Display.clm_step v _ 0 (hv.of_le (Nat.cast_le.mpr hj)) _).trans (congr_arg Z (recital_jet _ _ H JT vo hj))
    rw [he]; exact screen_glazed ζ X
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.legendary
