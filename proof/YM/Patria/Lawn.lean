import YM.Patria.Dooms
import YM.Parishes.Tucking
/-! Actual calibration from issued keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a v A D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open MultiNext.SignedSource PhysicalNext.JointLoad Lyre Metric
open QCD.Kit MassiveQCD.Plate QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Poised Display Beacon
local notation "V₀" => Grid c
local notation "X₀" => Directions su c
local notation "G₀" => Lat.Fields c 6
variable (H:TaperHol)(b: Cover)(J:Labels.Jet su)
local notation "z₀" => current H b
open Card Iris Puff
open Poised.Plans
variable {I J K Y:Type} (F:Patron.Rail c 6 J)(V: Grid c)
lemma absent (W:Film c 6 Unit I)(he:flags t V=∅) : Wcall 6 F W V (t:=t)=0:=by
    unfold Wcall; simp_rw [he]; refine Finset.sum_eq_zero fun i _=>?_ ; unfold billK; split; swap; rfl
    rename_i ht; obtain ⟨h₀,h⟩:= ht; refine Finset.sum_eq_zero fun j hj=>?_ ; obtain ⟨z,hz⟩:= j.alive; have hg:z∈ i.biUnion (fun x=> (id (x:Cove.Hat c)).inv):= subset_biUnion_of_mem (fun j=> (id (j:Cove.Hat c)).inv) hj hz; rw [h] at hg; exact False.elim (Finset.notMem_empty _ hg)
open Plans.Stamp Lining Lining.Temper Collage
open Stamp
-- On-match form
structure Tally (H:TaperHol)(b:Cover)(u:Label d)(P X:Density c 6) :Prop where
   unit : ∀ᶠ U in 𝓝 1,IsUnit (P U)
   sees : ActionTest H b (fun U=>Ring.inverse (P U)*X U) u.val
lemma stamps {H:TaperHol}{F G:Density c 6}{u: Label d}(h:Tally H 0 u F G):H.Matches u.val F G:=by
    intro J; have he:= current_read H d c J; let Z:= (fun V:Grid c=>Ring.inverse (F V)*G V); have hp:= h.sees J
    have hx: (fun h=>H.test d F G J h)= Beacon.moment H 0 J Z:= by funext x; unfold SourceRead.TaperHol.test Beacon.moment; rw [he,glow_read] <;> rfl
    rw [show TaperHol.test H d F G J= _ from hx]
    change (∀ᶠ x in 𝓝 (0:ℝ), IsUnit (F ((H.links c d J) x))) ∧ _
    refine ⟨?_,hp⟩; have hh:= (centered H 0 J (d:=d) (c:=c)).eventually h.unit; exact hh.mono fun x hx=> (he x) ▸ hx
variable {q:Bool}{U:Hol su}(Uv:Exhibit U){u:UV.Label d}{P:BudgetPoint}(hP:Pilot H Uv d m k n j r α β)(hO: P.order=m)(hK:P.power=k)(hv:1≤v)(ht:1≤t)(hg: 30*(r+1) ≤ c.val) (Z:CentreFrame (c:=c) P v u q Uv b (r+1) I K)
variable (hp:Published Z H n j a t D Θ)(ha:0≤a)(he:∀ V,Summable (fun i=> ‖F.warp i V‖)) (R: Grid c→EvenA c 6) (z:ℂ)(hz:z≠0)
include hP hp he hO hK ha ht hv hg hz
open MassiveQCD.Ribbon MassiveQCD.Cupola
lemma hoards : Tally H b u (fun V=> z • light (Keys c 6) (NormedSpace.exp (R V)*heartK F P.threshold V)) (z • Stamp.reading Z F R):=by
     obtain ⟨f,hf,hx⟩:= hp.costs; let A:= Z.p; let Q i:= A.fill i; let L:= reading Z F R; let T := P.threshold; let W(U:Grid c):=∑' i,Q i U; let N(V:Grid c):=light (Keys c 6) (NormedSpace.exp (R V))
     have hs(V:Grid c): IsUnit (z • N V):=by rw [Algebra.smul_def]; refine (.mul (.map (algebraMap ℂ G₀) (isUnit_iff_ne_zero.mpr hz)) ?_); exact IsUnit.map (Cove.light _) (NormedSpace.isUnit_exp _)
     let Xg (V:Grid c):= z • light (Keys c 6) (NormedSpace.exp (R V)*heartK F P.threshold V); have hu(V:Grid c)(he:flags P.threshold V=∅): Xg V=z • N V:=by unfold Xg; rw [QCD.High.PrismT.bank _ _ _ he,mul_one]
     have hm:Summable f:= (hit_collect (wrap c b) (fun i=>(A.addr i).support) f (fun i=>(hp.sailX.anchor i) ▸ (Z.p.addr i).anchor) hx).2.1.of_nonneg_of_le (fun i=>(hf i).sight.travels) (fun i=> le_mul_of_one_le_right (hf i).sight.travels (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))))
     let X(U:Grid c):=Orientation.graphs (c:=c) d Uv b u U; have hX:ActionTest H b (X+W) u.val:= by have ht:= Orientation.actsPlus H b d X W u.val 0 (hP.tested _ _ _ hg) (blackout H b (fun i=>(Z.p.addr i).support) _ (Z.p.fill) P (fun i=> (hf i).sight) (hP.order.trans (ge_of_eq hO)) hv hm hp.key); rwa [add_zero] at ht
     let P0(V:Grid c):= Ring.inverse (Xg V)*(z • L V)
     have hY: ∀ᶠ V:Grid c in 𝓝 1,P0 V=(X+W) V := by
         filter_upwards [allflag P] with V he'; rw [show (X+W) V=X V+W V from rfl]; unfold P0; rw [hu V he']; have hψ(S:Support c):Healthy P.threshold S V:=by unfold Healthy; rw [he']; simp
         let ψ:= vote Uv b u q Z.moor T (r+1) c V
         have hf0 : L V= N V*(X V+W V):=by
              unfold L; rw [Stamp.read_earn Z V hp ht hv ha F R hP hO hK hg he,absent F V _ he', QCD.High.PrismT.bank _ _ _ he',map_one,mul_one,zero_add,MassiveQCD.Twist.freights,map_add]; apply congr_arg
              have hK:pluck _ (goldM q) ψ=X V:=by unfold ψ Stamp.vote; rw [masked_eq _ _ _ _ (hψ _)]; exact worthG ..
              refine congr_arg₂ (·+·) hK ?_
              rw [Reel.rope,(pluck (Keys c 6) (goldM q)).map_tsum (grow_shape 6 (wrap c b) Z.p V ⟨_,fun i=>(hf i).sight,hx⟩ ha hv hp.sailX)]; unfold W
              refine tsum_congr fun i=>?_ ; rw [Reel.mist,masked_eq _ _ _ _ (hψ _)]; exact worthG 6 q _ (A.beams i) _
         rw [hf0,← Algebra.smul_mul_assoc,Ring.inverse_mul_cancel_left _ _ (hs V)] -- sig
     change Tally H b u Xg (z • L); refine ⟨?_,fun J=>?_⟩; · filter_upwards [allflag P] with V hv; exact hu V hv |>.symm ▸ hs V
     have ht: moment (d:=d) H b J P0=ᶠ[𝓝 0] moment H b J (X+W):=by filter_upwards [(centered H b J (d:=d) (c:=c)).eventually hY] with p hp; exact congr_arg _ hp
     have hp:=hX J; change Agrees (moment H b J P0) (desired u.val J); exact ⟨hp.1.congr_of_eventuallyEq ht,hp.2.1,fun i hi=> ((ht.iteratedDeriv _).eq_of_nhds).trans (hp.2.2 _ hi)⟩
end YM.Massive.Patria
#print axioms YM.Massive.Patria.hoards
#print axioms YM.Massive.Patria.stamps
