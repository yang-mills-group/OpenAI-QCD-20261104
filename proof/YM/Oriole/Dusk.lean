import YM.Oriole.Hoop
import YM.Patria.Lawn
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

open Plans.Stamp Lining Lining.Temper Collage
open Stamp Oriole
variable {q:Bool}{U:Hol su}(Uv:Exhibit U){u:UV.Label d}{P:BudgetPoint}(hP:Pilot H Uv d m k n j r α β)(hO: P.order=m)(hK:P.power=k)(hv:1≤v)(ht:1≤t)(hg: 30*(r+1) ≤ c.val) (Z:CentreFrame (c:=c) P v u q Uv b (r+1) I K)
variable (hp:Published Z H n j a t D Θ)(ha:0≤a)(he:∀ V,Summable (fun i=> ‖F.warp i V‖)) (R: Grid c→EvenA c 6) (z:ℂ)(hz:z≠0)
include hP hp he hO hK ha ht hv hg hz
open MassiveQCD.Ribbon MassiveQCD.Cupola

open Poised.Stative
variable (p q₀:Flavor 6) (M:Spike)
lemma Flour (hb:b=0): ‖diffS p q₀ M H.T (Canvas.foil (fun V=> z • light (Keys c 6) (NormedSpace.exp (R V)*heartK F P.threshold V)) (z • Stamp.reading Z F R) 1)‖ ≤ yieldS M c * (β * wealth u.val P.threshold v+D):=by
     obtain ⟨f,hf,hx⟩:= hp.costs; let A:= Z.p; let Q i:= A.fill i; let L:= reading Z F R; let T := P.threshold; let W(U:Grid c):=∑' i,Q i U; let N(V:Grid c):=light (Keys c 6) (NormedSpace.exp (R V))
     have hs(V:Grid c): IsUnit (z • N V):=by rw [Algebra.smul_def]; refine (.mul (.map (algebraMap ℂ G₀) (isUnit_iff_ne_zero.mpr hz)) ?_); exact IsUnit.map (Cove.light _) (NormedSpace.isUnit_exp _)
     let Xg (V:Grid c):= z • light (Keys c 6) (NormedSpace.exp (R V)*heartK F P.threshold V); have hu(V:Grid c)(he:flags P.threshold V=∅): Xg V=z • N V:=by unfold Xg; rw [QCD.High.PrismT.bank _ _ _ he,mul_one]
     have hm:Summable f:= (hit_collect (wrap c b) (fun i=>(A.addr i).support) f (fun i=>(hp.sailX.anchor i) ▸ (Z.p.addr i).anchor) hx).2.1.of_nonneg_of_le (fun i=>(hf i).sight.travels) (fun i=> le_mul_of_one_le_right (hf i).sight.travels (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))))
     let X(U:Grid c):=Orientation.graphs (c:=c) d Uv b u U
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
     change ‖diffS p q₀ M H.T (P0 1)‖ ≤ _; rw [show P0 1=(X+W) 1 from (show P0=ᶠ[𝓝 1] X+W from hY).eq_of_nhds]; have hk:(X+W) 1=X 1+∑' i,Q i 1:=rfl; rw [hk,map_add]; let L:=diffS (c:=c) p q₀ M H.T; let i':=(1:Grid c); have hs:flags P.threshold i'=∅:=(show flags P.threshold=ᶠ[𝓝 (1:Grid c)] (fun _=>∅) from allflag P).eq_of_nhds; have hψ(S:Support c):Healthy P.threshold S i':=by unfold Healthy; rw [hs]; simp
     have hh(i): MassiveQCD.Plate.view 0 2 (Q i i') v≤ f i:=by
          have hp:wrap c b=0:=by rw [hb,map_zero]
          rw [← hp]; exact (hf i).sight.pole 1 (hψ _) [] (Nat.zero_le _) (fun j h=>by simp at h)
     have hvv: Summable fun i=> Q i i':= Summable.of_norm (hm.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> (loaded (Q i i') (fun _=>v) (fun _=>hv)).trans ((viewer _ _ _ (zero_lt_one.trans_le hv)).trans (hh i))))
     have hQ:L.toContinuousLinearMap (∑' i,Q i i')= ∑' i,L (Q i i'):= L.toContinuousLinearMap.map_tsum hvv
     have hM:0 ≤ yieldS M c:=by unfold yieldS; have ht:= Oriole.e_bud M; have hw:=Oriole.cost_pos; positivity
     have hb1:∑' i,f i ≤ D:=by apply le_trans ?_ (hit_collect (wrap c b) _ _ (fun i=>(hp.sailX.anchor i) ▸ (Z.p.addr i).anchor) hx).2.2; apply hm.tsum_le_tsum (fun i=>le_mul_of_one_le_right (hf i).sight.travels (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))) (hit_collect (wrap c b) _ _ (fun i=>(hp.sailX.anchor i) ▸ (Z.p.addr i).anchor) hx).2.1
     have hv_(i): ‖L (Q i i')‖ ≤ yieldS M c*f i:= (Oriole.screen p q₀ (n:=2) _ H.T M v hv (by decide)).trans (mul_le_mul_of_nonneg_left (hh i) hM); have hz:‖L (∑' i,Q i i')‖ ≤ yieldS M c*D :=by
          have hp:= hm.mul_left (yieldS M c); have hQ': Summable (fun i=>‖L (Q i i')‖):= hp.of_nonneg_of_le (fun _=>norm_nonneg _) hv_
          rw [show L _= _ from hQ]; exact (norm_tsum_le_tsum_norm hQ').trans ((hQ'.tsum_le_tsum hv_ hp).trans (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hb1 hM))
     have hp0:‖L (X 1)‖ ≤ yieldS M c*(β*wealth u.val P.threshold v) :=by
          have hp:wrap c b=0:=by rw [hb,map_zero]
          apply (Oriole.screen p q₀ (n:=2) _ H.T M v hv (by decide)).trans; apply mul_le_mul_of_nonneg_left _ hM; rw[← hp]; exact (hP.bill c b P v u hO hK (by omega) (zero_lt_one.trans_le hv)).sight.pole 1 (hψ _) [] (Nat.zero_le _) (fun j h=>by simp at h)
     exact (norm_add_le ..).trans ((add_le_add hp0 hz).trans_eq (mul_add ..).symm)
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Flour
