import YM.Lobo.Jaw
import YM.Lobo.Perch
set_option maxHeartbeats 730000
set_option autoImplicit false
noncomputable section
namespace YM.Lobo
open Function Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice
open Massive Massive.UV TensorProduct Heron Tawny Tawny.Cast Tawny.Cast.Perla Tawny.Cast.Carnal Tawny.Cast.Drill Tawny.Cast.Zinc
open Massive.Oriole
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix Matrix.Norms.Frobenius Kronecker
open StressFlux (pair curl0)
open Finset
variable (G: EuPin)(p:PClan)(f:Flavor 6)(a b c d:Axis)(i j k:Tri)(t:ℝ)(w u:Bool)
lemma turnL : GG a b c d= -GG b a c d:=by
    have hh:pair su a b c d= -pair su b a c d:=by
          apply Subtype.ext; apply Labels.eval_ext; intro J; rw [Submodule.coe_neg,map_neg, StressFlux.pair_value,StressFlux.pair_value, StressFlux.curled_swap]; simp
    apply Subtype.ext; unfold GG; rw [hh]; exact map_neg (Perla.plain _) _
lemma turnR : GG a b c d= - GG a b d c:=by rw [show GG a b c d= GG c d a b from congr_arg (fun p:Labels.Label su 4=> dowry (d:=8) p) (StressFlux.pair_swap ..), turnL c d, show GG d c a b= GG a b d c from congr_arg (fun p:Labels.Label su 4=> dowry (d:=8) p) (StressFlux.pair_swap ..)]
noncomputable def nodes (w u:Bool)(i j:Tri):Label 8:= GG (hood w i).1 (hood w i).2 (hood u j).1 (hood u j).2
variable (hG:G.coord= Thr k t)
local notation "W" => wing k t
include hG
lemma racoon : putH (G,p) _ (nodes w u i j) = wing k t (fun a=>wing k t (nodes w u a) j) i:=by
      let A:= hood w i; let U:=hood u j; let Q:= Thr k t; rw [show nodes w u i j=GG A.1 A.2 U.1 U.2 from rfl,putG, hG]; change (∑ a:Axis,∑ b:Axis,∑ c:Axis,∑ d:Axis, (↑(Q.val a _ *Q.val b _ * (Q.val c _ * Q.val d _)):ℂ) • GG a b c d) =_; have hu(a b:Axis): (∑ c:Axis,∑ d:Axis,(↑(Q.val c U.1*Q.val d U.2):ℂ) • GG a b c d)=W (fun v=> GG a b (hood u v).1 (hood u v).2) j:= (wrapV k t U.1 U.2 (GG a b)).trans (screw k j t (GG a b) (fun c d=> turnR a b c d) u) -- fill
      let B(a b:Axis):= W (fun v=> GG a b (hood u v).1 (hood u v).2) j; have hx : palm k t (fun a=>palm k t (B a) A.2) A.1= W (fun a=>W (nodes w u a) j) i:= screw k i t B (fun a b=>by unfold B wing; refine Eq.trans (?_ : (∑ v:Tri,disk k t v j • GG a b (hood u v).1 (hood u v).2) = ∑ v:Tri,- (disk k t v j • GG b a (hood u v).1 (hood u v).2)) (sum_neg_distrib (fun v:Tri=>disk k t v j • GG b a (hood u v).1 (hood u v).2)); apply sum_congr rfl; intro v _; rw[turnL a b]; exact smul_neg (disk k t v j) (GG b a (hood u v).1 (hood u v).2)) w -- name
      rw[←hx, ← wrapV]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; change _= (↑(Q.val a A.1*Q.val b A.2):ℂ) • _; unfold B; rw[← hu]; simp_rw [smul_sum]; refine sum_congr rfl fun c _=>sum_congr rfl fun d _=>?_ ; rw [Complex.ofReal_mul, smul_smul]
omit hG
variable (M:Spike)
lemma bear : med f a b M = -med f b a M:=by
     apply Subtype.ext; apply Massive.Poised.Display.distinct; intro J; change Poised.Display.ready _ J (youthL f a b M)=_; rw [Submodule.coe_neg, map_neg]; change Poised.Display.ready _ J (youthL _ _ _ _)= -Poised.Display.ready _ _ (youthL f b a M); rw [yMobi,yMobi]
     unfold weave whirl; rw[StressFlux.curled_swap, show BendR.ore (-curl0 b a (J 0))= -BendR.ore (curl0 b a (J 0)) from map_neg _ _,show M ⊗ₖ (-BendR.ore (curl0 b a (J 0)))= -(M ⊗ₖ BendR.ore (curl0 b a (J 0))) from (by ext i j; simp),map_neg,map_neg]
noncomputable def pulseT(f:Flavor 6)(w:Bool)(i:Tri)(a:Axis): Label 10 := med f (hood w i).1 (hood w i).2 (gamma a)
local notation "Tp" i:arg a:arg=> pulseT f w i a
noncomputable def meal : Spike→ₗ[ℂ] Label 10 where
     toFun:=med f a b
     map_add' x y:= Subtype.ext (Massive.Poised.Display.distinct _ _ (fun J=>by
                              change Poised.Display.ready _ J (youthL f a b _)=_; rw [show (med f a b x+med f a b y).val=(youthL f a b x)+(youthL f a b y) from rfl, map_add,yMobi, yMobi,yMobi]; unfold weave whirl; rw[Matrix.add_kronecker,map_add,map_add]))
     map_smul' x y:=Subtype.ext (scaleY ..)
variable (v:ℝ)(hv:(p f).coord=Thr k v)
include hG hv
lemma faro : putH (G,p) _ (pulseT f w i a)= wing k t (fun i=>palm k v (pulseT f w i) a) i:=by
    rw [pulseT,wizard,hG]; let F:= fun b c=>med f b c (conjug (p f) (gamma a)); refine Eq.trans ((wrapV k t (hood w i).1 (hood w i).2 F).trans (screw k i t F (fun x y=> bear f x y _) w)) ?_ ; unfold wing; refine sum_congr rfl fun j _=>?_ ; apply congr_arg (fun l:Label 10=> disk k t j i • l); let B:= meal f (hood w j).1 (hood w j).2; change B (conjug _ _)=_; rw [tarG,hv,map_sum]; refine sum_congr rfl fun b _=>?_ ; rw [map_smul]; rfl
lemma wagonB : putH (G,p) _ (pulseT f w i (lieu j))= wing k t (fun i=> wing k v (fun j=>pulseT f w i (lieu j)) j) i:=by rw[faro G p f (lieu j) i k t w hG v hv]; simp_rw [hat]; rfl
lemma wagonC : putH (G,p) _ (pulseT f w i timeAxis)= wing k t (fun i=>pulseT f w i timeAxis) i:=by rw[faro G p f timeAxis i k t w hG v hv]; simp_rw[lastB]
end YM.Lobo
#print axioms YM.Lobo.faro
#print axioms YM.Lobo.wagonB
#print axioms YM.Lobo.wagonC
#print axioms YM.Lobo.racoon
