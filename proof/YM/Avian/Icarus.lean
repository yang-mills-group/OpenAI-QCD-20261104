import YM.Avian.Helot
/-! DS off-shell gauge rank components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall.Seals
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open StressFlux (pairDeriv curl0 curl1 leg0 leg1)
variable {c:Side} {d:ℕ} (X:Labels.Taylor su 0)(Y:Labels.Taylor su 1)(i j k l m:Axis)(J:Labels.Jet su)
noncomputable abbrev pole(a b d e f:Axis):ℂ:= (inner ℝ (curl0 a b X) (curl1 d e f Y):ℝ)
local notation "J★"=> leanY X Y
local notation "A"=> (0:Axis)
variable (u: Values 4)(p: Fin 4→ℂ)(v:Values 7)
lemma plot_E : pages J (eulerV.val i)=∑ j:Axis,∑ k:Axis, (↑(inner ℝ (curl0 i j (J 0)) (curl1 k k j (J 1))):ℂ):=by
    change pages J (∑ j:Axis,∑ k:Axis,GE i j k k j)=_; rw [map_sum]; refine sum_congr rfl fun b _=>?_ ; rw [map_sum]; refine sum_congr rfl fun a _=>?_ ; exact (railX _ _ _ rfl).trans (StressFlux.pairDeriv_value ..)
lemma rosy : ∑ j:Axis,∑ k:Axis, pole X Y j k j i k=(1/2:ℂ)*pages J★ (lunar.val i):=by
    let v(j k:Axis):= pole X Y j k j i k
    have hg : pages J★ (lunar.val i) = ∑ j:Axis,∑ k:Axis, pole X Y j k i j k:=by simp only [plotH,leanV0,leanV1,pole]
    have hh : pages J★ (lunar.val i)=(∑ j:Axis,∑ k:Axis,v j k)+(∑ j:Axis,∑ k:Axis,v j k):=by
        rw [hg]; conv_rhs=> arg 2; rw[sum_comm]
        
        rw [← Finset.sum_add_distrib]; apply sum_congr rfl; intro a _; rw[← sum_add_distrib]; apply sum_congr rfl; intro b _
        have hz:= (Maxwell.closedCurl Y).closed i a b 0; simp_rw [oneH,show curl1 a b i Y = -curl1 a i b Y from StressFlux.curled_swap ..] at hz; have ht:curl1 i a b Y=curl1 a i b Y-curl1 b i a Y:=by -- abel hz
             rw [show curl1 i a b Y=(curl1 i a b Y+- curl1 a i b Y+curl1 b i a Y)+(curl1 a i b Y-curl1 b i a Y) from (by abel),hz, zero_add]
        unfold v pole; rw[ht, show curl0 b a X= -curl0 a b X from StressFlux.curled_swap .., inner_neg_left, inner_sub_right]; push_cast; ring
    rw [hh]; unfold v; ring
-- formula
lemma pan_plotL : pan X Y k ((poseσ (u,p)).val (i,j)) = p 1 * (∑ l:Axis, (pole X Y i l k j l+pole X Y j l k i l)) + p 2 * (if i=j then ∑ l:Axis, (pole X Y i l k j l+pole X Y j l k i l) else 0) + p 3 * (if i=j then 2 * (∑ l:Axis,∑ m:Axis,pole X Y l m k l m) else 0):=by
    let D:=radial Y k; let F(x:Labels.Taylor su 0)(i j:Axis):=pages (leanY x 0) (spire.val (i,j)); let V(x:Labels.Taylor su 0)(i j:Axis):=pages (leanY x 0) (eclipse.val (i,j)); let R(X:Labels.Taylor su 0):= capote 8 (leanY X 0) ((poseσ (u,p)).val (i,j)); let s:= (∑ l:Axis,(pole X Y i l k j l+pole X Y j l k i l)); let t:= ∑ l:Axis,∑ m:Axis,pole X Y l m k l m; change R (X+D)-R X-R D=_
    have hx x: R x= p 1*F x i j + p 2*(if i=j then F x i j else 0)+p 3* V x i j:=by unfold R; rw [p_pose,heartP,plotS]
    have ht (a b i j:Axis) : (↑(inner ℝ (curl0 a b (X+D)) (curl0 i j (X+D))):ℂ) = (↑(inner ℝ (curl0 a b X) (curl0 i j X)):ℂ) + (↑(inner ℝ (curl1 k a b Y) (curl1 k i j Y)):ℂ)+ (pole X Y a b k i j+pole X Y i j k a b):=by rw [map_add,map_add,show curl0 _ _ D= _ from radialC Y a b k,show curl0 _ _ D= _ from radialC Y i j k]; simp only [inner_add_right, inner_add_left,pole,Complex.ofReal_add]; rw [real_inner_comm (curl1 k a b Y) (curl0 i j X)]; ring -- placeholder
    have h: F (X+D) i j=F X i j+F D i j+s:=by unfold F s; simp only[plots,leanV0,ht,D]; simp_rw [radialC]; exact Eq.trans (sum_add_distrib) (by rw [sum_add_distrib]) -- ht with D expanded? canonical
    have he: V (X+D) i j= V X i j+ V D i j+(if i=j then 2*t else 0):=by
         unfold V; simp only[plotD,leanV0]; split; swap; · simp
         unfold t; simp_rw[ht]; unfold D; simp_rw [radialC]; rw [two_mul, ← Finset.sum_add_distrib,← Finset.sum_add_distrib, ← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [← sum_add_distrib,←sum_add_distrib,←sum_add_distrib] -- simplify
    rw [hx,hx,hx,h,he]; split <;> ring
lemma pan_plot : ∑ k:Axis, pan X Y k ((poseσ (u,p)).val (k,i)) = p 1 * (pages J★ (eulerV.val i)+ (1/2:ℂ)*pages J★ (lunar.val i)) + p 2*(2*pages J★ (leapV.val i))+ p 3 * (2*pages J★ (lunar.val i)) :=by
    simp_rw [pan_plotL, mul_ite, mul_zero, sum_add_distrib]; simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [← Finset.mul_sum]; rw [Finset.sum_add_distrib, rosy,show (∑ x:Axis,∑ y:Axis,pole X Y i y x x y)= pages J★ (eulerV.val i) from (by rw [sum_comm,plot_E]; simp only [pole,leanV0,leanV1]),show (∑ x:Axis,pole X Y i x i i x)=pages J★ (leapV.val i) from (by rw[plotL]; simp only [pole,leanV0,leanV1]), show (∑ l:Axis,∑ m:Axis,pole X Y l m i l m)= pages J★ (lunar.val i) from (by rw [plotH];simp only[pole,leanV0,leanV1])]; ring
lemma absence (u:Values 2): ∑ k:Axis, pan X Y k ((poseα u).val (k,i))=0:=by unfold pan; simp_rw [LinearMap.sub_apply,p_α,sub_zero,sum_const_zero]
end YM.Massive.Patria.Gall.Seals
#print axioms YM.Massive.Patria.Gall.Seals.pan_plot
