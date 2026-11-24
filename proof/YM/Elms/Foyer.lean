import YM.Elms.Ready
import YM.Patria.Reflect
/-! # Site seam/sector for equation contents; transport of elementary grants and disjointness.

Not assuming same sign scheme parity at arbitrary plane.Finite transform. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
local notation "τ"=> su.probHaar
local notation "s"=>Signed.mirror a
local notation "V"=> Lat.Fields n 6
local notation "F"=> Insertion n 6
def unia (x:Insertion n 6):Insertion n 6:=⟨fun U=> Cylinder.Action.adj a x U,by simp_rw [Exposure.eye_value]; exact (tilt_cont _).comp (x.continuous.comp (Wilson.continuous_pull ..))⟩
local notation "E"=>Patria.Exposure.eyeP n a
lemma heroY (x:Insertion n 6): unia a x U=tilt E (x (pull s 0 U)):=Patria.Exposure.eye_value ..
noncomputable def via : Drape→ₛₗ[starRingEnd ℂ]Drape where
    toFun x:=fun n u=> unia a (x n (Signed.act s u))
    map_add' x y:=by funext n u; apply ContinuousMap.ext; intro T; simp_rw [heroY,Pi.add_apply, ContinuousMap.add_apply,map_add,heroY]; -- maybe face
    map_smul' c x:=by funext n u; apply ContinuousMap.ext; intro T; simp_rw [heroY,Pi.smul_apply,ContinuousMap.smul_apply,map_smulₛₗ,heroY]
def axisT (a:Axis) {A:Type*} [AddCommGroup A][One A](x:Four A):Four A:= (Signed.mirror a).act x
lemma axis_sq {A:Type*}[AddCommGroup A][One A](x:Four A): axisT a (axisT a x) = x:=by rw [axisT,axisT,← Signed.act_mul,show (s)*(s)=1 from mul_inv_cancel _,Signed.act_one]
lemma via_site (X:Drape): via a X n (axisT a o) = unia a (X n o):=by change unia a (X n (axisT a (axisT a o)))=_; rw [axis_sq]
lemma unia_prod (x y:F) : unia a (x*y)=unia a y*unia a x:=by ext1 u; rw [heroY,ContinuousMap.mul_apply,tilt_mul,ContinuousMap.mul_apply,heroY,heroY]
lemma via_rev (x y:Drape):via a (x*y)=via a y*via a x := funext fun i=>funext fun u=>unia_prod a (x i _) (y i _)
lemma arcQ (x:V): tilt E (tilt E x)=x:= untilt _ (eye_star a (c:=n)) (eye_sq a (c:=n)) _ -- args
lemma againZ(x:F): unia a (unia a x)=x:=by
     ext1 U; rw [heroY,heroY,arcQ,pull_pull,show s*s=1 from mul_inv_cancel _]; simp [affine]
lemma via_one:via a 1=1:=by funext n o; apply ContinuousMap.ext; intro p; change unia a (1:Insertion n 6) _ =1; rw [heroY]; exact tilt_one _
-- transforms leads: q=FALSE→bar with -gamma.transpose acted, TRUE→spin with -gamma.
noncomputable def ivZ(a:Axis)(q:Bool): ΔM:= -revM (!q) (mL (gamma a)) -- sign tilt minus. col false→ psi transforms to -E j_old indexing output row? tilt_psi R old i gives -R j i yes
local notation "I"=>Dike
lemma unpaid (x:Site n)(M: Spike)(i:I)(y:Site n)(j:I): Cylinder.Action.moved s M (place x i) (place y j)= if axisT a x=y then Cylinder.ap n ((s).act (Cylinder.sheet x))*mL M i j else 0:=by
    rw [Ferry.roller,Lining.spar_intro]; unfold mL copies; rw [Matrix.blockDiagonal_apply]; simp only [place]; by_cases hp:axisT a x=y <;> by_cases hx:i.2=j.2 <;> simp [axisT] at hp ⊢ <;> simp [hp,hx] -- syntax
lemma hemis (q:Bool)(i:I)(x:Site n): tilt E (lineT q (place x i))= (Cylinder.ap n ((s).act (Cylinder.sheet x))) • ∑ j:Dike, (ivZ a q i j) • lineT (!q) (place (axisT a x) j):=by
    let A:= eyeP n a; let f(y:Site n):= Cylinder.ap n ((Signed.mirror a).act (Cylinder.sheet y));
    have he:f (axisT a x) = f x:=by
       have hz: f x*f (axisT a x)=1:=Patria.Exposure.glowed a x
       have hv:f x*f x=1:=Pipes.ap_sq ..; exact mul_left_cancel₀ (left_ne_zero_of_mul (ne_zero_of_eq_one hv)) (hz.trans hv.symm) -- name check
    cases q
    · change tilt E (psi (place x i))=_; rw [tilt_psi,placed_sum,sum_eq_single (axisT a x)];
      swap; · intro j _ hw; apply sum_eq_zero; intro q _; rw [show E _ _= _ from ?_,neg_zero,zero_smul]; exact (unpaid a j (gamma a) q _ i).trans (if_neg fun h=>hw (by rw [← h,axis_sq]))
      swap; · simp
      rw [Finset.smul_sum]; apply sum_congr rfl; intro b _; rw [show E _ _=_ from unpaid (n:=n) a (axisT a x) _ b x i,if_pos (axis_sq ..)]; change (-(f (axisT a x)*_)) • _=f x • (- mL (gamma a) b i) • _; rw [he,smul_smul,mul_neg]; rfl
    change tilt E (bar (place x i))=_; rw [tilt_bar,placed_sum,sum_eq_single (axisT a x)]
    swap; · intro j _ hw; apply sum_eq_zero; intro q _; rw [show E _ _= _ from (unpaid a x (gamma a) i j q).trans (if_neg (Ne.symm hw)),neg_zero,zero_smul]
    swap; · simp
    rw [Finset.smul_sum]; apply sum_congr rfl; intro b _; rw [show E _ _=_ from unpaid a x (gamma a) i _ b,if_pos rfl]; change (-(f x*_)) • _= f x • (-mL (gamma a) i b) • _; rw [smul_smul,mul_neg]; rfl
-- move transport orientation. maps. More later
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
