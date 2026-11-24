import YM.Poised.Somni
import YM.QCD.Purse.Home
/-! Pre-L volume on all-spins price of high-spill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource
open Lining Lining.Ferry YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform QCD.Brick QCD.Spice
local notation "Ψ₁"=> Faces (Site l)
local notation "F'"=> Lat.Fields c 6
local notation "F₁"=> Lat.Fields l 6
local notation "Y"=> Faces (Site c)
noncomputable def spill [Fintype A][DecidableEq A] (n:ℕ):Alg A →L[ℝ] Alg A:= ContinuousLinearMap.id _ _-∑ i∈Finset.range n,mantel i
section ratings
variable [Fintype A][DecidableEq A]
lemma mantle_val (n:ℕ)(x:Alg A):mantel n x= panel n x:=rfl
lemma seldom(n:ℕ)(x:Alg A): spill n x= x-∑ i∈Finset.range n,panel i x:=by rw [spill,ContinuousLinearMap.sub_apply,_root_.sum_apply]; rfl
lemma star_ride(n:ℕ)(x:Alg A)(p:Finset A): coef p (spill n x)= if p.card<n then 0 else coef p x:=by
    rw [seldom,map_sub,map_sum]; simp only [angel,sum_ite_eq, Finset.mem_range]; split; next h=> simp [h]
    next h=> simp [h]
lemma stilt(n:ℕ)(s:A→ℕ)(x:Alg A)(t:ℝ)(h:0<t): visc s t (spill n x)≤visc s t x:=by
   rw [pricesD _ h.le,pricesD _ h.le]; apply sum_le_sum; intro i _; apply mul_le_mul_of_nonneg_left _ (starch_pos _ h.le i); rw [star_ride]; split; · rw [norm_zero]; exact norm_nonneg _
   exact le_rfl -- whitespace
lemma within(n:ℕ)(x:Alg A)(V:Finset A)(hx:x∈region V): spill n x∈ region V:=by rw [seldom]; exact Subalgebra.sub_mem _ hx (Subalgebra.sum_mem _ (fun i _=> region_mantel _ _ _ hx))
lemma akin [Fintype B][DecidableEq B](n:ℕ)(x:Alg A)(X:A→B→ℂ): spill n (changeVars X x)=changeVars X (spill n x):=by rw [seldom,seldom,map_sub,map_sum]; apply congr_arg; exact Finset.sum_congr rfl fun i _=> Pika X i _
end ratings
variable {R:Ratio c l}(p q:ℝ)(hp:0<p)(hq:0<q){Z:VectorD (Site l) (Faces (Site c))} {u v C:ℝ}{U:Support l} {o:Site l}
def Stanch (U: Support l) (R : Ratio c l) (Z: VectorD (Site l) Y)(k:ℕ)(V:ℝ):Prop:=∀ i:Ψ₁, i∈limits U→ (∑ j:Y,Fork.meets R (locationP i) k (locationP j)*‖Z i j‖) ≤ V
include hp hq
lemma soaringV (o:Site l)(h:Stanch U R (show VectorD (Site l) (Faces (Site c)) from Z) 2 u)(X:F₁)(hn:X∈region (limits U))(hg:∀ i:Finset Ψ₁,i.card < d→coef i X=0)(h1:0≤v)(h2:v≤1)(he:4*(u*p) ≤ v/2 * q): plank (R.parent o) p (changeVars Z X) ≤ v^d*plank o q X:=by
    apply sprinkles hp (show 0 ≤ v/2*q by positivity) _ _ _ _ hn hg (show 2*(v/2*q)=_ from by ring) h1 h2 hq.le; intro i hi; exact billows (i:=i) (f1:=(show Water c l 6 from Z)) (o:=o) (h i hi) he hp -- exact M
lemma rushM (o:Site l)(T:VectorD (Site l) Y)(hA:Stanch U R T 2 u) (h:Stanch U R (show VectorD (Site l) (Faces (Site c)) from Z) 2 u)(hV: Stanch U R (Z-T) 2 v)(X:F₁)(hn:X∈region (limits U))(hu:4*(u*p) ≤ q/4)(hc:0≤C) (hh:4*(v*p)≤C*(q/4)): plank (R.parent o) p (changeVars Z X-changeVars T X)≤ C*plank o q X:=by
   apply le_trans (rind (f:=Stew.lens (R.parent o)) (changeVars Z) (changeVars T) hp (show 0 ≤ q/4 from by linarith) (fun i hi=> billows (i:=i) (f1:=(show Water c l 6 from Z)) (o:=o) (h i hi) hu hp) (fun i hi=> billows (i:=i) (f1:=(show Water c l 6 from T)) (o:=o) (hA i hi) hu hp) _ hc X hn); swap
   · intro i hi; rw [rimDiff]; exact billows (i:=i) (f1:=(show Water c l 6 from Z-T)) (o:=o) (hV i hi) hh hp
   rw [show 4*(q/4)=q by ring]
lemma divisor (o:Site l)(a:ℕ)(h:Stanch U R (show VectorD (Site l) (Faces (Site c)) from Z) a u)(q':ℝ)(hc:0≤ u) (hx:p*2^a*u ≤ q'*q)(i:Ψ₁)(hU : i∈limits U): ∑ j:Y,purseX (R.parent o) a p j * ‖Z i j‖≤ q'*purseX o a q i:=by
   let v:=locationP i; let s:=Heir.spine a v o
   have he(j:Y): Heir.spine a (locationP j) (R.parent o) ≤ (2:ℝ)^a*s*Fork.meets R v a (locationP j):=by
       unfold Fork.meets s Heir.spine; rw [separation_comm (R.parent v),← mul_pow,← mul_pow]; apply pow_le_pow_left₀ (by positivity)
       let l := locationP j; let Q:ℝ:= separation l (R.parent v); have hv':0 ≤ Q:=by unfold Q; positivity
       have hs : (separation l (R.parent o):ℝ) ≤ Q+(separation (R.parent v) (R.parent o):ℝ):=by unfold Q; exact_mod_cast separation_triangle l (R.parent v) _
       have ht : (separation (R.parent v) (R.parent o):ℝ) ≤ separation v o+1:=by exact_mod_cast YM.Work.E04.parent_separation R v o
       change 1+(separation l (R.parent o):ℝ) ≤ 2*(1+ (separation v o:ℝ))*(1+Q)
       nlinarith [Nat.cast_nonneg (α:=ℝ) (separation v o)]
   let w:=p*2^a * s
   apply le_trans (b:= w* ∑ j:Y,meets R v a (locationP j)*‖Z i j‖); swap
   · unfold w; apply (mul_le_mul_of_nonneg_left (h i hU) (show 0 ≤ p*2^a*s by unfold s; positivity [Heir.spine_pos a v o])).trans; exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_right hx (show 0 ≤ s from (Heir.spine_pos ..).le)).trans_eq (mul_assoc ..)) -- try positivity
   rw [Finset.mul_sum]; refine sum_le_sum fun j _=>?_ ; rw [← mul_assoc w]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (mul_le_mul_of_nonneg_left (he j) hp.le).trans_eq (by unfold w; ring)
end Pipes
end YM.Massive.Poised
