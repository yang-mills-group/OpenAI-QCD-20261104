import YM.Heron.Beads
set_option autoImplicit false
noncomputable section
namespace YM.Heron
open Function Set Filter Tensor Analysis MeasureTheory QCD QCD.Lat QCD.Grass Lattice Maxwell.Free
open Massive Massive.UV Massive.UV.Free TensorProduct DawnS
open scoped ContDiff Topology BigOperators InnerProductSpace TensorProduct Classical Matrix
open Maxwell (grad away open_away)
open Arise.Range
variable {j l : ℕ}
variable (A:TinG)(hc:TrueC A){g f:Spins}
lemma zeroFlux {v : Drive} (h : Seam v) {U:Set E4}(hU:IsOpen U) {χ:E4→ℝ}(hχ:ContDiff ℝ ∞ χ) (Hχ: HasCompactSupport χ)(ht:tsupport χ⊆U)(hf:Way (FlipT A) U f)(hg:Way A U g)(hA:TrueC A):exportFlux (brook A f g v) χ=0:=by
     rw [by_parts hχ Hχ];
     · rw [show (fun y:E4=>χ y • ∑ a:Axis,grad a (brook A f g v a) y)=(fun _=> (0:ℂ)) from (by
                  funext y; by_cases hy:y∈tsupport χ
                  · let x:= ht hy; let F:= hf.live y x; let G:= hg.live y x; rw[spark A _ _ y v h F G];
                    have he(i: Axis): (∑ k:Axis, grad k (blaze A f g k i) y)=0:=by
                         simp_rw [show ∀ k, grad k (blaze A f g k i) y=grad k (streak A f g k i) y+grad k (streak A f g i k) y from fun k=>by unfold grad blaze D; rw[fderiv_add ((way_a _ _ _ _ _ _ F G).differentiableAt (by simp)) ((way_a _ _ _ _ _ _ F G).differentiableAt (by simp))]; rfl,Finset.sum_add_distrib]; rw [Stiff A i f g y F G, Heron.motion A i f g y F G, gore A i hU g y x hg, gore (FlipT A) i hU f y x hf,hg.lore y x,hf.lore y x, angel A hA hU g y x hg, angel (FlipT A) (flips A hA) hU f y x hf]; simp
                    simp_rw [he]; simp
                  rw [image_eq_zero_of_notMem_tsupport hy,zero_smul])]; exact integral_zero ..
     exact fun a y hy=> bow A a g f y v h (hf.live y (ht hy)) (hg.live y (ht hy))
variable (p:E4)(D₀:Faces)(c:ℝ)(hu:0<c) (L:List Axis)(v:E4)(hv:v≠0)(i j:Axis)
local notation "X"=> hull A D₀
local notation "Q"=> pose A D₀
include hu hv
lemma homJ : X (c • v)=c⁻¹^3 • X v:=by
    let U:= stocked 0 0 D₀; have h(z:E4)(hz:z≠0)(a:Axis): grad a U z = (-2* Maxwell.normal * z a * (‖z‖^2)⁻¹^2) • D₀:=by
       let F:=Maxwell.Free.soften 0; rw[show grad a U z= _ from bark _ _ _ _ _ (liftY 0 ((0:ℝ),z) (Ne.symm hz) 0 z (Ne.symm hz)), sub_zero, soften_first]; simp; have ht:= norm_pos_iff.mpr hz; positivity
    change -(∑ a:Axis,cog (FlipT A) a _) = _ • -(∑ a:Axis, cog (FlipT A) a (grad a U v)); rw [smul_neg,Finset.smul_sum]; congr 1; apply Finset.sum_congr rfl; intro a _; change cog (FlipT A) a (grad a U (c • v))= _; rw [h _ (smul_ne_zero hu.ne' hv),h _ hv, ← map_smul, smul_smul]; simp only [norm_smul, Real.norm_of_nonneg hu.le,PiLp.smul_apply,smul_eq_mul]; apply congr_arg; congr 1; have hg:=norm_pos_iff.mpr hv; field_simp -- inv algebra ring_nf may need ∥v∥
lemma shapeK :deriveL L X (c • v)=c⁻¹^(3+L.length) • deriveL L X v:=by
   induction L generalizing v with
   | nil=> exact homJ A D₀ c hu v hv
   | cons i L ih=>
        let K:=deriveL L X; let U': E4→L[ℝ]E4:= c • ContinuousLinearMap.id ℝ E4; have he : K ∘ U'=ᶠ[𝓝 v] (fun y=> c⁻¹^(3+L.length) • K y):=(eventually_ne_nhds hv).mono fun x hx=>ih x hx; have hh (v:E4)(hv:v≠0) : DifferentiableAt ℝ K v:= (balla L X _ open_away (fun y hy=> hotH _ _ _ hy) _ hv).differentiableAt (by simp); have hD:= congr_arg (fun T:E4→L[ℝ] Faces=>T (basis i)) (he.fderiv_eq (𝕜:=ℝ)); rw[fderiv_comp v (show DifferentiableAt ℝ K (U' v) from hh (c • v) (smul_ne_zero hu.ne' hv)) U'.differentiableAt,U'.fderiv, fderiv_fun_const_smul (hh _ hv)] at hD; change fderiv ℝ K (c • v) (c • basis i)= c⁻¹^(3+L.length) • (grad i K v) at hD; rw [map_smul] at hD; change c • grad i K (c • v)=_ at hD; change grad i K (c • v)= c⁻¹ ^ _ • grad i K v; rw [show 3+(i::L).length=(3+L.length)+1 from (by simp; omega),pow_succ',mul_smul,← hD, inv_smul_smul₀ hu.ne'] -- hD used r orientation
lemma grace : Q L p (p+c • v)= c⁻¹^(3+L.length) • Q L p (p+v):=by unfold pose; rw [show p-(p+ c • v)= c • (-v) from (by rw[smul_neg]; abel),show p-(p+v)= -v from (by abel)]; exact shapeK A D₀ c hu L (-v) (neg_ne_zero.mpr hv)
lemma touchS :grad i (Q L p) (p+c • v)= c⁻¹^(3+L.length+1) • grad i (Q L p) (p+v):=by
   rw [loveK, loveK, grace A p D₀ c hu (i::L) v hv,smul_neg, show 3+(i::L).length=(3+L.length)+1 from (by simp; omega)]; · simp [hv]
                                                                                      -- test
   simpa using smul_ne_zero hu.ne' hv

end YM.Heron
#print axioms YM.Heron.touchS
#print axioms YM.Heron.zeroFlux
