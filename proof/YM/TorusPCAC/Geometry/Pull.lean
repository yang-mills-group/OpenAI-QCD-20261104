import YM.TorusPCAC.Geometry.Thermal
import YM.TorusPCAC.Ward.Flavor
import YM.QCD.Revolve.Roots
import YM.Branch.Covariant

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Pull covariance for all signed+translated seas
Use actual branches, patch and all integrations. `crank` includes a nowhere singular
sign texture; at link and site insertions/sums must use the texture exactly. For
the translation specializations use the **cover** cocycle `heat`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Geometry
open QCD QCD.Lat QCD.Kit QCD.Grass Lattice Wilson Finite Finset MeasureTheory Function RG Revolve Ward QCD.Flume
open scoped Matrix Topology BigOperators Kronecker Matrix.Norms.Frobenius

variable {n c f : Side} {N : ℕ} {s : Signed} {P : Spike}
variable (hP : Swing s P)
section bare
variable {b t t' : Site n}{l : Site n→ℂ} (h : Glare s t t' b l) (U : Grid n)
local notation "A" => hues b s l P
include h hP
lemma hue_lo (i : Axis) : onSpin n (lo i)= aura A (if s.flip i then onSpin n (hi (s.perm i)) else onSpin n (lo (s.perm i))) :=by
  -- lo = 1/2(1-γ)
  have hg : onSpin n (gamma i)=aura A (if s.flip i then -onSpin n (gamma (s.perm i)) else onSpin n (gamma (s.perm i))) := hue_gamma h hP i
  have hv (V : Spike) : onSpin n ((2:ℂ)⁻¹ • V) = (2:ℂ)⁻¹ • onSpin n V:=by unfold onSpin wave; rw [Matrix.smul_kronecker, ride_smul]; rfl
  have he (V W : Spike) : onSpin n (V-W)=onSpin n V-onSpin n W :=by rw [eq_sub_iff_add_eq,on_spin_add,sub_add_cancel]
  cases hi : s.flip i
  · rw [lo,hv,he,hg,on_spin_one]; simp only [hi, Bool.false_eq_true,↓reduceIte]; rw [lo,hv,aura_scale,he,on_spin_one,aura_sub,aura_one (colour_wheel h hP)]
  rw [lo,hv,he,hg,on_spin_one]; simp only [hi,if_true]; rw [aura_neg,sub_neg_eq_add,Lat.hi,hv, ← on_spin_add,on_spin_one,aura_scale,aura_add,aura_one (colour_wheel h hP)]
lemma hue_hi (i : Axis) : onSpin n (hi i)= aura A (if s.flip i then onSpin n (lo (s.perm i)) else onSpin n (hi (s.perm i))) :=by
  have he (i : Axis) : onSpin n (hi i)=1-onSpin n (lo i):=by rw [eq_sub_iff_add_eq, add_comm, on_spin_add,Lat.projectors, on_spin_one]
  rw [he i,hue_lo hP h]
  conv_lhs=>lhs; rw [← aura_one (colour_wheel h hP)]
  rw [← aura_sub]
  congr 1
  cases H : s.flip i <;> simp only [Bool.false_eq_true, ↓reduceIte]; rw [he]; rw [he]; abel -- split
lemma single_hue (i : Axis) : singleHop t (pull s b U) i=aura A (singleHop t' U (s.perm i)) := by
  unfold singleHop; rw [hue_hi hP h, hue_lo hP h,hue_march h hP]; change _ * aura A _ + _ * star (aura A _) = _
  cases H : s.flip i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> rw [← aura_ad, ← aura_prod (colour_wheel h hP),← aura_prod (colour_wheel h hP),← aura_add]
  rw [star_star,add_comm]
lemma bare_cov (m : ℝ) : bareD t (pull s b U) m=aura A (bareD t' U m) := by
  unfold bareD; rw [aura_add,aura_scale,aura_one (colour_wheel h hP)]; unfold aura; rw [mul_sum, sum_mul]
  conv_rhs=> rhs; rw [← Equiv.sum_comp s.perm]
  congr 1; exact sum_congr rfl fun i _=> by rw [single_hue hP h U, mul_sub,sub_mul,mul_one,(colour_wheel h hP).2]; rfl
omit h hP
end bare

def crank (s : Signed) (P : Spike) (b : Site n) (l : Site n→ℂ): Fields n N →ₐ[ℂ] Fields n N := disguise (Lat.copies N (hues b s l P))
def post (s : Signed) (P : Spike) (b : Site n) (l : Site n→ℂ) (X : Density n N) : Density n N := fun U=> crank s P b l (X (pull s b U))
lemma post_cts (b : Site n) (l : Site n→ℂ) (X : Density n N) (h : Continuous X) : Continuous (post s P b l X):=(crank s P b l).toLinearMap.continuous_of_finiteDimensional.comp (h.comp (continuous_pull _ _)) -- check

variable {b : Site c}{l : Site f→ℂ} (M : StepData c f)
include hP in
lemma bare_pivot (B : TorusPCAC.Torus n N) (p) {l : Site n→ℂ} (h : Glare s B.seam B.seam p l) : post s P p l B.weight=B.weight:=by
  funext U; unfold post; rw [Torus.weight_complex,B.weight_complex, bare_pull,map_smul]
  let X:=hues p s l P
  rw [show B.fermion (pull s p U)=Lat.copies N X * B.fermion U * star (Lat.copies N X) from ?_,crank, disguised (copies_unitary N _ (colour_wheel h hP))]
  unfold Torus.fermion Lat.copies; simp_rw [bare_cov hP h U]; rw [block_star, ← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]
  rfl

variable (Dg : M.patch.Branches M.kernel su) (β w : ℝ) (h : Glare s 0 0 (M.ratio.embed b) l)
include hP h
lemma stencil_pull (U : Grid f) :
    meanSpin (N:=N) M (pull s (M.ratio.embed b) U)= copies N (hues b s (l∘M.ratio.embed) P)* meanSpin M U * star (copies N (hues (M.ratio.embed b) s l P)) :=by
  have he : sliceL (prototype M.patch) M.sizes = M.ratio := rfl
  have ht:= dual (prototype M.patch) M.sizes (t:=0) (t':=0) (b:=b) (l:=l) (by
    rw [he, show M.ratio.embed 0=0 from map_zero (M.ratio.root)]; exact h) hP U
  dsimp only at ht; rw [he, show M.ratio.embed 0=0 from map_zero (M.ratio.root)] at ht
  unfold meanSpin copies; rw [block_star,← Matrix.blockDiagonal_mul,← Matrix.blockDiagonal_mul]; simp only [ht]
lemma identity_pull (X : Density f N) (U) : crank s P b (l∘M.ratio.embed) (TorusPCAC.high M X (pull s (M.ratio.embed b) U))=TorusPCAC.high M (post s P (M.ratio.embed b) l X) U :=by
  unfold crank post TorusPCAC.high; rw [stencil_pull hP _ h]; apply compat (copies_unitary _ _ (colour_wheel h hP)) (copies_unitary _ _ (colour_wheel (shrouds M.ratio (a:=0) (y:=0) (b:=b) (d:=l) (by rw [show M.ratio.embed 0=0 from map_zero M.ratio.root]; exact h)) hP))

omit hP h in
include Dg in
lemma push_pull (s : Signed) (p : Site c) (V : Grid c) (F : Grid f → Fields c N) (hc : Continuous F) : M.push β F (pull s p V)=M.push β (fun U=>F (pull s (M.ratio.embed p) U)) V :=by
  let k:= pull (K:=su.El) s (M.ratio.embed p); have hk : MeasurePreserving k (prior su f) (prior su f):= prior_pull ..
  let W:=pull s p V; let f'(U):= M.density β U W • F U; have ht : Integrable f' (prior su f):=StepData.push_slice (M.isKernel Dg β) W F (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  unfold StepData.push; change (∫ U, f' U ∂prior su f)= ∫ U,M.density β U V • F (k U) ∂prior su f
  have hx : AEStronglyMeasurable f' (Measure.map k (prior su f)):=hk.map_eq.symm ▸ ht.aestronglyMeasurable
  have ha : (∫ U, f' U ∂prior su f)=∫ U, f' (k U) ∂prior su f:=by rw [← integral_map hk.aemeasurable hx,hk.map_eq]
  rw [ha]; apply integral_congr_ae; exact .of_forall (fun U=> congr_arg (· • F (k U)) (M.channel Dg s p β U V))
include hP h Dg
lemma post_block (X : Density f N) (hc : Continuous X) : post s P b (l∘M.ratio.embed) (block M β w X)=block M β w (post s P (M.ratio.embed b) l X) :=by
  funext U
  have he (F : Fields c N) : crank s P b (l∘M.ratio.embed) (rescaleSpin w F)= rescaleSpin w (crank s P b (l∘M.ratio.embed) F):=by unfold crank disguise rescaleSpin; simp [adapt_together]
  let V:= fun U=> TorusPCAC.high M X (pull s (M.ratio.embed b) U); have hv : Continuous V := (high_cont M X hc).comp (continuous_pull _ _)
  let T:= (crank s P b (l∘M.ratio.embed) (N:=N)).toLinearMap
  have ht V := identity_pull hP M h X V
  rw [post,block,he,push_pull M Dg β s b U (TorusPCAC.high M X) (high_cont M X hc)]
  rw [show crank s P b (l∘ M.ratio.embed) (M.push β V U) = _ from (congr_fun (Pass.evaluate M β Dg T V
    (hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) U).symm,
    show (fun U=>T (V U))=TorusPCAC.high M (post s P (M.ratio.embed b) l X) from funext ht]; rfl
end YM.TorusPCAC.Geometry

#print axioms YM.TorusPCAC.Geometry.post_block
