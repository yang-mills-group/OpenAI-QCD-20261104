import YM.TorusPCAC.Ward.Variation

/-!
# Spectator bias density and transmission

`Pass.car` already includes spin/flavor slots on A AND actual densities. In the notation of
work/massread: `Pass.car ((x,c),f,l) ((y,c'),f',l')` (with those index conventions)
is `A_ff'ℓℓ' G_xc,yc'`. Require no assertion of cleaning or even
translation covariance to prove the symbol-passage identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TorusPCAC.Ward
open QCD QCD.Grass QCD.Lat RG MeasureTheory Finite Finset Lattice Wilson Function
open scoped Matrix Topology BigOperators Matrix.Norms.Frobenius

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

abbrev temp (w : ℂ) : Dirac A →ₐ[ℂ] Dirac A := adapter (w • 1) (w • 1)

lemma fee (i : A) {w : ℂ} (h : w≠0) (s : Bool) (x : Dirac A) : temp w (D s i x)= w⁻¹ • D s i (temp w x) := by
  unfold temp; rw [varying]
  simp [Matrix.one_apply, ite_smul,mul_ite,h]

lemma fee₂ (i j : A) {w : ℂ} (h : w≠0) (x : Dirac A) : temp w (hess i j x)=hess i j ((w^2)⁻¹ • temp w x) :=by
  simp only [hess, LinearMap.comp_apply, fee i h,fee j h,map_smul, smul_smul,pow_two,mul_inv_rev]

lemma fee_rotation (a : Matrix A A ℂ) (w : ℂ) (h : w≠0) (s : Bool) (x : Dirac A) : temp w (rotation s a x)= rotation s a (temp w x) := by
  have hh (i : A) : temp w (letter s i)=w • letter s i := by
    unfold letter bin; cases s
    · change adapter _ _ (psi i)=w • psi i; rw [adapt_psi]; simp [Matrix.one_apply,mul_ite,ite_smul]
    change adapter _ _ (bar i)=w • bar i; rw [adapt_bar]; simp [Matrix.one_apply,mul_ite,ite_smul]
  simp only [rotation, LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,map_mul,
    fee _ h,mul_smul_comm,hh,smul_mul_assoc,inv_smul_smul₀ h]

abbrev massMix (Q : Matrix B A ℂ) (x : A → A → Dirac A) (p v : B) : Grass.Dirac A :=
    ∑ i, ∑ j, Q p i • Qᴴ j v • x i j

lemma ship (Q : Matrix B A ℂ) (x : A → A → Dirac A) : Z Q (∑ i, ∑ j, hess i j (x i j))=
    ∑ p, ∑ v, hess p v (Z Q (massMix Q x p v)) := by
  unfold massMix; simp_rw [hess, LinearMap.comp_apply,map_sum,map_smul,transfer Q,map_sum,map_smul,smul_sum]
  have hh := sum_comm (s:=univ) (t:=univ) (f:= fun (y : A×A) (z : B×B) => Q z.1 y.1 • Qᴴ y.2 z.2 • hess z.1 z.2 (Z Q (x y.1 y.2)))
  simp only [Fintype.sum_prod_type] at hh; exact hh

def totalL (s : Bool) (a : Matrix A A ℂ) (X : Dirac A) (Y : A→A→Dirac A) :=
  rotation s a X-∑ i, ∑ j, hess i j (Y i j)

lemma ship_mass (Q : Matrix B A ℂ) (s : Bool) (a : Matrix A A ℂ) (b : Matrix B B ℂ)
    (h : st s Q*alpha s a=alpha s b*st s Q) (ht : a.trace=b.trace) (X : Dirac A) (Y : A→A→Dirac A) :
    Z Q (totalL s a X Y)=totalL s b (Z Q X) (fun i j=> b i j • Z Q X + Z Q (massMix Q Y i j)) := by
  unfold totalL; rw [map_sub,ship, Ward.commutes Q _ _ s h ht]; simp only [map_add,map_smul,sum_add_distrib]; abel

variable {c f n : Side} {N : ℕ}

structure Pass (n : Side) (N : ℕ) where
  kernel : Density n N
  car : Modes n N → Modes n N → Density n N
  usable : Continuous kernel
  freight (i j) : Continuous (car i j)

abbrev MatS (n : Side) (N : ℕ) := Matrix (Modes n N) (Modes n N) ℂ

namespace Pass
variable (F : Pass n N)

def total (s : Bool) (a : MatS n N) : Density n N := fun U => totalL s a (F.kernel U) (fun i j=> F.car i j U)
lemma travel (s : Bool) (a : MatS n N) : Continuous (F.total s a) := by
  unfold total totalL; apply Continuous.sub ((rotation _ _).continuous_of_finiteDimensional.comp F.usable)
  refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> ?_
  exact (hess _ _).continuous_of_finiteDimensional.comp (F.freight i j)

variable (F : Pass f N) (J : StepData c f)

def massMixD (i j : Modes c N) : Density f N := fun U=> massMix (meanSpin J U) (fun p v => F.car p v U) i j

lemma continuous_mix (i j) : Continuous (F.massMixD J i j) := by
  unfold massMixD massMix
  have H := Finite.mean_usable (N:=N) J
  refine continuous_finsetSum _ fun i' _=> continuous_finsetSum _ fun j' _=>  (show Continuous (fun U => (meanSpin J (N:=N) U) i i') from ?_).smul ((show Continuous (fun U => (meanSpin J (N:=N) U)ᴴ j' j) from ?_).smul (F.freight i' j')) <;> fun_prop

variable (Dg : J.patch.Branches J.kernel su) (b w : ℝ) (t : MatS c N)

def onward : Pass c N where
  kernel := TorusPCAC.block J b w F.kernel
  car i j := ((w:ℂ)^2)⁻¹ • (t i j • TorusPCAC.block J b w F.kernel + TorusPCAC.block J b w (F.massMixD J i j))
  usable := continuous_block J Dg F.kernel F.usable ..
  freight i j := Continuous.const_smul (Continuous.add (Continuous.const_smul (continuous_block J Dg _ F.usable ..) _) (continuous_block J Dg _ (F.continuous_mix J i j) ..)) _

lemma evaluate (hS : J.patch.Branches J.kernel su) (W : Fields c N →ₗ[ℂ] Fields c N)
    (f' : Grid f → Fields c N) (hf : Integrable f' (prior su f)) : J.push b (fun U=> W (f' U)) = fun V=> W (J.push b f' V) := by
  let W' := (LinearMap.toContinuousLinearMap W).restrictScalars ℝ
  funext V; unfold StepData.push
  rw [show W (∫ U, J.density b U V • f' U ∂prior su f)=∫ U, W' (J.density b U V • f' U) ∂prior su _ from
    (W'.integral_comp_comm (StepData.push_slice (J.isKernel hS b) V _ hf)).symm]
  congr 1; funext U; rw [map_smul]; rfl

lemma pack_sum {K : Type*}[Fintype K] (hS : J.patch.Branches J.kernel su) (x : K→ Grid f → Fields c N)
    (hx : ∀ i, Continuous (x i)) : J.push b (fun U=> ∑ i, x i U) = fun V=> ∑ i, J.push b (x i) V := by
  funext V; unfold StepData.push; simp_rw [smul_sum]; rw [integral_finsetSum]
  exact fun i _=> StepData.push_slice (J.isKernel hS b) V _ ((hx i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

set_option maxHeartbeats 800000 in
/-- This is the exact identity, on *all V*. Includes gauge conditioning
on branches, rather than using Q at any frozen configuration. -/
theorem polymer (s : Bool) {a : MatS f N}
    (h : ∀ U, st s (meanSpin J U) * alpha s a= alpha s t * st s (meanSpin J U))
    (ht : a.trace=t.trace) (hw : w ≠ 0) : (F.onward J Dg b w t).total s t=TorusPCAC.block J b w (F.total s a) := by
  funext V
  let X := TorusPCAC.high J F.kernel
  let Y := fun i j : Modes c N=> TorusPCAC.high J (F.massMixD J i j)
  let H := fun i j : Modes c N => t i j • X + Y i j
  have hX := show Continuous X from high_cont J _ F.usable
  have hY (i j) : Continuous (Y i j):= high_cont J _ (F.continuous_mix J i j)
  have hT (i j) : Continuous (H i j) := (hX.const_smul (t i j)).add (hY i j)
  have hp (U : Grid f) : TorusPCAC.high J (F.total s a) U= rotation s t (X U)-∑ i, ∑ j, hess i j (H i j U):= ship_mass (meanSpin J U) s a t (h U) ht _ _
  have helps (f' : Grid f → Fields c N) (hf : Continuous f') : Integrable f' (prior su f):=hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh : J.push b (TorusPCAC.high J (F.total s a)) V= rotation s t (J.push b X V)-∑ i, ∑ j, hess i j (J.push b (H i j) V):=by
    let g (i j : Modes c N) (U : Grid f) := hess i j (H i j U)
    have hg i j : Continuous (g i j) := (hess i j).continuous_of_finiteDimensional.comp (hT i j)
    have he (W W' : Grid f → Fields c N) (he : Continuous W) (hi : Continuous W') : J.push b (fun U=> W U-W' U) V= J.push b W V-J.push b W' V:=by
      unfold StepData.push; simp_rw [smul_sub]; rw [integral_sub]
      · exact StepData.push_slice (J.isKernel Dg b) V _ (helps _ he)
      exact StepData.push_slice (J.isKernel Dg b) V _ (helps _ hi)
    rw [show TorusPCAC.high J (F.total s a) = fun U=> ((rotation s t) (X U))-(∑ i, ∑ j, g i j U) from funext hp,
      he (fun U => rotation s t (X U)) (fun U=> ∑ i, ∑ j, g i j U) ((rotation s t).continuous_of_finiteDimensional.comp hX) (continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> hg i j),
      evaluate J b Dg _ X (helps _ hX), pack_sum J b Dg (fun i U=> ∑ j, g i j U) (fun i=>continuous_finsetSum _ fun j _=> hg i j)];
    simp_rw [pack_sum J b Dg (g _) (hg _)]; dsimp only [g]; simp_rw [evaluate J b Dg (hess _ _) (H _ _) (helps _ (hT _ _))]
  have hi (i j) : J.push b (H i j) V=t i j • J.push b X V+J.push b (Y i j) V:=by
    rw [show H i j=t i j • X + _ from rfl, StepData.push_add (J.isKernel Dg b) _ _ (helps _ (hX.const_smul _)) (helps _ (hY i j))]
    rw [Pi.add_apply, show t i j • X=(fun U=> ((t i j • (LinearMap.id)) : Fields c N→ₗ[ℂ] Fields c N) (X U)) from rfl,evaluate J b Dg _ X (helps _ hX)]; rfl
  have hw : (w:ℂ)≠0:= Complex.ofReal_ne_zero.mpr hw
  change totalL s t _ _= temp (↑w) (J.push b (TorusPCAC.high J (F.total s a)) V)
  simp_rw [hh,map_sub,fee_rotation _ (↑w) hw,map_sum,fee₂ _ _ hw, hi,map_add (temp (A:=Modes c N) (↑w)),map_smul (temp (A:=Modes c N) (↑w))]
  rfl
end Pass
end YM.TorusPCAC.Ward
