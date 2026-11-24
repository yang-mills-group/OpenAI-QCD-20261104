import YM.QCD.Coda.Sun
import YM.QCD.Kites.Alone
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Coda
open Lattice Wilson Function Finset Filter Metric RG Precision Extra Iteration PhysicalNext.Repeat
open Lat Octave Kit Leaf Tee Port Garden Run Orbit Cove Loom Fleet
open ConnectedActivityE6 Blaze Brush Sienna NormedSpace Lantern Push MeasureTheory Tree
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
open Reggae Tidings Grass Kites
variable {n f:Side}{N j:ℕ}
local notation "A"=>EvenA n N
lemma stature (x:A): wearK n N 0 x= sparkF n N (mud x):=by
   apply Subtype.ext; apply Stew.poster; intro i
   change coef i (engine 0 (Keys n N) x.val)=coef i ((mud x) • (1: Grass.Alg (Keys n N))); rw [fundW]; by_cases he:i=∅
   · subst i; rw [card_empty,pow_zero,one_mul,map_smul, ← mono_empty, Grass.read,smul_eq_mul,mul_one]; rfl
   rw [Complex.ofReal_zero,zero_pow (Nat.pos_iff_ne_zero.mp (card_pos.mpr (nonempty_iff_ne_empty.mpr he))),zero_mul, map_smul,← mono_empty, Grass.read_other _ _ he,smul_zero]
lemma term (x:A) : mud (exp x)=Complex.exp (mud x):=by
   have he := (map_exp (wearK n N 0) (songT (c:=n) (N:=N) 0).continuous x).symm
   rw [stature,stature,sky_first] at he; have hh:=congr_arg (clay n N) he; unfold sparkF at hh; rw [map_smul,map_smul, show clay n N 1=1 from ?_,smul_eq_mul,mul_one,smul_eq_mul,mul_one] at hh; exact hh.symm
   change coef ∅ (1:Dirac (Modes n N))=1; rw [← mono_empty,Grass.read]
set_option maxHeartbeats 420000 in
lemma exclusive (x:A) (ht:mud x=0)(hx:exp x=1): x=0:=by
   let f v:= wearK n N v x; have hf: Continuous f:=by
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr; -- check
      exact continuous_by_coef _ fun i=>by change Continuous (fun v=> coef i (engine v (Keys n N) x.val)); simp_rw [fundW]; fun_prop
   have he: f 0=0:=by unfold f; rw [stature,ht]; simp [sparkF]
   let S:= ContinuousLinearEquiv.refl ℂ A; have hv: HasStrictFDerivAt exp (S.toContinuousLinearMap) (0:A):= hasStrictFDerivAt_exp_zero
   let W:= hv.toOpenPartialHomeomorph exp; have hp: (0:A)∈W.source:= hv.mem_toOpenPartialHomeomorph_source
   have hh : ∀ᶠ v in 𝓝[>] (0:ℝ), f v ∈ W.source:= nhdsWithin_le_nhds ((hf.continuousAt) (W.open_source.mem_nhds (he.symm ▸ hp))) -- function syntax
   obtain ⟨u,hu,hM⟩:= ((show ∀ᶠ v in 𝓝[>] (0:ℝ),0<v from self_mem_nhdsWithin).and hh).exists
   have hW:wearK n N u x=0:=W.injOn hM hp (show exp (f u)=exp 0 by unfold f; rw [← map_exp (wearK n N u) (songT (c:=n) (N:=N) u).continuous,hx,map_one,exp_zero]); exact (wit x u⁻¹ u (inv_mul_cancel₀ hu.ne')).symm.trans (by rw [hW,map_zero])
lemma beryl (x y:A)(ht:exp x=exp y)(hx:(mud x).im=0) (hy: |(mud y).im|≤2): x=y:=by
   have he : mud x=mud y:=by
      have hQ:=congr_arg mud ht; rw [term,term] at hQ
      have hh:=congr_arg Complex.log hQ; have hp:=Real.pi_gt_three; rw [Complex.log_exp (by linarith) (by linarith), Complex.log_exp (by linarith [abs_le.mp hy|>.1]) (by linarith [abs_le.mp hy|>.2])] at hh; exact hh
   apply sub_eq_zero.mp; apply exclusive; exact (map_sub (clay n N) x y).trans (sub_eq_zero.mpr he)
   rw [sub_eq_add_neg, exp_add,ht, ← exp_add,add_neg_cancel,exp_zero]
abbrev indigo (c:Side)(N:ℕ):EvenA c N→L[ℝ]ℝ:= Complex.imCLM.comp ((clay c N).restrictScalars ℝ)
lemma indigoF (x:A): |indigo n N x|≤‖x‖:=(Complex.abs_im_le_norm _).trans (Grass.piece_le _ _)
lemma freed (X:Sheet n)(v:ℝ): indigo n N (powerZ n N v X)=0:= by
   change (mud (wearK n N v (paleF N X))).im=_; rw [proofM]; have hv : mud (paleF N X)=0:= Grass.spectrum (form_two _) ∅ (by simp); rw [hv]; rfl
end YM.QCD.Coda
