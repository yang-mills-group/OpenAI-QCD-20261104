import YM.Poised.Somni
import YM.MassiveQCD.Lyre.Elevator
/-!
# PAYOUT fee on Small regular lenses, including transform and displacement
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource -- Lyre conflicts
open Lining Lining.Ferry YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform
variable [Fintype A][Fintype B]{f:A→ℝ}{g:B→ℝ}{x a' p u v τ:ℝ}{o:Site c}
section smallest
-- without exterior typeclass parity constraint. u-uniform, includes empty matrices. All lengths CASE PRINCE
variable {V:Finset A}
private lemma monotag(f:A→ℝ)(hf:∀ i,0<f i)(i:Finset A): load f (mono i)=∏ j∈i,f j:=by rw [dry f hf,sum_eq_single i]; simp; intro j _ h; rw [read_other _ _ h,norm_zero,mul_zero]; simp
lemma redisplay (f:A→ℝ)(hf:∀ i,0<f i)(g:B→ℝ)(hg:∀ i,0<g i)(X:A→ B→ℂ)(i:A): load g (changeVars X (atom i)) ≤ ∑ j,g j*‖X i j‖:=by
   rw [change_atom]; exact (load_sum ..).trans (Finset.sum_le_sum fun j _=>(le_of_eq (by rw [load_scale,load_atom g hg,mul_comm]))) -- f unused
variable (R:A→ B→ℂ)(S:A→B→ℂ)(f:A→ℝ)(g:B→ℝ)(W:Finset A) {M:ℝ}(hf:∀ i,0<f i)(hg:∀ i,0<g i)(hM:0≤M)
include hf hg hM
lemma lane (hr:∀ i∈W,(∑ j,g j*‖R i j‖) ≤ M*f i) (A':Alg A)(h: A'∈region W)(hh:A'∈layer _ n): load g (changeVars R A') ≤ M^n*load f A':=by
    conv_lhs=>rw [← write A',map_sum]
    apply (load_sum ..).trans; rw [dry f hf, mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [map_smul, load_scale]
    have he(j:A)(hj:j∈W):load g (changeVars R (atom j)) ≤ M*f j := (redisplay f hf g hg R j).trans (hr _ hj)
    have ht(i:Finset A)(hi:i⊆W):load g (changeVars R (mono i))≤ M^i.card*∏ j∈i,f j:=by
       induction i using Finset.induction_on with
       | empty=> simp [Creek.load,wscale]
       | @insert j i hj ih=>
         have hm:i⊆ W:= Finset.Subset.trans (Finset.subset_insert _ _) hi; have hv:= ih hm; have hL:0≤M*f j:=mul_nonneg hM (hf j).le; rw [card_insert_of_notMem hj, prod_insert hj,pow_succ]; have hV: Disjoint {j} i:=by simp [hj]
         have hh:=mono_mul_sign _ _ hV; rw [disjUnion_eq_union,Finset.singleton_union,mono_single] at hh
         have h :load g (changeVars R (atom j*mono i)) ≤ (M^i.card*M) * (f j*∏ k∈i,f k):=by rw [map_mul]; exact (load_mul ..).trans ((mul_le_mul (he j (hi (mem_insert_self ..))) hv (load_nn ..) hL).trans_eq (by ring))
         rcases hh with h'|h'; · rwa [h'] at h
         simpa only [h',map_neg,Creek.load,wscale,norm_neg] using h
    by_cases hX:coef i A'=0; · rw [hX,norm_zero,mul_zero,zero_mul,mul_zero]
    have hy:i⊆W:= not_not.mp (mt (Cove.ember A' h i) hX); specialize ht i hy
    have hq:i.card=n:= not_not.mp (mt (spectrum hh i) hX); rw [hq] at ht
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by ring) -- hq affects Lhs budget
-- coarse polynomial Lipschitz lane.Bill method with ≥1 on M
lemma tenderV (C:ℝ)(hc:0≤C) (hm:1 ≤ M)(hr:∀ i∈W,(∑ j,g j*‖R i j‖) ≤ M*f i) (hu:∀ i∈W,(∑ j,g j*‖S i j‖) ≤ M*f i)(hz:∀ i∈W, (∑ j,g j*‖R i j-S i j‖) ≤ C*f i) (A':Alg A)(h: A'∈region W)(hh:A'∈layer _ n): load g (changeVars R A' -changeVars S A') ≤ ((n:ℝ)*C*M^n)* load f A':=by
    conv_lhs=>rw [← write A',map_sum,map_sum,← Finset.sum_sub_distrib]
    apply (load_sum ..).trans; rw [dry f hf, mul_sum]; refine sum_le_sum fun i _=>?_ ; rw [map_smul,map_smul, ← smul_sub, load_scale]
    have he(j:A)(hj:j∈W):load g (changeVars R (atom j)) ≤ M*f j := (redisplay f hf g hg R j).trans (hr _ hj)
    have hz(j:A)(hj:j∈W): load g (changeVars R (atom j) -changeVars S (atom j)) ≤ C*f j:=by rw [show changeVars R (atom j)-changeVars S (atom j) =changeVars (R-S:A→B→ℂ) (atom j) from ?_]; exact (redisplay f hf g hg (R-S) j).trans (hz _ hj); rw [change_atom,change_atom, ← Finset.sum_sub_distrib,change_atom]; exact sum_congr rfl fun i _=>(sub_smul ..).symm
    have ht(i:Finset A)(hi:i⊆W):load g (changeVars R (mono i) - changeVars S (mono i)) ≤((i.card:ℝ)*C*M^i.card)*∏ j∈i,f j:=by
       induction i using Finset.induction_on with
       | empty=> simp [Creek.load,wscale]
       | @insert j i hj ih=>
         have hm₁:i⊆ W:= Finset.Subset.trans (Finset.subset_insert _ _) hi; have hv:= ih hm₁; have hL:0≤M*f j:=mul_nonneg hM (hf j).le; have hV: Disjoint {j} i:=by simp [hj]
         have hh:=mono_mul_sign _ _ hV; rw [disjUnion_eq_union,Finset.singleton_union,mono_single] at hh
         let U:=changeVars R ; let T:=changeVars S; let P:= f j; let V:= ∏ j∈i,f j; have hP:0≤P:=(hf _).le; have hU:0≤V:=prod_nonneg fun j _=>(hf j).le
         have hk:j∈W:= hi (mem_insert_self ..)
         have hI:mono i∈region W:=by obtain ⟨z,-,hh,H⟩:= expression i; rw [H]; refine Subalgebra.list_prod_mem _ ?_; simp only [List.mem_ofFn]; rintro _ ⟨j,rfl⟩; exact Creek.marked _ _ (hm₁ ((hh _).mpr ⟨j,rfl⟩))
         have hD: load g (T (mono i))≤M^i.card*V:=by have h := lane S f g W hf hg hM hu (mono i) hI (homogeneous ..); rwa [monotag f hf] at h
         rw [card_insert_of_notMem hj, prod_insert hj,pow_succ,Nat.cast_add_one]
         have h: load g (U (atom j*mono i)-T (atom j*mono i))≤(i.card+1:ℝ)*C*(M^i.card*M)*(f j*V):=by
            rw [map_mul,map_mul,show U _*U _-T _*T _=U (atom j)*(U (mono i)-T (mono i))+(U (atom j)-T (atom j))*T (mono i) from (by noncomm_ring)]
            apply (Spice.spawnA ..).trans; have hv₀:=mul_le_mul (hz j hk) hD (load_nn ..) (show 0 ≤ C*P by positivity); refine (add_le_add ((load_mul ..).trans (mul_le_mul (he j hk) hv (load_nn ..) hL)) ((load_mul ..).trans hv₀)).trans ?_; have hx:0≤M^i.card:= pow_nonneg hM _; nlinarith only [mul_le_mul_of_nonneg_right hm (show 0 ≤ C*f j * (M^i.card*V) by positivity [hf j])]
         rcases hh with h'|h'; · rwa [h'] at h
         rw [h',map_neg,map_neg, show - (U _)- -(T _)=-(U (mono (insert j i))-T (mono (insert j i))) from (by abel),Creek.load,wscale,map_neg,norm_neg] at h; exact h
    by_cases hX:coef i A'=0; · rw [hX,norm_zero,mul_zero,zero_mul,mul_zero]
    have hy:i⊆ W:= not_not.mp (mt (Cove.ember A' h i) hX); specialize ht i hy
    have hq:i.card=n:= not_not.mp (mt (spectrum hh i) hX); rw [hq] at ht
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by ring)
end smallest
end Pipes
end YM.Massive.Poised
