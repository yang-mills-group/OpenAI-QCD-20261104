import YM.Intag.Shift
import YM.Intag.Column
import YM.Bloom.Jar
/-!
# max separation converter on AUTHENTIC Euclidean probes from native lifts
 preserves offsets not just torus metric. also helps checked-field fit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG Finset
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.L2Operator ContDiff Topology TensorProduct
namespace Consent
open YM.Bank YM.Bank.Jule YM.Bloom YM.Bloom.Jar
variable (z z' : Cover){f: Side}(w:ℝ)(n:ℕ)
local notation "sz"=> w^n
-- liftNorm.K.Obsolete sizes.
lemma hereN : ‖Kith.rock (Lattice.lift (wrap f z))‖ ≤2*pdist (wrap f z) :=by
    let x:=wrap f z; let y:= Kith.rock (Lattice.lift x); let m:ℝ:= ↑(pdist x)
    have hh i: ‖y i‖≤ m:=calc ‖(((Lattice.lift x i):ℤ):ℝ)‖=((Lattice.lift x i).natAbs:ℝ) := by rw [← norm_natAbs,Real.norm_natCast]
                               _≤ m := by unfold m; exact_mod_cast component_le x i
    have hb : ‖y‖^2 ≤ (4:ℝ)*m^2 :=by
       rw [PiLp.norm_sq_eq_of_L2]; refine (Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hh i) 2)).trans_eq ?_
       simp [Axis]
    change ‖y‖ ≤ 2*m; nlinarith [show 0 ≤ m by unfold m; positivity]
lemma boot (i: Axis): ((z i).natAbs:ℝ)= ‖Kith.rock z i‖:=by change _=‖(↑(z i):ℝ)‖; rw [← norm_natAbs, Real.norm_natCast]
lemma rotor (i:Axis): ((z i).natAbs:ℝ) ≤ ‖Kith.rock z‖:=by rw[boot]; exact PiLp.norm_apply_le ..
variable (hw:0<w)
local notation "P"=> posT w n
include hw
lemma pulse: ‖posT w n z‖ *w^n= ‖Kith.rock z‖:=by have hv:0<sz:=pow_pos hw _; unfold posT; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le),inv_mul_eq_div, div_mul_cancel₀ _ hv.ne']
variable (a b:ℝ)
lemma rootV (hp:posT w n z -posT w n z'∈ Oasis a b) (hc:2*(b*w^n)<(f.val:ℝ)) : a*w^n ≤ 2*separation (wrap f z) (wrap f z')∧ (separation (wrap f z) (wrap f z'):ℝ) ≤ b*w^n:=by
      rw [←unspread] at hp; obtain ⟨h,hq⟩:= consp hp
      let t:ℝ:= sz; have h₁:‖Kith.rock (z-z')‖ ≤ b*t:=by rw [←pulse _ _ _ hw]; exact mul_le_mul_of_nonneg_right hq (pow_nonneg hw.le _)
      let x:= wrap f (z-z'); let D:= z-z'; have hv:Lattice.lift x=z-z':=by
           refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; have hp₁:= (mul_le_mul_of_nonneg_left ((rotor D i).trans h₁) (by norm_num : (0:ℝ) ≤2)).trans_lt hc; have ht: 2*((D i).natAbs)<f.val:=by exact_mod_cast hp₁
           change -(↑_:ℤ)<2*D i ∧ 2*D i≤_; omega
      have hz:= hereN (f:=f) D; rw [show wrap f D=x from rfl, hv] at hz
      have hh: separation (wrap f z) (wrap f z')= pdist x:=by rw [separation,← map_sub]
      rw [hh]; constructor; · apply le_trans _ hz; rw [←pulse _ _ _ hw]; exact mul_le_mul_of_nonneg_right h (pow_nonneg hw.le _)
      obtain ⟨i,hi,h'⟩:= Finset.exists_mem_eq_sup (s:= (univ:Finset Axis)) Finset.univ_nonempty (fun i=> (Lattice.lift x i).natAbs)
      change pdist x= _ at h'; rw [h',hv]; exact (rotor ..).trans h₁
lemma solo (i: Cover)(v:ℕ)(hh: i∈ box v): ‖posT w n i‖ ≤ (2*v:ℝ)/w^n:=by
     let Y:= Kith.rock i
     have hc: ∀ a:Axis, ‖Y a‖ ≤ v:=by
          intro a; rw [show ‖Y a‖= ((i a).natAbs:ℝ) from (boot i a).symm]; obtain ⟨h,h'⟩:= box_test.mp hh; have he: (i a).natAbs ≤ v:=by specialize h a; specialize h' a; omega
          exact_mod_cast he
     have hp: ‖Y‖≤2*v:=by
         have hh:‖Y‖^2≤ 4*(v:ℝ)^2:=by rw [PiLp.norm_sq_eq_of_L2]; exact (Finset.sum_le_sum (fun a _=> pow_le_pow_left₀ (norm_nonneg _) (hc a) 2)).trans_eq (by simp [Axis])
         nlinarith only [hh,norm_nonneg Y, Nat.cast_nonneg (α:=ℝ) v]
     rw [le_div_iff₀ (pow_pos hw _), pulse i w n hw]; exact hp
end Consent
end YM.Intag
#print axioms YM.Intag.Consent.rootV
#print axioms YM.Intag.Consent.solo
