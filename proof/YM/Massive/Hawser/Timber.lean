import YM.Massive.Hawser.Alcyon
/-!
Rank lower bound preparation: explicit spinor derivative-zero projection counts even after imposing the
full equation ideal on the polynomial forms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV.Free
open Lattice Wilson RG Source Function QCD Lat Massive Lining Papyrus Filter Work.G05 Finset Matrix Grass TensorProduct
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
namespace Fountain
variable {d:ℕ}
local notation "L" => SpinMode d
local notation "Q" => Pairs L
local notation "T" => SpinPol d
local notation "Γ" => Seed Q
abbrev origin (u: Q): Multi d:= Sum.elim (fun x:SpinMode d=>x.1.1) (fun x:SpinMode d=>x.1.1) u
def mask (s:Finset Q) : Matrix Q Q ℂ:= Matrix.diagonal (fun i=>if i∈s then 1 else 0)
def waveP (s: Finset Q) : Alg Q →ₐ[ℂ] Alg Q := changeVars (mask s)
lemma carrier (s: Finset Q)(i:Q) :waveP s (atom i)=if i∈s then atom i else 0:=by rw [waveP,change_atom]; unfold mask; by_cases ht:i∈s <;> simp [diagonal_apply, ite_smul, ht]
def Floor (s:Finset Q):= ∀ i∈s, origin i=0
lemma excluded {s:Finset Q}(h:Floor s){i:Q}(hp: origin i≠0): waveP s (atom i)=0:=by rw [carrier]; exact if_neg fun hv=>hp (h i hv)
lemma taboo {s:Finset Q}(h:Floor s){i:Q}(hp: origin i≠0): substitution (mask s) (thetaBasis _ i)=0:=by
    have he:= excluded h hp; unfold waveP changeVars atom at he; rw [ExteriorAlgebra.map_apply_ι] at he; exact (ExteriorAlgebra.ι_eq_zero_iff (R:=ℂ) _).mp he
lemma lift_m (a:Axis)(x y:Multi d)(h:AtNext a x y): y ≠ 0:= by intro ht; have hv:= congr_fun h a; rw [ht,Purl.power_zero,update_self] at hv; omega
lemma slash_k {s:Finset Q}(h:Floor s)(i:L): substitution (mask s) (slashCol i)=0:=by
    unfold slashCol; simp_rw [map_sum]; refine sum_eq_zero fun a _=> sum_eq_zero fun i' _=> sum_eq_zero fun q _=>?_ ; split; next H=> rw [map_smul]; exact (congr_arg (fun f:Γ=> _ • f) (taboo h (i:=Sum.inl ((q,i',i.1.2.2),i.2)) (lift_m a _ _ H))).trans (smul_zero _)
    next H=> exact map_zero _
lemma slash_c {s:Finset Q}(h:Floor s)(i:L): substitution (mask s) (slashBar i)=0:=by
    unfold slashBar; simp_rw [map_sum]; refine sum_eq_zero fun a _=> sum_eq_zero fun i' _=> sum_eq_zero fun q _=>?_ ; split; next H=> rw [map_smul]; exact (congr_arg (fun f:Γ=> _ • f) (taboo h (i:=Sum.inr ((q,i',i.1.2.2),i.2)) (lift_m a _ _ H))).trans (smul_zero _)
    next H=> exact map_zero _
lemma slash_l {s:Finset Q}(h:Floor s) : slashEq _ ≤ LinearMap.ker (substitution (mask s)):= Submodule.span_le.mpr fun x hx=>by
   rcases hx with hx|hx <;> rcases hx with ⟨i,rfl⟩; exact LinearMap.mem_ker.mpr (slash_k h i); exact LinearMap.mem_ker.mpr (slash_c h i)
local notation "V" => ExteriorAlgebra ℂ (Seed Q ⧸ (slashEq d))
def stairs (s: Finset Q)(h:Floor s) : V →ₐ[ℂ] T:= ExteriorAlgebra.map ((slashEq d).liftQ _ (slash_l h))
def oracle (s:Finset Q)(h:Floor s): Maxwell.WickPol su ⊗[ℂ] V →ₗ[ℂ] T:= (TensorProduct.lid ℂ _).toLinearMap.comp
  (TensorProduct.map (Maxwell.probe (0:Maxwell.TaylorTower su)).toLinearMap (stairs s h).toLinearMap)
lemma oracle_eq (s:Finset Q)(h:Floor s)(x:T): oracle s h (reduceEq (tmul ℂ (1:GPol) x))= waveP s x:=by
    unfold oracle reduceEq; rw [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.map_tmul, LinearEquiv.coe_coe,TensorProduct.lid_tmul]; simp only [AlgHom.toLinearMap_apply,map_one,one_smul]; unfold stairs waveP changeVars; rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]; congr 2
lemma crystal {s:Finset Q}(hf:Floor s)(y:Label d)(x:T)(he:y.val=(1:GPol) ⊗ₜ[ℂ] x)(hx: waveP s x≠0): projection y≠0:=by
    intro hv; have h:=congr_arg Subtype.val hv; change reduceEq (y.val)=0 at h; apply hx; rw [← oracle_eq s hf,← he,h,map_zero]
lemma flame {A:Type*}[Fintype A][DecidableEq A](x:List A)(h:x.Nodup): (x.map Grass.atom).prod≠0:=by
    have he: mono x.toFinset≠0:=by intro h; simpa only [h,map_zero,zero_ne_one] using Grass.read x.toFinset
    rcases sign_product x h with h|h <;> rw [h] <;> simp [he]
end Fountain
end YM.Massive.UV.Free
#print axioms YM.Massive.UV.Free.Fountain.crystal
