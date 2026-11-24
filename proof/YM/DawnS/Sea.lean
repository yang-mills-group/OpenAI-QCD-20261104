import YM.DawnS.Christ
import YM.DawnS.Figs
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder ENNReal
variable {d:ℕ}(r:ℝ)(hr:0<r)
local notation "η"=> sigL (d:=d) r
local notation "T"=> Vault d
local notation "S"=> expandVt (d:=d)
variable (C:Matrix (Vault d) (Vault d) ℂ)(hc:IsUnit C)(he:Cᴴ*hank d r*C=1)
noncomputable def vaultT(C:Matrix T T ℂ): Seed (Vault d)→ₗ[ℂ] beam d:=(thetaBasis _).constr ℂ (fun i=> expandVt (fun k=> C k i))
noncomputable def jewel(i:T):= vaultT C (thetaBasis _ i)
include he
lemma ports(a b:Vault d): sigL r (jewel C a) (jewel C b)=if a=b then 1 else 0:=by
     let K:=hank d r; unfold jewel vaultT; rw[Module.Basis.constr_basis,Module.Basis.constr_basis,quadratic,←Matrix.one_apply]; rw [mul_assoc] at he; exact congr_fun (congr_fun he a) b -- matrix colVec formula defeq sums
omit he
include hc
lemma lofty: LinearMap.range ((slashEq d).mkQ.comp (vaultT C))=⊤:=by
     let K:= (slashEq d).mkQ; let F:= K.comp (vaultT C); let X(i:T):= K (jewel C i); let Y(i:T):= K (lantern i); let L:= hc.unit⁻¹; have ht:C*L.val=1:= hc.unit.mul_inv
     have h(a:T): Y a=(∑ i,L.val i a • X i):=by
          unfold X jewel vaultT; simp_rw [Module.Basis.constr_basis]; unfold expandVt; simp only[map_sum,map_smul,Finset.smul_sum, smul_smul]; rw[sum_comm];simp_rw [← Finset.sum_smul]; unfold Y; have hp(i:T): (∑ j,L.val j a* C i j)=(1:Matrix T T ℂ) i a:=( (show _=(C*L.val) i a from Finset.sum_congr rfl fun j _=> mul_comm ..)).trans (congr_fun (congr_fun ht i) a); simp_rw [hp,Matrix.one_apply,ite_smul]; simp
     refine eq_top_iff.mpr ?_; rw [← radiant d]; apply Submodule.span_le.mpr; rintro t ⟨i,rfl⟩; change Y i∈_; rw [h i]; refine Submodule.sum_mem (LinearMap.range F) (fun i _=>Submodule.smul_mem _ _ ?_); exact ⟨_,rfl⟩ -- F_AP
end YM.DawnS
