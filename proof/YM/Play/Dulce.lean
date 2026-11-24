import YM.Play.Quiet
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Play
open QCD QCD.Grass QCD.Creek QCD.Cove Function Finset Filter NormedSpace Cupola Ribbon QCD.Bera QCD.Anomaly
open MeasureTheory BigOperators Matrix
open scoped Topology BigOperators ContDiff Classical
variable {I K A B G E: Type}[Fintype I][Fintype A][Fintype G]
namespace Chamber
local notation "H"=> Finset I
local notation "H1"=> Patio (A ⊕ Spine I)
local notation "TA"=> QCD.Bera.Papers G (Patio (A⊕Spine I))
-- field.Q
variable (f: Finset I → Patio (A⊕Spine I))(p:Finset I→ Papers G (Patio (A⊕Spine I)))(q:I→Bool)
variable {S:Finset A}{D:Finset (A⊕ Spine I)}{T:Finset I}{j n m:ℕ}
lemma parcelR (x:H1)(ht:x∈ VaultP A q T)(hw:clad S x.val) (hx:x.val ∈ Rim univ n): x.val∈ Rim (S.disjSum (burst q T)) n:=by
   let i:=burst q T; have hp:x.val∈ region (S.disjSum i):=by
      rw [← (Polite.exact ht), markedOut]; apply Subalgebra.mul_mem; · exact effects (fiber (Spine I)) (fun j hj=>by unfold fiber; rw [embed_atom]; exact Creek.marked _ _ (inl_mem_disjSum.mpr hj)) _ (hw _)
      exact effects (quill A) (fun j hj=>by unfold quill; rw [embed_atom]; exact Creek.marked _ _ (inr_mem_disjSum.mpr hj)) _ (Rim.monoIn _)
   intro j hj; exact ⟨Rim.whenever _ hp hj,(Rim.rimIn hx j hj).2⟩
lemma censusD (he:∀ i⊆T,i.Nonempty→ f i∈ vaultS D (i.card*n)): parties f T∈ vaultS D (T.card*n):=by
   have hm v (h:∀ i∈v,i⊆T∧i.Nonempty): (∏ i∈ v,f i) ∈vaultS D (∑ i∈v,i.card*n):=by induction v using Finset.induction_on with
    | empty=>rw [prod_empty]; exact Rim.one D
    | insert i v hi ih=> rw [prod_insert hi,sum_insert hi]; exact Rim.multiply (he _ (h i (mem_insert_self ..)).1 (h i (mem_insert_self ..)).2) (ih (fun i hi=> h i (mem_insert_of_mem hi)))
   refine Submodule.sum_mem _ fun i hi=>?_ 
   have h:=hm i (fun j hj=> (member hi hj).symm); rwa [←sum_mul, patrons hi] at h
lemma parcelP {a v:ℝ}(h:1 ≤ v)(X:G→ℝ)(hs:0 ≤ a)(hf:∀ i⊆T,i.Nonempty→ ‖f i‖ ≤ v)(hp:∀ i⊆T,i.Nonempty→ ‖Oce.rose (A⊕Spine I) X (p i)‖ ≤ v)(hk:∀ i⊆T,i.Nonempty→ ‖f i - Oce.rose (A⊕Spine I) X (p i)‖ ≤ a)(ht:T.card ≤ m) : ‖parties f T - Oce.rose (A⊕Spine I) X (parties p T)‖ ≤ face m v*a:=by
   convert! spendingX (marksV _) f (fun i=> Oce.rose (A⊕Spine I) X (p i)) T ht hf hp hk h hs using 1; congr 2; unfold parties; simp_rw [map_sum,map_prod] -- direction
end Chamber
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Chamber.censusD
#print axioms YM.MassiveQCD.Play.Chamber.parcelP
