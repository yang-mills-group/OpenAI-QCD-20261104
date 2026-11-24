import YM.DawnS.Mocha
import YM.Elms.Pulse
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
variable {d:ℕ}
-- orbit comprises all spatial leaves. use bool encoding.
abbrev chit(d:ℕ) := {p:Multi d // power p timeAxis=0}
abbrev Vault(d:ℕ):= Flavor 6 × Hue × Bool × chit d × Pinor
noncomputable def prop (b:Bool)(i:SpinMode d):beam d:= if b then dnL i else upL i
noncomputable def lantern (i:Vault d):beam d:= prop i.2.2.1 ((i.2.2.2.1.val,i.2.2.2.2,i.2.1),i.1)
noncomputable def spanned(d:ℕ):= Submodule.span ℂ (Set.range ((slashEq d).mkQ ∘ lantern))
local notation "T"=> (spanned d)
set_option quotPrecheck false
local notation "qK"=> (slashEq d).mkQ
private lemma all_up(p:Multi d)(b:Hue)(c:Flavor 6) : ∀ a:Pinor,qK (upL ((p,a,b),c)) ∈ T:=by
     induction h:power p K using Nat.strong_induction_on generalizing p with
     | h m ih =>
       by_cases hm:m=0
       · exact fun a=>Submodule.subset_span (Set.mem_range.mpr ⟨(c,b,false,(⟨p,h.trans hm⟩:chit d),a),rfl⟩)
       obtain ⟨q,hq⟩:= (Elm.Pulses.nextFound p K).mpr (by omega); let f(j):= qK (upL ((p,j,b),c));
       let F(i:Axis)(a:Pinor):scarG d:= ∑ j:Pinor, ∑ y:Multi d,qK (if AtNext i q y then gamma i a j • upL ((y,j,b),c) else 0)
       have hx(a:Pinor): (∑ j:Pinor,gamma K a j • f j)∈T:=by
              have he(j:Pinor): (∑ y:Multi d,qK (if AtNext K q y then gamma K a j • upL ((y,j,b),c) else 0))= gamma K a j • f j:=by
                   rw [Finset.sum_eq_single p,if_pos hq,map_smul]
                   intro y hm ht; rw [if_neg (fun h=> ht (echoUnique h hq)), map_zero]
                   simp
              have hF: F K a= ∑ j:Pinor, gamma K a j • f j:= Finset.sum_congr rfl fun i _=> he i
              have ht: qK (slashCol ((q,a,b),c))=0:=(Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inl ⟨_,rfl⟩))
              unfold slashCol at ht; simp_rw [map_sum] at ht
              let I:= ∑ i∈ (Finset.univ.erase K), F i a
              change ∑ i:Axis,F i a=0 at ht; rw [← Finset.add_sum_erase _ (fun i=> F i a) (Finset.mem_univ K)] at ht; rw [← hF, eq_neg_of_add_eq_zero_left ht]; apply Submodule.neg_mem; apply Submodule.sum_mem T
              intro i hi; let hb:= (Finset.mem_erase.mp hi).1; refine Submodule.sum_mem T fun j _=> Submodule.sum_mem T fun t _=>?_ ; split_ifs; next he=>
                   rw [map_smul]; apply Submodule.smul_mem; apply ih (power t K) _ t rfl; rw [show power t K=power q K from by rw[he,update_of_ne hb.symm]]; rw [← h,hq,update_self]; omega
              rw [map_zero]; exact (spanned d).zero_mem
       intro a; have hp : f a=∑ j:Pinor, gamma K a j • ∑ k:Pinor,gamma K j k • f k:=by
            simp_rw [Finset.smul_sum,smul_smul]; rw [sum_comm]; simp_rw[← Finset.sum_smul]; simp_rw [show ∀ x:Pinor, (∑ j,gamma K a j* gamma K j x)=(1:Spike) a x from fun k=> congr_fun (congr_fun (gamma_sq K) a) k]; simp [Matrix.one_apply,ite_smul]
       change f a∈_; rw[hp]; exact Submodule.sum_mem T fun i _=> Submodule.smul_mem T _ (hx i)
private lemma all_down(p:Multi d)(b:Hue)(c:Flavor 6) : ∀ a:Pinor,qK (dnL ((p,a,b),c)) ∈ T:=by
     induction h:power p K using Nat.strong_induction_on generalizing p with
     | h m ih =>
       by_cases hm:m=0
       · exact fun a=>Submodule.subset_span (Set.mem_range.mpr ⟨(c,b,true,(⟨p,h.trans hm⟩:chit d),a),rfl⟩)
       obtain ⟨q,hq⟩:= (Elm.Pulses.nextFound p K).mpr (by omega); let f(j):= qK (dnL ((p,j,b),c));
       let F(i:Axis)(a:Pinor):scarG d:= ∑ j:Pinor, ∑ y:Multi d,qK (if AtNext i q y then gamma i j a • dnL ((y,j,b),c) else 0)
       have hx(a:Pinor): (∑ j:Pinor,gamma K j a • f j)∈T:=by
              have he(j:Pinor): (∑ y:Multi d,qK (if AtNext K q y then gamma K j a • dnL ((y,j,b),c) else 0))= gamma K j a • f j:=by
                   rw [Finset.sum_eq_single p,if_pos hq,map_smul]
                   intro y hm ht; rw [if_neg (fun h=> ht (echoUnique h hq)), map_zero]
                   simp
              have hF: F K a= ∑ j:Pinor, gamma K j a • f j:= Finset.sum_congr rfl fun i _=> he i
              have ht: qK (slashBar ((q,a,b),c))=0:=(Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span (Or.inr ⟨_,rfl⟩))
              unfold slashBar at ht; simp_rw [map_sum] at ht
              let I:= ∑ i∈ (Finset.univ.erase K), F i a
              change ∑ i:Axis,F i a=0 at ht; rw [← Finset.add_sum_erase _ (fun i=> F i a) (Finset.mem_univ K)] at ht; rw [← hF, eq_neg_of_add_eq_zero_left ht]; apply Submodule.neg_mem; apply Submodule.sum_mem T
              intro i hi; let hb:= (Finset.mem_erase.mp hi).1; refine Submodule.sum_mem T fun j _=> Submodule.sum_mem T fun t _=>?_ ; split_ifs; next he=>
                   rw [map_smul]; apply Submodule.smul_mem; apply ih (power t K) _ t rfl; rw [show power t K=power q K from by rw[he,update_of_ne hb.symm]]; rw [← h,hq,update_self]; omega
              rw [map_zero]; exact (spanned d).zero_mem
       intro a; have hp : f a=∑ j:Pinor, gamma K j a • ∑ k:Pinor,gamma K k j • f k:=by
            simp_rw [Finset.smul_sum,smul_smul]; rw [sum_comm]; simp_rw[← Finset.sum_smul]; simp_rw [show ∀ x:Pinor, (∑ j,gamma K j a* gamma K x j)=(1:Spike) x a from fun k=> (by rw [show (∑ j,gamma K j a * gamma K k j) = (gamma K * gamma K) k a from Finset.sum_congr rfl fun j _=> mul_comm ..,gamma_sq])]; simp [Matrix.one_apply,ite_smul]
       change f a∈_; rw[hp]; exact Submodule.sum_mem T fun i _=> Submodule.smul_mem T _ (hx i)
lemma radiant(d:ℕ):spanned d=⊤:=by
    refine eq_top_iff.mpr fun x _=>?_; obtain ⟨x,rfl⟩:= (slashEq d).mkQ_surjective x
    rw[← (thetaBasis _).sum_repr x,map_sum]; refine Submodule.sum_mem (spanned d) fun i _ =>?_ ; rw[map_smul]; apply Submodule.smul_mem; rcases i with ⟨⟨p,a,b⟩,c⟩|⟨⟨p,a,b⟩,c⟩; exact all_up p b c a; exact all_down p b c a
end YM.DawnS
#print axioms YM.DawnS.radiant
