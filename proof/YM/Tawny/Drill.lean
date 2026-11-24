import YM.Tawny.Dree
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tawny
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a:Flavor 6)
open Poised.Display Poised.Stative Module Finset Oriole Pane TensorProduct Revolve UV.Free KeysP BendR Clifford
namespace Cast
open StressFlux.Offer (acts marks Vc)
namespace Drill
open Matrix TableT Carnal Rays Perla Zinc
open scoped Kronecker
variable (v:Axis→ℂ)(b c: Hue)(M:Spike)(f g: Pinor →ℂ)
noncomputable def sectionV (v:Axis→ℂ): Spike:=∑ i: Axis,v i • gamma i
abbrev SlashV(v:Axis→ℂ)(f:Pinor→ℂ):Prop := ∀ i:Pinor,∑ j:Pinor,(sectionV v i j)*f j=0 -- col file
noncomputable def pay (p:Multi d)(v:Axis→ℂ):ℂ:=∏ i:Axis,(v i)^power p i
lemma cost_next (p q:Multi d)(i:Axis)(h:AtNext i p q): pay q v= v i*pay p v:=by
     unfold pay; rw [h, ← mul_prod_erase _ _ (mem_univ i), ← mul_prod_erase _ (fun i=>v i ^ power p i) (mem_univ i),update_self,pow_succ',mul_assoc]; congr 2; refine Finset.prod_congr rfl fun j hj=>?_ ; rw [Function.update_of_ne (mem_erase.mp hj).1]
private lemma plus1 (f:Axis→ℕ) (i:Axis) : order (update f i (f i+1))=order f+1:=by unfold order; rw [show update f i (f i+1)=fun x=>f x + if i=x then 1 else 0 from (funext fun j=>by by_cases h:i=j; subst i; simp; simp [Ne.symm h,h]),sum_add_distrib]; simp
lemma next_iff (p:Multi d)(i:Axis): (∃ q,AtNext i p q)↔ order (power p)<d:=by
     let f:= update (power p) i (power p i+1); constructor
     · rintro ⟨q,h⟩; have hp:q.val=q.val:=rfl; have he: order (power q) ≤d:= q.property; rw [show power q=_ from h, plus1] at he; exact he
     intro h; have he:order f ≤d:=by rw [show order f= _ from plus1 ..]; exact h
     have hv(j:Axis):f j < d+1:= Nat.lt_succ_of_le (le_trans (b:=order f) (Finset.single_le_sum (f:=f) (fun _ _=>Nat.zero_le _) (mem_univ _)) he); exact ⟨⟨fun j=>⟨_,hv j⟩,he⟩,rfl⟩
lemma base_price(d:ℕ) : pay (0:Multi d) v=1:=by simp [pay, show ∀ i, power (0:Multi d) i=0 from fun _=>rfl]
lemma lens_P(q:Multi d)(h:q≠0):pay q (0:Axis→ℂ)=0:=by
   unfold pay; obtain ⟨i,hi⟩:∃ i,power q i≠0:=by by_contra! he; exact h ((ground_iff q).mp (by simp [order,he]))
   exact Finset.prod_eq_zero (mem_univ i) (zero_pow hi)
-- two-leg form.B.Full projection evaluating free only.G.θ choose p for eigen ν.
local notation "A"=>Pairs (SpinMode d)
local notation "K"=>ExteriorAlgebra ℂ (Seed A ⧸ (slashEq d))
local notation "Q"=>Dirac Unit
local notation "Ψ" => Seed (Pairs Unit)
local notation "P" => thetaBasis (Pairs Unit)
local notation "u"=> ()
noncomputable def drow (a:Flavor 6)(c:Hue)(g:Pinor→ℂ) (p:SpinMode d):ℂ:=if p.2=a∧p.1.2.2=c∧ p.1.1=0 then g p.1.2.1 else 0
noncomputable def dcol (v:Axis→ℂ)(a:Flavor 6)(c:Hue)(f:Pinor→ℂ)(p:SpinMode d):ℂ:= if p.2=a∧p.1.2.2=c then pay p.1.1 v * f p.1.2.1 else 0
noncomputable def throne : Seed A →ₗ[ℂ] Ψ:= (thetaBasis A).constr ℂ (Sum.elim (fun i:SpinMode d=> dcol v a b f i • P (Sum.inl ())) (fun i:SpinMode d=>drow a c g i • P (Sum.inr ()))) -- variable b shadows Flavor b ensure b∈Hue
local notation "L"=> throne a v b c f g
variable (p:SpinMode d)
lemma C_th : L (thetaBasis A (Sum.inl p)) = dcol v a b f p • P (Sum.inl ()):=by rw[throne,Module.Basis.constr_basis]; rfl
lemma B_th : L (thetaBasis A (Sum.inr p))=drow a c g p • P (Sum.inr ()):=by rw[throne,Module.Basis.constr_basis]; rfl
lemma floor_hz(p:Multi d)(i:Axis)(q:Multi d)(h:AtNext i p q): q≠0:= Fountain.lift_m i _ _ h
lemma terrace : L (slashBar p)=0:=by
    unfold slashBar; simp_rw [map_sum]; refine sum_eq_zero (fun i _=> sum_eq_zero (fun k _=> sum_eq_zero fun q _=>?_ )); split <;> rename_i h
    · rw [_root_.map_smul, B_th]; simp [drow, floor_hz _ _ _ h]
    exact map_zero _
variable (h:SlashV v f)
include h
lemma metricZ (i:Pinor): ∑ t:Axis,∑ j:Pinor,v t *gamma t i j*f j=0:=by
      have ht:=h i; unfold sectionV at ht; rw [sum_comm]; simp only [Matrix.sum_apply, Matrix.smul_apply,smul_eq_mul,sum_mul] at ht; exact ht
lemma lawns : L (slashCol p)=0:=by
    by_cases hY: order (power p.1.1)< d
    · choose w hw using fun i=> (next_iff _ i).2 hY; have hP(i:Axis)(q:Multi d):AtNext i p.1.1 q ↔ q=w i:=⟨fun h=> via_eq q _ (h.trans (hw i).symm),fun h=>h.symm▸ hw i⟩
      simp only [slashCol,hP,ite_smul,sum_ite_eq',mem_univ,if_true,sum_ite_eq,map_sum,map_smul,C_th,dcol]; by_cases hv:p.2=a ∧ p.1.2.2=b
      · simp only [if_pos hv, fun i=> cost_next v _ _ i (hw i)]; simp_rw[smul_smul]; rw [← show (pay p.1.1 v* ∑ t:Axis,∑ j:Pinor, v t*gamma t p.1.2.1 j*f j) • P (Sum.inl u)=0 from (by rw[metricZ v f h,mul_zero,zero_smul]),Finset.mul_sum,sum_smul]; apply sum_congr rfl; intro k _; rw [Finset.mul_sum,sum_smul]; apply sum_congr rfl; intro i _; congr 1; ring
      simp [hv]
    have ht(i:Axis)(q: Multi d): ¬AtNext i p.1.1 q:= fun z=> hY ((next_iff _ i).mp ⟨_,z⟩); simp_rw[slashCol,if_neg (ht _ _),sum_const_zero]; exact map_zero _
noncomputable def goldH: (Seed A ⧸ (slashEq d)) →ₗ[ℂ] Ψ:= (slashEq d).liftQ (throne a v b c f g) (Submodule.span_le.mpr fun x hx=>by rcases hx with h'|h' <;> rcases h' with ⟨i,rfl⟩; exact (lawns a v b c f g i h); exact terrace ..) -- h explicit used include but unused syntax in type of def?
variable (X:Maxwell.TaylorTower su)
noncomputable def hear : Maxwell.WickPol su ⊗[ℂ] K →ₗ[ℂ] Q:=(TensorProduct.lid ℂ Q).toLinearMap.comp (TensorProduct.map (Maxwell.probe X).toLinearMap (ExteriorAlgebra.map (goldH a v b c f g h)).toLinearMap)
-- liaises
lemma hears (A':GPol)(Y:SpinPol d): let S:=ExteriorAlgebra.map (L); hear a v b c f g h X (reduceEq (A' ⊗ₜ[ℂ] Y)) = Labels.read (Perla.Fore.lexY X) A' • S Y:=by
     intro S; unfold hear reduceEq; rw [LinearMap.comp_apply,TensorProduct.map_tmul,TensorProduct.map_tmul,LinearEquiv.coe_coe,TensorProduct.lid_tmul]; simp only [AlgHom.toLinearMap_apply,Maxwell.jet_value]; congr 1; rw [← AlgHom.comp_apply,ExteriorAlgebra.map_comp_map]; congr 2
end Drill
end Cast
end YM.Massive.Tawny
#print axioms YM.Massive.Tawny.Cast.Drill.hears
