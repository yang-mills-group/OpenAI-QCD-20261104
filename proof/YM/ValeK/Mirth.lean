import YM.ValeK.Book
import YM.DawnS.Dwelling
import YM.Alum.Sip

set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix ComplexOrder
namespace Vale
variable {d:ℕ}(sym:UV.RawSym)(H:Laurel d)
local notation "A"=> Stokes d
local notation "w" => fun _ : Fin 2 =>d
local notation "B"=> basis timeAxis
local notation "X"=> sym.adj d timeAxis
noncomputable def ΦGram(x:E4)(i j : Stokes d): ℂ:= UV.Free.wick (fun _ : Fin 2=>d) (points ![(0:E4),x]) ![(opposite sym timeAxis (H.F i)).mark,(H.F j).mark]
private lemma base_rankH {V Y:Type} [AddCommGroup V][Module ℂ V][AddCommGroup Y][Module ℂ Y]{I:Type}[Fintype I] (B0:Module.Basis I ℂ V)(f:I→Y)(A0:Y→ₗ[ℂ] V)(h:∀ i,B0 i=A0 (f i))(c:I→ℂ)(hc:c≠0): A0 (∑ i,c i • f i)≠0:=by
     intro hv; rw[map_sum] at hv; simp_rw[map_smul,← h] at hv; exact hc (funext fun i=> Fintype.linearIndependent_iff.mp B0.linearIndependent c hv i)
lemma paidGram(c:A → ℂ)(hc:c≠0): 0<(∑ i:A,∑ j:A, star (c i)*ΦGram sym H (basis timeAxis) i j * c j):=by
     let G:= fun p:A=> c p • (H.F p).mark; let g:=∑ i,G i
     have hg: projection (∑ i,G i)≠0:=base_rankH (V:=Symbol d) (Y:=Label d) H.B (fun i=>(H.F i).mark) projection H.h c hc
     have he:= YM.DawnS.detecting 1 zero_lt_one g sym hg
     simp only [one_smul] at he
     let K:= points ![0,B]; let Q:= wick w K; let f(i):=(H.F i).mark
     have hx : (∑ i,∑ j, star (c i)*ΦGram sym H B i j*c j)=Q ![X (∑ i,G i),∑ i,G i]:=by
          have h₁(a b: Label d): update ![a,0] 1 b=![a,b]:=by funext i; fin_cases i <;> simp
          have h₂(a b: Label d): update ![0,b] 0 a=![a,b]:=by funext i; fin_cases i<;>simp
          rw[map_sum,← h₂,Q.map_update_sum]; refine sum_congr rfl fun i _=>?_ ; rw[h₂,← h₁,Q.map_update_sum]; refine sum_congr rfl fun j _=>?_ ; rw[h₁]; change _=Q ![X (c i•f i),c j • f j]; rw [map_smulₛₗ,←h₂,Q.map_update_smul,h₂,←h₁,Q.map_update_smul,h₁]; change (star _ * ΦGram sym H B i j)* (c j)=star (c i)*(c j*ΦGram sym H B i j); ring
     rw[hx]; exact he
noncomputable def Γ (S: Stokes d → Stokes d →ℂ): (Stokes d→ℂ)→L[ℂ](Stokes d→ℂ):=(Matrix.mulVecLin (Matrix.of S)).toContinuousLinearMap
lemma worth : Injective (Γ (ΦGram sym H B)) := fun x y he=>by
   apply sub_eq_zero.mp; by_contra hp; let g:A→ℂ:=x-y; let f:= ΦGram sym H B
   have hb:Γ (ΦGram sym H B) g=0:=by rw[show g=x-y from rfl,map_sub,he,sub_self]
   apply (paidGram sym H g hp).ne'; apply Finset.sum_eq_zero; intro i _; have ht:∑ j,f i j*g j=0:= congr_fun hb i; change ∑ j,star (g i)*f i j*g j=_; simp_rw [mul_assoc,←Finset.mul_sum,ht,mul_zero]
-- quantitative by direct operator UB; scaled ℓ∞. directions map turned.G.
noncomputable def nearG (ε:ℝ)(f: Stokes d→Stokes d→ℂ):Prop:=∀ i j, ‖f i j- ΦGram sym H B i j‖ ≤ ε
lemma herd : ∃ ε J:ℝ, 0< ε ∧ 0 ≤ J ∧ ∀ f: A→A→ℂ, nearG sym H ε f→∀ x:A→ℂ, ‖x‖ ≤ J * ‖Γ f x‖:=by
     let f:= ΦGram sym H B; let A₀:=Γ f; let φ:= LinearEquiv.ofBijective (A₀.toLinearMap) ⟨worth sym H, (LinearMap.injective_iff_surjective).mp (worth sym H)⟩; let LK:= φ.symm.toLinearMap.toContinuousLinearMap -- L notation.H.
     let Q:=‖LK‖+1; let n:= Fintype.card (Stokes d);
     -- set epsilon = ...
     have ht:0<Q:=by unfold Q; positivity
     let e:= 1/(2*Q*((n:ℝ)+1)); have he:0<e:=by unfold e; positivity
     refine ⟨e,2*Q,he,by positivity,fun g hg x=>?_⟩; let b:=Γ (d:=d) g x; let a:=A₀ x; have hx: LK a=x:=φ.symm_apply_apply x
     have hP: ‖a-b‖ ≤ (n:ℝ)*(e*‖x‖):=by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>?_ ; change ‖(∑ j,f i j*x j)-(∑ j,g i j*x j)‖ ≤ _; rw[← sum_sub_distrib]; simp_rw[← sub_mul]; apply (norm_sum_le ..).trans; have h(i' : Stokes d): ‖(f i i'-g i i')*x i'‖ ≤e*‖x‖:=by rw[norm_mul,norm_sub_rev]; exact mul_le_mul (hg i i') (norm_le_pi_norm x i') (norm_nonneg _) he.le
          apply le_trans (sum_le_sum fun i _=>h i); simp only [sum_const,nsmul_eq_mul,card_univ,n,le_refl]
     have hb:‖x‖ ≤ Q* ‖a‖:=calc
          _=‖LK a‖:= (congr_arg _ hx).symm
          _≤Q*‖a‖:= (LK.le_opNorm a).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (norm_nonneg _))
     have hv: Q*((n:ℝ)*e) ≤1/2:=by
          calc _≤Q*(((n:ℝ)+1)*e):=by gcongr; linarith
               _=_:=by unfold e; field_simp
     have ha: ‖x‖ ≤ Q*‖b‖+1/2*‖x‖:=calc
          _ ≤ Q*((n:ℝ)*(e*‖x‖)+‖b‖):= hb.trans (mul_le_mul_of_nonneg_left (show ‖a‖ ≤ _ from (congr_arg _ (sub_add_cancel a b)).symm.le.trans ((norm_add_le ..).trans (add_le_add_left hP _))) ht.le)
          _ ≤ _:= (show Q*(_+‖b‖)=Q*‖b‖+Q*((n:ℝ)*e)*‖x‖ by ring).trans_le (add_le_add_right (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) _)
     change ‖x‖≤ 2*Q*‖b‖; linarith
end Vale
end YM.Intag
