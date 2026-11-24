import YM.Kly.Size
import YM.Work.B08
set_option autoImplicit false
set_option maxHeartbeats 610000
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis
open OS (Cross)
open Fields (pointMoment distinct)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder
open MassiveTwoEstimates Spinor Spinor.Lift
variable {F:Fields} {S:F.Kernel}{V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(R:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){X:Bases F}{M':Momentum F}(U:X.Content C M')
variable {n:ℕ}(x:Points n)(v:Fin n→F.W)
local notation "t₀"=>timeAxis
local notation "Ω"=> P.algebra
variable (A:V.VacuumOp →L[ℂ]ℂ) (X': P.algebra→⋆ₐ[ℂ]ℂ)(hX:Continuous X')
local notation "G"=> bloom P H X'
variable (l:Fin n→Future F t₀)(u:Fin n→ℂ)
noncomputable def punch := ∑ i:Fin n, u i • Kly.X P (l i)
noncomputable def fiat :Ω:=∑ i:Fin n,∑ j:Fin n,(star (u i)*u j) • M P _ (twoSides (l i).property (l j).property)
include H Y E
lemma helpX : (fiat P l u).val = (punch P l u).adjoint.comp (punch P l u):=by
      let f (i:Fin n):= Kly.X P (l i); let b(i j:Fin n):= M P _ (twoSides (l i).property (l j).property)
      let L :=P.algebra.subtype.toAlgHom.toLinearMap; have he(i j):L (b i j)=(f i).adjoint.comp (f j):= slim P (E.reflected _) Y H (l i) (l j) -- order
      change L (∑ i,∑ j,(star (u i)*u j) • b i j) = (∑ i,u i • f i).adjoint.comp (∑ i,u i • f i)
      ext1 x; simp only [map_sum, map_smul,map_smulₛₗ,he,ContinuousLinearMap.comp_apply,sum_apply,smul_apply,Finset.smul_sum,mul_smul]; rw[Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; exact smul_comm _ _ _
omit Y E
lemma lab : X' (fiat P l u)= Fields.gram (G) t₀ (fun i=>(l i).val) u:=by
      unfold fiat Fields.gram; simp_rw [map_sum,map_smul]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [← bless P H X',smul_eq_mul]; ring
include E Y
lemma realPr : 0 ≤ Fields.gram (G) t₀ (fun i=>(l i).val) u:=by
      rw [←lab]; exact Work.B08.char_nonneg P.algebra isClosed_closure X' _ (helpX P H Y E l u ▸ ContinuousLinearMap.isPositive_adjoint_comp_self _)
omit E H Y
variable (d:ℝ≥0)(v:Cluster F)(hs:Slab t₀ d v)
include hs
lemma sally (p:Future F t₀) : Kly.X P (entering hs p) = (P.place d v).comp (Kly.X P p):=by
      obtain ⟨e,he⟩:= future_reach p; rw [standing P (entering hs p) (connects hs he),standing P p he]; change (P.place (d+e) (linked t₀ d v p.val)).comp _ = _; rw [P.concatenate hs he]; rfl
omit hs
lemma audience {D Y:Type}[NormedAddCommGroup D][InnerProductSpace ℂ D][CompleteSpace D][NormedAddCommGroup Y][InnerProductSpace ℂ Y][CompleteSpace Y] (A B:D→L[ℂ]Y) (r:ℝ)(hr:0 ≤r)(hx:∀ x,‖B x‖ ≤r*‖A x‖): (((r^2:ℝ):ℂ) • A.adjoint.comp A-B.adjoint.comp B).IsPositive:=by
     let T:= ((r^2:ℝ):ℂ) • A.adjoint.comp A - B.adjoint.comp B; have ht(x:D): inner ℂ x (T x) = (↑(r^2*‖A x‖^2-‖B x‖^2):ℂ):=by
           unfold T; simp only[sub_apply,smul_apply,inner_sub_right,inner_smul_right,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K, Complex.ofReal_sub,Complex.ofReal_mul, Complex.ofReal_pow]; rfl
     apply (ContinuousLinearMap.isPositive_iff_complex T).2; intro x; rw [← inner_conj_symm,ht]; let s:=r^2*‖A x‖^2-‖B x‖^2; rw [show starRingEnd ℂ (s:ℂ)=(s:ℂ) from Complex.conj_ofReal _]; refine ⟨rfl,?_⟩; apply (sub_nonneg.mpr : _ → 0 ≤ r^2*‖A x‖^2-‖B x‖^2); have he:= pow_le_pow_left₀ (norm_nonneg _) (hx x) 2; rwa [mul_pow] at he
include H Y E hs
variable (z:ℝ)(hz:0 ≤ z)(hf:‖P.place d v‖ ≤ z)
include hz hf
lemma payQ : Fields.gram (G) t₀ (fun i=>(entering hs (l i)).val) u ≤ (↑(z^2):ℂ)*Fields.gram (G) t₀ (fun i=>(l i).val) u:=by
      let m(i:Fin n):= entering hs (l i); set U:= punch P l u; let W:=punch P m u; have hv(x): W x=P.place d v (U x):=by
             unfold W U punch; simp only [_root_.sum_apply,map_sum,_root_.smul_apply,map_smul]; apply Finset.sum_congr rfl; intro i _; unfold m; rw [sally]; rfl
      let L:ℂ:= (↑(z^2):ℂ); let A:= L • fiat P l u-fiat P m u; have h:A.val.IsPositive:=by
                change (L • (fiat P l u).val - (fiat P m u).val).IsPositive; rw [helpX P H Y E,helpX P H Y E]; exact audience U W z hz (fun x=> by rw [hv]; exact ((P.place _ _).le_opNorm (U x)).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg _)))
      apply sub_nonneg.mp; have ht:= Work.B08.char_nonneg P.algebra isClosed_closure X' A h; change 0 ≤ L*_ - _; unfold A at ht; rw [map_sub,show X' (L • fiat P l u)=L • X' (fiat P l u) from X'.toAlgHom.toLinearMap.map_smul L _,lab,lab] at ht; exact ht
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.payQ
#print axioms YM.Massive.Bridge.Kly.realPr
