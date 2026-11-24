import YM.QCD.Tide.Channel
import Mathlib.Analysis.Convex.Integral
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C] {n c f : Side} {F : ℕ} {β:ℝ}{S:StepData c f}
lemma bruM (hB:S.patch.Branches S.kernel su)(P:Grid c→Alg A)(hP:Stays P)(M:Alg A→L[ℝ] Alg B) (U Y:Grid f)(g: Grid c→Grid c)(hg:MeasurePreserving g (prior su c) (prior su c))(H:∀ V,S.density β Y (g V)=S.density β U V) : M (brook S β P Y)=brook S β (fun V=> M (P (g V))) U :=by
    rw [brook, ← M.integral_comp_comm (deltaPay hB P hP Y)]; let Q:=prior su c; let L(V:Grid c):= M (S.density β Y V • P V); change (∫ V,L V ∂Q)=_; have h':Integrable L Q:= M.integrable_comp (deltaPay hB P hP Y); have hi:= integral_map (φ:=g) (μ:=Q) hg.aemeasurable (f:=L) (by rw [show Q.map g=Q from hg.map_eq]; exact h'.aestronglyMeasurable); rw [show Q.map g=Q from hg.map_eq] at hi; rw [hi]; unfold L; simp_rw [H,map_smul]; rfl
-- Real linear lifts
noncomputable def muter (W:Alg A→ₛₗ[starRingEnd ℂ]Alg B) (h:Continuous W):Alg A→L[ℝ]Alg B where
    toFun:= W
    map_add':=W.map_add'
    map_smul':=fun r x=>by change W ((r:ℂ) • x)=_ ; rw [map_smulₛₗ]; change (starRingEnd ℂ) (r:ℂ) • W x=(r:ℂ) • W x; rw [show (starRingEnd ℂ) (r:ℂ)=_ from Complex.conj_ofReal _]
    cont:=h
lemma tiltH (R:Cells.Cut c)(x:Stud c F): let V:= tilt (A:=Modes c F) (RP.folds R F); let H:=muter V (tilt_cont _); ∀ U:Grid c, foldsT R x U=H (x (R.pullC su U)):=by intro a b c; rfl
lemma inS (X:Set (Site c))(x:Fields c F): let p:=LinearMap.range (pass (setDay X (F:=F))).toLinearMap; let h:=p.restrictScalars ℝ; inSlot X x ↔ x∈h:=by intro p h; exact ⟨fun ⟨i,r⟩=> ⟨i,r.symm⟩, fun ⟨i,r⟩=>⟨i,r.symm⟩⟩
lemma hold (hB:S.patch.Branches S.kernel su)(X:Set (Site c))(P:Stud c F)(hP:Stays P)(hp:Uses X P)(U:Grid f): inSlot X (brook S β P U):=by
     let T:=LinearMap.range (pass (setDay X (F:=F))).toLinearMap; let W:= T.restrictScalars ℝ; have he:IsClosed (W:Set (Fields c F)):=Submodule.closed_of_finiteDimensional T
     exact (inS X _).2 (W.convex.integral_mem he (ae_of_all _ fun _=> W.smul_mem _ ((inS X _).1 (hp.2 _))) (deltaPay hB P hP U))
lemma flowH (hB:S.patch.Branches S.kernel su)(P:Stud c F)(hP:Stays P)(hp: Neutral P)(U:Grid f)(g: Frame f): slots F (g∘ S.ratio.embed) (brook S β P (gauge g U))= brook S β P U:=by
    let T:= slots F (g ∘ S.ratio.embed); let Q: Fields c F→L[ℝ] Fields c F:= (T.toLinearMap.toContinuousLinearMap).restrictScalars ℝ
    change Q _= _; rw [bruM hB P hP Q U _ _ (prior_gauge (g∘S.ratio.embed)) (fun _=> S.covary hB g β _ _), show (fun V=> Q (P (gauge (g ∘ S.ratio.embed) V)))=P from funext fun _=> hp _ _]
-- enough sum support
variable [DecidableEq A] (u:C ↪ A) {M Q:Matrix A B ℂ}
lemma rowed (hh:∀ i, M (u i)= Q (u i)) (x:Dirac C):furnace M (pass u x)= furnace Q (pass u x):=by
    classical
    change adapter _ _ (winter A (pass u x))=adapter _ _ (winter A (pass u x)); rw [frosted]
    let U:=winter C x; refine AlgHom.congr_fun (ext_atoms (f:=(adapter M (Twist M)).comp (pass u)) (g:=(adapter Q (Twist Q)).comp (pass u)) ?_) U
    rintro (i|i)
    · change adapter _ _ (pass u (psi i))= adapter _ _ (pass u (psi i)); rw [pass_psi,adapt_psi,adapt_psi,hh]
    change adapter _ _ (pass u (bar i))=adapter _ _ (pass u (bar i)); rw [pass_bar,adapt_bar,adapt_bar]; simp [Twist,hh]
open scoped Classical in
lemma excite {D:Type*}[Fintype D](b:D↪B)(hh:∀ i j,M (u i) j≠0 → j∈Set.range b)(x:Dirac C): furnace M (pass u x)= pass b (adapter (M.submatrix u b) (Twist (M.submatrix u b)) (winter C x)) :=by -- needs Dec.C in signature
   change adapter M _ (winter A (pass u x))=_; rw [frosted]; refine AlgHom.congr_fun (ext_atoms (f:=(adapter M _).comp (pass u)) (g:=(pass b).comp (adapter (M.submatrix u b) _)) ?_) (winter C x)
   rintro (i|i)
   · change adapter _ _ (pass u (psi i))=pass b (adapter _ _ (psi i)); rw [pass_psi,adapt_psi,adapt_psi,map_sum]; let L:=univ.map b; symm
     refine Eq.trans ?_ (sum_subset (f:=fun j => M (u i) j • psi j) (subset_univ L) (fun a _ h=>?_))
     · unfold L; rw [sum_map]; apply sum_congr rfl; intro k _; rw [map_smul,pass_psi]; rfl
     have he : M (u i) a=0:= not_ne_iff.mp fun hv=> let ⟨z,hz⟩:= hh _ _ hv; h (mem_map.mpr ⟨z,mem_univ _,hz⟩); rw [he, zero_smul]
   change adapter _ _ (pass u (bar i))=pass b (adapter _ _ (bar i)); rw [pass_bar,adapt_bar,adapt_bar,map_sum]; let L:=univ.map b; symm
   refine Eq.trans ?_ (sum_subset (f:=fun j=> Twist M (u i) j • bar j) (subset_univ L) (fun a _ h=>?_))
   · unfold L; rw [sum_map]; apply sum_congr rfl; intro k _; rw [map_smul,pass_bar]; rfl
   have he : M (u i) a=0:= not_ne_iff.mp fun hv=>let ⟨z,hz⟩:=hh _ _ hv; h (mem_map.mpr ⟨z,mem_univ _,hz⟩); simp only [Twist,Matrix.transpose_apply,Matrix.conjTranspose_apply,he,star_zero,zero_smul]
end YM.QCD.Tide
