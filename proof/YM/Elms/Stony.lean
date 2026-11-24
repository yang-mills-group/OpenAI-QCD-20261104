import YM.Elms.Niche
/-! # Bare link gradient.Beamed geometry explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable {n:Side}(U:Grid n)(P : Regulator n 6)
local notation "M" => Mat
local notation "N" => Lat.Fields n 6
section Deriv
set_option maxRecDepth 2300 in
set_option maxHeartbeats 600000 in
noncomputable def spansLm (x y:Site n)(a:Axis) : M→ₗ[ℝ] N:=by
      refine { toFun := fun t=> spans 6 a t x y, map_add':=fun i j=>?_, map_smul':=fun c j=>?_ }
      · simp only [RP.spans,RP.down,RP.up,star_add, ← touch_add,Matrix.mul_add,RP.copies_add,linkB_add]; abel
      · have hu:=blux_s j (↑c); unfold RP.spans RP.up RP.down; simp_rw [copies_mul]; rw [star_smul,star_trivial]; change - linkB x y (mL (Lat.lo a)* blux (c • j))-linkB y x (mL (hi a)* blux (c • star j))=(c:ℝ) • (-linkB x y _-linkB y x _); rw [tensorScale c j,tensorScale c (star j),blux_s,blux_s,Matrix.mul_smul,Matrix.mul_smul,linkB_smul,linkB_smul]; rw [smul_sub,smul_neg]; rfl -- beware R module compat
 where
    tensorScale (c:ℝ) (x:M): c • x=(c:ℂ) • x:=by ext i j; rfl
lemma spansL (x y:Site n)(a:Axis) : ∃ L: M →L[ℝ] N, ⇑L=(fun t:M => spans 6 a t x y):=by
   let L:=spansLm x y a; let H:=L.toContinuousLinearMap; refine ⟨H,?_⟩; funext i; change L i=_; rfl
variable (e : Edge (Site n)) (A:su.Color)
local notation "φ" => thread P.t
abbrev cob(A:su.Color):Mat:= su.colorMat A
noncomputable def pathDeriv (e:Edge (Site n))(A:su.Color): M:= cob A * thread P.t U e.2 e.1 -- order. su.colorMat types ambiguity.Matrix PMt
noncomputable def ΔZ (e:Edge (Site n))(A:su.Color): N:= spans 6 e.2 (pathDeriv U P e A) e.1 (e.1+step e.2)
lemma occurs : HasDerivAt (fun t:ℝ=>Grass.form (P.D (turnLink e A t U))) (ΔZ U P e A) 0:=by
   let f(x:Site n)(i:Axis)(t:ℝ):=spans 6 i (thread P.t (turnLink e A t U) i x) x (x+step i); have hz(x i): HasDerivAt (f x i) (if (x,i)=e then ΔZ U P e A else 0) 0:=by
       dsimp only [f]; split
       next h=> subst e; obtain ⟨L,hL⟩:=spansL x (x+step i) i; simp only [thread,Push.Mark.turn_here, Lat.colour_mul]
                have ht : HasDerivAt (fun t:ℝ=>su.mat (su.lieExp (t • A))) (su.colorMat A) 0:= by
                   simp only [su.mat_lieExp, map_smul]; simpa using! hasDerivAt_exp_smul_const (su.colorMat A) (0:ℝ)
                have hs:HasDerivAt (fun t:ℝ=>colour (su.lieExp (t • A))) (cob A) 0:= ht
                have hl(y): spans 6 i y x (x+step i)=L y:=(congr_fun hL y).symm; simp only [hl]; apply HasDerivAt.congr_deriv (L.hasFDerivAt.comp_hasDerivAt _ ((hs.mul_const (colour (U (x,i)))).const_smul (seam P.t x i))); change L _ = spans 6 i (cob A * (seam P.t x i • colour _)) _ _; rw [hl,Matrix.mul_smul]
       next h=> simp_rw [thread,turn_away U A _ h]; exact hasDerivAt_const ..
   simp only [formOg]; have he:= HasDerivAt.add (hasDerivAt_const (0:ℝ) (Grass.form (extra P) +∑ x:Site n, bank (0+4) 6 x)) (HasDerivAt.fun_sum (u:=Finset.univ) fun x _=> HasDerivAt.fun_sum (u:=Finset.univ) fun i _=>hz x i); refine HasDerivAt.congr_deriv he ?_; rcases e with ⟨x,i⟩; rw [zero_add, sum_eq_single x]; simp; intro j _ hh; simp [hh]; simp
set_option maxRecDepth 3200 in
set_option maxHeartbeats 450000 in
lemma grazes : HasDerivAt (fun t:ℝ=>gauss (P.D (turnLink e A t U))) (gauss (P.D U)*ΔZ U P e A) 0:=by
   let f(t:ℝ):= Grass.form (P.D (turnLink e A t U)); let z:=Grass.form (P.D U); let F(t:ℝ):= f t-z; have hF:F 0=0:=by simp [F,z,f]
   unfold gauss; have he : HasFDerivAt NormedSpace.exp (1:N→L[ℝ] N) (F 0):=hF.symm ▸ hasFDerivAt_exp_zero; have hx:HasDerivAt F (ΔZ U P e A) 0:=(occurs U P e A).sub_const _; have h:= (he.comp_hasDerivAt _ hx).const_mul (NormedSpace.exp z)
   letI : NormedAlgebra ℚ (Lat.Fields n 6):= .restrictScalars ℚ ℝ _
   rw [show (fun t=> NormedSpace.exp (f t))=(fun t=>NormedSpace.exp z*NormedSpace.exp (F t)) from funext fun t=> by rw [← NormedSpace.exp_add_of_commute ((form_plus (P.D U)).central (F t)).symm]; unfold F z; congr 1; abel] -- z in simp
   exact h
   -- commute: Exp.S analytic.deriv.
lemma Δ_cash (h:2≤n.val): HasDerivAt (fun t:ℝ=> P.density (turnLink e A t U)) (P.density U * ΔZ U P e A - (↑(P.β*inner ℝ A (Push.Mark.field U e)):ℂ) • P.density U) 0:=by
   let B:=fun U:Grid n=> (bare P.β U:ℂ); have hb : HasDerivAt (fun t:ℝ=> B (turnLink e A t U)) (- (↑(P.β*inner ℝ A (Push.Mark.field U e)):ℂ)* B U) 0:=by
       refine (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (((Push.Mark.field_deriv U e h A).const_mul (-P.β)).exp)).congr_deriv ?_; simp [B,bare,Complex.ofReal_mul]; ring
   refine HasDerivAt.congr_deriv (hb.smul (grazes U P e A)) ?_; simp only [Regulator.density_apply,turn_zero,_root_.smul_mul_assoc,smul_smul]; rw [← neg_mul_eq_neg_mul,neg_smul]; abel
lemma exactZ (Y:Insertion n 6)(he: ∀ (U:Grid n) (t:ℝ), Y (turnLink e A t U)= Y U)(hn:2≤n.val):
    ∫ U:Grid n, ber _ ((P.density U * ΔZ U P e A - ((↑(P.β*inner ℝ A (Push.Mark.field U e))):ℂ) • P.density U)*Y U) ∂prior su n=0:=by
    let X:=fun U:Grid n=>ber _ (P.density U*Y U); let Z U:=ber _ ((P.density U*ΔZ U P e A- ((↑(P.β*inner ℝ A (Push.Mark.field U e))):ℂ) • P.density U)*Y U); have hx:Continuous X:= by unfold X; fun_prop
    have hp: Continuous (fun U:Grid n=> pathDeriv U P e A) :=by unfold pathDeriv thread; fun_prop
    have hq:= (Push.Mark.continuous_field su e); have hz:Continuous Z:=by unfold Z ΔZ; fun_prop
    have hf(U:Grid n):HasDerivAt (fun t:ℝ=> X (turnLink e A t U)) (Z U) 0:= by
       unfold X; simp_rw [he]; exact ((ber _).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt _ ((Δ_cash U P e A hn).mul_const (Y U)) -- output HasDeriv
    simpa only [mul_one] using integral_variation e A hx hz hf (Push.Mark.cont_envelope (continuous_const (y:=(1:ℂ)))) (fun _ _=>rfl)
end Deriv
end Arbor
end SparK
end YM.Massive.Elm
