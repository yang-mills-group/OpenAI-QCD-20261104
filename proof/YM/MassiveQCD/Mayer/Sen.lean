import YM.MassiveQCD.Mayer.Core
/-! # Dyadic kernel tilt costs once per Lie weight package
 Uses the point seminorm only to obtain LAMBDA prices, not asserting a radius of log series
 at every V (use mask cuts). `Gated` doesn't assume any analyticity in λ over bad outputs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew.Phased
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.Frobenius
open Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint
variable {c:Side}{N:ℕ}{o:Site c}{B:Support c}{t q a r:ℝ}{k n:ℕ}
local notation "Z"=>EvenA c N
local notation "Q"=>Sen (N:=N) o t
open MassiveQCD.Analysis.Many
open Next.Foundations
variable {V:Config su c}{f g:Grid c→EvenA c N}{p:BudgetPoint}{D:Directions su c→Prop}
abbrev est (D:Directions su c→Prop)(o:Site c)(t r:ℝ)(k:ℕ)(f:Grid c→ EvenA c N) (V: Grid c):=∀ l:List (Directions su c),l.length≤ k → (∀ v∈l, D v) → Sen o t (leftDerivs f l V) ≤ r
-- permit hB arbitrary scales but here consume t budget only when purchasing diverging mask outputs.
lemma nthBudget {A:Directions su c} (hz:D A) (hp:n < k) (hf:Chart k f V) (hh: est D o t r k f V) : Chart n (leftDerivs f [A]) V∧ est D o t r n (leftDerivs f [A]) V:=by
    refine ⟨leftDerivs_chart _ _ (hf.of_le (Nat.cast_le.mpr (by simp; omega))),fun i hi hx=>?_⟩; rw [← Work.G07.left_append]; apply hh _ (by simp; omega) ; intro v hv; rcases List.mem_append.mp hv with hv|hv; exact hx _ hv; simpa only [List.mem_singleton.mp hv] using hz
-- neg sign order not identity converse
lemma antiP (t:ℝ)(o:Site c)(hx:Chart k f V)(w:List (Directions su c))(hp:w.length≤k): Sen o t (leftDerivs (-f) w V)=Sen o t (leftDerivs f w V):= by
     let K:= - ContinuousLinearMap.id ℝ (EvenA c N); rw [show -f=K ∘ f from rfl,left_linear K w hx hp]; change Sen o t (-(leftDerivs f w V))=_; rw [← measures,map_neg,norm_neg,measures]
noncomputable def seedInv (k:ℕ):ℕ→ℝ
 | 0=>2
 | n+1=>2+ (2^k)*(2^k)*(seedInv k n)^2
lemma seedInv_grant (k n:ℕ):2 ≤ seedInv k n:=by cases n with | zero=> exact le_rfl | succ n=> rw [seedInv]; exact le_add_of_nonneg_right (by positivity)
lemma seedInv_pos (k n:ℕ):0≤ seedInv k n:=by linarith [seedInv_grant k n]
local notation "U"=> sideH ∘ f
-- estimates use v≤1/2
variable (hp:t≥1)(h:Chart k f V)(hh: est D o t a k f V)(hc:a≤1/2)
include h hh hc hp
omit h in
private lemma priceV : Q (f V) ≤ a ∧ 0≤a ∧ 0<t∧ ‖f V‖<1:=by
    have he:Q (f V) ≤ a:=hh [] (by simp) (by simp); exact ⟨he,(norm_nonneg _).trans he,zero_lt_one.trans_le hp,((pass_high _ hp (o:=o)).trans (he.trans hc)).trans_lt (by norm_num)⟩
set_option maxHeartbeats 420000 in
lemma tear (hn:n≤k): est D o t (seedInv k n) n (sideH ∘ f) V:=by
    obtain ⟨hD,h₀,hV,hx⟩:=priceV hp hh hc -- order; edit possible
    intro i hi hz
    have hI:=shallow h hx
    have he:Q ((U) V) ≤2:= subGeom (f V) hp (hD.trans hc)
    induction n generalizing i with
    | zero=> cases i with
       | nil=> exact he
       | cons i l=>simp at hi
    | succ n ih=>
       cases i using List.reverseRecOn with
       | nil=> exact he.trans (seedInv_grant k (n+1))
       | append_singleton l w =>
          have hl: l.length≤ n:=by simpa using hi
          let s':=U; let q:=s'*s'; have hs : Chart n s' V:= hI.2.of_le (Nat.cast_le.mpr (n.le_succ.trans hn))
          let Z' := seedInv k n; have hZ:0 ≤ Z':=seedInv_pos ..
          have hℓ:Chart 1 f V:= h.of_le (Nat.cast_le.mpr (by omega))
          let Y:= leftDerivs f [w]; have hv:=nearlog w hℓ hx; have he : leftDerivs s' [w] ∘ increment V =ᶠ[𝓝 0] (-(q*Y)) ∘ increment V:= hv.mono (fun i h=>h.2) -- defeq
          obtain ⟨hY,hp'⟩:= nthBudget (hz w (by simp)) hn h hh (A:=w)
          let y:= 2^k*(Z'*Z'); have hr:0 ≤ y:=by unfold y; positivity
          have hy: est D o t y n q V:=fun i hi hx=> (left_mul_tax (o:=o) hV.le hs hs (ih (n.le_succ.trans hn)) (ih (n.le_succ.trans hn)) i hi hx).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (mul_nonneg hZ hZ))
          rw [Work.G07.left_append,left_congr _ V he,antiP _ _ ((hs.mul hs).mul hY) l hl]
          apply (left_mul_tax hV.le (hs.mul hs) hY hy hp' l hl (fun i hi=> hz _ (by simp [hi]))).trans
          apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hl.trans (n.le_succ.trans hn))) (by positivity : 0 ≤ y*a)).trans; unfold y seedInv; nlinarith only [mul_le_mul_of_nonneg_left (show a≤1 by linarith) (sq_nonneg ((2:ℝ)^k*Z'))] -- seed delta
noncomputable def logFee (k:ℕ):ℝ:=2+(2^k)*(seedInv k k)
omit h hh hc hp in
lemma logFee_post (k:ℕ):2 ≤logFee k:=le_add_of_nonneg_right (mul_nonneg (by positivity) (seedInv_pos k k))
lemma stampLog : est D o t (logFee k*a) k (logM ∘ f) V:=by
    obtain ⟨hD,h₀,hV,hx⟩:=priceV hp hh hc; obtain ⟨hi,hI⟩:=shallow h hx
    intro i hi hz; cases i using List.reverseRecOn with
    | nil=> exact (subRoll (f V) hp (hD.trans hc)).trans ((mul_le_mul (logFee_post k) hD (norm_nonneg _) ((by norm_num : (0:ℝ)≤2).trans (logFee_post k))))
    | append_singleton l w=>
       have hl : l.length < k:= by simpa using hi
       obtain ⟨he,hr⟩:= nthBudget (hz w (by simp)) hl h hh
       let K := U; have hK : Chart l.length K V:= hI.of_le (Nat.cast_le.mpr hl.le)
       have hv : Chart 1 f V:= h.of_le (Nat.cast_le.mpr (by omega))
       have he' : leftDerivs (logM ∘ f) [w] ∘ increment V =ᶠ[𝓝 0] ((sideH ∘ f) * (leftDerivs f [w])) ∘ increment V:= (nearlog w hv hx).mono fun _ h=>h.1
       rw [Work.G07.left_append,left_congr l V he']; apply (left_mul_tax hV.le hK he (fun i hi h=> tear hp ‹Chart k f V› hh hc (le_refl k) i (hi.trans hl.le) h) hr l le_rfl (fun i hi => hz _ (by simp [hi]))).trans
       let K:=seedInv k k; have hK:0 ≤ K:=seedInv_pos ..
       apply (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hl.le) (by positivity : 0 ≤ K*a)).trans; unfold logFee; nlinarith -- slow
end YM.QCD.Stew.Phased
