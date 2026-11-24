import YM.Poised.Project
import YM.Planned.PRIMARY_INTEGRAL_295.Spot
import YM.Planned.PRIMARY_INTEGRAL_295.Bigrade
/-!
# Mixed probes: even the Grassmann arguments in the same budget.
Extract order through shared joint chart, polynomial incl spin legs. General dilation. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
variable {c : Side}{d l k n:ℕ}
namespace Drives
variable {ι E F : Type*}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F]
variable (G:ι→E→L[ℝ]E)(w:ι→ℕ)
abbrev road (t:ℝ):E→L[ℝ]E := ∑ i:ι,t^(w i) • G i
local notation "L"=> road G w
lemma road_at (t:ℝ)(x:E): L t x = ∑ i:ι,t^(w i) • G i x:=by rw [road,_root_.sum_apply]; rfl
lemma zeroC (h:∀ i,0 < w i)(x:E): L 0 x=0:=by simp_rw [road_at]; exact Finset.sum_eq_zero fun i _=>by rw [zero_pow (ne_of_gt (h i)), zero_smul]
lemma smooth (x:E) : ContDiff ℝ ω (fun t:ℝ=>L t x):= by simp_rw [road_at]; fun_prop
def book (T : Tensor.T E F n)(k:ℕ): Tensor.T E F n:= ∑ p : Fin n → ι with (∑ i,w (p i))=k,T.compContinuousLinearMap (fun i=>G (p i))
lemma step (T:Tensor.T E F n)(k:ℕ)(x:Fin n→E): leading k (fun t=>T (fun i=>L t (x i)))=book G w T k x:=by
    let f (p : Fin n → ι) : F:= T fun i=> G (p i) (x i); let m(p:Fin n →ι):=∑ i,w (p i); have ht (t:ℝ) : T (fun i=> L t (x i))=∑ p:Fin n→ι,t^(m p) • f p:=by
       simp_rw [road_at]; rw [T.map_sum (fun i j=>t^(w j) • G j (x i))]; refine sum_congr rfl fun i _=>?_ ; rw [T.map_smul_univ,prod_pow_eq_pow_sum]
    simp_rw [ht]; rw [lead_sum (n:=k) Finset.univ (fun i (x:ℝ)=>x^(m i) • f i) (fun i _=>(monoSmooth ..).contDiffAt)]; simp_rw [lead_monomial]; unfold book; rw [_root_.sum_apply]; simp [Finset.sum_filter,eq_comm,f,m]
lemma orbit (T:Tensor.T E F n)(h:Tensor.Sym T)(k:ℕ): Tensor.Sym (book G w T k):=by
    intro x σ; rw [← step, ← step]; exact congr_arg _ (funext fun i=>h (fun j=>L i (x j)) σ)
private lemma leadingBlock (f:E→F)(hf:ContDiffAt ℝ d f 0)(hk:k ≤ d)(x:E)(h:∀ i,0 < w i): leading k (fun t=> f (L t x))=∑ l ∈ Finset.range (d+1), book G w (Tensor.coeff f l 0) k (fun _=>x):=by
    let r(t:ℝ):=L t x; have hh:r 0=0:=zeroC G w h x; have hu:=smooth G w x; have hT:ContDiffAt ℝ d r 0:=hu.contDiffAt.of_le le_top
    have he:= jets_comp (g':=blockTaylor d f) hT hT (show ContDiffAt ℝ d f (r 0) from hh.symm ▸ hf) -- import
    let g l t:=Tensor.diagonal (Tensor.coeff f l 0) (r t)
    change leading k (f∘r)=_
    calc _=leading k (blockTaylor d f∘r):=by unfold leading iteratedDeriv; rw [he (blockTaylor_contDiff d f _|>.contDiffAt) rfl (fun _ _ => rfl) (fun l hl => hh.symm ▸ (blockTaylor_jets hf l hl).symm) _ hk]
         _=leading k (fun t=> ∑ l∈Finset.range (d+1),g l t):=by apply congr_arg; funext t; simp only [blockTaylor, Function.comp_apply,Finset.sum_apply,g]
         _=_ :=by rw [lead_sum _ _ (fun i _=> (show ContDiff ℝ _ (g i) from (Tensor.diag_smooth _ _).comp (hu.of_le le_top)).contDiffAt)]; exact Finset.sum_congr rfl fun i _=> step G w ..
lemma detects (f:E→F)(hf:ContDiffAt ℝ d f 0)(hl:l≤d)(a:Fin l→ℕ)(h:∀ i,0<w i)(ha:(∑ i,a i)≤d)(ht:∀ x:E, leading (∑ i,a i) (fun t:ℝ=>f (L t x))=0)(u: Fin l→ E)(hz:∀ i t,L t (u i)=t^(a i) • u i): iteratedFDeriv ℝ l f 0 u=0:=by
    let n:= ∑ i,a i; let g l:=book G w (Tensor.coeff f l 0) n; have hZ : g l=0:=by
       apply Tensor.ext_diag (g l) 0 (orbit G w _ (Tensor.coeff_symm (hf.of_le (by exact_mod_cast hl))) _) (fun _ _ => rfl); funext x
       let r (i:ℕ)(t:ℝ):=t^i • Tensor.diagonal (g i) x
       have he(t:ℝ): ∑ i∈Finset.range (d+1), r i t=0:=by
          specialize ht (t • x); rw [leadingBlock G w f hf ha _ h] at ht
          calc _= ∑ i∈Finset.range (d+1),Tensor.diagonal (g i) (t • x):=by refine sum_congr rfl fun i _=>?_ ; unfold r Tensor.diagonal; rw [(g i).map_smul_univ (fun _:Fin i=>t) (fun _=>x)]; simp
               _=_:=ht
       have h0:=lead_sum (n:=l) (Finset.range (d+1)) r (fun i _=>(monoSmooth ..).contDiffAt); rw [funext he,show leading l (fun _=>(0:F))=0 from leading_zero_iff.mpr (by simp),sum_eq_single l] at h0; swap
       · intro i _ hi; unfold r; rw [lead_monomial, if_neg (Ne.symm hi)]
       swap; · simp [Nat.lt_succ_of_le hl]
       unfold r at h0; rw [lead_monomial,if_pos rfl] at h0; exact h0.symm
    let q:= Tensor.coeff f l 0; have he (t:ℝ) : q (fun i=> L t (u i))= t^n • q u:=by simp_rw [hz,q.map_smul_univ, prod_pow_eq_pow_sum]; rfl
    have hΦ := step G w q n u; change leading n _=g l u at hΦ; rw [funext he,lead_monomial,if_pos rfl,hZ] at hΦ
    change (l.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ l f 0 u=0 at hΦ; exact (smul_eq_zero.mp hΦ).resolve_left (by positivity)
lemma capped (f:E→F)(hf:ContDiffAt ℝ d f 0)(hl:l≤d)(a:Fin l→ℕ)(h:∀ i,0<w i)(hu:∀ x:E,L 1 x=x) (hz:∀ i x t,L t (G i x)=t^(w i) • G i x)(ha:(∑ i,a i)<n)(hn:n≤d+1)(ht:∀ x:E,∀ k<n, leading k (fun t:ℝ=>f (L t x))=0)(u: Fin l→ E)(he:∀ i j,a i<w j→ G j (u i)=0): iteratedFDeriv ℝ l f 0 u=0:=by
    let J:=iteratedFDeriv ℝ l f 0
    have h₀(i:Fin l): ∑ j:ι,G j (u i)=u i:=by simpa only [road_at,one_pow,one_smul] using hu (u i)
    change J u=0; trans J (fun i=>∑ j:ι,G j (u i)); swap
    · rw [J.map_sum (fun i j=>G j (u i))]; apply Finset.sum_eq_zero; intro r _; by_cases hv:∀ i,w (r i)≤ a i
      · have hx:∑ i,w (r i) < n:= lt_of_le_of_lt (Finset.sum_le_sum fun i _=> hv i) ha
        exact detects G w f hf hl (w ∘ r) h (by exact Nat.le_of_lt_succ (hx.trans_le hn)) (fun x=> ht x _ hx) _ fun i=>hz (r i) (u i)
      push Not at hv; obtain ⟨i,hi⟩:= hv; exact J.map_coord_zero i (he i _ hi)
    rw [funext h₀]
end Drives
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Drives.capped
