import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! # Two-variable price for K (Sliver)

Reserve a special algebra of Taylor jets in the s marker. Use it after
normal-Mayer K flag-merging so don't need support derivatives of the K part of
a shifted family. Marker increments genuinely represented by values of a
*single* function. This lemma deliberately doesn't price the baseline inside
the variant jets; that must be done along with the actual histories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Filament
open Function Filter Complex Metric Finset
open scoped BigOperators Topology ContDiff Classical
variable {r R C b : ℝ} {z s: ℂ}
variable {E F X: Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
variable (n:ℕ) {p q:ℂ→ E}
def bead (n:ℕ)(f:ℂ→E): E:= (n.factorial:ℂ)⁻¹ • iteratedDeriv n f 0
abbrev Holo (f:ℂ→E) (r:ℝ:=1):= DifferentiableOn ℂ f (ball 0 r)
variable [CompleteSpace E]
lemma Holo.apex (h0:Holo p r)(he:0<r): ContDiffAt ℂ (↑n) p 0:=(h0.analyticAt (ball_mem_nhds _ he)).contDiffAt
lemma Holo.spread (he:Holo p r) (h:‖z‖<r): HasSum (fun n:ℕ=> z^n • bead n p) (p z):=by
    have h1:=Complex.hasSum_taylorSeries_on_ball he (mem_ball_zero_iff.mpr h); apply h1.congr_fun; intro i; rw [sub_zero]; exact smul_comm ..
omit [CompleteSpace E] in
@[simp] lemma bead_baseline (p:ℂ→E) : bead 0 p=p 0:=by simp [bead]
omit [CompleteSpace E] in
@[simp] lemma bead_first (p:ℂ→E) : bead 1 p=deriv p 0:=by simp [bead]
lemma bead_add (he:Holo p r)(hc:Holo q r)(hr:0<r): bead n (p+q)=bead n p + bead n q:=by simp only [bead, iteratedDeriv_add (he.apex _ hr) (hc.apex _ hr), smul_add]
lemma bead_sub (he:Holo p r)(hc:Holo q r)(hr:0<r): bead n (p-q)=bead n p - bead n q:=by simp only [bead, iteratedDeriv_sub (he.apex _ hr) (hc.apex _ hr), smul_sub]
lemma bead_fin {f:X→ℂ→E} {B:Finset X} (hf:∀ i∈B,Holo (f i) r)(hr:0<r): bead n (fun z=> ∑ i∈ B,f i z)=∑ i∈ B,bead n (f i):=by
    simp only [bead, iteratedDeriv_fun_sum (fun i hi=> Holo.apex n (hf i hi) hr),smul_sum]
lemma handset (A:E→L[ℂ] F) (hf:Holo p r)(hr:0<r): bead n (A ∘ p) = A (bead n p):= by
     unfold bead; rw [iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_eq_iteratedFDeriv,A.iteratedFDeriv_comp_left (hf.apex n hr) le_rfl,map_smul]; rfl
omit [CompleteSpace E] in
lemma bead_mono (n m:ℕ) (c:E) : bead n (fun x:ℂ=>x^m • c) = if n=m then c else 0 := by
    unfold bead; rw [iteratedDeriv_smul_const (by fun_prop : ContDiffAt ℂ n (fun z:ℂ=>z^m) 0), iteratedDeriv_fun_pow_zero]; split
    next h=> subst m; exact inv_smul_smul₀ (by exact_mod_cast n.factorial_ne_zero) _
    next h => simp
omit [CompleteSpace E] in
lemma bead_const (t:E)(i:ℕ): bead i (fun _=>t)=if i=0 then t else 0:=by simpa only [pow_zero,one_smul] using bead_mono i 0 t

-- separate analytic despite being actually tame; jet A linear in z (unit disk not incl fees at outer circle)
structure Fused (f:ℂ→ℂ→E) : Prop where
 lamp (z:ℂ): ‖z‖<1 → Holo (f z)
 wire (s:ℂ): ‖s‖<1 → Holo (fun z=> f z s)
 baseS (s:ℂ): ‖s‖ <1 → f 0 s=f 0 0
 base (z:ℂ): ‖z‖ <1 → f z 0=f 0 0
 mute (z:ℂ): ‖z‖ <1 → bead 1 (f z)=0
 linear: ∃ x:E,∀ z:ℂ, ‖z‖<1 → bead 2 (f z)=z • x

lemma Holo.cauchy (hp:Holo p r)(hb:∀ z:ℂ, ‖z‖=R → ‖p z‖≤ C) (h:0 < R) (hz:R < r): ‖bead n p‖ ≤ C/R^n:=by
   unfold bead; rw [norm_smul,norm_inv,norm_natCast,inv_mul_le_iff₀ (by positivity)]; rw [← mul_div_assoc]; exact norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n h ((hp.mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hz))).diffContOnCl) fun z hz=> hb z ((dist_zero_right _).symm.trans (mem_sphere.mp hz))
-- uniform Taylor truncation at any ν. doesn't require positivity of C
lemma Holo.afterglow (hp:Holo p r)(hb: ∀ z:ℂ, ‖z‖=R→ ‖p z‖≤C)(h:0<R)(hz:R<r)(he:‖s‖<R):
   ‖p s-∑ i∈range n,s^i • bead i p‖ ≤ (‖s‖/R)^n * (1-‖s‖/R)⁻¹ * C := by
   let q:= ‖s‖/R; have hq:0≤q:=by unfold q; positivity
   have hr : q<1 := (div_lt_one h).2 he
   have hsum (i):= hp.cauchy i hb h hz; have hw:= (hp.spread (z:=s) (he.trans hz))
   let f i:= s^(i+n) • bead (i+n) p; let g i:= q^i*(q^n*C)
   have hh: HasSum f (p s-∑ i∈range n,s^i • bead i p) := (hasSum_nat_add_iff' ..).mpr hw
   have hg: HasSum g ((1-q)⁻¹*(q^n*C)) := (hasSum_geometric_of_lt_one hq hr).mul_right _
   have hd(i): ‖f i‖≤g i:=by unfold f g; rw [norm_smul,norm_pow]; refine le_trans (mul_le_mul_of_nonneg_left (hsum _) (by positivity)) (le_of_eq ?_); rw [← mul_assoc,← pow_add]; unfold q; rw [div_pow]; ring
   have hx := hg.summable.of_nonneg_of_le (fun _=>norm_nonneg _) hd
   rw [← hh.tsum_eq]; refine (norm_tsum_le_tsum_norm hx).trans ((hx.tsum_le_tsum hd hg.summable).trans (le_of_eq ?_)); rw [hg.tsum_eq]; unfold q; ring
namespace Fused
variable {f : ℂ→ℂ→E} (h:Fused f)
abbrev Safe (s:ℂ): Prop:= ‖s‖≤1/4
lemma withinS (he:Safe s) : ‖s‖<1/2:= he.trans_lt (by norm_num : (1/4:ℝ)<1/2)
lemma withinL (he:Safe s) : ‖s‖<1:= he.trans_lt (by norm_num : (1/4:ℝ)<1)
def luster (C:ℝ)(n:ℕ)(s:ℂ):ℝ:=2*C*(2*‖s‖)^n
def peso (n:ℕ):ℕ:= if n=1 then 2 else 3
lemma lucre (h:0≤C): 0≤luster C n s:=by unfold luster; positivity
variable (hb : ∀ z s:ℂ, ‖z‖<1→‖s‖<1→‖f z s‖≤C) (hs:Safe s)
include h hb hs
private lemma short (hz:‖z‖<1): ‖f z s-∑ i∈range n,s^i • bead i (f z)‖≤ luster C n s:=by
    refine ((h.lamp _ hz).afterglow n (fun t ht=> hb _ t hz (ht.trans_lt (by norm_num : (1/2:ℝ)<1))) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) (withinS hs)).trans ?_
    unfold luster; field_simp (discharger:=skip)
    have he:‖s‖≤1/4:=hs; have hp:1/2≤ 1-‖s‖*2:=by linarith
    have hv:0≤C:=(norm_nonneg _).trans (hb _ _ hz (withinL hs))
    apply (div_le_iff₀ ((by norm_num : (0:ℝ)<1/2).trans_le hp)).2; linarith only [mul_le_mul_of_nonneg_left hp (show 0≤(‖s‖*2)^n*C from (by positivity))]
lemma benefits (hr:0<R)(hz:R<1)(hn:n≠0) : ‖bead n (fun z:ℂ=> f z s)‖≤ luster C (peso n) s/R^n:=by
    let F (z:ℂ):=f z s; let x:=f 0 0
    have hg:Holo F:=h.wire _ (withinL hs)
    have hX:Holo (fun _=>x):=differentiableOn_const x
    rcases eq_or_ne n 1 with he|he
    · let G (z:ℂ):=x
      rw [peso,if_pos he]; have hL := hg.sub hX
      have hx: bead n (F-G)=bead n F:=by rw [bead_sub n hg hX zero_lt_one, bead_const,if_neg hn,sub_zero]
      rw [show bead n _=bead n F from rfl,← hx]; apply Holo.cauchy n hL _ hr hz
      intro t ht; have he:= ht.trans_lt hz; have hi := short (n:=2) h hb hs he; simp only [sum_range_succ, sum_range_zero,zero_add,pow_zero,one_smul,bead_baseline,pow_one,h.mute t he,smul_zero,add_zero,h.base t he] at hi; exact hi
    obtain ⟨a,ha⟩:= h.linear
    let v:=s^2 • a; let G:ℂ → E:= (fun _=>x)+(fun z=>z^1 • v)
    have hv:Holo (fun z:ℂ=> z^1 • v):=(by unfold Holo; fun_prop)
    have hU:Holo G:=hX.add hv
    have hh:bead n (F-G)=bead n F:= by
        have hl: bead n G=0:=by unfold G; rw [bead_add n hX hv zero_lt_one,bead_mono n 1 v,bead_const,if_neg he,if_neg hn,zero_add]
        rw [bead_sub n hg hU zero_lt_one,hl,sub_zero]
    rw [show bead n _=bead n F from rfl,← hh,peso,if_neg he]; apply Holo.cauchy n (hg.sub hU) _ hr hz
    intro t ht; have hf:= ht.trans_lt hz; have hi:= short (n:=3) h hb hs hf
    simp only [sum_range_succ, sum_range_zero,zero_add,pow_zero,one_smul,pow_one,h.mute t hf, smul_zero,add_zero,ha t hf,bead_baseline,h.base t hf] at hi
    change ‖f t s-(x+t^1 • (s^2 • a))‖ ≤ _; rw [pow_one,smul_comm]; exact hi
end Fused

end YM.Massive.Filament
#print axioms YM.Massive.Filament.Fused.benefits
