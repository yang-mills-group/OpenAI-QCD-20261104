import YM.Bank.Wale
import YM.Bank.Pilot
/-! Oscillator class for comparative grid tests. Polarity through arbitrary difference stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Osc
open Function Lattice Laurent Bloch Metric RG Precision Filter Finset Next.Free Learn Wale
open Pilot
open Complex (I)
open scoped Matrix Topology Matrix.Norms.L2Operator BigOperators ComplexConjugate
variable {c:Side}{X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X] {a b r s t A:ℝ}
def collar (p:Momentum) (s:ℝ):= ball p (s*‖p‖)
-- ν engineering order = denominator pole possibly two. 3 for dirac first? target crossing exponent N+? use f ≤ ‖p‖^(ν) / ‖p‖, spin ν=q+q', gauge ν+1. supports. small error ≤ ‖p‖^ν.
structure Genie (k:ℕ)(σ:Bool)(c:Side)(f g:Momentum→ℂ)(a A:ℝ): Prop where
   radius: 0<a
   sheer:a ≤ 1
   money:0≤ A
   clean: f 0=0 ∨ σ=true -- p=0 gauge means zero
   pole: g 0=0
   tall (i:Site c){v:Momentum}(hk:grid σ i≠0)(h:v∈ collar (grid σ i) a): DifferentiableAt ℂ f v∧ ‖f v‖ ≤ A/‖grid σ i‖
   scope (i:Site c){v:Momentum}(hk:grid σ i≠0)(h:v∈ collar (grid σ i) a): v∈cube zone
   -- relation on REAL near even Φ through periodic shifts
   shifts (x: Cover) {p:Momentum}: p∈baseCube→physical (p+reciprocal x)→p+reciprocal x ∈ cube zone → f (p+reciprocal x)=f p -- any shifts that small
   sparks (i:Site c): grid σ i≠0→ ‖grid σ i‖≤ a→ Twin (f (grid σ i)) (g (grid σ i)) A (‖grid σ i‖^k/‖grid σ i‖) ‖grid σ i‖
lemma Genie.mono {k:ℕ}{σ:Bool}{c:Side}{f g: Momentum → ℂ}(h:Genie k σ c f g s A)(he:0<r)(hp:r≤s)(hm:A≤a):Genie k σ c f g r a := by
    have hg (i:Site c) (v:Momentum):v∈collar (grid σ i) r→v∈collar (grid σ i) s:=fun hv=>ball_subset_ball (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) hv
    exact ⟨he, hp.trans h.sheer,h.money.trans hm,h.clean,h.pole,fun i q he hv=> ⟨(h.tall i he (hg i q hv)).1, (h.tall i he (hg i q hv)).2.trans (div_le_div_of_nonneg_right hm (norm_nonneg _))⟩,fun i q he hv=> h.scope i he (hg i q hv),h.shifts, fun i he hv=> (h.sparks i he (hv.trans hp)).higher hm (by positivity) (by positivity)⟩
lemma cup_z (r:ℝ)(hr:0<r): ∃ a,0<a∧ a ≤ 1 ∧∀ p: Momentum,p∈baseCube → ∀ v∈collar p a, v∈cube (r/2)∧v∈ cube zone∧‖v‖≤2*‖p‖:=by
   let t:=min (r/2) zone; let s:=t/2; let a:= min 1 (s/Real.pi)
   have ht:0<t:=lt_min (by positivity) zone_pos; have hs:0<s:=half_pos ht; have ha:0<a:=lt_min one_pos (by positivity); have h1:a≤1:=min_le_left ..
   refine ⟨a,ha,h1,fun p hp v h=>?_⟩
   have he:a*‖p‖ ≤ s:= (mul_le_mul_of_nonneg_left (QCD.Pearl.cap_base hp) ha.le).trans ((le_div_iff₀ Real.pi_pos).mp (min_le_right ..))
   have hx:v∈cube t:= ball_inside_cube (mem_cube_real (base_subset_realCube hs hp) hs) (ball_subset_ball (he.trans (le_of_eq (by unfold s; ring : s=t-s))) h)
   refine ⟨cube_mono (min_le_left ..) hx,cube_mono (min_le_right ..) hx,?_⟩
   have hg : ‖v‖-‖p‖ ≤ 1*‖p‖ := (norm_sub_norm_le ..).trans ((show ‖v-p‖ ≤ a*‖p‖ by rw [←dist_eq_norm]; exact (mem_ball.mp h).le).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg p))); linarith

lemma sector (l:List Axis)(v:Momentum) :DifferentiableAt ℂ (fun p=>listChip p l) v :=by
   induction l with
   | nil=> simp [listChip]
   | cons a s ih=> have hx:DifferentiableAt ℂ (fun p: Momentum=>chip (p a)) v:=by unfold chip; fun_prop
                   simp only [listChip,List.map_cons,List.prod_cons]; exact hx.mul ih
lemma road (l:List Axis)(p:Momentum)(h:p∈cube zone): ‖listChip p l‖ ≤ (Next.Free.meter.high*‖p‖)^l.length :=by
    induction l with
    | nil=>simp [listChip]
    | cons a s ih=> simp only [listChip,List.map_cons,List.prod_cons,norm_mul,List.length_cons]; rw [pow_succ']; exact mul_le_mul (Merchant.chip_bill h _) ih (norm_nonneg _) (mul_nonneg meter.high_pos.le (norm_nonneg _))
lemma spins_back (l: List Axis) (p:Momentum)(x:Cover): listChip (p+reciprocal x) l = listChip p l:=by induction l with
   | nil=> simp [listChip]
   | cons a s ih=> change chip ((p+reciprocal x) a)*listChip _ _=chip (p a)*listChip _ _; rw [ih]; simp only [Pi.add_apply, Laurent.reciprocal, chip_repeat]
lemma turns_back (l:List Axis)(p : Momentum)(h: physical p):star (barrier p l) = barrier (-p) l:=by induction l with
   | nil=> simp [barrier]
   | cons a s ih=> change star ((I*p a)*barrier p s)=(I*_)*barrier (-p) s; rw [star_mul, ih,star_mul,show star (p a)=p a from congr_fun h _]; simp [mul_comm]
lemma stars_back (l:List Axis)(p : Momentum)(h: physical p):star (listChip p l)=listChip (-p) l:=by induction l with
   | nil=> simp [listChip]
   | cons a s ih=> change star (chip (p a)*listChip _ _)=chip ((-p) a)*listChip _ _; rw [star_mul, ih, flip_chip, show star (p a)=p a from congr_fun h _]; rw [mul_comm]; rfl

def spinWin (u v: List Axis)(f:Momentum→ℂ)(p:Momentum):= f p* listChip p u*listChip (-p) v
def spinJet (u v : List Axis)(g:Momentum→ℂ)(p:Momentum):= g p*barrier p u*barrier (-p) v
lemma turbo {a C:ℝ}(ha:0≤C)(u v: List Axis): ∃ A,0≤ A ∧∀ (f g:Momentum→ℂ) c σ k,
     Genie k σ c f g a C → Genie (k+u.length+v.length) σ c (spinWin u v f) (spinJet u v g) a A:=by
   let D:=meter.high*(2*Real.pi); let w:=(4:ℝ); let E:=C*D^u.length*D^v.length; let A:=2*(2*C*w^u.length)*w^v.length
   have hd:0<D:=by unfold D; have ht:=meter.high_pos; positivity
   have hp:0≤E:=by unfold E; positivity
   refine ⟨max E A,le_trans hp (le_max_left ..),fun f g c σ k h=> ⟨h.radius,h.sheer,hp.trans (le_max_left ..),?_, ?_,?_, h.scope, ?_,?_⟩⟩
   · rcases h.clean with h|h; exact Or.inl (by simp [spinWin,h]); exact Or.inr h
   · simp [spinJet,h.pole]
   · intro i z he hx; obtain ⟨hf,hf'⟩:=h.tall i he hx
     have hb:= h.scope i he hx
     let r:=grid σ i; have hs :‖z‖≤ 2*Real.pi:=by
         have hl: ‖z-r‖ ≤ a*‖r‖:=by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hx).le
         have hp:=norm_nonneg r; have hu : ‖r‖≤Real.pi:=QCD.Pearl.cap_base (cubic σ _); nlinarith [norm_sub_norm_le z r,h.sheer]
     have hm:0 < ‖r‖:= norm_pos_iff.mpr he
     refine ⟨(hf.mul (sector u z)).mul ((sector v (-z)).comp z (show DifferentiableAt ℂ (fun i : Momentum=> -i) z from differentiableAt_id.neg)),?_⟩
     have hU x (z:Momentum)(ht: z∈cube zone)(hi:‖z‖≤2*Real.pi): ‖listChip z x‖≤ D^x.length:= (road x z ht).trans (pow_le_pow_left₀ (mul_nonneg meter.high_pos.le (norm_nonneg _)) (mul_le_mul_of_nonneg_left hi meter.high_pos.le) _)
     unfold spinWin; rw [norm_mul,norm_mul]; refine (mul_le_mul (mul_le_mul hf' (hU u z hb hs) (norm_nonneg _) ((norm_nonneg _).trans hf')) (hU v _ (cube_neg z hb) (by rw [norm_neg]; exact hs)) (norm_nonneg _) (mul_nonneg (div_nonneg ha hm.le) (pow_nonneg hd.le _))).trans ((le_of_eq (show (_:ℝ)=E/‖r‖ from ?_)).trans (div_le_div_of_nonneg_right (le_max_left ..) hm.le)) -- annotation
     unfold E r; ring
   · intro x p hp ht hx; unfold spinWin; rw [h.shifts _ hp ht hx, spins_back, show -(p+reciprocal x : Momentum)=-p+reciprocal (-x) by rw [reciprocal_negate]; abel, spins_back]
   intro i he hv
   let p:=grid σ i; have hQ:‖p‖ ≤1:=hv.trans h.sheer
   have hg:= chips v (q:=-p) (by rw [norm_neg]; exact hQ); rw [norm_neg] at hg
   have hx := ((h.sparks i he hv).click (chips u hQ)).click hg
   refine Twin.higher ?_ (le_max_right E A) (by positivity) (norm_nonneg _)
   rw [pow_add,pow_add]; convert hx using 1 <;> first | rfl | (unfold p; ring)
end YM.Bank.Osc
#print axioms YM.Bank.Osc.turbo
