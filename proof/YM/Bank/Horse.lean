import YM.Bank.Zoom
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Horse
open Function Lattice Laurent Bloch Metric Filter Finset Zoom Pilot Pap Osc Bee
open QCD.Pearl (beamH beam0 beamP)
open scoped Topology BigOperators ENNReal Matrix.Norms.L2Operator
variable {A:Type*}[AddCommGroup A]
def lap (z:A)(f:A→ℂ) (x:A):= f (x+z)-f x
def gigs (z:A)(f:A→ℂ): ℕ → A→ℂ
   | 0=> f
   | n+1=> lap z (gigs z f n)
lemma gigs_sub (z:A)(f g:A→ℂ)(n:ℕ): gigs z (f-g) n=gigs z f n-gigs z g n :=by induction n with
   | zero=>rfl
   | succ n ih=>rw [gigs,gigs,gigs,ih]; ext1; simp only [lap,Pi.sub_apply]; abel
lemma gigs_formula {B:Type*}[AddCommGroup B]{x y:A}{p q:B}{n:ℕ}{f:A→ℂ}{g:B→ℂ}(h:∀ i≤n,f (x+i • y)=g (p+i • q)):gigs y f n x=gigs q g n p:=by
   induction n generalizing x p with
   | zero=> simpa only [le_refl, zero_smul,add_zero,gigs] using h 0 (le_refl _)
   | succ n ih=> rw [gigs,gigs,lap,lap,ih (fun i hi=> ?_),ih (fun i hi=> h i (by omega))]
                 simpa only [add_assoc,succ_nsmul,add_comm (i • y),add_comm (i • q)] using h (i+1) (by omega)
lemma gigs_price {x y:A}{n:ℕ}{C:ℝ}{f:A→ℂ}(h:∀ i≤n,‖f (x+i • y)‖≤ C):‖gigs y f n x‖ ≤2^n*C :=by
   induction n generalizing x with
   | zero=> simpa [gigs] using h 0 (le_refl _)
   | succ n ih=>
      rw [gigs,lap]; apply (norm_sub_le ..).trans; refine (add_le_add (ih (x:=x+y) (fun i hi=> ?_)) (ih (x:=x) (fun i hi=> h i (by omega)))).trans_eq ?_; · simpa only [add_assoc,succ_nsmul,add_comm (i • y)] using h (i+1) (by omega)
      rw [pow_succ]; ring
-- rough analytic chords shrink

def tailH (n:ℕ)(r:ℝ):ℝ:= r/8^n
def headH (n:ℕ) (R z r:ℝ) := R*(z/(r/8^n))^n
lemma smooth_iter {f:Momentum→ℂ}{x p:Momentum}{r C:ℝ}(n:ℕ)(hr:0<r)(hc:0≤C)(hf:∀ i∈ball p r,DifferentiableAt ℂ f i∧ ‖f i‖≤C)(hx:‖x‖< r/8^n):
   ∀ i∈ball p (tailH n r), DifferentiableAt ℂ (gigs x f n) i ∧ ‖gigs x f n i‖ ≤ headH n C ‖x‖ r :=by
    induction n with
    | zero=> simpa only [headH, pow_zero,tailH,gigs,mul_one,div_one] using hf
    | succ n ih=>
       let t:= tailH n r; let b := headH n C ‖x‖ r; have ht:0<t:=by unfold t tailH; positivity
       have he: tailH (n+1) r=t/8:=by unfold t tailH; rw [div_div,pow_succ]
       change ‖x‖<tailH (n+1) r at hx
       rw [he] at hx;
       have h := ih (hx.trans (show t/8<t by linarith)); intro i hi
       have hp :dist i p<t/8:=he ▸ mem_ball.mp hi
       have hP : ball i (t/2) ⊆ ball p t:= ball_subset_ball' (by linarith : t/2+dist i p≤t) -- check
       have hi' : i+x∈ball i (t/2/2):=by rw [mem_ball,dist_eq_norm,add_sub_cancel_left]; linarith
       have hv := (h (i+x) (hP (ball_subset_ball (by linarith) hi'))).1
       refine ⟨(hv.comp i ((differentiableAt_id).add_const x)).sub (h i (hP (mem_ball_self (by positivity)))).1,?_⟩
       change ‖gigs x f n (i+x)-gigs x f n i‖ ≤ _
       apply (QCD.Run.lastwig (gigs x f n) (show 0<t/2 by positivity) (fun y hy=> (h y (hP hy)).1) (fun y hy=> (h y (hP hy)).2) hi').trans
       rw [add_sub_cancel_left]; have hv :0≤ b:=by unfold b headH; positivity
       change b/(t/2/2)*‖x‖ ≤ headH (n+1) _ _ _
       change b/(t/2/2)*‖x‖ ≤ C*(‖x‖/ tailH (n+1) r)^(n+1); rw [he,pow_succ,← mul_assoc]
       have ht': 0 ≤ ‖x‖/t:=by positivity
       have hs : b ≤ C * (‖x‖/(t/8))^n := by unfold b headH; apply mul_le_mul_of_nonneg_left _ hc; exact pow_le_pow_left₀ ht' (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)) _
       calc
         _ = b* (‖x‖/(t/2/2)):= by ring
         _ ≤ _:= mul_le_mul hs (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by linarith)) (by positivity) (hv.trans hs)
variable {c:Side}{χ:Bool}
def summit (c:Side)(v:Cover)(σ:Bool)(f:Site c→ℂ):ℂ:= ∑ p,mode (grid σ p) v*f p
lemma payment (v z:Cover)(σ:Bool)(f:Site c→ℂ)(n:ℕ): summit c v σ (gigs (wrap c z) f n) = (mode (-phaseΔ c z) v -1)^n * summit c v σ f:=by
   let h p:= mode (grid (c:=c) σ p) v; let M:=mode (phaseΔ c z) v
   have he i : h (i+wrap c z)= M * h i:= by unfold h; rw [echo,mul_comm]
   have hm : mode (-phaseΔ c z) v=M⁻¹ := by rw [mode_inverse] -- check
   have ht (f:Site c→ℂ): summit c v σ (lap (wrap c z) f)=(M⁻¹-1)* summit c v σ f :=by
       unfold summit lap; simp_rw [mul_sub,sum_sub_distrib,sub_mul,one_mul, mul_sum]; congr 1;
       rw [← Equiv.sum_comp (Equiv.addRight (wrap c z)) (fun i:Site c=> M⁻¹ * (mode (grid σ i) v*f i))]; refine sum_congr rfl fun i _=> ?_; change h i*_ =M⁻¹*(h (i+wrap c z)*_); rw [he]; have hg:M≠0:=Complex.exp_ne_zero _; simp [← mul_assoc,Equiv.addRight,hg]
   rw [hm]; induction n with
   | zero=>simp [gigs]
   | succ n ih=> rw [gigs,ht,ih,pow_succ',mul_assoc]
end YM.Bank.Horse
#print axioms YM.Bank.Horse.payment
#print axioms YM.Bank.Horse.smooth_iter
