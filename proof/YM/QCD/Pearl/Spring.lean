import YM.QCD.Pearl.Joy

/-! # absolute analytic estimates in momentum on narrow strips. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Function Finset Metric Lat Rudder Kit RG Laurent Bloch Flume
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker Topology
variable {n : Side} {η : ℝ} (C : su.Color) {p : Momentum}

lemma shortStep (a : Step): size a.vec=1:=by unfold Step.vec; cases a.neg <;> simp [size,apply_ite]
lemma stepStop (x:Cover)(w:Walk):size (stop x w) ≤ size x+w.length:=by
  induction w generalizing x with
  | nil=> simp [stop]
  | cons a w ih=>
    rw [stop,List.length_cons]; apply (ih (x+a.vec)).trans; apply (Nat.add_le_add_right (size_add ..) _).trans; rw [shortStep]; omega
lemma flashBound (hp: p∈strip η)(x:Cover)(a i:Axis): ‖flash p a (x,i)‖ ≤ Real.exp (η*size x):=by unfold flash; split; exact reward _ _ _ (fun i=>(hp i).le); rw [norm_zero]; positivity
lemma flashSize {a:Step} (x:Cover)(y) (h : y=a.used x):size y.1≤size x+1:=by
  subst y; unfold Step.used; split
  next hi=> have he:a.vec (R:=ℤ)= -step a.dir:=if_pos hi; simp only []; rw [sub_eq_add_neg,← he]; exact (size_add ..).trans (by rw [shortStep])
  next=> simp
lemma shortBill (he:0≤η)(hp:p∈strip η) (a:Axis)(w:Walk)(x: Cover): ‖bill (flash p a) x w‖ ≤ w.length*Real.exp (η*((size x+w.length:ℕ):ℝ)):=by
  induction w generalizing x with
  | nil=> simp[bill]
  | cons i w ih=>
    have he' : size (x+i.vec)≤ size x+1 := (size_add ..).trans (by rw [shortStep])
    let g:=Real.exp (η*((size x+w.length+1:ℕ):ℝ));
    have h₂: ‖bill (flash p a) (x+i.vec) w‖≤ w.length*g:=by apply (ih _).trans; unfold g; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast (show size (x+i.vec)+w.length≤size x+w.length+1 from by omega)) he)) (by positivity)
    have h₁: ‖flash p a (i.used x)‖ ≤ g:=by
      apply (flashBound hp (i.used x).1 a (i.used x).2).trans; unfold g; gcongr; have he := flashSize (a:=i) x _ rfl; omega
    rw [bill,List.length_cons, ← Nat.add_assoc]; push_cast; split_ifs; all_goals apply (norm_add_le ..).trans
    all_goals try rw [norm_neg]
    all_goals apply (add_le_add h₁ h₂).trans_eq; unfold g; push_cast; ring
lemma mode_zeroPay {w:Walk}(he:0≤η)(hp : p∈strip η): ‖mode p (stop 0 w)‖ ≤ Real.exp (η*w.length):= by
  apply (reward _ _ _ (fun i=>(hp i).le)).trans; gcongr; simpa [size] using stepStop 0 w
lemma glitter_cap (he:0≤η)(hp:p∈strip η)(w:Walk)(a:Axis): ‖glitter w p a‖≤w.length*Real.exp (η*w.length):=by unfold glitter; convert shortBill he hp a w 0 using 1; simp [size]
lemma strip_negX (hp:p∈strip η): -p∈strip η:=by intro i; simpa using hp i
lemma hap {m : ℕ} (W:Bloom m)(a:Axis)(hp:p∈strip η)(he:0≤η)(i): ‖hack (W.petals i) p a‖ ≤ 4*Real.exp (η * W.span):=by
  let S:= W.petals i
  apply (shortBill he hp a (Lattice.square S.plaq.val.1 S.plaq.val.2) S.offset).trans
  rw [show List.length _=4 from rfl]; push_cast; gcongr
  have hh: size S.offset+4 ≤ W.span:=by
    have he : size S.offset≤ S.walk.length:=by simpa [size,Slot.offset] using stepStop 0 S.walk
    unfold Bloom.span; exact (Nat.add_le_add_right he 4).trans ((single_le_sum (fun i _=> Nat.zero_le (W.petals i).length) (mem_univ i)).trans (Nat.le_add_left ..))
  exact_mod_cast hh -- check
lemma blossomC (C : su.Color)(m : ℕ):∃ K : ℝ,0 ≤ K ∧ ∀ V : Bloom m, ‖bloomC C V‖ ≤ K * V.price:=by
  let g (i:Fin m →su.ColorIndex):= ∏ j:Fin m,(C (i j):ℂ)
  refine ⟨∑ i, ‖g i‖,by positivity,fun V=>?_ ⟩; refine (norm_sum_le ..).trans ?_; unfold Bloom.price; rw [mul_sum]; apply sum_le_sum; intro i _; rw [norm_smul]; exact mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>norm_nonneg (g i)) (mem_univ _)) (norm_nonneg _)
lemma wane_size (he:0≤η)(hp:p∈strip η)(w:Walk):‖wane p w‖≤Real.exp (η*w.length):=by rw [wane,norm_smul,oneNorm,mul_one]; apply mode_zeroPay he hp
-- length funding: zⁿ e^(3σz) ≤ C exp(4σ z)
lemma length_gift (hp : 0<η)(k:ℕ):∃ C : ℝ,0≤C∧∀ z : ℕ,(z:ℝ)^k* Real.exp (3*η*z)≤C* Real.exp (4*η*z):=by
  have hh := Run.tides 1 k hp; obtain ⟨C,hC⟩:= (Filter.Tendsto.bddAbove_range hh)
  refine ⟨|C|,abs_nonneg _,fun z=> ?_⟩
  have hx : 1*(z:ℝ)^k*Real.exp (-η*z)≤ C := hC (Set.mem_range_self z)
  rw [one_mul] at hx
  apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (Real.exp_pos (4*η*z)).le)
  rw [mul_assoc _ (Real.exp _) (Real.exp _),← Real.exp_add]; ring_nf
lemma hill (he:0<η): ∃ K:ℝ,0≤K ∧ ∀ G:Gleam, ∀ p k: Momentum,p∈strip η→ k∈strip η→ ∀ i:Axis,
    ‖boom G k‖≤K*G.rate (4*η) ∧ ‖boom₁ C G i p k‖ ≤ K*G.rate (4*η) ∧ ‖boom₂ C G i p k‖≤ K*G.rate (4*η):=by
  obtain ⟨A,hA,h₁⟩:=length_gift he 1; obtain ⟨B,hB,h₂⟩:=length_gift he 2
  let T:=touch (echo C); let U:=touch (echo C*echo C)
  let L : Spike→L[ℂ] Bundle:=LinearMap.toContinuousLinearMap { toFun:=wave,map_add':=fun _ _ =>(wave_add ..).symm,map_smul':=fun _ _=> Matrix.smul_kronecker .. }
  let Z:=‖L‖
  refine ⟨Z+‖T‖*Z*A+‖U‖*Z*B,by unfold Z; positivity,fun G p k hp hk i => ?_⟩
  let n:=G.w.length; let R:= Real.exp (η*n); have hR: 1≤R:=Real.one_le_exp (by positivity)
  have ht : ‖boom G k‖ ≤ R*(Z*‖G.B‖):= (norm_mul_le ..).trans (mul_le_mul (wane_size he.le hk _) (L.le_opNorm _) (norm_nonneg _) (zero_le_one.trans hR))
  have hd : G.rate (4*η) = R^4*‖G.B‖:=by unfold Gleam.rate R; rw [← Real.exp_nat_mul]; push_cast; unfold n; ring_nf
  have heq : R^3 = Real.exp (3*η*n):=by unfold R; rw [← Real.exp_nat_mul]; push_cast; congr 1; ring
  have hf : 0≤Z:=norm_nonneg L
  have hl := G.valid (4*η)
  constructor
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (show Z≤Z+‖T‖*Z*A+‖U‖*Z*B by exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))) hl)
    apply ht.trans; rw [hd,mul_left_comm]; gcongr; exact le_self_pow₀ hR (by norm_num)
  constructor
  · refine le_trans ?_ (mul_le_mul_of_nonneg_right (show ‖T‖*Z*A ≤ Z+‖T‖*Z*A+‖U‖*Z*B by exact le_trans (le_add_of_nonneg_left hf) (le_add_of_nonneg_right (by positivity))) hl)
    apply (norm_mul_le ..).trans; apply (mul_le_mul (show ‖_‖≤n*R*‖T‖ from ?_) ht (norm_nonneg _) (by positivity)).trans
    · have hs:=h₁ n; rw [pow_one,← heq] at hs
      rw [Gleam.rate];
      calc _ ≤ ((n:ℝ)*R^3) * (‖T‖*Z*‖G.B‖):= by calc
                  _ = ((n:ℝ)*R^2)*(‖T‖*Z*‖G.B‖):= by ring
                  _ ≤ _:=by gcongr <;> norm_num
           _ ≤ _ := by dsimp [n] at hs ⊢; apply (mul_le_mul_of_nonneg_right hs (by positivity : 0≤‖T‖*Z*‖G.B‖)).trans (le_of_eq (by ring))
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (glitter_cap he.le hp _ _) (norm_nonneg _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (show ‖U‖*Z*B≤Z+‖T‖*Z*A+‖U‖*Z*B by exact le_add_of_nonneg_left (by positivity)) hl)
  apply (norm_mul_le ..).trans; apply (mul_le_mul (show ‖_‖≤ ((n:ℝ)*R)*((n:ℝ)*R)*‖U‖ from ?_) ht (norm_nonneg _) (by positivity)).trans
  · rw [show ↑n*R*(↑n*R)*‖U‖*(R*(Z*‖G.B‖))=(↑n^2*R^3)*(‖U‖*Z*‖G.B‖) by ring, heq,Gleam.rate]; exact (mul_le_mul_of_nonneg_right (h₂ n) (by positivity : 0≤‖U‖*Z*‖G.B‖)).trans_eq (by unfold n; ring)
  rw [norm_smul,norm_mul]; refine mul_le_mul_of_nonneg_right (mul_le_mul (glitter_cap he.le (strip_negX hp) _ _) (glitter_cap he.le hp _ _) (norm_nonneg _) (by positivity)) (norm_nonneg _)
end YM.QCD.Pearl
