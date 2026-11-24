import YM.QCD.Pearl.Spring

/-! # uniform widths for summed functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Function Filter Finset Metric Lat Rudder Kit RG Laurent Bloch Flume
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker Topology
variable {n : Side} {I J: Type} {m : ℕ} {η : ℝ} {p k : Momentum} (C : su.Color)
lemma heft (W:Bloom m)(he: 0<η)(hp:p∈strip η)(a:Axis): ‖glitter W.tail p a‖≤ W.span*Real.exp (η * W.span) :=by
  apply (glitter_cap he.le hp W.tail _).trans; have hh : W.tail.length≤W.span:=Nat.le_add_right ..; gcongr
lemma wear (W:Bloom m)(he: 0<η)(hk:k∈strip η): ‖wane k W.tail‖≤Real.exp (η * W.span):=by apply (wane_size he.le hk _).trans; gcongr; exact Nat.le_add_right ..
lemma knoll (he:0<η): ∃ K:ℝ,0≤K ∧ ∀ (V:Bloom 1)(W:Bloom 2),∀ p k:Momentum,p∈strip η→k∈strip η→∀ i,
    ‖nil₁ C V i p k‖≤K*V.paid (4*η) ∧ ‖yet₁ C V i p k‖≤ K*V.paid (4*η) ∧ ‖yet₂ C W i p k‖≤ K*W.paid (4*η):=by
  obtain ⟨A,hA,h₁⟩:= length_gift he 1; obtain ⟨B,hB,hv⟩:= blossomC C 1; obtain ⟨D,hD,hw⟩:=blossomC C 2
  let U:= touch (echo C); let T:=4*B+8*B*A*‖U‖+32*D
  refine ⟨T,by unfold T; positivity,fun V W p k hp hk i=>?_⟩
  have hvp:= V.price_nn; have hwp := W.price_nn
  let R := Real.exp (η*V.span); let S:=Real.exp (η*W.span); have hr:1≤R:=Real.one_le_exp (by positivity); have hs:1≤S:=Real.one_le_exp (by positivity)
  -- m polymorphism? hh m fixed
  have hT:V.paid (4*η)=R^4*V.price:=by unfold R Bloom.paid; rw [← Real.exp_nat_mul]; push_cast; rw [mul_assoc 4]
  have hS:W.paid (4*η)=S^4*W.price:=by unfold S Bloom.paid; rw [← Real.exp_nat_mul]; push_cast; rw [mul_assoc 4]
  rw [hT,hS]
  constructor
  · have he': ‖nil₁ C V i p k‖≤4*R*(B*V.price)*R:=by unfold nil₁; apply (norm_mul_le ..).trans; rw [norm_smul]; exact mul_le_mul (mul_le_mul (hap V i hp he.le 0) (hv V) (norm_nonneg _) (by positivity)) (wear V he hk) (by positivity) (by positivity)
    apply he'.trans; rw [show 4*R*(B*V.price)*R=4*B*(R^2*V.price) by ring]; refine mul_le_mul ?_ ?_ (by positivity) (by unfold T; positivity)
    · unfold T; linarith [mul_nonneg (show 0≤8*B*A by positivity) (norm_nonneg U)]
    gcongr; norm_num
  constructor
  · have hh1: ‖hack (V.petals 0) p i*glitter V.tail (-p) i+hack (V.petals 0) (-p) i*glitter V.tail p i‖≤4*R*(V.span*R)+4*R*(V.span*R):= (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (hap V i hp he.le 0) (heft V he (strip_negX hp) i) (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul (hap V i (strip_negX hp) he.le 0) (heft V he hp i) (norm_nonneg _) (by positivity))))
    have hL : ((V.span:ℝ)*R^3) ≤ A*R^4:=by have ht:=h₁ V.span; rw [pow_one] at ht; unfold R; simp_rw [← Real.exp_nat_mul]; push_cast; simpa only [mul_assoc] using ht
    apply (norm_mul_le ..).trans; rw [norm_smul]; apply (mul_le_mul (mul_le_mul hh1 ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right (hv V) (norm_nonneg U))) (by positivity) (by positivity)) (wear V he hk) (norm_nonneg _) (by positivity)).trans
    change _*R ≤ _; calc
      _ = (↑V.span*R^3)*(8*B*‖U‖*V.price):= by ring
      _ ≤ A*R^4*(8*B*‖U‖*V.price):= mul_le_mul_of_nonneg_right hL (by positivity)
      _ = (8*B*A*‖U‖)*(R^4*V.price):= by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (show 8*B*A*‖U‖ ≤ T by unfold T; linarith) (by positivity)
  have hh2: ‖hack (W.petals 0) p i*hack (W.petals 1) (-p) i+ hack (W.petals 0) (-p) i*hack (W.petals 1) p i‖ ≤ (4*S)*(4*S)+(4*S)*(4*S):= (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (hap W i hp he.le _) (hap W i (strip_negX hp) he.le _) (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul (hap W i (strip_negX hp) he.le _) (hap W i hp he.le _) (norm_nonneg _) (by positivity))))
  apply (norm_mul_le ..).trans; rw [norm_smul]; apply (mul_le_mul (mul_le_mul hh2 (hw W) (norm_nonneg _) (by positivity)) (wear W he hk) (norm_nonneg _) (by positivity)).trans
  change _ *S≤_
  calc _ = 32*D*(S^3*W.price):= by ring
       _ ≤ _ := by apply mul_le_mul _ _ (by positivity) (by unfold T; positivity); · unfold T; linarith [mul_nonneg (show 0≤8*B*A by positivity) (norm_nonneg U)]
                   gcongr; norm_num
@[fun_prop] lemma flash_d (i : Axis) (x:Edge Cover): Differentiable ℂ (fun p=> flash p i x):=by
  unfold flash; split; · unfold mode; fun_prop
  exact differentiable_const _
@[fun_prop] lemma frisk (x:Cover)(i:Axis)(w):Differentiable ℂ (fun p=> bill (flash p i) x w):=by
  induction w generalizing x with
  | nil=> exact differentiable_const _
  | cons a w ih=> simp_rw [bill]; split <;> fun_prop
@[fun_prop] lemma wane_d (w:Walk): Differentiable ℂ (fun p=> wane p w):=by unfold wane mode; fun_prop
lemma b₁d (G:Gleam)(i): Differentiable ℂ (fun v : Momentum × Momentum=> boom₁ C G i v.1 v.2):= by
  unfold boom₁ boom glitter; exact (((frisk (0:Cover) i G.w).comp differentiable_fst).smul_const _).mul (((wane_d G.w).comp (differentiable_snd)).mul_const _)
lemma b₂d (G:Gleam)(i): Differentiable ℂ (fun v : Momentum×Momentum=>boom₂ C G i v.1 v.2):= by
  unfold boom₂ boom glitter; exact ((((frisk (0:Cover) i G.w).comp differentiable_fst.neg).mul ((frisk (0:Cover) i G.w).comp differentiable_fst)).smul_const _).mul (((wane_d G.w).comp (differentiable_snd)).mul_const _)
lemma nil_d (W: Bloom 1)(i): Differentiable ℂ (fun v : Momentum×Momentum=>nil₁ C W i v.1 v.2):= by
  unfold nil₁ hack; exact (((frisk (W.petals 0).offset i (Lattice.square (W.petals 0).plaq.val.1 (W.petals 0).plaq.val.2)).comp differentiable_fst).smul_const _).mul ((wane_d W.tail).comp (differentiable_snd))
lemma y₁d (W: Bloom 1)(i): Differentiable ℂ (fun v : Momentum×Momentum=>yet₁ C W i v.1 v.2):= by
  unfold yet₁ hack glitter; exact (((((frisk (W.petals 0).offset i (Lattice.square (W.petals 0).plaq.val.1 (W.petals 0).plaq.val.2)).comp differentiable_fst).mul ((frisk (0:Cover) i W.tail).comp differentiable_fst.neg)).add (((frisk (W.petals 0).offset i (Lattice.square (W.petals 0).plaq.val.1 (W.petals 0).plaq.val.2)).comp differentiable_fst.neg).mul ((frisk (0:Cover) i W.tail).comp differentiable_fst))).smul_const _).mul ((wane_d W.tail).comp (differentiable_snd))
lemma y₂d (W: Bloom 2)(i): Differentiable ℂ (fun v : Momentum×Momentum=>yet₂ C W i v.1 v.2):= by
  unfold yet₂ hack; exact (((((frisk (W.petals 0).offset i (Lattice.square (W.petals 0).plaq.val.1 (W.petals 0).plaq.val.2)).comp differentiable_fst).mul ((frisk (W.petals 1).offset i (Lattice.square (W.petals 1).plaq.val.1 (W.petals 1).plaq.val.2)).comp differentiable_fst.neg)).add (((frisk (W.petals 0).offset i (Lattice.square (W.petals 0).plaq.val.1 (W.petals 0).plaq.val.2)).comp differentiable_fst.neg).mul ((frisk (W.petals 1).offset i (Lattice.square (W.petals 1).plaq.val.1 (W.petals 1).plaq.val.2)).comp differentiable_fst))).smul_const _).mul ((wane_d W.tail).comp (differentiable_snd))
end YM.QCD.Pearl
