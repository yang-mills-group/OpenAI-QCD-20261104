import YM.QCD.Nola.Faze
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Nola
open Lattice Function NormedSpace Filter Relation RG Finset
open GasP Push.AbsoluteSums Partition Graph Ursell Gas Trees Coef Cove Grass Creek
open scoped BigOperators Classical Topology ContDiff
variable {ι κ A B:Type*} {n : Side} {m:ℕ} [Fintype A]{s t a χ δ v C H η b:ℝ}
open Kites Pads Creek.Ledge
-- kernel footprints. need region norm as direct sum of abs mon.Co.
def grainH (p:A→Site n)(X:Alg A)(v:ℝ)(m:ℕ)(i: Finset A):ℝ:= ‖coef i X‖ *v^i.card *tell (edges p i) m
abbrev soilH (p:A→Site n)(X:Alg A)(v:ℝ)(m:ℕ) (x: Site n):ℝ:=∑ i: Finset A, if x∈edges p i then grainH p X v m i else 0
lemma grains (p:A→Site n)(X:Alg A)(hv:0<v)(i:Finset A):0 ≤ grainH p X v m i:=by unfold grainH; exact mul_nonneg (by positivity) (zero_le_one.trans (tell_one ..))
variable (p: Pairs A→Site n)(V:Matrix A A ℂ)(X:Patio (Pairs A))
def taxS (t:ℝ): Peak (Pairs A)⊕(A×A)→ ℝ:= Sum.elim (fun i=> ‖tyre t ((mist p X V).source i)‖) (fun i=>‖V i.1 i.2‖ * t⁻¹^2)
def scaleS (t χ:ℝ)(m:ℕ):Peak (Pairs A)⊕(A×A)→ℝ:= fun i=>(if i.isLeft then χ⁻¹ else 1) *taxS p V X t i*tell ((mist p X V).leaves i) m
lemma tax_pos i:0 ≤ taxS p V X t i:=by cases i <;> first| exact norm_nonneg _ | exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
lemma scale_pos (hv:0≤χ) (m t' :ℕ)(i: Peak (Pairs A)⊕(A×A)) : 0 ≤ scaleS p V X t χ m i:=by
   unfold scaleS; refine mul_nonneg (mul_nonneg ?_ (tax_pos ..)) (zero_le_one.trans (tell_one ..)); split <;> positivity
lemma spices (i : Peak (Pairs A)) (ht:0 < t): taxS p V X t (.inl i)= ‖coef i.val X.val‖* t^i.val.card:=by
    change ‖engine t _ (coef i.val X.val • mono i.val)‖= _; rw [map_smul, nominate (mono i.val) t _ (homogeneous i.val),norm_smul,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht.le,norm_mono,mul_one]
lemma recoup (hv:0< t)(he:s=Real.exp 2*t)(hχ:0 ≤ χ)(k:Peak (Pairs A)) : scaleS p V X t χ m (.inl k)*currencyCard 2 ((mist p X V).leaves (.inl k))≤χ⁻¹ * grainH p X.val s m k.val:=by
    subst s; unfold scaleS currencyCard; rw [show Sum.isLeft (.inl k:Peak _ ⊕ (A × A))=true from rfl, if_pos rfl,spices p V X k hv]
    have he : #((mist p X V).leaves (.inl k)) ≤ k.val.card:= card_image_le
    unfold grainH; rw [mul_pow,← Real.exp_nat_mul];
    apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_comm (2:ℝ) _|>.trans_le (mul_le_mul_of_nonneg_right ((Nat.cast_le (α:=ℝ)).mpr he) (by norm_num)))) (show 0 ≤ (χ⁻¹ * (‖coef k.1 X.val‖* t^_) * tell _ m) from mul_nonneg (by positivity) (zero_le_one.trans (tell_one ..))))
    change _* Real.exp (↑k.val.card*2)≤ χ⁻¹ * (‖coef k.1 _‖*(Real.exp _* _)*tell ((mist p X V).leaves (.inl k)) m); apply le_of_eq; ring -- inspect
-- operator pair sum supplied
abbrev rayK (p:Pairs A→Site n)(V: Matrix A A ℂ)(m:ℕ)(x:Site n):ℝ:= ∑ i:A×A, let E:= poly p (.inr i); if x∈ E then ‖V i.1 i.2‖*tell E m else 0
lemma June (hx:∀ i,rayK p V m i ≤ b) (x:Site n): ∑ i:A × A,(if x∈ poly p (.inr i) then scaleS p V X t χ m (.inr i)*currencyCard 2 (poly p (.inr i)) else 0) ≤ t⁻¹^2*Real.exp 4*b:=by -- b implicit
    apply le_trans _ (mul_le_mul_of_nonneg_left (hx x) (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)); unfold rayK; rw [mul_sum]; apply sum_le_sum; intro i _; dsimp only; split
    next H=> have he : currencyCard 2 (poly p (.inr i)) ≤ Real.exp 4:=Real.exp_le_exp.mpr (by
                   have hp : # (poly p (.inr i)) ≤ 2:= card_le_two; have hx:((#(poly p (.inr i))):ℝ)≤2:=by exact_mod_cast hp
                   linarith)
             let Y:= poly p (.inr i); change 1*(‖V _ _‖*t⁻¹^2)*tell Y m*_ ≤ _ -- not defeq cond
             refine (mul_le_mul_of_nonneg_left he (mul_nonneg (by positivity: 0 ≤ 1*(‖V i.1 i.2‖*t⁻¹^2)) (zero_le_one.trans (tell_one ..)))).trans ?_; unfold Y; apply le_of_eq; ring
    next H=> simp
end YM.QCD.Nola
