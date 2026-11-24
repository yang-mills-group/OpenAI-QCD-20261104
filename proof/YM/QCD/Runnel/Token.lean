import YM.QCD.Runnel.Frost

/-!
# Anchored block kernel bookkeeping. Gauge law per label. Finite support aggregation; labels
live on a volume-independent tube. Budgets paid separately in rows and columns. Sym can later
be imposed on aggregated values at settled fields.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Run
open Lat Lattice Gauge Wilson Cost Function Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {f : Side} {D E F : Type*} [Fintype D] [Fintype E] [Fintype F] [DecidableEq D] [DecidableEq E]
variable {x : D→Site f} {y : E→Site f} {z : F→Site f}
variable {δ b R R' S S' : ℝ} {B : ℕ}

abbrev ArrayL (D E : Type*) := Matrix (D×Fiber) (E×Fiber) ℂ

def cell (M : ArrayL D E) (i : D) (j : E) := Matrix.of fun a r : Fiber=> M (i,a) (j,r)
lemma cell_mul (M : ArrayL D E) (N : ArrayL E F) (i j): cell (M*N) i j=∑ k:E, cell M i k*cell N k j:=by
  ext a r; rw [Matrix.sum_apply]; change ∑ _, _= _; rw [Fintype.sum_prod_type]; rfl
lemma cell_add (M N : ArrayL D E) (i j): cell (M+N) i j=cell M i j+cell N i j:=rfl
lemma cell_one (i j : D): cell (1:ArrayL D D) i j=if i=j then 1 else 0:=by
  split_ifs with h
  · subst j; ext; simp [cell,Matrix.one_apply]
  ext; simp [cell,h,Matrix.one_apply]
lemma cell_scale (M : ArrayL D E) (p : ℂ) (i j) : cell (p • M) i j=p • cell M i j :=rfl
lemma cell_flip (M : ArrayL D E) (i j): cell Mᴴ i j=star (cell M j i):=rfl

def Crop (p q : Site f) (δ : ℝ) (S : Support f) (M : Pulse f→Bundle) (m : ℝ) : Prop:=
  0≤m ∧ (m≠0 → p∈S∧q∈S) ∧
  (∀ Z∈Kingdom f δ, DifferentiableAt ℂ M Z) ∧ (∀ Z∈Kingdom f δ, ‖M Z‖≤m) ∧
  LocalOn S (M∘settled) ∧ (∀ U (k : Lat.Frame f), M (settled (gauge k U))=
    touch (colour (k p))*M (settled U)*star (touch (colour (k q))))
namespace Crop
variable {p q r : Site f} {P Q : Support f} {X Y : Pulse f→Bundle}
lemma zero : Crop p q δ P 0 0:=⟨le_rfl,(fun h=>absurd rfl h), (fun Z _=>differentiableAt_const _), (fun _ _=> by simp), (fun _ _ _=>rfl),fun _ _=> by simp⟩
lemma plus (h : Crop p q δ P X R) (e : Crop p q δ P Y S) : Crop p q δ P (X+Y) (R+S):=by
  rcases h with ⟨h,hp,hh,hs,hL,hG⟩; rcases e with ⟨e,ep,eh,es,eL,eG⟩
  refine ⟨add_nonneg h e, fun a=> ?_,(fun i v=> (hh i v).add (eh i v)),(fun i v=> (norm_add_le ..).trans (add_le_add (hs i v) (es i v))),fun U V H=> congr_arg₂ (·+·) (hL U V H) (eL U V H),fun U k=>by simp only [Pi.add_apply,hG,eG,mul_add,add_mul]⟩
  by_cases he : R=0; · apply ep (fun h=> a (by rw [he,h,add_zero]))
  exact hp he
lemma alloy (h : Crop p q δ P X R) (m : ℂ): Crop p q δ P (m • X) (‖m‖*R):=by
  rcases h with ⟨h,p,hh,hs,hL,hG⟩; refine ⟨by positivity,fun hm=>p (fun he=>hm (by rw [he,mul_zero])),fun i hi=> (hh i hi).const_smul m,fun i hi=>?_, fun U V H=>congr_arg (m • ·) (hL U V H), fun U k=>by simp only [Pi.smul_apply,hG, Matrix.mul_smul,Matrix.smul_mul]⟩
  rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hs i hi) (norm_nonneg _)
lemma joined (h : Crop p r δ P X R) (e : Crop r q δ Q Y S) (hd : 0<δ) : Crop p q δ (P∪Q) (X*Y) (R*S):=by
  rcases h with ⟨h,hp,hh,hs,hL,hG⟩; rcases e with ⟨e,ep,eh,es,eL,eG⟩
  have hu (k : Lat.Frame f):star (touch (colour (k r)))*touch (colour (k r))=1:= (touch_u (x:=colour (k r)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩).1
  refine ⟨mul_nonneg h e, fun a=>⟨mem_union_left _ (hp (fun b=>a (by rw [b,zero_mul]))).1,mem_union_right _ (ep (fun b=>a (by rw [b,mul_zero]))).2⟩,fun i hw=> (hh i hw).mul (eh i hw),fun i hw=> (norm_mul_le ..).trans (mul_le_mul (hs i hw) (es i hw) (by positivity) h),fun i j hv=> congr_arg₂ (·*·) (hL i j (agrees_mono hv (fun w hw=>mem_union_left _ hw))) (eL i j (agrees_mono hv (fun w hw=>mem_union_right _ hw))),fun i k=>?_⟩
  simp only [Pi.mul_apply,hG,eG,mul_assoc]; rw [← mul_assoc (star (touch (colour (k r)))) (touch (colour (k r))),hu,one_mul]
lemma cluster {A : Type*} (L : Finset A) {M : A→Pulse f→Bundle} {m : A→ℝ} (h : ∀ i∈L, Crop p q δ P (M i) (m i)): Crop p q δ P (∑ i∈L, M i) (∑ i∈L,m i):=by
  classical
  induction L using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact zero
  | insert a L ha ih=> rw [sum_insert ha,sum_insert ha]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=>h i (mem_insert_of_mem hi))) -- check args
lemma rent_sum {A : Type*} (U : Finset A) (P : Support f) (M : A→ℝ) : rent b B P * ∑ j∈U,M j=∑ j∈U,rent b B P*M j:=Finset.mul_sum .. -- b B omit
lemma church {A : Type*} (m : A→ℝ) {M : A→Pulse f→Bundle} (hm : Summable m) (h : ∀ i, Crop p q δ P (M i) (m i)) (hd : 0<δ): Crop p q δ P (fun Z=>∑' i, M i Z) (∑' i,m i):=by
  have hu i := (h i).2.2.2
  have ht (Z) (hz : Z∈ Kingdom f δ) := (hm.of_norm_bounded (f:=fun i=>M i Z) fun i=> (hu i).1 Z hz)
  refine ⟨tsum_nonneg fun i=> (h i).1,?_,frosty M (country _ _) (fun i=> (h i).2.2.1) hm (fun i=> (hu i).1),fun Z hz=> ?_,fun X Y H=> tsum_congr (fun i=> (hu i).2.1 X Y H), fun U k=> ?_⟩
  · intro v; by_contra he; apply v; simp_rw [fun i=> by_contra fun hi=>he ((h i).2.1 hi)]; rw [tsum_zero]
  · have hs : Summable fun i=>‖M i Z‖:= hm.of_nonneg_of_le (fun i=>norm_nonneg _) fun i=>(hu i).1 Z hz
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum (fun i=> (hu i).1 Z hz) hm)
  dsimp only
  simp_rw [fun i=>(hu i).2.2 U k]
  rw [Summable.tsum_mul_right, (ht _ (citizenship f hd U)).tsum_mul_left]; exact (ht _ (citizenship f hd U)).mul_left _
end Crop
abbrev Land (f : Side) (D E : Type*):= D→E→Support f→Pulse f→Bundle
abbrev Pays (f : Side) (D E : Type*):= D→E→Support f→ℝ
def duel (Y : Pays f D E) (i j) (b : ℝ) (B : ℕ):= ∑ P,rent b B P*Y i j P
structure Pack (x : D→Site f) (y : E→Site f) (δ b : ℝ) (B : ℕ) (M : Grid f→ArrayL D E) (R : ℝ) (X : Land f D E) (Y : Pays f D E) : Prop where
  crop (i j S): Crop (x i) (y j) δ S (X i j S) (Y i j S)
  sells (i j U): (∑ S : Support f,X i j S (settled U))=cell (M U) i j
  spends (i): ∑ j, duel Y i j b B ≤ R
  dues (j): ∑ i, duel Y i j b B ≤ R

def Heritage (x : D→Site f) (y : E→Site f) (δ b : ℝ) (B : ℕ) (M : Grid f→ArrayL D E) (R : ℝ) := ∃ X Y, Pack x y δ b B M R X Y
end YM.QCD.Run
