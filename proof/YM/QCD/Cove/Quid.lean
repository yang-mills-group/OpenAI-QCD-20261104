import YM.QCD.Cove.Low
/-! # money. Nonneg throughout, nearest bad short-particle penalty charged via K inventory. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj Filter
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator

variable {A: Type*}[Fintype A]{D E J:Type}
variable {f c: Side}{S: Ratio c f}{F:ℕ}{t l T u h h' a:ℝ}{q:ℕ}
lemma pledge_spin (w:Finset D) (x:D→EndA A)(g: A→ℝ)(p:D→ℝ)(hp:∀ i∈w,Ledge.Pledge g (x i) (p i))(ht:(w:Set _).Pairwise fun i j=> Commute (x i) (x j)): Ledge.Pledge g (w.noncommProd x ht) (∏ i∈w,p i):=by
  induction w using Finset.induction_on with
  | empty=> simp only [noncommProd_empty,prod_empty]; exact ⟨zero_le_one,by intro u; simp⟩
  | insert i s hi ih=>
    rw [noncommProd_insert_of_notMem _ _ _ ht hi,prod_insert hi]; apply (hp i (mem_insert_self ..)).combines; exact ih (fun j hj=> hp j (mem_insert_of_mem hj)) _

lemma bought (g:A→ℝ)(x: Patio A)(z:ℝ)(h: load g (light _ x)≤z): load g (light A (NormedSpace.exp x-1))≤Real.exp z-1:=by
  rw [map_sub,map_one,light_exp]; let X:= light A x; let T (n:ℕ): Alg A:= (n.factorial:ℂ)⁻¹ • X^n; let Z (n:ℕ):=(n.factorial:ℝ)⁻¹*z^n
  have hz:0≤z:=(load_nn ..).trans h; have ht : HasSum T (NormedSpace.exp X):=exp_series_hasSum_exp' X
  have hp : HasSum Z (Real.exp z):=by rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (𝕂:=ℝ) z
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show T 0=1 by simp [T]] at ht
  rw [← hasSum_nat_add_iff' (k:=1),sum_range_one,show Z 0=1 by simp [Z]] at hp
  have he n : load g (T n)≤Z n := by
    have hv n:load g (X^n)≤z^n:=by induction n with
      | zero=> simp [load_one]
      | succ n ih=> rw [pow_succ,pow_succ]; exact (load_mul ..).trans (mul_le_mul ih h (load_nn ..) (pow_nonneg hz _))
    dsimp only [T,Z]; rw [load_scale]; simpa using mul_le_mul_of_nonneg_left (hv n) (by positivity : 0 ≤ (n.factorial:ℝ)⁻¹)
  exact le_of_tendsto_of_tendsto' ((payload g).continuousAt.tendsto.comp ht) (hp) (fun s:Finset ℕ=> (load_sum g s (fun n=> T (n+1))).trans (sum_le_sum fun k _=>he _))
lemma funded (g:A→ℝ)(s:Finset D)(x:D→ Patio A)(p:D→ℝ) (hp: ∀ i ∈s,load g (light _ (x i))≤p i): load g (light _ (∏ i∈s,x i))≤∏ i∈s,p i:=by
  induction s using Finset.induction_on with
  | empty=> simp only [prod_empty,map_one,load_one]; exact le_rfl
  | insert i s hi ih=>
    rw [prod_insert hi,prod_insert hi,map_mul]; have he:=hp _ (mem_insert_self ..); exact (load_mul ..).trans (mul_le_mul he (ih fun i hi=> hp i (mem_insert_of_mem hi)) (load_nn ..) ((load_nn ..).trans he))

lemma inflated [DecidableEq A] (Q:Finset A)(R V: Finset A)(G:A→ℝ)(t:ℝ)(hp:1≤t)(he:0≤ G):
    let Y (i:A):=if i∈V then t*G i else G i
    ∏ i∈Q,Y i ≤ (t)^V.card * ∏ i∈Q,G i := by
  intro Y; let w (i:A):= if i∈V then t else 1
  have hh:Y=fun i=>w i * G i:=by funext i; unfold Y w; split <;> simp
  rw [hh,prod_mul_distrib]
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _=> he i)
  rw [show ∏ i∈Q,w i=∏ i∈Q with i∈V,t from (prod_filter ..).symm]
  rw [prod_const]; apply pow_le_pow_right₀ hp (Finset.card_le_card ?_); exact fun i hi=> (mem_filter.mp hi).2 -- prod_const form?

lemma sail [DecidableEq A] (Q: Finset A)(g:A→ℝ)(z:ℝ)(hp:∀ i, 0<g i)(he:1≤z)(x:Alg A): load (fun i=> if i∈Q then z*g i else g i) x ≤ z^Q.card * load g x:=by
  let w (i:A):= if i∈Q then z*g i else g i; have hz:∀ i,0<w i:= fun i=> by unfold w; split; exact mul_pos (by linarith) (hp i); exact hp _
  change load w x≤_; rw [dry w hz, dry g hp, mul_sum]; refine sum_le_sum fun i _=> ?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (inflated i Q Q g z he (fun i=> (hp i).le)) (norm_nonneg _)

lemma boarded (x:Alg A): x ∈ region (univ: Finset A):=by
  let V:A→↥(univ: Finset A):= fun i=> ⟨i,mem_univ _⟩
  exact ⟨embed V x,(embed_comp ..).trans (show embed id x=x by rw [embed_id]; rfl)⟩
-- currency mixed weight functions
local notation "I"=> Fj D E J
def wages (h h':ℝ) (M: Type*) (N:Type*) : Pairs (M⊕N) → ℝ:=Sum.elim (Sum.elim (fun _=>h) (fun _=>h')) (Sum.elim (fun _=>h) (fun _=>h'))
lemma wagesA {Q : Type*}(R: Type*) (x:Pairs Q)(h h') : wages h h' Q R (head Q R x)=h:=by cases x<;>rfl
lemma wagesB {Q : Type*}(P:Type*)(x:Pairs Q)(h h') : wages h h' P Q (tail P Q x)=h':=by cases x <;>rfl

local notation "Uj"=> Modes f F
local notation "Uc"=> Modes c F
abbrev rateF (c f:Side)(F:ℕ)(h h':ℝ):=wages h h' (Modes f F) (Modes c F)
-- arbitrary O basis adaptable. h' reserves
variable (G : Send S F D) (P : Rise f F E J)

def priceSet (x: Finset (Fj D E J))(μ:D→ℝ)(β:E→ℝ)(φ:J→ℝ):ℝ:= (∏ i∈ops x,μ i)*((∏ i∈leftE x,(Real.exp (β i)-1))*∏ j∈spent x,φ j)

lemma makes (μ:D→ℝ)(β:E→ℝ)(φ:J→ℝ)(hh:0<h)(s:Finset I)(U:Grid f)
   (hμ:∀ i∈ops s,Ledge.Pledge (rateF c f F h h') (bucks G i U) (μ i)) (hβ:∀ i∈leftE s,load (fun _=>h) (light _ (P.reading t U i))≤β i)
   (hφ: ∀ i∈spent s, load (fun _=>h) (light _ (P.plug i U))≤ φ i): load (rateF c f F h h') (light _ (crate G P t s U))≤priceSet s μ β φ:=by
  let x : Uj→ ℝ:=fun _=>h
  let f := rateF c f F h h'; let T:=light _ (made P t U s)
  have he:Ledge.Pledge f (axle G U s) (∏ i∈ops s,μ i):=pledge_spin (ops s) _ f μ hμ _ -- unsolved proof?
  have hr : load f (near Uj Uc T)≤ load (fun _=>h) T:= ferry (near Uj Uc) (fun _=>hh) (fun i _=>by
    have hv: near Uj Uc (atom i)=atom (head Uj Uc i):=embed_atom (head Uj Uc) _; rw [hv]; unfold Creek.load wscale; rw [change_atom]; simp only [Matrix.diagonal_apply,ite_smul,zero_smul,Fintype.sum_ite_eq,norm_smul,norm_atom,mul_one,Complex.norm_real,show f _ = _ from wagesA Uc i h h',Real.norm_of_nonneg hh.le]; exact le_rfl) T (boarded T) -- overpermissibility f negative?' 
  have hz:=funded (fun _=>h) (leftE s) (fun i=> exp (P.reading t U i)-1) (fun i=>Real.exp (β i)-1) (fun i hi=> bought _ _ _ (hβ i hi))
  have ht : load (fun _=>h) T ≤ (∏ i∈leftE s,(Real.exp (β i)-1))*∏ i∈ spent s,φ i:=by
    unfold T made; rw [map_mul]; exact (load_mul ..).trans (mul_le_mul hz (funded _ (spent s) _ _ hφ) (load_nn ..) ((load_nn ..).trans hz))
  exact (he.rates _).trans (mul_le_mul_of_nonneg_left (hr.trans ht) he.nn)

end YM.QCD.Cove
