import YM.Kwick.Sorrel
/-! Elementary triangular receipts L2. Uniform both orientations.Vector. 
Variant estimates depending grade row tested pre-distances.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Oriole Counting Counting.Click
local notation "Z"=> RawVec 10
variable {d n:ℕ}{a b c j:Axis} (i:Axis)(K:ℕ→Fin 4→Z)(T:Fin 4→ℕ→ℝ)(Y:ℕ→ℝ)(u L Lb G α ε η B0 B E U C m D d₀:ℝ)
noncomputable abbrev blip (K:ℕ→Fin 4→Z)(i:Axis)(v:ℕ):ℝ:= ∑ k:Fin 4,wages i (K v k)
local notation "mP" v:arg k:arg=> wages i (K v k)
local notation "X" v:arg=> blip K i v
-- Y:R.S charge bound.R.Ge formula.Exp. ANY post >0.
structure Bowl (i:Axis)(K:ℕ→Fin 4→Z)(M:ℕ→ℝ)(T:Fin 4→ℕ→ℝ)(n:ℕ)(L α ε:ℝ) : Prop where
    funds (v:ℕ)(h:v ≤ n): blip K i v ≤ M v
    emphasis(v:ℕ)(h:v<n): M v ≤ L* blip K i (v+1) + (1/2:ℝ)*M (v+1)+blip K i v
    curve (k:Fin 4)(v:ℕ)(h:v<n) : wages i (K v k - (T k v:ℂ) • K (v+1) k) ≤ (if k=0 then 0 else α*wages i (K (v+1) 0))+ ε*M (v+1)
variable (hG:0 ≤ G)(hL:0≤L)(hα:0 ≤α)(hε:0≤ε)(hT:0 ≤ η)(h:Bowl i K Y T n L α ε)
lemma paso(t:ℕ)(k:Fin 4): mP t k≤ X t:=single_le_sum (fun u _=>wageG ..) (mem_univ _)
lemma pass(t:ℕ):0≤X t:=sum_nonneg fun i _=>wageG ..
include h
lemma Mp (t:ℕ)(ht:t ≤ n):0≤Y t:=(pass i K _).trans (h.funds t ht)
local notation "τ"=> B+(2*(L+1))*m
variable (hm:∀ v,v ≤ n → blip K i v ≤ m)(hp:Y n ≤ B)
include hm hp hL
lemma startup (v:ℕ)(hv:v ≤ n): Y v ≤ τ:=by
     have hq:0 ≤ m:= (pass i K _).trans (hm v hv); induction hv using Nat.decreasingInduction with
     | self=> exact hp.trans (le_add_of_nonneg_right (by positivity))
     | of_succ i hi ih=> have hb:0 ≤ B:=le_trans (Mp _ _ _ _ _ _ _ h _ le_rfl) hp; have he:= (h.emphasis i hi).trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hm _ hi) hL) (mul_le_mul_of_nonneg_left ih (by norm_num))) (hm _ hi.le)); linarith only[he,hb]
include hε
local notation "ϕ" k:arg v:arg=> wages i (K v k-(T k v:ℂ) • K (v+1) k)
lemma bow0(v:ℕ)(hv:v<n): ϕ 0 v≤ ε*(τ):=le_trans (by simpa only[if_true,zero_add] using h.curve 0 v hv) (mul_le_mul_of_nonneg_left (startup i K T Y L α ε B m hL h hm hp _ hv) hε) -- .. syntax
-- receipts loose. Set budget expansion B0 polynomial in τ, Y.High O(B). Enough with δ shrinking post.
omit h hε hm hp hL
lemma shift_down (k:Fin 4)(v:ℕ) : wages i (K v k-K (v+1) k) ≤ ϕ k v+ |T k v-1| *mP (v+1) k:=by
     let a:= (T k v:ℝ); let p:= K v k; let q:= K (v+1) k; change wages i (p-q) ≤ _
     rw [show p-q=(p-(a:ℂ) • q)+ ((↑(a-1):ℂ)) • q from ?_]; apply (wageA ..).trans_eq; rw [wageS,Complex.norm_real,Real.norm_eq_abs]
     rw [Complex.ofReal_sub, Complex.ofReal_one,sub_smul,one_smul]; abel
include h hε hm hp hL
section backward
variable (ha:1≤ η) -- remove
variable (hk:∀ i,i < n → 2 ≤ T 0 i)(hη:∀ (k:Fin 4),k≠0→∀ i,i<n→ |T k i-1|≤η)(ht:wages i (K 0 0) ≤ E) -- notation binder invalid?
include hk ht
local notation "Φ"=> E+ ε*τ
lemma lightB (j:ℕ)(hj:j≤ n): mP j 0≤ Φ:=by
     have hq:0 ≤ τ:=(Mp i K T Y L α ε h n le_rfl).trans (startup i K T Y L α ε B m hL h hm hp n le_rfl); induction j with
     | zero=> exact ht.trans (le_add_of_nonneg_right (mul_nonneg hε hq))
     | succ j ih=>
          let x:= K j 0; let y:= K (j+1) 0; let b:ℝ:= T 0 j; have hI:mP j 0 ≤ Φ:= ih (by omega : j ≤ n) -- hj.le notation invalid
          have he : wages i ((b:ℂ) • y) ≤ wages i x + wages i (x-(b:ℂ) • y):=calc
               _= wages i (x+ -(x-(b:ℂ) • y)):=by rw [← sub_eq_add_neg,sub_sub_cancel]
               _ ≤ _:= (wageA ..).trans_eq (by rw[wageN])
          have hp0:0 ≤ E:=(wageG ..).trans ht; have hB:0 ≤ b:=by have hh:2≤b:=hk _ hj; positivity
          rw [wageS,Complex.norm_real,Real.norm_of_nonneg hB] at he; have hz:=bow0 i K T Y L α ε B m hL hε h hm hp j hj -- hp shadow
          have ht':2*mP (j+1) 0≤ Φ + ε*τ:= (mul_le_mul_of_nonneg_right (hk j hj) (wageG i y)).trans (he.trans (add_le_add hI hz)); linarith only[hp0, ht']
local notation "Ω"=> α*Φ+ ε*τ+ η*m
include hη hT hα
lemma lacquer(k:Fin 4)(he:k ≠0)(v:ℕ)(h₀:v<n): wages i (K v k-K (v+1) k) ≤ Ω:=by
     apply (shift_down i K T k v).trans; refine add_le_add ((h.curve k v h₀).trans ?_) (mul_le_mul (hη k he v h₀) ((paso i K (v+1) k).trans (hm _ h₀)) (wageG ..) hT)
     rw [if_neg he]; exact add_le_add (mul_le_mul_of_nonneg_left (lightB i K T Y L α ε B E m hL hε h hm hp hk ht _ h₀) hα) (mul_le_mul_of_nonneg_left (startup i K T Y L α ε B m hL h hm hp _ h₀) hε)
lemma marches(k:Fin 4)(he:k≠0)(v:ℕ)(htv:v ≤ n ) : wages i (K v k - K n k)≤ (n-v:ℕ)*Ω:=by
     induction htv using Nat.decreasingInduction with
     | self=> rw[sub_self,wageT,Nat.sub_self,Nat.cast_zero,zero_mul]
     | of_succ v hV ih=> rw [show K v k-K n k=(K v k-K (v+1) k)+(K (v+1) k-K n k) from by abel]; exact (wageA ..).trans ((add_le_add (lacquer i K T Y L α ε η B E m hL hα hε hT h hm hp hk hη ht k he v hV) ih).trans_eq (by rw[show n-v=n-(v+1)+1 from by omega, Nat.cast_add]; push_cast; ring))
-- economic closure.For given m. Standard right bias with floor α*Φ polynomial. If strict estimate obtains w/out hyp global.B.
lemma highAmt (v:ℕ)(hv:v ≤ n): X v ≤ Φ+(3*((n:ℝ)*Ω)+ Y n):=by
     let p:ℝ:= (n:ℝ)*Ω; have hz : ∀ (k:Fin 4),k≠0 → mP v k ≤ mP n k+p:=by
          intro k h0; let x:= K v k; let y:= K n k; change wages i x ≤ _; nth_rw 1[show x=y+(x-y) from by abel]; have hL₀:0 ≤ Φ:=(wageG ..).trans (lightB i K T Y L α ε B E m hL hε h hm hp hk ht v hv); have hL₁:0 ≤ m:= (pass i K _).trans (hm _ hv); have hQ:0 ≤ B:= le_trans (Mp _ _ _ _ _ _ _ h _ le_rfl) hp
          refine (wageA ..).trans (add_le_add_right ((marches i K T Y L α ε η B E m hL hα hε hT h hm hp hk hη ht k h0 v hv).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by positivity))) _) -- order
     have hq:= h.funds n le_rfl; change (∑ k:Fin 4,_:ℝ) ≤_ at hq; unfold blip; rw [Fin.sum_univ_four] at hq ⊢; linarith only [hq,hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),wageG i (K n 0),lightB i K T Y L α ε B E m hL hε h hm hp hk ht v hv]
end backward
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.bow0
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.highAmt
