import YM.DawnS.Trop
import YM.Arise.Rex
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical
local notation "Y"=>Vertex
local notation "P"=>RingS
local notation "B"=>basis timeAxis
local notation "Ω"=>muS
local notation "I₀"=>Complex.I
variable {d:ℕ}(i:Multi d)(a b c e:Pinor)
lemma permutation {i j:Multi d}{a:Axis}(h:AtNext a i j):List.Perm (steps j) (a::steps i):=by
     apply List.perm_iff_count.mpr; intro b; rw[List.count_cons,Arise.spine_code,Arise.spine_code,h]; by_cases he:b=a <;> simp[he] <;> first|rfl|tauto
lemma afterP(p:Multi d)(a:Axis) : (∃ q,AtNext a p q) ↔ UV.order (power p)<d:=by
     constructor
     · rintro ⟨q,hq⟩; rw [← Arise.spine_cost]; have hp:= (permutation hq).length_eq; simp only [List.length_cons] at hp; apply Nat.lt_of_succ_le; exact le_trans hp.symm.le (Arise.spine_cost q |>.trans_le q.property) -- ▸ motive
     intro h; let u:ℕ:= power p a+1
     have hp:power p a ≤ UV.order (power p):= Finset.single_le_sum (fun i _=> Nat.zero_le _) (Finset.mem_univ _)
     let y:= update p.val a (⟨power p a+1, (by omega)⟩ : Fin (d+1)); have he : UV.order (fun i=>(y i).val)≤d:=by
           have ht(b:Axis) : (y b).val= power p b+ if a=b then 1 else 0:=by by_cases h:b=a <;> simp [y,h,power] <;> tauto
           unfold UV.order at *; simp only [ht,sum_add_distrib]; simpa using h
     exact ⟨⟨y,he⟩,funext fun b=>by by_cases h:b=a <;> simp[UV.power,y,h]⟩ -- cleanup
lemma echoUnique {i p q:Multi d}{a:Axis}(hp:AtNext a i p)(hq:AtNext a i q): p=q:= Subtype.ext (funext fun b=>Fin.ext (show power p b= power q b from congr_fun (hp.trans hq.symm) b))
variable {x:E4}(hx:x≠0)
include hx
-- matrix trace skew identity.
noncomputable abbrev hessian (x:E4) (i j:Axis) :ℂ:= (↑(Maxwell.grad i (Maxwell.grad j Maxwell.Green) x) :ℂ) -- namespace grad? 
lemma annul (Q:Axis→Axis→Spike)(p q:Pinor)(h:∀ i j:Axis, Q i j + Q j i = if i=j then 2 else 0) : ∑ i:Axis,∑ j:Axis,(Q i j p q)* (hessian x i j)=0:=by
     let F : Axis→Axis→ℂ:= fun i j=> Q i j p q * hessian x i j; let Z:=∑ i:Axis,∑ j:Axis,F i j
     let C:= (2:Spike) p q; have hf(i j:Axis): F i j+F j i= if i=j then C*hessian x i i else 0:=by
          unfold F; rw [show hessian x j i=hessian x i j from congr_arg _ (Maxwell.Hess_sym hx ..),← add_mul, show Q i j p q+Q j i p q=(Q i j + Q j i) p q from rfl,h]; by_cases he:i=j <;> simp only [he,↓reduceIte] <;> first|rfl|exact zero_mul _
     have hu : Z+Z=0:=by
          have ht:Z = ∑ i:Axis,∑ j:Axis,F j i:=sum_comm
          conv_lhs=>rhs; rw[ht];
          unfold Z; rw [←sum_add_distrib]; simp_rw [←sum_add_distrib,hf]; simp; rw [←mul_sum]; rw[show (∑ i:Axis,hessian x i i)=0 from ?_,mul_zero]; unfold hessian; rw [← Complex.ofReal_sum,Maxwell.harmonic hx];rfl
     rw [← two_mul Z] at hu; exact (mul_eq_zero.mp hu).resolve_left (by norm_num)
-- both col/row slash; matrices orders. want derivatives l commutation no smooth special beyond.G
omit hx in
lemma clays(i j:Axis): (gamma i*gamma j)+(gamma j*gamma i)= if i=j then 2 else 0:=by
    by_cases h:i=j; · subst i; simp [show (1:Spike)+1=2 from (by norm_num)]
    rw[if_neg h,clifford h, neg_add_cancel]
lemma wave_left(p q:Pinor): ∑ i:Axis,∑ k:Pinor,gamma i p k * D (basis i) (dirac k q) x=0:=by
     have h(k:Pinor)(i:Axis) := derived_res k q [i] x hx
     let H:= hessian x; have hp(k:Pinor)(i:Axis) :D (basis i) (dirac k q) x = -∑ a:Axis,gamma a k q * H i a:= h k i
     simp_rw[hp,mul_neg,mul_sum,sum_neg_distrib]; rw [neg_eq_zero]; apply Eq.trans _ (annul hx (fun i j=> gamma i*gamma j) p q (fun i j=> clays i j)); apply sum_congr rfl fun i _=> ?_; rw[sum_comm]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [Matrix.mul_apply,sum_mul]; apply Finset.sum_congr rfl; intro k _; rw[←mul_assoc]
lemma wave_right(p q:Pinor): ∑ i:Axis,∑ k:Pinor,gamma i k q * D (basis i) (dirac p k) x=0:=by
     have h(k:Pinor)(i:Axis) := derived_res p k [i] x hx
     let H:= hessian x; have hp(k:Pinor)(i:Axis) :D (basis i) (dirac p k) x = -∑ a:Axis,gamma a p k * H i a:= h k i
     simp_rw[hp,mul_neg,mul_sum,sum_neg_distrib]; rw [neg_eq_zero]; apply Eq.trans _ (annul hx (fun i j=> gamma j*gamma i) p q (fun i j=>by rw [add_comm]; exact clays i j)); apply sum_congr rfl fun i _=> ?_; rw[sum_comm]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [Matrix.mul_apply,sum_mul]; apply Finset.sum_congr rfl; intro k _; rw[←mul_assoc,mul_comm (gamma i k q) (gamma a p k)]
end YM.DawnS
