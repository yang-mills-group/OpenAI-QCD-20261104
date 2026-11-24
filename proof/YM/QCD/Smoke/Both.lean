import YM.QCD.Garden.Temple

/-! # Install doubly differing scalar curvature patterns at true offsets.

Actual all-fields action uses ordinary covariant plaquette atoms, not shifted
gradients without rebasing. Equality of *linear-flux* readings only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Smoke
open Lattice Wilson Finset Filter Function Metric Extra Iteration RG Placement
open scoped Matrix BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {n:Side}{I:Type*}{η σ A C:ℝ}{G:Gauge}{k:ℕ}
abbrev PairG (G:Gauge):= Pattern G 2
def Palisade (R:I→PairG G)(σ A:ℝ):= (∀ i,both (R i)) ∧(∀ i,(R i).atom.Invariant)∧ Charged (fun i=>(R i).atom) σ A
def shear (p : Option Axis) (i:Bool): ℝ:=p.elim (if i then 0 else 1) (fun _ => if i then 1 else -1)
def pebble (p: Option Axis)(i:Bool): Cover:=p.elim 0 (fun j=> if i then step j else 0)
abbrev BranchG (k:ℕ):= Fin k → Bool
def cartoon (P:Pattern G k)(i:BranchG k):Atom G k:=relocate P.atom (∏ j,shear (P.op j) (i j)) (fun j=>(P.atom.leg j).offset+pebble (P.op j) (i j)) (fun j=>(P.atom.leg j).plaq)
lemma cartoon_sample (P: Pattern G k)(V:Iteration.Flux G n)(x:Site n): P.sample V x=∑ p,(plain (cartoon P p)).sample V x:=by
  let K (b:Fin k→G.ColorIndex) (j:Fin k) i:=shear (P.op j) i * V (P.atom.leg j).plaq (b j) (x+wrap n ((P.atom.leg j).offset + pebble (P.op j) i))
  have hh (b:Fin k→G.ColorIndex) (j:Fin k) : Iteration.read (P.op j) (V (P.atom.leg j).plaq (b j)) (x+wrap n (P.atom.leg j).offset)=∑ i,K b j i:=by
    cases h:P.op j <;> simp [K,shear,pebble,Iteration.read,h,Iteration.grad,add_assoc,sub_eq_add_neg]
  have hu (p: BranchG k): (plain (cartoon P p)).sample V x=∑ b,P.atom.coeff b *∏ j,K b j (p j):=by
    unfold K; unfold Pattern.sample plain cartoon relocate; simp only [slot_offset,slot_plaq,Iteration.read,Option.elim,prod_mul_distrib]; apply sum_congr rfl; intros; ring
  simp_rw [hu]; rw [sum_comm]; simp_rw [Pattern.sample,hh,Fintype.prod_sum,mul_sum]
lemma pebble_fit (p:Option Axis)(i:Bool): Laurent.size (pebble p i)≤ 1:=by
  have h (x:Axis) : Laurent.size (step x : Cover)=1:=step_size (posDir x)
  have hx : Laurent.size (0:Cover)=0:=by simp [Laurent.size]
  cases i <;> cases p <;> simp [pebble,h,hx]
lemma shear_fit (p:Option Axis)(i:Bool): |shear p i|≤1:=by cases p <;> cases i <;> simp [shear]
lemma cartoons (P: Pattern G k)(b:BranchG k): (cartoon P b).length≤ P.atom.length + 8*k :=by
  unfold cartoon; rw [relocated_length]
  have hh (i:Fin k): Laurent.size ((P.atom.leg i).offset+pebble (P.op i) (b i)) ≤ (P.atom.leg i).length+4:=by
    have ht:=Laurent.size_add (P.atom.leg i).offset (pebble (P.op i) (b i)); have hh:= pebble_fit (P.op i) (b i); have hy:=offset_size (P.atom.leg i); unfold Slot.length; omega
  have hp:=sum_le_sum (s:=univ) (fun i _=> hh i); rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hp; unfold Atom.length; simp only [Nat.cast_id] at hp; omega
lemma cartoon_price (P:Pattern G k)(hs:0 ≤ σ):Charged (cartoon P) σ ((Fintype.card (BranchG k):ℝ)*(Real.exp (σ*(8*k))*P.atom.budget σ)):=by
  have hp : 0≤P.atom.budget σ:=by unfold Atom.budget Atom.magnitude; positivity
  apply Cost.mono (g:=fun _ => Real.exp (σ*(8*k))*P.atom.budget σ) (Cost.finite _ (mul_nonneg (Real.exp_pos _).le hp)) (fun i=> by unfold Atom.budget Atom.magnitude; positivity)
  intro i
  have hu : (cartoon P i).magnitude≤P.atom.magnitude:=by
    unfold cartoon; rw [relocated_coeff,Finset.abs_prod]; apply mul_le_of_le_one_left (by unfold Atom.magnitude; positivity); exact prod_le_one (fun x _=> abs_nonneg _) (fun j _=> shear_fit ..)
  have hh : ((cartoon P i).length:ℝ)≤ P.atom.length +8*k:=by exact_mod_cast cartoons P i
  refine (mul_le_mul hu (Real.exp_monotone (mul_le_mul_of_nonneg_left hh hs)) (Real.exp_pos _).le (by unfold Atom.magnitude; positivity)).trans_eq ?_
  unfold Atom.budget; rw [mul_add,Real.exp_add]; ring

def assembleP (P:I→Pattern G k)(p:I×BranchG k):= cartoon (P p.1) p.2
def expPrice (k:ℕ)(σ:ℝ):= (Fintype.card (BranchG k):ℝ)*Real.exp (σ*(8*k))
lemma assemble_symm (P:I→Pattern G k)(h:∀ p,(P p).atom.Invariant):SymmetricAtoms (assembleP P):=fun i=>relocated_symm _ (h _) _ _ _
lemma assembled {P:I→Pattern G k}(he:0 ≤σ)(h: Charged (fun i=>(P i).atom) σ A):Charged (assembleP P) σ (expPrice k σ * A):=by
  apply Cost.product (Cost.scale h (expPrice k σ) (by unfold expPrice; positivity))
  intro i; unfold expPrice; rw [mul_assoc]; exact cartoon_price (P i) he
lemma assemble_at {P:I→Pattern G k} (h:Charged (fun i=> (P i).atom) σ A)(he:0≤σ)(V:Flux G n): total (plain ∘ assembleP P) V=total P V:=by
  have H:= net_summable (plain ∘ assembleP P) V he (assembled he h)
  unfold total; rw [H.tsum_prod]; apply tsum_congr; intro i
  rw [tsum_fintype,sum_comm]; exact sum_congr rfl (fun x _=> (cartoon_sample (P i) V x).symm)

-- strict silence, useful also for graft to periodic counterterm estimates
lemma shell_cost (p : Option Axis) (h : p.isSome): ∑ i,shear p i=0:=by
  cases p <;> simp [shear] at *
lemma shell_silent (P: PairG G)(he: both P) : Silent (cartoon P):=by
  intro v d; let Q i j:= (P.atom.leg i).offset+pebble (P.op i) j; let a:= if (fun i=> (P.atom.leg i).plaq)=v then P.atom.coeff d else 0
  have hp (b:BranchG 2):charge (cartoon P b) v d=a*∏ j,shear (P.op j) (b j):=by unfold cartoon charge a relocate; dsimp only; rw [show (fun k=>(slot _ (P.atom.leg k).plaq).plaq)=(fun k=>(P.atom.leg k).plaq) from rfl]; split <;> simp [mul_comm]
  simp_rw [hp]; constructor
  · have hh:=hasSum_fintype (fun b:BranchG 2=> a*∏ j,shear (P.op j) (b j))
    rwa [← mul_sum,← Fintype.prod_sum,Fin.prod_univ_two,shell_cost _ (he 0),zero_mul,mul_zero] at hh
  intro d'
  have hm (j:Fin 2): HasSum (fun b:BranchG 2=> (a*∏ j,shear (P.op j) (b j))* ↑(Q j (b j) d')) 0:=by
    let g k (i:Bool):= if k=j then shear (P.op k) i * ↑(Q k i d') else shear (P.op k) i
    have heq (b:BranchG 2):(a*∏ k,shear (P.op k) (b k))* (↑(Q j (b j) d'):ℝ)=a*∏ k,g k (b k):=by fin_cases j <;> simp [g,Fin.prod_univ_two] <;> ring
    simp_rw [heq]
    have H:=hasSum_fintype (fun b:BranchG 2=> a*∏ k,g k (b k))
    rw [← mul_sum,← Fintype.prod_sum,Fin.prod_univ_two] at H
    have hv k (hp:k ≠ j): ∑ i, g k i=0:=by simp_rw [g,if_neg hp]; exact shell_cost _ (he k)
    rcases Fin.eq_zero_or_eq_succ j with hj|⟨l,hj⟩ -- inspect
    · rwa [hv 1 (by rw [hj]; decide),mul_zero,mul_zero] at H
    rwa [hv 0 (by rw [hj]; exact (Fin.succ_ne_zero _).symm),zero_mul,mul_zero] at H
  convert! (hm 1).sub (hm 0) using 1
  · ext p; simp only [delta,cartoon,relocate,slot_offset,Q,Pi.sub_apply,Int.cast_sub,mul_sub]
  simp
lemma assemble_silent {P:I→PairG G}(he: 0<σ)(hp:Palisade P σ A): Silent (assembleP P):=by
  intro i b; have hb := moments_summable he (assembled he.le hp.2.2) i b
  have heq (f:I×BranchG 2→ℝ)(hf: Summable f) (h:∀ i:I,HasSum (fun p=> f (i,p)) 0): HasSum f 0 :=by
    convert hf.hasSum using 1; rw [hf.tsum_prod]; simp_rw [(h _).tsum_eq]; rw [tsum_zero]
  exact ⟨heq _ hb.1 (fun j=> (shell_silent (P j) (hp.1 j) i b).1),fun x=> heq _ (hb.2 x) fun j=> (shell_silent (P j) (hp.1 j) i b).2 x⟩
end YM.QCD.Smoke
