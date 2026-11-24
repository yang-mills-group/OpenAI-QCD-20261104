import Mathlib

/-! Regulator-independent form of the accepted six-flavor least-squares fit.
The mass, objective, and Fit definitions are copied from `YM.Massive.Spec.Mass`.
The arithmetic declarations are copied from `YM.Massive.PCAC.Fit` (SHA-256
d248b2f9199772c645c3db337e884c7acb71ab935c408aa7ff6f547c72c17938). These modules originally imported a second, incompatible Wilson project.
The namespace below allows the same arithmetic to be used by either project. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveCompletion.SixFit
open Finset
open scoped Topology BigOperators

abbrev Mass := Fin 6 → ℝ
abbrev PairMass := Fin 6 → Fin 6 → ℝ

def objective (b : PairMass) (m : Mass) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (b i j - (m i + m j))^2

def Fit (b : PairMass) (m : Mass) : Prop := ∀ x, objective b m ≤ objective b x

namespace Squares
variable (ι : Fin 6) (Q: PairMass) (μ : Mass)

def fitted (μ:Mass):PairMass:=fun i j=> μ i+μ j
def patch (b: PairMass) (p : Fin 6):= ∑ j ∈ univ.erase p,b p j
def average (b: PairMass) : Mass:=fun p=> (patch b p - (∑ i, patch b i)/10)/4
lemma folds : ∑ j ∈ (univ.erase ι), ((μ ι)+μ j)=4*μ ι+∑ i, μ i :=by
  rw [sum_add_distrib, sum_const]; have hh : ∑ i∈ univ.erase ι, μ i=∑ i, μ i-μ ι:=sum_erase_eq_sub (mem_univ _);
  rw [hh,card_erase_of_mem (mem_univ _), card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; ring -- inspect
lemma common : ∑ i, average Q i=(∑ i,patch Q i)/10:=by
  unfold average; rw [← sum_div,sum_sub_distrib,sum_const]; simp only [nsmul_eq_mul, card_univ,Fintype.card_fin]; ring
lemma ready (i): patch Q i= patch (fitted (average Q)) i:=by
  rw [show patch (fitted (average Q)) i= _ from folds i _,common]; unfold average; ring
lemma onFull (b: PairMass) : patch b ι+b ι ι=∑ i,b ι i:= by unfold patch; exact sum_erase_add _ _ (mem_univ _)
lemma switch (b:PairMass): ∑ i, patch b i=∑ i, patch (fun x y => b y x) i:=by
  apply add_right_cancel (b:=∑ i,b i i); simp_rw [← sum_add_distrib ,onFull _ b,show ∀ i,patch (fun x y=> b y x) i+b i i=∑ j,b j i from fun _=> onFull _ _]; -- wrong
  exact sum_comm
lemma deviation (i j : Fin 6) (μ m: Mass) :
    (Q i j-fitted (μ+m) i j)^2=(Q i j - fitted μ i j)^2+-2*(Q i j - fitted μ i j)*fitted m i j+(fitted m i j)^2 :=by unfold fitted; simp only [Pi.add_apply]; ring
lemma exact_fit (h:∀ i j,i≠ j → Q i j=Q j i) (p:Mass): objective Q (average Q+p)=objective Q (average Q)+∑ i, patch (fun i j=>(p i+p j)^2) i :=by
  let u:=fitted (average Q); let r:= Q-u
  have he(i) : ∑ j∈univ.erase i,r i j=0:=by unfold r; simp_rw [Pi.sub_apply]; rw [sum_sub_distrib]; exact sub_eq_zero.mpr (ready ..) -- fix
  have hp(i j): r i j=r j i:=by by_cases hi:i=j; · rw [hi];
                                simp only [r,Pi.sub_apply]; rw [h i j hi]; exact congr_arg _ (add_comm ..)
  have hv (i j : Fin 6) : -2 * r i j*(p i+p j) = (-2*p i)*r i j + (-2*p j)*r i j :=by ring
  have hx : ∑ i : Fin 6, (∑ j∈ univ.erase i, (-2*p i)*r i j)=0:=by simp_rw [← mul_sum,he]; simp
  have hh : ∑ i : Fin 6,(∑ j∈ univ.erase i, (-2*p j)*r i j)=0:=by
    rw [show ∑ i, (∑ j∈ univ.erase i,(-2*p j)*r i j)= ∑ i, (∑ j∈ univ.erase i, (-2*p i)*r j i) from switch _]; conv_lhs => arg 2; intro i; arg 2; intro j; rw [hp j i];
    exact hx
  unfold objective patch; simp_rw [show ∀ i j, (Q i j-( (average Q+p) i+(average Q+p) j))^2=(Q i j- (average Q i+average Q j))^2+-2*r i j*(p i+p j)+(p i+p j)^2 from fun i j=>deviation Q i j (average Q) p,hv,sum_add_distrib,hx,hh]; abel
lemma measure (x : Mass):0≤ ∑ i, patch (fun i j=> (x i+x j)^2) i := sum_nonneg fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _)
lemma fit (h:∀ i j,i≠ j → Q i j=Q j i): Fit Q (average Q):= by intro x; have ht:= exact_fit Q h (x-average Q); rw [add_sub_cancel ..] at ht; rw [ht]; exact le_add_of_nonneg_right (Squares.measure _)
lemma unique (h: ∀ i j, i≠ j→Q i j=Q j i)(hv:Fit Q μ): μ=average Q:=by
  let p:=μ-average Q; have he: average Q+p=μ:=add_sub_cancel ..; rw [← he] at hv; have hf:=hv (average Q); rw [exact_fit Q h] at hf
  have hp := show ∑ i, patch (fun i j=> (p i+p j)^2) i=0 from le_antisymm (by linarith) (Squares.measure _)
  have hx (i j:Fin 6)(h:i≠j) : p i+p j=0:=by
    have ht:(p i+p j)^2≤0:=by rw [← hp]; exact (single_le_sum (f:=fun j=>(p i+p j)^2) (fun k _=>sq_nonneg _) (show j ∈ univ.erase i by simpa using Ne.symm h)).trans (single_le_sum (f:=fun i=> patch (fun i j=> (p i+p j)^2) i) (fun i _=> sum_nonneg fun _ _=> sq_nonneg _) (mem_univ i))
    nlinarith only [ht]
  have hy : p 0=0 :=by linarith only [hx 0 1 (by decide),hx 0 2 (by decide), hx 1 2 (by decide)]
  have ht : p=0:=by
    ext i; by_cases h:i=0
    · subst i; exact hy
    change p i=0; linarith only [hx i 0 h,hy]
  rw [ht,add_zero] at he; exact he.symm
lemma near (ε : ℝ) (he : ∀ i j, i≠j→ |Q i j-(μ i+μ j)|≤ε) : |average Q ι-μ ι|≤ 2*ε :=by
  let P:=∑ i,μ i; have h (i : Fin 6) : |patch Q i - (4*μ i+P)| ≤ 5*ε :=by
    unfold patch; rw [show 4*μ i+P=_ from (folds i μ).symm, ← sum_sub_distrib];
    apply (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun j (hj:j∈univ.erase i)=> he i j (Ne.symm (ne_of_mem_erase hj)))).trans_eq ?_); simp
  have hp : (∑ i, (4*μ i+P))=10*P:=by rw [sum_add_distrib,← Finset.mul_sum]; simp; unfold P; ring
  have ht : |(∑ i,patch Q i)-10*P| ≤ 30*ε:=by rw [← hp,← sum_sub_distrib]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=> h i)).trans_eq ?_); simp; ring
  rw [abs_le] at ht ⊢; specialize h ι; rw [abs_le] at h; unfold Squares.average; constructor <;> linarith
end Squares
end YM.MassiveCompletion.SixFit
