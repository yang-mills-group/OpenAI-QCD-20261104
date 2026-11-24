import YM.Poised.Lit
import YM.MassiveQCD.Plate.Sight
/-!
# Price arbitrary spin substitutions & projection service
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k : ℕ}
namespace Beacon
variable (T:Taper)(H:TaperHol)(b : Cover)
local notation "F" => Lat.Fields c 6
local notation "G" => SpinPol d
local notation "N" => Pairs (SpinMode d)
local notation "P" => Pairs (Modes c 6)
open Creek
lemma length_pay (x:Cover) : ‖ap c x‖=1:=by unfold ap; simp
lemma spun_pay (y:Site c) : ‖spun T b y‖≤1:=by unfold spun; dsimp only; rw [norm_mul,length_pay,mul_one,Complex.norm_real, Real.norm_of_nonneg (T.interval _).1]; exact (T.interval _).2
lemma profile_pay (v:Multi d)(x: Site c): ‖profile v (offset b x) 1‖ ≤ (1+(separation x (wrap c b):ℝ))^ order (power v):=by
    let y:=x-wrap c b; let p:ℝ:=pdist y; let l:= 1+p -- edit
    rw [profile,Complex.norm_real, norm_mul,norm_prod]; simp only [one_pow,norm_one,one_mul]
    unfold order; rw [← prod_pow_eq_pow_sum]; apply prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>?_)
    let w:=power v i
    calc
       _ ≤ ‖((lift y i:ℤ):ℝ)‖^w :=by rw [norm_div,norm_pow]; exact div_le_self (pow_nonneg (norm_nonneg _) _) (by simp; exact Nat.factorial_pos _) -- syntax
       _ ≤ l^w :=by rw [← norm_natAbs,Real.norm_natCast]; gcongr; exact ((Nat.cast_le.mpr (component_le y i)).trans (by unfold l p; linarith))
lemma glow_pay (i:Modes c 6)(y:SpinMode d): ‖glow T b 1 i y‖ ≤ (1+(separation i.1.1 (wrap c b):ℝ))^d:=by
    unfold glow; dsimp only [Matrix.of_apply]; split; swap; · rw [norm_zero]; positivity
    rw [norm_mul]; exact ((mul_le_of_le_one_left (norm_nonneg _) (spun_pay T b i.1.1)).trans (profile_pay b y.1.1 i.1.1)).trans (pow_le_pow_right₀ (by simp) y.1.1.property)
local notation "C0"=> 1+(Fintype.card N:ℝ)
open Stew Cove
lemma allGlow (i:P) (j:N) : ‖Matrix.fromBlocks (glow T b 1) 0 0 (glow T b 1) i j‖ ≤ (1+(lens (wrap c b) i:ℝ))^d:=by
   rcases i with i|i <;> rcases j with j|j
   · exact glow_pay ..
   · rw [Matrix.fromBlocks_apply₁₂]; change ‖(0:ℂ)‖≤_; rw [norm_zero]; positivity
   · rw [Matrix.fromBlocks_apply₂₁]; change ‖(0:ℂ)‖≤_; rw [norm_zero]; positivity
   exact glow_pay ..
abbrev whisper (T:Taper)(b:Cover): F→ₐ[ℂ]G:= adapter (glow T b 1) (glow T b 1)
lemma atomGlow (i:P): ‖whisper T b (d:=d) (atom i)‖ ≤ C0*(1+(lens (wrap c b) i:ℝ))^d:=by
   unfold whisper adapter; rw [change_atom]; apply (norm_sum_le ..).trans; calc
      _≤ ∑ _j:N, (1+(lens (wrap c b) i:ℝ))^d:= Finset.sum_le_sum fun j _=> by rw [norm_smul,← mono_single j,norm_mono,mul_one]; exact allGlow T b i j
      _ ≤ _:=by rw [sum_const,card_univ,nsmul_eq_mul]; gcongr; linarith
lemma progresses (i : Finset P)(R:ℝ) (he:0≤R)(hg:∀ j∈i, ‖whisper (d:=d) T b (atom j)‖≤R): ‖whisper (d:=d) T b (mono i)‖ ≤ R^i.card:=by
   induction i using Finset.induction_on with
   | empty=> simp
   | insert k s h hp=>
       have hh : Disjoint {k} s:=by simp [h]
       have hv:= hp (fun v hv=> hg v (mem_insert_of_mem hv)); have hy:‖whisper (d:=d) T b (atom k)‖ ≤ R:=hg k (mem_insert_self ..)
       have ha : ‖whisper (d:=d) T b (atom k*mono s)‖ ≤ R^(insert k s).card:=by rw [map_mul,card_insert_of_notMem h,pow_succ',mul_comm R]; exact (norm_mul_le ..).trans ((mul_le_mul hy hv (norm_nonneg _) he).trans_eq (mul_comm ..))
       have hy:=mono_mul_sign _ _ hh; rw [mono_single,disjUnion_eq_union,Finset.singleton_union] at hy; rcases hy with hy|hy <;> rw [hy] at ha <;> simpa using ha
abbrev pick (d:ℕ):= Fintype.card (Pairs (SpinMode d))
def penny (d:ℕ):ℝ:= (1+(pick d:ℝ))^(pick d)
def surface (d:ℕ) := d * pick d
variable (v:ℝ)
lemma hush (x:Finset P)(hp:surface d ≤ k)(ht:0≤v): ‖engine v N (whisper T b (mono x))‖ ≤ penny d * toll (wrap c b) k x v :=by
   let g:=lens (wrap c b) («N»:=6); let ℓ:=1+(↑(x.sup g):ℝ); let R:= (1+(pick d:ℝ))*ℓ^d; let U:=whisper (d:=d) T b (mono x); have hx: U∈layer N x.card:= exterior_layer _ (Grass.homogeneous x)
   have hR: 0≤R:=by unfold R ℓ; positivity; -- don't engulf
   by_cases hv: x.card ≤ pick d; swap; · rw [nominate _ v _ hx,show U=0 from overflow hx (lt_of_not_ge hv)]; simp only [smul_zero,norm_zero]; unfold penny toll; positivity
   change ‖engine _ N U‖ ≤ _; rw [nominate U v _ hx,norm_smul,norm_pow, Complex.norm_real,Real.norm_of_nonneg ht]
   have hκ(j)(hi:j∈x): ‖whisper (d:=d) T b (atom j)‖≤R:= (atomGlow T b _).trans (by unfold R ℓ pick g; gcongr; exact Finset.le_sup (f:=g) hi)
   apply le_trans (mul_le_mul_of_nonneg_left (progresses T b x R hR hκ) (pow_nonneg ht _))
   rw [mul_comm]; unfold penny; unfold R; unfold surface at hp; rw [mul_pow,← pow_mul]; unfold toll; rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ (by simp) hv) ?_ ?_ (by positivity)) (pow_nonneg ht _)
   · apply pow_le_pow_right₀ (by simp only [ℓ,g]; simp); exact le_trans (Nat.mul_le_mul_left _ hv) hp
   unfold ℓ; positivity
lemma lots (x:F)(ht:0≤v)(hp:surface d ≤ k): ‖engine v N (whisper T b x)‖ ≤ penny d * view (wrap c b) k x v:=by
   conv_lhs => rw [←write x]; simp only [map_sum,map_smul]
   apply (norm_sum_le ..).trans; rw [view,mul_sum]; refine Finset.sum_le_sum fun i _=> ?_; rw [norm_smul]; exact (mul_le_mul_of_nonneg_left (hush T b v i hp ht) (norm_nonneg _)).trans_eq (by ring)
end Beacon
end YM.Massive.Poised
