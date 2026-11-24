import YM.QCD.Finch.Boat
import YM.QCD.Globe.Dome
import YM.QCD.Lunar.Musk
/-!
# Equivalence of different AP mass readings to first order, at identity field

For a five-real covariant momentum kernel with row estimates. Need no plane Fourier
transform of the entire kernel here; control the row mass (matrix in spin) of the
particular half mode. Uses actual AP seams (at zero), sensitivity to the winding reads
O(1/L). Precisely track both spin and color indices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe.HalfMass
open Lattice Wilson Lat Grass Flume Kit Run Sway Cove Stew Entr Port Finch
open Finset Function Filter
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side} {m j N:ℕ} {A Q B:ℝ} (X:Sheet c) (o:Site c) (s:Signed)

def straightRow : Bundle:= ∑ i:Site c, Stew.shine o i • cell X o i

def partRow : Bundle:= ∑ i:Site c, onset X o (Globe.foam s i)

lemma pivot : straightRow X o = partRow X o 1:=by
  unfold straightRow partRow; rw [← Equiv.sum_comp (Equiv.addLeft o) _]
  apply sum_congr rfl; intro i _; change shine o (o+i) • _ = _
  rw [foamy, onset, wrap_lift,signsH]; rfl

lemma row_value (h: Tempo X) : Fintype.card Signed • ((mass X:ℂ) • (1:Bundle))=∑ i:Signed, partRow X o i:=by
  let x:=h.night o; unfold Pina CoatM at x; simp only [Option.elim_none,wavS,one_smul, Lat.wave_one] at x
  rw [← x, ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α:=Signed))),one_smul]; unfold partRow; rw [sum_comm]

lemma bias_part (hm:1 ≤ m) (hp:Beam X m A) :
    (c.val:ℝ)*‖partRow X o s-straightRow X o‖ ≤ 20*A:=by
  let W(s:Signed)(v:Site c):= onset X o (Globe.foam s v); let Y(v:Site c):=costS m o (o+v)*‖cell X o (o+v)‖
  have hh(v:Site c): (c.val:ℝ)*‖W s v-W 1 v‖ ≤20 * Y v:=by
    by_cases h:10*pdist v < c.val
    · unfold W Y; rw [foam_near _ _ h,foamy,sub_self,norm_zero,mul_zero]; have hh:0 ≤ costS m o (o+v):=cost_nn ..; positivity
    let D:=pdist v; let k : Bundle:=cell X o (o+v); have hx : (c.val:ℝ) ≤10*D:=by unfold D; exact_mod_cast not_lt.mp h
    have he : ∀ j:Signed, ‖W j v‖=‖k‖:=fun i=>by unfold W onset k; rw [norm_smul, pathLength,foams,one_mul]; -- k in hyp matches
    have hz:(D:ℝ) ≤ costS m o (o+v):=by
        unfold costS separation; rw [show o-(o+v)= -v from (by abel),pdist_neg]
        apply le_trans (b:=1+(D:ℝ)) (le_add_of_nonneg_left zero_le_one)
        exact le_self_pow₀ (by unfold D; simp) (by omega)
    have hk: ‖W s v-W 1 v‖ ≤ 2*‖k‖:=(norm_sub_le ..).trans_eq (by rw [he,he,two_mul]);
    unfold Y; apply (mul_le_mul hx hk (norm_nonneg _) (by positivity : 0 ≤ (10*(D:ℝ)))).trans
    change _ ≤20 * (_* ‖k‖); linarith only [mul_le_mul_of_nonneg_right hz (norm_nonneg k)]
  rw [pivot]; unfold partRow; rw [← sum_sub_distrib]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> hh i).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left ((Equiv.sum_comp (Equiv.addLeft o) _).trans_le (hp.toR _)) (by norm_num) -- HO infer

lemma bias (hm:1 ≤ m) (hp:Beam X m A)(h:Tempo X) :
    (c.val:ℝ)*‖straightRow X o - (mass X:ℂ) • (1:Bundle)‖≤20*A:=by
   let z:ℝ:=Fintype.card Signed; have hz:0<z:=by unfold z; positivity
   let T:=straightRow X o; let Y:Bundle:= (mass X:ℂ) • 1;
   rw [norm_sub_rev]; apply le_of_mul_le_mul_left _ hz; have he : z*‖Y-T‖= ‖∑ i:Signed,(partRow X o i-T)‖:=by
     rw [sum_sub_distrib,sum_const,card_univ,← row_value X o h];
     rw [← nsmul_sub, ← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_of_nonneg hz.le]
   rw [mul_left_comm,he]
   apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> bias_part X o i hm hp).trans_eq; rw [sum_const,nsmul_eq_mul,card_univ]

variable (w:Site c → Site c → ℂ)
noncomputable abbrev amount (c:Side):ℝ:=c.val
local notation "σ"=>amount c

def Close (w:Site c→Site c→ℂ) (p:ℝ) : Prop:=∀ x y, amount c* ‖w x y-shine x y‖ ≤ p*(separation x y:ℝ)

def cashRow (o:Site c) : Bundle:=∑ i:Site c,w o i •cell X o i

lemma near (hm:1 ≤ m) (hQ:0≤Q) (h:Close w Q) (hp:Beam X m A)(hx:Tempo X) :
    amount c* ‖cashRow X w o-(mass X:ℂ) • (1:Bundle)‖ ≤ (Q+20)*A:=by
  have hc:0≤σ:= Nat.cast_nonneg _; let Y:= straightRow X o; rw [show (cashRow _ _ _)- _=(cashRow X w o-Y)+(Y-(mass X:ℂ) • (1:Bundle)) from by abel]; apply (mul_le_mul_of_nonneg_left (norm_add_le ..) hc).trans; rw [mul_add,add_mul]; apply add_le_add _ (bias ..);
  all_goals try assumption
  change σ*‖cashRow X w o-straightRow X o‖≤_; unfold straightRow cashRow; rw [← sum_sub_distrib]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) hc); rw [mul_sum]; apply le_trans _ (mul_le_mul_of_nonneg_left (hp.toR o) hQ); unfold Gan; rw [mul_sum]; refine sum_le_sum fun i _=>?_; rw [← sub_smul, norm_smul,← mul_assoc,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (h o i).trans; apply mul_le_mul_of_nonneg_left _ hQ; change (separation o i:ℝ) ≤ (1+↑(separation o i))^m; exact le_trans (le_add_of_nonneg_left zero_le_one) (le_self_pow₀ (by simp) (by omega))

def center := (↑(Fintype.card (Site c)):ℂ)⁻¹ • (∑ x:Site c,cashRow X w x)

lemma velocity (hm:1 ≤ m) (hQ:0≤Q) (h:Close w Q) (hp:Beam X m A)(hx:Tempo X) :
   amount c*‖center X w-(mass X:ℂ) • (1:Bundle)‖≤(Q+20)*A:=by
  let a:= Fintype.card (Site c); let Z:= (mass X:ℂ) • (1:Bundle); have h0:0<(a:ℝ):=by unfold a; positivity
  have he: a • (center X w-Z) = ∑ i:Site c,(cashRow X w i - Z):=by rw [smul_sub,sum_sub_distrib,sum_const,card_univ,center,←Nat.cast_smul_eq_nsmul ℂ, smul_smul,mul_inv_cancel₀ ?_,one_smul]; exact_mod_cast (Fintype.card_ne_zero (α:=Site c)) -- meta
  apply le_of_mul_le_mul_left _ h0; rw [mul_left_comm]; apply le_trans (b:=σ*‖∑ i:Site c,(cashRow X w i-Z)‖)
  · rw [← he,← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_of_nonneg h0.le];
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Nat.cast_nonneg _)).trans; rw [mul_sum]; apply (sum_le_sum fun i _=> near X i w hm hQ h hp hx).trans_eq; rw [sum_const, nsmul_eq_mul, card_univ]

lemma coat (hm:1 ≤ m) (hQ:0≤Q) (h:Close w Q) (hp:Beam X m A)(hx:Tempo X)(u:Lat.Fiber) : amount c*‖center X w u u - mass X‖≤(Q+20)*A:=by
  apply le_trans _ (velocity X w hm hQ h hp hx); apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _);
  convert Cost.north (center X w-(mass X:ℂ) • (1:Bundle)) u u using 1; rfl; simp
end YM.QCD.Globe.HalfMass
#print axioms YM.QCD.Globe.HalfMass.coat
