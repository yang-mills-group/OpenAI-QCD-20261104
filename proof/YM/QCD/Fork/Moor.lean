import YM.QCD.Fork.Seal
import YM.QCD.Fork.Ridge
import YM.Work.E04
/-! # central row alpha including poly endpoint moments for tall Prairie -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fork
open Lat Kit Lattice Wilson RG Run Leaf Tee Function Finset Metric Filter
open Orbit Flume Sparks Quarry Pine QCD.Cost Eyrie Revolve Rudder Garden
open YM.Next.Free Laurent
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {I V:Type*}{Y:HSMul I V V}{L f c:Side}{t p η ξ w R u v C D G:ℝ}{B b j k m:ℕ}{F:Flight j k}{P:Plan j} {e:f.val=c.val*F.L.val}
local notation "S"=> sliceL F e
lemma duration (x:Site c)(u:Cover) : separation x (x+wrap c u)≤ size u:=by
 rw [separation_comm,separation,add_comm x,add_sub_cancel_right]; apply YM.Work.E01.pdist_wrap_le; rw [box_test]; constructor
 all_goals
   intro i; have h:= single_le_sum (s:=univ) (f:=fun i=> (u i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i); change (u i).natAbs ≤size u at h; omega

lemma eats (k:ℕ)(η:ℝ)(he:0<η): ∃ c:ℝ, 0<c∧∀ (n:ℕ),(1+n:ℝ)^k ≤ c*Real.exp (η*n):=by
  let f:= YM.Next.Scheduling.decay k η; have h:= YM.Next.Scheduling.decay_summable k η he; have he (i): 0<f i:=by unfold f YM.Next.Scheduling.decay; positivity
  have hp i : f i≤∑' i,f i:=h.le_tsum _ fun i _=> (he i).le
  refine ⟨∑' i,f i,(he 0).trans_le (hp 0),fun i=>?_⟩
  apply (div_le_iff₀ (Real.exp_pos _)).1; simpa only [f,YM.Next.Scheduling.decay,neg_mul,Real.exp_neg, add_comm (↑i:ℝ),div_eq_mul_inv] using hp i
lemma scales (x:Site c)(p:Site F.L)(A:Cover→Bundle)(l:ℕ)(hu: ∀ i:ℕ,(1+i:ℝ)^l ≤ D*Real.exp (η*i)) (he:0<D)(ht:Width η C A)(T: Site c→Bundle)(h:∀ y,HasSum (fun z=> caption F e (A z) x y p z) (T y)): ∑ y:Site c,(1+(separation x y:ℝ))^l * ‖T y‖ ≤ D*C:=by
  have hh y := (h y).summable.norm.mul_left ((1+(separation x y:ℝ))^l)
  refine le_trans (sum_le_sum (s:=univ) (g:=fun y=>∑' z, (1+(separation x y:ℝ))^l* ‖caption F e (A z) x y p z‖) (fun y _=> ?_)) ?_
  · rw [tsum_mul_left]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← (h y).tsum_eq]; exact norm_tsum_le_tsum_norm (h y).summable.norm
  have hP:=summable_sum (s:=univ) (f:=fun y z=> (1+(separation x y:ℝ))^l* ‖caption F e (A z) x y p z‖) (fun y _=> hh y)
  rw [← Summable.tsum_finsetSum (fun y _=>hh y)]
  apply (Summable.tsum_le_tsum ?_ hP (ht.2.1.mul_left D)).trans
  · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left ht.2.2 he.le
  intro z; rw [sum_eq_single (x+wrap c z)]; rotate_left
  · intro i _ hi; unfold caption; rw [if_neg hi.symm,norm_zero,mul_zero]
  · simp
  unfold caption; rw [if_pos rfl,norm_smul,norm_mul]; simp_rw [Flume.pathLength]; simp only [one_mul]; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply le_trans _ (hu (size z)); gcongr; exact_mod_cast duration x z

def meets (r : Ratio c f)(o : Site f)(k:ℕ)(x:Site c):ℝ:= (1+(separation (r.parent o) x:ℝ))^k
lemma meets_nn (r:Ratio c f)(o:Site f)(k:ℕ)(x:Site c): 0≤ meets r o k x:=by unfold meets; positivity
lemma sizesP (P:Plan j)(hj:4≤j)(hk:4≤k)(l:ℕ): ∃ C:ℝ,0≤ C∧∀ (F:Flight j k)(f c:Side)(e:f.val=c.val*F.L.val)(o:Site f), (∑ i:Site c,meets (sliceL F e) o l i * ‖cell (proton F e) o i‖) ≤ C*slope F.L/(F.L.val:ℝ) ∧ ∑ i:Site c,meets (sliceL F e) o l i* ‖cell (barP F e) i o‖ ≤ C*slope F.L/(F.L.val:ℝ):=by
  obtain ⟨u,a,hu,hv,h⟩:= pack_funds hj hk; obtain ⟨Q,hQ,H⟩:=eats l u hu
  refine ⟨Q*a,mul_nonneg hQ.le hv,fun F f c e o=>?_⟩
  let r:= sliceL F e; let w:=r.residue o; let x:=r.parent o; have hp:r.assemble (x,w)=o:= r.unpack_at o -- check
  obtain ⟨h₁,h₂⟩:= h F w; have hz i:=pepper (e:=e) x i w hj hk; have hb i:=unPepper (e:=e) x i w P hj hk; unfold r at hp; simp_rw [hp] at hz hb
  rw [mul_assoc,mul_div_assoc]; exact ⟨scales x w _ l H hQ h₁ _ hz, scales x w _ l H hQ h₂ _ hb⟩
end YM.QCD.Fork
