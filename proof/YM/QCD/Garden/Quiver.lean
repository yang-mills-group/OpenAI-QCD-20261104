import YM.QCD.Garden.Wave

/-! # whole-path weights from paid moment response -/
set_option autoImplicit false
set_option maxHeartbeats 35000
set_option synthInstance.maxHeartbeats 4000
noncomputable section
namespace YM.QCD.Garden
open Lat Kit Lattice Wilson Function Finset Filter Metric Tree RG Precision Bloch Laurent
open Orbit Flume Sparks Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder
open Extra Iteration Placement QCD.Run
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical Kronecker
variable {a b c f L:Side}{j k:ℕ}{P:Flight j k}{e:f.val=c.val*P.L.val}
def sheath (P:Flight j k)(r:Site P.L)(x:Cover):Bundle := Matrix.of fun i j=> fonts P [] r i j x
def fork (P:Flight j k)(r:Site P.L)(x:Cover):Bundle := stampC (sheath P r x)
def unFork (P:Flight j k)(r:Site P.L)(x:Cover):Bundle := flag g5 (star (fork P r x))
lemma pillar (P:Flight j k) (r:Site P.L)(x:Cover): fork P r x∈Moon:= moony _
lemma pillar_l (P:Flight j k) (r:Site P.L)(x:Cover):unFork P r x∈Moon:= moon_mul (moon_mul (moony _) (moon_star (pillar ..))) (by rw [wave_star]; exact moony _) -- flag order
lemma pack_funds (hj:4≤j)(hk:4≤k) : ∃ t A:ℝ,0<t∧0≤A∧ ∀ (P:Flight j k) (r:Site P.L), Width t (A*slope P.L/(P.L.val:ℝ)) (fork P r) ∧ Width t (A*slope P.L/(P.L.val:ℝ)) (unFork P r):=by
  obtain ⟨σ,C,hσ,hC,H⟩:=reserves_font hj hk
  obtain ⟨b,hb,K⟩:=float_norm
  let I:=Fiber×Fiber; let U:ℝ := Fintype.card I * C
  refine ⟨σ,‖stampC‖*(b*U),hσ,?_ ,fun P r=>?_⟩
  · unfold U I; positivity
  let F (x:I) (u:Cover):= ‖fonts P [] r x.1 x.2 u‖
  have he (x:I): RG.SumBudget (fun u=> Real.exp (σ * size u)*F x u) (C*slope P.L/(P.L.val:ℝ)):= by simpa only [List.length_nil,add_zero,pow_one] using! H P r [] (by simp) x.1 x.2 -- need simplify
  have hs : SumBudget (fun u=> ∑ i:I,Real.exp (σ * size u)* F i u) (U*slope P.L/(P.L.val:ℝ)):=by
    have hc : Summable (fun u=> ∑ i:I, Real.exp (σ * size u) * F i u):= summable_sum fun i _=> (he i).2.1
    refine ⟨fun i=>sum_nonneg (fun j _=> (he j).1 _),hc,?_⟩; rw [Summable.tsum_finsetSum (f:=fun i u=> Real.exp (σ*size u)*F i u) fun i _=>(he i).2.1]; apply (sum_le_sum fun i _=> (he i).2.2).trans; unfold U; simp only [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by ring)
  have hx (x:Cover) : ‖sheath P r x‖≤ b*∑ i:I,F i x:=by
    have ha (i:I): 0≤ F i x:=norm_nonneg _; apply K _ _ (sum_nonneg fun i _=>ha i)
    intro i j; change F (i,j) x≤_; exact single_le_sum (s:=univ) (f:=fun i=>F i x) (fun i _=>ha i) (mem_univ (α:=I) (i,j))
  have hu : Width σ (‖stampC‖*(b*U)*slope P.L/(P.L.val:ℝ)) (fork P r):=by
    have ht:= Iteration.Cost.scale hs (‖stampC‖ * b) (mul_nonneg (norm_nonneg stampC) hb)
    refine Iteration.Cost.enlarge (Iteration.Cost.mono ht (fun u=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (fun u=>?_)) (le_of_eq (by ring))
    rw [← mul_sum]; calc
      _ ≤ Real.exp (σ*size u) * (‖stampC‖*(b*∑ i:I,F i u)):= mul_le_mul_of_nonneg_left ((stampC.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hx u) (norm_nonneg stampC))) (Real.exp_pos _).le
      _ = _:=by ring
  exact ⟨hu, Iteration.Cost.mono hu (fun u=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (fun u=>mul_le_mul_of_nonneg_left ((pays_five _ g5_unit _).trans_eq (norm_star (fork P r u))) (Real.exp_pos _).le)⟩

-- reporting cells
variable (x y: Site c)(r:Site P.L)
def caption (P:Flight j k)(e:f.val=c.val*P.L.val)(R:Bundle)(x y:Site c)(r:Site P.L)(u:Cover):Bundle:= if x+wrap c u=y then (occ ((sliceL P e).embed x) (lift r)*occ x u) • R else 0
lemma pepper (hj:4≤j)(hk:4≤k) : HasSum (fun u=>caption P e (fork P r u) x y r u) (cell (proton P e) ((sliceL P e).assemble (x,r)) y):=by
  let ζ:=occ ((sliceL P e).embed x) (lift r)
  have H : HasSum (fun u=> caption P e (sheath P r u) x y r u) (cell (proton P e) ((sliceL P e).assemble (x,r)) y):=by
    refine Pi.hasSum.mpr (fun i => Pi.hasSum.mpr (fun j=>?_))
    obtain ⟨σ,C,hσ,hC,H⟩:=reserves_font hj hk
    have he:= (splash_budget x y (((H P r [] (by simp) i j).unweighted hσ.le).2.1)).of_norm.hasSum.mul_left ζ
    convert! he using 1
    · funext u; by_cases h:x+wrap c u=y <;> simp only [caption,h, Matrix.smul_apply,Matrix.zero_apply, ↓reduceIte,sheath,Matrix.of_apply,splashL, mul_zero]; ring
    change proton P e ((sliceL P e).assemble (x,r),i) (y,j)=_
    rw [show proton P e=printed P e [] from eligible P e hj hk [] (by simp)]; exact prints ..
  have hi := stampC.hasSum H
  rw [show stampC _ = cell (proton P e) _ _ from harbor (Sun.palette ..)] at hi
  have h (u:Cover) : (stampC (caption P e (sheath P r u) x y r u))=caption P e (fork P r u) x y r u:=by unfold caption fork; split <;> simp
  simp_rw [h] at hi; exact hi
lemma halo (M:Rail a b)(i j) :cell (chirality a*M*chirality b) i j=Lat.wave g5 *cell M i j*Lat.wave g5:=by
  have ht (m:Side) (i j:Site m):cell (chirality m) i j=if i=j then Lat.wave g5 else 0:=by
    split_ifs with hi; · subst j; ext; simp [Run.cell,chirality,onSpin,Lat.wave,rr]
    ext; simp [Run.cell,chirality,onSpin,rr,hi]
  rw [cell_mul]; simp_rw [ht]; rw [sum_eq_single j]
  · rw [if_pos rfl,cell_mul]; simp_rw [ht]; simp
  · intro z _ hi; rw [if_neg hi,mul_zero]
  simp
lemma unPepper (A:Plan j)(hj:4≤j)(hk:4≤k): HasSum (fun u=> caption P e (unFork P r u) x y r u) (cell (barP P e) y ((sliceL P e).assemble (x,r))):=by
  have he:=((((pepper (P:=P) (e:=e) x y r hj hk).star).mul_left (Lat.wave g5)).mul_right (Lat.wave g5))
  rw [rotateP A, halo,cell_flip]
  have heq u : Lat.wave g5 * star (caption P e (fork P r u) x y r u) * Lat.wave g5 =caption P e (unFork P r u) x y r u:=by
    unfold caption unFork; split
    · rw [star_smul]; unfold flag; rw [star_mul,Matrix.mul_smul,Matrix.smul_mul,wave_star,g5_star,show star (occ x u)=occ x u from (realSeam ..).1,show star (occ _ (lift r))= _ from (realSeam ..).1, mul_comm (occ x u)]; rfl
    simp
  simp_rw [heq] at he; exact he
end YM.QCD.Garden
