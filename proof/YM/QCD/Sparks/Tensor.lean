import YM.QCD.Eyrie.Grain
import YM.Extra.ITERATION_NO_LOSS.Sums

/-! # Signed period roots. Raw row coefficients coherent, curvature not used yet -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Cost Run Revolve Metric Push.Uniform
open Eyrie Quarry Tree RG Precision Rudder Flume Pine YM.Next.Free Finset
open YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {c C n N: Side} {k m M:ℕ}

structure SparkMesh where
  n : ℕ→Side
  cofinal : Tendsto (fun x=> (n x).val) atTop atTop
  ratio (i j:ℕ):ℕ
  factor i j : i≤j→ (n j).val=(n i).val*ratio i j
  parity i j : i≤j → Odd (ratio i j)

namespace SparkMesh
variable (S:SparkMesh)
def vista (i j:ℕ)(h:i≤j):Window (S.n i) (S.n j) ((S.ratio i j)^4):= normal ⟨S.ratio i j,S.factor i j h⟩ (S.factor i j h)
abbrev Field := ∀ i:ℕ,Cnr (S.n i) → Sheet (S.n i)
end SparkMesh
abbrev Angle := Exterior.TypeFace 1
abbrev Nub := Cover×(Angle × su.ColorIndex)
abbrev Tilt (k:ℕ):= Cover × (Fin k→ Nub)
abbrev Typewriter (k:ℕ):= Tilt k→Bundle
abbrev Plane (n:Side) (k:ℕ):= Site n×(Fin k→Road n)
def down (n:Side)(v:Tilt k): Plane n k:= (wrap n v.1,Prod.map (wrap n) id ∘ v.2)
def up (n:Side)(p:Plane n k): Tilt k := (Lattice.lift p.1,Prod.map Lattice.lift id ∘ p.2)
lemma land (p: Plane n k):down n (up n p)=p:=by apply Prod.ext (wrap_lift ..); funext i; rcases p with ⟨p,P⟩; exact Prod.ext (wrap_lift ..) rfl
lemma safe (n):Injective (up (k:=k) n):= fun i j h=> (land i).symm.trans ((congr_arg _ h).trans (land j)) -- type?

def AtMap (n:Side)(p:Tilt k): Prop:= up n (down n p)=p
lemma ins (p : Plane n k): AtMap n (up n p):= congr_arg _ (land p)
-- verify Wind weighted sum eval

def timbre (a : Tilt k) := Laurent.size a.1+∑ j, Laurent.size (a.2 j).1
def aim (u:ℝ) (p:Tilt k):= Real.exp (-u*timbre p)
lemma aim_pos (u:ℝ)(p:Tilt k):0<aim u p:=Real.exp_pos _
lemma beam_bill (P:Tilt k)(r:ℝ): aim r P= Real.exp (-r*Laurent.size P.1)*∏ i, Real.exp (-r*Laurent.size (P.2 i).1):= by simp only [aim,timbre,Nat.cast_add,mul_add,Nat.cast_sum,mul_sum,Real.exp_add,Real.exp_sum]
set_option maxHeartbeats 25000 in
lemma aim_supply (k:ℕ){u:ℝ}(hp:0<u): Summable (aim (k:=k) u):=by
  let F (x:Cover):=Real.exp (-u*Laurent.size x)
  have he : Summable F:= (Laurent.Width.compactPay u hp).2.1
  have hh:Summable (fun i:Nub=> F i.1):=by
    rw [summable_prod_of_nonneg (fun i=> (Real.exp_pos _).le)]
    exact ⟨fun v=> Summable.of_finite,by simp_rw [tsum_fintype,sum_const,card_univ,nsmul_eq_mul]; exact he.mul_left _⟩
  have hv: Summable (fun p:Fin k→Nub=> ∏ j,F (p j).1):=(YM.Extra.Iteration.Cost.pi (A:=fun _=> ∑' i:Nub,F i.1) (fun j=>show SumBudget _ _ from ⟨fun i=> (Real.exp_pos _).le,hh,le_rfl⟩)).2.1 -- ambiguous
  rw [show aim (k:=k) u=(fun w:Tilt k=>F w.1* ∏ i,F (w.2 i).1) from funext fun w=> beam_bill w u]
  have h (p:Fin k→Nub):0 ≤ ∏ j,F (p j).1:=prod_nonneg (fun _ _=> (Real.exp_pos _).le)
  exact @paid_product Cover (Fin k→Nub) F (fun p=> ∏ j,F (p j).1) he (fun _=> (Real.exp_pos _).le) hv h

/-- derivative (integer factorial fee appears only in issue) -/
def DutyT (n : Side)(k:ℕ):= ContinuousMultilinearMap ℝ (fun _:Fin k=> Cnr n) (Sheet n)
abbrev trackG (n:Side):= Cnr n → Sheet n
def dotP (F: trackG n)(m:ℕ) (p: Plane n m):=
    Run.cell (entry F (0 : Cnr n) p.2) 0 p.1

def normedD (F:trackG n)(p:Plane n m):Bundle:= occ (0:Site n) (Lattice.lift p.1) • dotP F m p

def design (F:trackG n)(v:Tilt m): Bundle:= if AtMap n v then normedD F (down n v) else 0
lemma designer (F:trackG n)(p:Plane n m):design F (up n p)=normedD F p:=by rw [design,if_pos (ins _),land]
lemma city_length (x : Site n): Laurent.size (lift x) ≤ 4 * separation 0 x:=by
  rw [separation_comm,separation,sub_zero]; unfold Laurent.size
  calc _ ≤ ∑ i :Axis, pdist x := sum_le_sum fun i _=> component_le ..
       _ = _ := by simp [Axis]
end YM.QCD.Sparks
