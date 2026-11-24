import YM.QCD.Brick.Glitter
import YM.Next.RANK.LineBox
/-! # Leading moment proof uses true flavor-vacuum and Warrant. Matrices rather than coefficients of local paths, pays cancellations for all endpoints. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open Revolve AnalyticBridge.VerifiedReset
open scoped BigOperators Topology ContDiff Classical Matrix
variable {f c : Side} {N n:ℕ} {p b r v :ℝ}{X:Support f}(o:Site f)
-- freight null shelves
open scoped Matrix.Norms.L2Operator
local notation "Ω"=> EvenA f N
def locQ (A:SampleX)(M:Lat.Sheet f): Bundle:=∑ i,∑ j, (shine o i*shine o j*mark o A i j) • cell M i j
lemma locales {A:Ω} (h:Fit A) (b: Flavor N) (B:SampleX)(i j:Note N):flowN o (grasp A.val) i j B= if i.2=j.2 then locQ o B (feeF b A) i.1 j.1 else 0:=by
   unfold flowN; simp only [signN]; rw [legal A h b]; by_cases he:i.2=j.2
   · rw [if_pos he]; unfold locQ; simp_rw [Matrix.sum_apply]; refine sum_congr rfl fun x _=>sum_congr rfl (fun y _=>?_)
     unfold copies; rw [Matrix.blockDiagonal_apply,if_pos (show (placeQ x i).2=(placeQ y j).2 from he), Matrix.smul_apply]; unfold cell; change _* (_* _)=(shine o x* shine o y*_) * _; simp [placeQ]; ring
   rw [if_neg he]; apply sum_eq_zero; intro x _; apply sum_eq_zero; intro y _; rw [copies,Matrix.blockDiagonal_apply,if_neg (show ¬ (placeQ x i).2=(placeQ y j).2 from he), mul_zero,mul_zero]
lemma decbr (A: Grid f→ Ω)(hp:Fit (A 1))(hv:shadeG A)(b:Flavor N)(p:SampleX)(ht:Stew.shape o (feeF b (A 1)) p=0) : locQ o p (feeF b (A 1))=0:=by
    let M:= A 1; have he(i j): cell (feeF b M) i j=Stew.goldW (Stew.gold (cell (feeF b M) i j)):= known A hv hp b i j
    have hx:locQ o p (feeF b M)=Stew.goldW (shape o (feeF b M) p):=by unfold locQ Stew.shape; simp_rw [map_sum,map_smul]; refine sum_congr rfl fun i _=>sum_congr rfl (fun j _=>?_) ; rw [← he]
    exact hx.trans (ht ▸ Stew.goldW.map_zero) -- check transport
lemma neon (A: Grid f→ Ω)(hp:Fit (A 1))(hv:shadeG A)(b:Flavor N)(ht:∀ p,shape o (feeF b (A 1)) p=0) : lights o true (grasp (A 1).val):= by
    have hx x y z : flowN o (grasp (A 1).val) x y z=0:=by rw [locales o hp b,decbr o A hp hv b z (ht z)]; split <;> rfl
    intro i j; exact ⟨hx ..,fun _ p=>hx ..⟩
lemma hoopG (A: Grid f→ Ω)(hp:∀ V,Fit (A V))(hv:shadeG A)(b:Flavor N)(U:Grid f)(X:Frame f): feeF b (A (gauge X U))=siteRot X * feeF b (A U)*star (siteRot X):=by
    let P:= siteRot X; have hp':feeF b (A U)=star P* feeF b (A (gauge X U))*P:=
       let h: A U=sways (Lat.copies N P) (A (gauge X U)) := Subtype.ext (hv U X).symm
       ((congr_arg (feeF b) h).trans (rite _ _ _ (hp _)))
    rw [hp']; rw [← Matrix.mul_assoc,← Matrix.mul_assoc, show _*star P=1 from (siteRot_u X).2,one_mul,Matrix.mul_assoc _ _ (star _),show P*star (siteRot X)=1 from (siteRot_u X).2,mul_one]
lemma onion (i j:Site c):∃ L: Sheet c→L[ℂ]Bundle, (∀ Q,L Q=cell Q i j):=by refine ⟨LinearMap.toContinuousLinearMap { toFun:=fun Q=>cell Q i j,map_add':=fun x y=>rfl,map_smul':=fun c x=>rfl }, fun i=>rfl⟩
noncomputable def leadC (i j: Site f)(b:Flavor N):EvenA f N→L[ℝ] Bundle:= ContinuousLinearMap.restrictScalars ℝ ((Classical.choose (onion i j)).comp (meter b))
lemma leadingC (i j : Site f)(b: Flavor N)(X:Ω): leadC i j b X=cell (feeF b X) i j:= (Classical.choose_spec (onion i j)) ((meter b) X)
end YM.QCD.Brick
