import YM.Intag.Dial
import YM.Oars.Canyon
/-!
# Registration purchases at EVERY slot. EXACT averaging over holes. no phase simpl.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory Finset RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open MassiveQCD.Cupola MassiveQCD.Sample
open scoped BigOperators Classical
namespace CardsT
open Column Massive.Patria.Rolls
variable (S:Scheme)(R:Side)(i k:ℕ){I:Type} [Fintype I]
variable (X:I→ Cover) (U:I→ Averaging)
-- recipe.Weight post chosen.Sell.S.Track singular cost proof independent of charges at EACH Step. Need signed linear.E across whole unions.
local notation "H" k:arg=> Hole I S i k
local notation "p" k:arg=> showX S i k X
local notation "T"=>link S i k X
set_option quotPrecheck false
local notation "L"=> (S.step k).L.val
local notation "Ω" u:arg=> MassiveQCD.Sample.LoomT.To T u
noncomputable def offset (u:H k)(t:H(k+1)):= showX S i (k+1) X t-L • showX S i k X u
lemma mail(u:H k)(t:H (k+1)) : showX S i (k+1) X t=L • (showX S i k X u)+offset S i k X u t:=by unfold offset; abel
-- Toe universe elimination.[DecidableEq] logistic.T.P hazard. keep explicit.
noncomputable def wΓ_T (g:H(k+1)→ H k→ℝ) (u:H k)(j:Ω u) := g j.val u -- h implicit print
-- choose merge deterministic weights. ticket.Count.Signed Lift.
private lemma collapse {A B Y:Type}[Fintype A][Fintype B][DecidableEq A][AddCommGroup Y][Module ℝ Y](f:B→A)(Q:B→ℝ)(F:A→Y) : ∑ i:B,Q i • F (f i) = ∑ i:A, (∑ j:B, if f j=i then Q j else 0) • F i:=by
      rw [sum_congr rfl (s₁:=univ (α:=A)) (g:=fun i=>∑ j:B,if f j=i then Q j • F i else (0:Y)) (by intro i _; rw [sum_smul]; refine sum_congr rfl fun j _=>?_ ; split <;> simp_all)] -- simp_arg
      rw [Finset.sum_comm]; apply sum_congr rfl; intro x _; rw [sum_eq_single (f x)]; simp; intro i _ h; simp [Ne.symm h]; intro h; exact False.elim (h (mem_univ _))
lemma purchase (hk:i≤k)(u:H k) : ∃ w:MassiveQCD.Sample.LoomT.To (link S i k X) u → ℝ, (∀ j,0 ≤ w j) ∧ (∑ i,w i)=1 ∧ Fans (U u.1) ((S.step k).L.val) w (fun j=> offset S i k X u j.val):=by
     let v:= U u.1; let Y:=Cover →₀ℝ
     obtain ⟨A,a1,a2,Q,t,hq,hP,hJ,h⟩:= ladder (menu v) (X:=Y) 0 (S.step k).L.property (widths_menu v)
     -- proof aptitude via roles
     choose Z h1 h2 using fun j:A => touch S i k X u (t j) hk ((hJ j).trans (Nat.mul_le_mul_right _ (length_menu v)))
     let f(j:A):MassiveQCD.Sample.LoomT.To T u:=⟨Z j,h1 j⟩; have hZ(j:A): offset S i k X u (f j).val=t j:=by unfold offset f; rw [h2 j,add_sub_cancel_left] -- dsimp Subtype
     let w (i:Ω u):= ∑ j:A,if f j=i then Q j else 0; refine ⟨w,fun i=> sum_nonneg (fun j _=> ite_nonneg (hq j) le_rfl),?_,?_⟩
     · rw [← hP]; exact Eq.symm (by simpa only [smul_eq_mul,mul_one,w] using (collapse f Q (fun _=> (1:ℝ))))
     intro x b; rw [roles]; change rolls _ _ (menu v) x b = _; refine (h x b).trans ?_; let F (i:Ω u):= x (b+offset S _ _ X u i.val)
     have hx(j): x (b+t j)= F (f j):= congr_arg x (congr_arg (b+·) (hZ j).symm)
     apply Eq.trans _ (collapse f Q F); exact sum_congr rfl fun i _=>by rw [hx]
-- unify all t.Choose g first.
structure SignedWeights (g:H(k+1)→ H k→ℝ): Prop where
     cash x y : 0 ≤ g x y
     bill u : (∑ i: MassiveQCD.Sample.LoomT.To (link S i k X) u,g i.val u)=1
     toll u : Fans (U u.1) (S.step k).L.val (fun j:Ω u=> g j.val u) (fun j=> offset S i k X u j.val)
lemma allS (hk:i≤k):∃ g:H(k+1)→ H k→ℝ,SignedWeights S i k X U g:=by
     choose w h hx hr using purchase S i k X U hk; let g : H(k+1)→ H k→ℝ:=fun x y=> if ht:T x y then w y ⟨x,ht⟩ else 0; have he(y)(x:Ω y):w y x=g x.val y:=by unfold g; rw [dif_pos x.property]
     refine ⟨g,⟨fun x y=> dite_nonneg (fun h'=> h y _) (fun _=>le_rfl),?_,?_⟩⟩
     · intro u; have hP:=hx u; simp_rw[he u] at hP; exact hP
     intro u; convert hr u using 1; ext x; exact (he _ _).symm
-- weights apply in *any* linear receptor. Source HW distribution not pre-cycle.
variable {Y:Type}[AddCommGroup Y][Module ℝ Y]
lemma rollsT (g:H(k+1)→ H k→ℝ)(h: SignedWeights S i k X U g)(u:H k)(Y':Cover→Y): Averaging.filter (U u.1) (S.step k).L.val Y' ((S.step k).L.val • showX S i k X u)=∑ j:Ω u,g j.val u • Y' (showX S i (k+1) X j.val):=by
     rw [ticket (U u.1) _ _ (h.toll u)]; exact sum_congr rfl (fun j _=> congr_arg (g j.val u •·) (congr_arg Y' (mail S i k X u j.val).symm))
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.rollsT
#print axioms YM.Intag.CardsT.purchase
#print axioms YM.Intag.CardsT.allS
